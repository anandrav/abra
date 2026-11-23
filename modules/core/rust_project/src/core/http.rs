/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use abra_core::vm::AbraInt;
use bytes::Bytes;
use reqwest::{Client, Method, RequestBuilder, Response as ReqwestResponse};
use tokio::runtime::{Builder, Runtime};
use tokio::sync::{mpsc, oneshot};
use tokio::task::AbortHandle;

use super::from_bytes;
use crate::ffi::core::http::{HttpError, HttpStream, Response, StreamingResponse};

fn runtime() -> Result<&'static Runtime, HttpError> {
    static RUNTIME: OnceLock<Result<Runtime, std::io::Error>> = OnceLock::new();
    match RUNTIME.get_or_init(|| {
        Builder::new_multi_thread()
            .worker_threads(1)
            .enable_all()
            .build()
    }) {
        Ok(runtime) => Ok(runtime),
        Err(error) => Err(HttpError::Other(error.to_string())),
    }
}

fn client() -> Result<&'static Client, HttpError> {
    static CLIENT: OnceLock<Result<Client, reqwest::Error>> = OnceLock::new();
    match CLIENT.get_or_init(|| Client::builder().build()) {
        Ok(client) => Ok(client),
        Err(error) => Err(HttpError::Other(error.to_string())),
    }
}

fn http_err(e: reqwest::Error) -> HttpError {
    let msg = e.to_string();
    if e.is_timeout() {
        HttpError::Timeout(msg)
    } else if e.is_connect() || e.is_request() {
        HttpError::ConnectionFailed(msg)
    } else {
        HttpError::Other(msg)
    }
}

fn duration(seconds: f64) -> Result<Duration, HttpError> {
    let duration = Duration::try_from_secs_f64(seconds).map_err(|_| {
        HttpError::Other("timeout must be a positive, finite number of seconds".to_string())
    })?;
    if duration.is_zero() {
        return Err(HttpError::Other(
            "timeout must be greater than zero".to_string(),
        ));
    }
    Ok(duration)
}

fn build_request(
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    query: Vec<(String, String)>,
) -> Result<RequestBuilder, HttpError> {
    let method = Method::from_bytes(method.as_bytes())
        .map_err(|error| HttpError::Other(error.to_string()))?;
    let mut request = client()?.request(method, &url).query(&query);
    for (name, value) in headers {
        request = request.header(name, value);
    }
    if let Some(body) = body {
        request = request.body(body);
    }
    Ok(request)
}

fn response_headers(response: &ReqwestResponse) -> Vec<(String, String)> {
    response
        .headers()
        .iter()
        .filter_map(|(name, value)| {
            value
                .to_str()
                .ok()
                .map(|value| (name.to_string(), value.to_string()))
        })
        .collect()
}

pub fn get(
    url: String,
    timeout: f64,
    headers: Vec<(String, String)>,
    query: Vec<(String, String)>,
) -> Result<Response, HttpError> {
    send_request("GET".to_string(), url, headers, None, timeout, query)
}

pub fn post(
    url: String,
    body: String,
    timeout: f64,
    headers: Vec<(String, String)>,
    query: Vec<(String, String)>,
) -> Result<Response, HttpError> {
    send_request("POST".to_string(), url, headers, Some(body), timeout, query)
}

pub fn send_request(
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout: f64,
    query: Vec<(String, String)>,
) -> Result<Response, HttpError> {
    let timeout = duration(timeout)?;
    runtime()?.block_on(async {
        let response = build_request(method, url, headers, body, query)?
            .timeout(timeout)
            .send()
            .await
            .map_err(http_err)?;
        let status = response.status().as_u16() as AbraInt;
        let headers = response_headers(&response);
        let body = response.text().await.map_err(http_err)?;
        Ok(Response {
            status,
            body,
            headers,
        })
    })
}

struct ReadCommand {
    max_bytes: usize,
    timeout: Option<Duration>,
    reply: oneshot::Sender<Result<Option<Vec<u8>>, HttpError>>,
}

// Read only when requested, keeping slow consumers from buffering the whole body.
struct Stream {
    commands: mpsc::Sender<ReadCommand>,
    task: AbortHandle,
}

fn streams() -> &'static Mutex<HashMap<AbraInt, Arc<Stream>>> {
    static STREAMS: OnceLock<Mutex<HashMap<AbraInt, Arc<Stream>>>> = OnceLock::new();
    STREAMS.get_or_init(|| Mutex::new(HashMap::new()))
}

pub fn send_request_streaming(
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout: f64,
    query: Vec<(String, String)>,
) -> Result<StreamingResponse, HttpError> {
    let timeout = duration(timeout)?;
    runtime()?.block_on(async {
        let response = tokio::time::timeout(
            timeout,
            build_request(method, url, headers, body, query)?.send(),
        )
        .await
        .map_err(|_| HttpError::Timeout("timed out waiting for response headers".to_string()))?
        .map_err(http_err)?;
        let status = response.status().as_u16() as AbraInt;
        let headers = response_headers(&response);
        let (commands, receiver) = mpsc::channel(1);
        let task = tokio::spawn(read_stream(response, receiver));
        static NEXT_ID: AtomicI64 = AtomicI64::new(1);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        streams().lock().unwrap().insert(
            id,
            Arc::new(Stream {
                commands,
                task: task.abort_handle(),
            }),
        );
        Ok(StreamingResponse {
            status,
            headers,
            body: HttpStream { id },
        })
    })
}

async fn read_stream(mut response: ReqwestResponse, mut commands: mpsc::Receiver<ReadCommand>) {
    let mut pending = Bytes::new();
    while let Some(command) = commands.recv().await {
        let read = async {
            while pending.is_empty() {
                match response.chunk().await.map_err(http_err)? {
                    Some(chunk) => pending = chunk,
                    None => return Ok(None),
                }
            }
            let size = command.max_bytes.min(pending.len());
            Ok(Some(pending.split_to(size).to_vec()))
        };
        let result = if let Some(timeout) = command.timeout {
            match tokio::time::timeout(timeout, read).await {
                Ok(result) => result,
                Err(_) => Err(HttpError::Timeout("stream read timed out".to_string())),
            }
        } else {
            read.await
        };
        let finished = matches!(&result, Ok(None) | Err(_));
        let _ = command.reply.send(result);
        if finished {
            break;
        }
    }
}

pub fn http_stream_read_chunk(
    id: AbraInt,
    max_bytes: AbraInt,
    timeout: Option<f64>,
) -> Result<Option<Vec<AbraInt>>, HttpError> {
    let max_bytes = usize::try_from(max_bytes)
        .ok()
        .filter(|size| *size > 0)
        .ok_or_else(|| HttpError::Other("max_bytes must be greater than zero".to_string()))?;
    let timeout = timeout.map(duration).transpose()?;
    let stream = streams()
        .lock()
        .unwrap()
        .get(&id)
        .cloned()
        .ok_or_else(|| HttpError::Other("HTTP stream is closed".to_string()))?;
    let (reply, receiver) = oneshot::channel();
    let result = stream
        .commands
        .blocking_send(ReadCommand {
            max_bytes,
            timeout,
            reply,
        })
        .map_err(|_| HttpError::Other("HTTP stream is closed".to_string()))
        .and_then(|()| {
            receiver
                .blocking_recv()
                .map_err(|_| HttpError::Other("HTTP stream is closed".to_string()))?
        });
    if matches!(&result, Ok(None) | Err(_)) {
        streams().lock().unwrap().remove(&id);
    }
    result.map(|chunk| chunk.map(|bytes| from_bytes(&bytes)))
}

pub fn http_stream_close(id: AbraInt) -> Result<(), HttpError> {
    if let Some(stream) = streams().lock().unwrap().remove(&id) {
        stream.task.abort();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc as sync;

    #[test]
    fn blocked_reads_allow_other_streams_and_close() {
        let runtime = runtime().unwrap_or_else(|_| panic!("HTTP runtime failed"));
        let (commands, mut receiver) = mpsc::channel::<ReadCommand>(1);
        let (started, start_receiver) = sync::channel();
        let task = runtime.spawn(async move {
            let command = receiver.recv().await.unwrap();
            started.send(()).unwrap();
            std::future::pending::<()>().await;
            drop(command);
        });
        streams().lock().unwrap().insert(
            -1,
            Arc::new(Stream {
                commands,
                task: task.abort_handle(),
            }),
        );
        let (result, result_receiver) = sync::channel();
        let reader = std::thread::spawn(move || {
            result.send(http_stream_read_chunk(-1, 8192, None)).unwrap();
        });
        start_receiver.recv_timeout(Duration::from_secs(2)).unwrap();

        let (commands, mut receiver) = mpsc::channel::<ReadCommand>(1);
        let task = runtime.spawn(async move {
            let command = receiver.recv().await.unwrap();
            assert!(command.reply.send(Ok(Some(vec![42]))).is_ok());
        });
        streams().lock().unwrap().insert(
            -2,
            Arc::new(Stream {
                commands,
                task: task.abort_handle(),
            }),
        );
        assert_eq!(
            http_stream_read_chunk(-2, 8192, Some(1.0))
                .unwrap_or_else(|_| panic!("independent stream read failed")),
            Some(vec![42])
        );
        assert!(http_stream_close(-2).is_ok());
        assert!(http_stream_close(-1).is_ok());
        assert!(
            result_receiver
                .recv_timeout(Duration::from_secs(2))
                .unwrap()
                .is_err()
        );
        reader.join().unwrap();
    }
}

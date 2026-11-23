/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::sync::OnceLock;
use std::time::Duration;

use abra_core::vm::AbraInt;
use reqwest::Method;
use reqwest::blocking::{Client, Response as ReqwestResponse};

use crate::ffi::core::http::{HttpError, Response};

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

fn read_response(resp: ReqwestResponse) -> Result<Response, HttpError> {
    let status = resp.status().as_u16() as AbraInt;
    let headers: Vec<(String, String)> = resp
        .headers()
        .iter()
        .filter_map(|(k, v)| v.to_str().ok().map(|v| (k.to_string(), v.to_string())))
        .collect();
    let body = resp.text().map_err(http_err)?;
    Ok(Response {
        status,
        body,
        headers,
    })
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
    let timeout = Duration::try_from_secs_f64(timeout).map_err(|_| {
        HttpError::Other("timeout must be a positive, finite number of seconds".to_string())
    })?;
    if timeout.is_zero() {
        return Err(HttpError::Other(
            "timeout must be greater than zero".to_string(),
        ));
    }
    let method =
        Method::from_bytes(method.as_bytes()).map_err(|e| HttpError::Other(e.to_string()))?;
    let mut req = client()?
        .request(method, &url)
        .query(&query)
        .timeout(timeout);
    for (name, value) in headers {
        req = req.header(name, value);
    }
    if let Some(b) = body {
        req = req.body(b);
    }
    let resp = req.send().map_err(http_err)?;
    read_response(resp)
}

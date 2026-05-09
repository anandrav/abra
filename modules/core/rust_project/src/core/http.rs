/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::sync::OnceLock;

use abra_core::vm::AbraInt;
use reqwest::Method;
use reqwest::blocking::{Client, Response as ReqwestResponse};

use crate::ffi::core::http::{HttpError, Response};

fn client() -> &'static Client {
    static CLIENT: OnceLock<Client> = OnceLock::new();
    CLIENT.get_or_init(Client::new)
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

pub fn get(url: String) -> Result<Response, HttpError> {
    let resp = client().get(&url).send().map_err(http_err)?;
    read_response(resp)
}

pub fn post(url: String, body: String) -> Result<Response, HttpError> {
    let resp = client()
        .post(&url)
        .body(body)
        .send()
        .map_err(http_err)?;
    read_response(resp)
}

pub fn send_request(
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
) -> Result<Response, HttpError> {
    let method =
        Method::from_bytes(method.as_bytes()).map_err(|e| HttpError::Other(e.to_string()))?;
    let mut req = client().request(method, &url);
    for (name, value) in headers {
        req = req.header(name, value);
    }
    if let Some(b) = body {
        req = req.body(b);
    }
    let resp = req.send().map_err(http_err)?;
    read_response(resp)
}

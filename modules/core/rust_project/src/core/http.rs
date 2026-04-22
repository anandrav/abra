/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// use abra_core::vm::AbraInt;
// use ureq::http;

use crate::ffi::core::http::{HttpError, Response};

// fn ureq_err(e: ureq::Error) -> HttpError {
//     let msg = e.to_string();
//     match e {
//         ureq::Error::HostNotFound | ureq::Error::ConnectionFailed => {
//             HttpError::ConnectionFailed(msg)
//         }
//         ureq::Error::Timeout(_) => HttpError::Timeout(msg),
//         _ => HttpError::Other(msg),
//     }
// }

// fn make_agent() -> ureq::Agent {
//     ureq::Agent::config_builder()
//         .http_status_as_error(false)
//         .build()
//         .new_agent()
// }
//
// fn read_response(mut response: http::Response<ureq::Body>) -> Result<Response, HttpError> {
//     let status = response.status().as_u16() as AbraInt;
//     let headers: Vec<(String, String)> = response
//         .headers()
//         .iter()
//         .filter_map(|(name, value)| {
//             value
//                 .to_str()
//                 .ok()
//                 .map(|v| (name.to_string(), v.to_string()))
//         })
//         .collect();
//     let body = response
//         .body_mut()
//         .read_to_string()
//         .map_err(|e| HttpError::Other(e.to_string()))?;
//
//     Ok(Response {
//         status,
//         body,
//         headers,
//     })
// }

pub fn get(_url: String) -> Result<Response, HttpError> {
    unimplemented!()
    // let response = make_agent().get(&url).call().map_err(ureq_err)?;
    // read_response(response)
}

pub fn post(_url: String, _body: String) -> Result<Response, HttpError> {
    unimplemented!()
    // let response = make_agent()
    //     .post(&url)
    //     .send(body.as_str())
    //     .map_err(ureq_err)?;
    // read_response(response)
}

pub fn send_request(
    _method: String,
    _url: String,
    _headers: Vec<(String, String)>,
    _body: Option<String>,
) -> Result<Response, HttpError> {
    unimplemented!()
    // let agent = make_agent();
    // let mut builder = http::Request::builder().method(method.as_str()).uri(&url);
    // for (name, value) in &headers {
    //     builder = builder.header(name.as_str(), value.as_str());
    // }
    // let response = match body {
    //     Some(b) => {
    //         let request = builder
    //             .body(b.as_str())
    //             .map_err(|e| HttpError::Other(e.to_string()))?;
    //         agent.run(request).map_err(ureq_err)?
    //     }
    //     None => {
    //         let request = builder
    //             .body(())
    //             .map_err(|e| HttpError::Other(e.to_string()))?;
    //         agent.run(request).map_err(ureq_err)?
    //     }
    // };
    // read_response(response)
}

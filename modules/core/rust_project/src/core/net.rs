/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ffi::core::net::{Shutdown, SocketError, UnixListener, UnixStream};
use abra_core::vm::AbraInt;

pub use platform::*;

#[cfg(unix)]
mod platform {
    use super::*;
    use socket2::{Domain, SockAddr, Socket, Type};
    use std::collections::HashMap;
    use std::fs::{self, Permissions};
    use std::io::{self, Read, Write};
    use std::net::Shutdown as OsShutdown;
    use std::os::fd::{AsRawFd, RawFd};
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::{UnixListener as OsListener, UnixStream as OsStream};
    use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
    use std::sync::{Arc, Mutex, OnceLock};
    use std::time::{Duration, Instant};

    struct Listener {
        socket: OsListener,
        closed: AtomicBool,
    }

    struct Stream {
        socket: OsStream,
        closed: AtomicBool,
    }

    static NEXT_ID: AtomicI64 = AtomicI64::new(1);
    static LISTENERS: OnceLock<Mutex<HashMap<AbraInt, Arc<Listener>>>> = OnceLock::new();
    static STREAMS: OnceLock<Mutex<HashMap<AbraInt, Arc<Stream>>>> = OnceLock::new();

    fn listeners() -> &'static Mutex<HashMap<AbraInt, Arc<Listener>>> {
        LISTENERS.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn streams() -> &'static Mutex<HashMap<AbraInt, Arc<Stream>>> {
        STREAMS.get_or_init(|| Mutex::new(HashMap::new()))
    }

    fn closed_error() -> SocketError {
        SocketError::Other("socket handle is closed or invalid".to_string())
    }

    fn io_error(error: io::Error) -> SocketError {
        let message = error.to_string();
        match error.kind() {
            io::ErrorKind::NotFound => SocketError::NotFound(message),
            io::ErrorKind::PermissionDenied => SocketError::PermissionDenied(message),
            io::ErrorKind::AddrInUse => SocketError::AddressInUse(message),
            io::ErrorKind::ConnectionRefused => SocketError::ConnectionRefused(message),
            io::ErrorKind::TimedOut => SocketError::Timeout(message),
            _ => SocketError::Other(message),
        }
    }

    fn deadline(timeout: Option<f64>) -> Result<Option<Instant>, SocketError> {
        let Some(seconds) = timeout else { return Ok(None) };
        let duration = Duration::try_from_secs_f64(seconds).map_err(|_| {
            SocketError::Other("timeout must be a positive, finite number of seconds".to_string())
        })?;
        if duration.is_zero() {
            return Err(SocketError::Other(
                "timeout must be greater than zero".to_string(),
            ));
        }
        Instant::now()
            .checked_add(duration)
            .map(Some)
            .ok_or_else(|| SocketError::Other("timeout is too large".to_string()))
    }

    // Short poll intervals allow close() in another task to cancel pending I/O.
    fn wait_ready(
        fd: RawFd,
        events: i16,
        deadline: Option<Instant>,
        closed: &AtomicBool,
    ) -> Result<(), SocketError> {
        loop {
            if closed.load(Ordering::Acquire) {
                return Err(closed_error());
            }
            let timeout_ms = if let Some(deadline) = deadline {
                let remaining =
                    deadline
                        .checked_duration_since(Instant::now())
                        .ok_or_else(|| {
                            SocketError::Timeout("socket operation timed out".to_string())
                        })?;
                remaining.as_millis().clamp(1, 50) as i32
            } else {
                50
            };
            let mut pollfd = libc::pollfd {
                fd,
                events,
                revents: 0,
            };
            let result = unsafe { libc::poll(&mut pollfd, 1, timeout_ms) };
            if result > 0 {
                return Ok(());
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(io_error(error));
                }
            }
        }
    }

    fn stream(id: AbraInt) -> Result<Arc<Stream>, SocketError> {
        streams()
            .lock()
            .unwrap()
            .get(&id)
            .cloned()
            .ok_or_else(closed_error)
    }

    fn register_stream(socket: OsStream) -> Result<UnixStream, SocketError> {
        socket.set_nonblocking(true).map_err(io_error)?;
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        streams().lock().unwrap().insert(
            id,
            Arc::new(Stream {
                socket,
                closed: AtomicBool::new(false),
            }),
        );
        Ok(UnixStream { id })
    }

    pub fn unix_listener_bind(path: String, backlog: AbraInt) -> Result<UnixListener, SocketError> {
        if path.is_empty() {
            return Err(SocketError::Other(
                "socket path must not be empty".to_string(),
            ));
        }
        let backlog = i32::try_from(backlog)
            .ok()
            .filter(|n| *n >= 0)
            .ok_or_else(|| {
                SocketError::Other("backlog must be a non-negative 32-bit integer".to_string())
            })?;
        let address = SockAddr::unix(&path).map_err(io_error)?;
        let socket = Socket::new(Domain::UNIX, Type::STREAM, None).map_err(io_error)?;
        socket.bind(&address).map_err(io_error)?;
        fs::set_permissions(&path, Permissions::from_mode(0o600)).map_err(io_error)?;
        socket.listen(backlog).map_err(io_error)?;
        socket.set_nonblocking(true).map_err(io_error)?;
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        listeners().lock().unwrap().insert(
            id,
            Arc::new(Listener {
                socket: socket.into(),
                closed: AtomicBool::new(false),
            }),
        );
        Ok(UnixListener { id })
    }

    pub fn unix_listener_accept(
        id: AbraInt,
        timeout: Option<f64>,
    ) -> Result<UnixStream, SocketError> {
        let deadline = deadline(timeout)?;
        let listener = listeners()
            .lock()
            .unwrap()
            .get(&id)
            .cloned()
            .ok_or_else(closed_error)?;
        loop {
            if listener.closed.load(Ordering::Acquire) {
                return Err(closed_error());
            }
            match listener.socket.accept() {
                Ok((socket, _)) => {
                    if listener.closed.load(Ordering::Acquire) {
                        return Err(closed_error());
                    }
                    return register_stream(socket);
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    wait_ready(
                        listener.socket.as_raw_fd(),
                        libc::POLLIN,
                        deadline,
                        &listener.closed,
                    )?;
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => return Err(io_error(error)),
            }
        }
    }

    pub fn unix_listener_close(id: AbraInt) -> Result<(), SocketError> {
        if let Some(listener) = listeners().lock().unwrap().remove(&id) {
            listener.closed.store(true, Ordering::Release);
        }
        Ok(())
    }

    pub fn unix_stream_connect(path: String) -> Result<UnixStream, SocketError> {
        register_stream(OsStream::connect(path).map_err(io_error)?)
    }

    pub fn unix_stream_read(
        id: AbraInt,
        max_bytes: AbraInt,
        timeout: Option<f64>,
    ) -> Result<Option<Vec<AbraInt>>, SocketError> {
        let max_bytes = usize::try_from(max_bytes)
            .ok()
            .filter(|n| *n > 0)
            .ok_or_else(|| SocketError::Other("max_bytes must be greater than zero".to_string()))?;
        let deadline = deadline(timeout)?;
        let stream = stream(id)?;
        let mut buffer = Vec::new();
        buffer.try_reserve_exact(max_bytes).map_err(|error| {
            SocketError::Other(format!("could not allocate read buffer: {error}"))
        })?;
        buffer.resize(max_bytes, 0);
        let mut socket = &stream.socket;
        loop {
            if stream.closed.load(Ordering::Acquire) {
                return Err(closed_error());
            }
            match socket.read(&mut buffer) {
                Ok(count) => {
                    if stream.closed.load(Ordering::Acquire) {
                        return Err(closed_error());
                    }
                    if count == 0 {
                        return Ok(None);
                    }
                    buffer.truncate(count);
                    return Ok(Some(crate::core::from_bytes(&buffer)));
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    wait_ready(
                        stream.socket.as_raw_fd(),
                        libc::POLLIN,
                        deadline,
                        &stream.closed,
                    )?;
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => return Err(io_error(error)),
            }
        }
    }

    pub fn unix_stream_write_all(
        id: AbraInt,
        bytes: Vec<AbraInt>,
        timeout: Option<f64>,
    ) -> Result<(), SocketError> {
        let bytes: Vec<u8> = bytes
            .into_iter()
            .map(u8::try_from)
            .collect::<Result<_, _>>()
            .map_err(|_| {
                SocketError::Other("socket bytes must be between 0 and 255".to_string())
            })?;
        let deadline = deadline(timeout)?;
        let stream = stream(id)?;
        let mut socket = &stream.socket;
        let mut remaining = bytes.as_slice();
        loop {
            if stream.closed.load(Ordering::Acquire) {
                return Err(closed_error());
            }
            if remaining.is_empty() {
                return Ok(());
            }
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return Err(SocketError::Timeout(
                    "socket operation timed out".to_string(),
                ));
            }
            match socket.write(remaining) {
                Ok(0) => {
                    return Err(SocketError::Other(
                        "socket write made no progress".to_string(),
                    ));
                }
                Ok(count) => remaining = &remaining[count..],
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    wait_ready(
                        stream.socket.as_raw_fd(),
                        libc::POLLOUT,
                        deadline,
                        &stream.closed,
                    )?;
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => return Err(io_error(error)),
            }
        }
    }

    pub fn unix_stream_shutdown(id: AbraInt, how: Shutdown) -> Result<(), SocketError> {
        let stream = stream(id)?;
        let how = match how {
            Shutdown::Read => OsShutdown::Read,
            Shutdown::Write => OsShutdown::Write,
            Shutdown::Both => OsShutdown::Both,
        };
        stream.socket.shutdown(how).map_err(io_error)
    }

    pub fn unix_stream_close(id: AbraInt) -> Result<(), SocketError> {
        if let Some(stream) = streams().lock().unwrap().remove(&id) {
            stream.closed.store(true, Ordering::Release);
            let _ = stream.socket.shutdown(OsShutdown::Both);
        }
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::sync::mpsc;
        use std::thread;

        fn socket_path() -> (tempfile::TempDir, String) {
            let directory = tempfile::tempdir_in("/tmp").unwrap();
            let path = directory
                .path()
                .join("socket")
                .to_str()
                .unwrap()
                .to_string();
            (directory, path)
        }

        #[test]
        fn listener_is_private_and_keeps_path_on_close() {
            let (_directory, path) = socket_path();
            let listener =
                unix_listener_bind(path.clone(), 128).unwrap_or_else(|_| panic!("bind failed"));
            assert_eq!(
                fs::metadata(&path).unwrap().permissions().mode() & 0o777,
                0o600
            );
            assert!(unix_listener_close(listener.id).is_ok());
            assert!(unix_listener_close(listener.id).is_ok());
            assert!(fs::symlink_metadata(&path).is_ok());
            assert!(matches!(
                unix_listener_bind(path, 128),
                Err(SocketError::AddressInUse(_))
            ));
        }

        #[test]
        fn close_cancels_accept() {
            let (_directory, path) = socket_path();
            let listener = unix_listener_bind(path, 128).unwrap_or_else(|_| panic!("bind failed"));
            let (started, ready) = mpsc::channel();
            let (result, received) = mpsc::channel();
            let id = listener.id;
            let accepter = thread::spawn(move || {
                started.send(()).unwrap();
                result
                    .send(unix_listener_accept(id, None).is_err())
                    .unwrap();
            });
            ready.recv_timeout(Duration::from_secs(2)).unwrap();
            assert!(unix_listener_close(id).is_ok());
            assert!(received.recv_timeout(Duration::from_secs(2)).unwrap());
            accepter.join().unwrap();
        }

        #[test]
        fn close_cancels_reads_and_blocked_writes() {
            let (_directory, path) = socket_path();
            let listener =
                unix_listener_bind(path.clone(), 128).unwrap_or_else(|_| panic!("bind failed"));
            let client = unix_stream_connect(path).unwrap_or_else(|_| panic!("connect failed"));
            let server = unix_listener_accept(listener.id, Some(1.0))
                .unwrap_or_else(|_| panic!("accept failed"));

            let (result, received) = mpsc::channel();
            let id = client.id;
            let read_result = result.clone();
            let reader = thread::spawn(move || {
                read_result
                    .send(unix_stream_read(id, 1, None).is_err())
                    .unwrap();
            });
            let writer = thread::spawn(move || {
                result
                    .send(unix_stream_write_all(id, vec![42; 4 * 1024 * 1024], None).is_err())
                    .unwrap();
            });
            // The peer does not read or write, so neither operation can complete.
            thread::sleep(Duration::from_millis(20));
            assert!(unix_stream_close(id).is_ok());
            assert!(received.recv_timeout(Duration::from_secs(2)).unwrap());
            assert!(received.recv_timeout(Duration::from_secs(2)).unwrap());
            reader.join().unwrap();
            writer.join().unwrap();
            assert!(unix_stream_close(server.id).is_ok());
            assert!(unix_listener_close(listener.id).is_ok());
        }

        #[test]
        fn write_timeout_keeps_socket_usable() {
            let (_directory, path) = socket_path();
            let listener =
                unix_listener_bind(path.clone(), 128).unwrap_or_else(|_| panic!("bind failed"));
            let client = unix_stream_connect(path).unwrap_or_else(|_| panic!("connect failed"));
            let server = unix_listener_accept(listener.id, Some(1.0))
                .unwrap_or_else(|_| panic!("accept failed"));
            let resource = stream(client.id).unwrap_or_else(|_| panic!("stream missing"));
            socket2::SockRef::from(&resource.socket)
                .set_send_buffer_size(4096)
                .unwrap();
            assert!(matches!(
                unix_stream_write_all(client.id, vec![42; 1024 * 1024], Some(0.01)),
                Err(SocketError::Timeout(_))
            ));
            assert!(
                unix_stream_shutdown(client.id, Shutdown::Write).is_ok(),
                "timeout must leave the handle open"
            );
            assert_eq!(
                unix_stream_read(server.id, 1, Some(1.0)).unwrap_or_else(|_| panic!("read failed")),
                Some(vec![42]),
                "a timed-out write may have sent part of the input"
            );
            assert!(unix_stream_close(client.id).is_ok());
            assert!(unix_stream_close(server.id).is_ok());
            assert!(unix_listener_close(listener.id).is_ok());
        }
    }
}

#[cfg(not(unix))]
mod platform {
    use super::*;

    fn unsupported() -> SocketError {
        SocketError::Other("Unix-domain sockets are unavailable on this platform".to_string())
    }

    pub fn unix_listener_bind(_: String, _: AbraInt) -> Result<UnixListener, SocketError> {
        Err(unsupported())
    }
    pub fn unix_listener_accept(_: AbraInt, _: Option<f64>) -> Result<UnixStream, SocketError> {
        Err(unsupported())
    }
    pub fn unix_listener_close(_: AbraInt) -> Result<(), SocketError> {
        Err(unsupported())
    }
    pub fn unix_stream_connect(_: String) -> Result<UnixStream, SocketError> {
        Err(unsupported())
    }
    pub fn unix_stream_read(
        _: AbraInt,
        _: AbraInt,
        _: Option<f64>,
    ) -> Result<Option<Vec<AbraInt>>, SocketError> {
        Err(unsupported())
    }
    pub fn unix_stream_write_all(
        _: AbraInt,
        _: Vec<AbraInt>,
        _: Option<f64>,
    ) -> Result<(), SocketError> {
        Err(unsupported())
    }
    pub fn unix_stream_shutdown(_: AbraInt, _: Shutdown) -> Result<(), SocketError> {
        Err(unsupported())
    }
    pub fn unix_stream_close(_: AbraInt) -> Result<(), SocketError> {
        Err(unsupported())
    }
}

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use crate::ffi::core::signals::Signal;
use signal_hook::consts::FORBIDDEN;

static LAST_SIGNAL: OnceLock<Arc<AtomicUsize>> = OnceLock::new();
static WATCHED_SIGNALS: OnceLock<Mutex<HashSet<i32>>> = OnceLock::new();

fn last_signal() -> Arc<AtomicUsize> {
    LAST_SIGNAL
        .get_or_init(|| Arc::new(AtomicUsize::new(0)))
        .clone()
}

fn watched_signals() -> &'static Mutex<HashSet<i32>> {
    WATCHED_SIGNALS.get_or_init(|| Mutex::new(HashSet::new()))
}

#[cfg(windows)]
fn unsupported(name: &str) -> Result<i32, String> {
    Err(format!("signal {name} is not supported on this platform"))
}

fn signal_to_raw(signal: Signal) -> Result<i32, String> {
    match signal {
        Signal::Abort => Ok(signal_hook::consts::SIGABRT),
        #[cfg(not(windows))]
        Signal::Alarm => Ok(signal_hook::consts::SIGALRM),
        #[cfg(windows)]
        Signal::Alarm => unsupported("SIGALRM"),
        #[cfg(not(windows))]
        Signal::Child => Ok(signal_hook::consts::SIGCHLD),
        #[cfg(windows)]
        Signal::Child => unsupported("SIGCHLD"),
        Signal::FloatingPointException => Ok(signal_hook::consts::SIGFPE),
        #[cfg(not(windows))]
        Signal::Hangup => Ok(signal_hook::consts::SIGHUP),
        #[cfg(windows)]
        Signal::Hangup => unsupported("SIGHUP"),
        Signal::IllegalInstruction => Ok(signal_hook::consts::SIGILL),
        Signal::Interrupt => Ok(signal_hook::consts::SIGINT),
        #[cfg(not(windows))]
        Signal::Kill => Ok(signal_hook::consts::SIGKILL),
        #[cfg(windows)]
        Signal::Kill => unsupported("SIGKILL"),
        #[cfg(not(windows))]
        Signal::Pipe => Ok(signal_hook::consts::SIGPIPE),
        #[cfg(windows)]
        Signal::Pipe => unsupported("SIGPIPE"),
        #[cfg(not(windows))]
        Signal::Quit => Ok(signal_hook::consts::SIGQUIT),
        #[cfg(windows)]
        Signal::Quit => unsupported("SIGQUIT"),
        Signal::SegmentationFault => Ok(signal_hook::consts::SIGSEGV),
        #[cfg(not(windows))]
        Signal::Stop => Ok(signal_hook::consts::SIGSTOP),
        #[cfg(windows)]
        Signal::Stop => unsupported("SIGSTOP"),
        Signal::Terminate => Ok(signal_hook::consts::SIGTERM),
        #[cfg(not(windows))]
        Signal::User1 => Ok(signal_hook::consts::SIGUSR1),
        #[cfg(windows)]
        Signal::User1 => unsupported("SIGUSR1"),
        #[cfg(not(windows))]
        Signal::User2 => Ok(signal_hook::consts::SIGUSR2),
        #[cfg(windows)]
        Signal::User2 => unsupported("SIGUSR2"),
        #[cfg(not(windows))]
        Signal::WindowChange => Ok(signal_hook::consts::SIGWINCH),
        #[cfg(windows)]
        Signal::WindowChange => unsupported("SIGWINCH"),
    }
}

fn signal_from_raw(signal: i32) -> Option<Signal> {
    if signal == signal_hook::consts::SIGABRT {
        return Some(Signal::Abort);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGALRM {
        return Some(Signal::Alarm);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGCHLD {
        return Some(Signal::Child);
    }
    if signal == signal_hook::consts::SIGFPE {
        return Some(Signal::FloatingPointException);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGHUP {
        return Some(Signal::Hangup);
    }
    if signal == signal_hook::consts::SIGILL {
        return Some(Signal::IllegalInstruction);
    }
    if signal == signal_hook::consts::SIGINT {
        return Some(Signal::Interrupt);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGKILL {
        return Some(Signal::Kill);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGPIPE {
        return Some(Signal::Pipe);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGQUIT {
        return Some(Signal::Quit);
    }
    if signal == signal_hook::consts::SIGSEGV {
        return Some(Signal::SegmentationFault);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGSTOP {
        return Some(Signal::Stop);
    }
    if signal == signal_hook::consts::SIGTERM {
        return Some(Signal::Terminate);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGUSR1 {
        return Some(Signal::User1);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGUSR2 {
        return Some(Signal::User2);
    }
    #[cfg(not(windows))]
    if signal == signal_hook::consts::SIGWINCH {
        return Some(Signal::WindowChange);
    }
    None
}

pub fn watch(signal: Signal) -> Result<(), String> {
    let signal = signal_to_raw(signal)?;
    if FORBIDDEN.contains(&signal) {
        return Err(format!("signal {signal} cannot be caught"));
    }

    let mut watched = watched_signals().lock().unwrap();
    if watched.contains(&signal) {
        return Ok(());
    }

    signal_hook::flag::register_usize(signal, last_signal(), signal as usize)
        .map_err(|e| e.to_string())?;
    watched.insert(signal);
    Ok(())
}

pub fn poll() -> Option<Signal> {
    let signal = last_signal().swap(0, Ordering::Relaxed);
    if signal == 0 {
        None
    } else {
        signal_from_raw(signal as i32)
    }
}

pub fn clear() {
    last_signal().store(0, Ordering::Relaxed);
}

pub fn raise(signal: Signal) -> Result<(), String> {
    signal_hook::low_level::raise(signal_to_raw(signal)?).map_err(|e| e.to_string())
}

pub fn signal_name(signal: Signal) -> Option<String> {
    let Ok(signal) = signal_to_raw(signal) else {
        return None;
    };
    signal_hook::low_level::signal_name(signal).map(str::to_string)
}

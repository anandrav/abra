use std::time::Duration;

use crate::ffi::term::KeyCode;
use crossterm::{
    event::{
        poll, read, DisableBracketedPaste, DisableFocusChange, EnableBracketedPaste,
        EnableFocusChange, Event, KeyCode as CtKeyCode, KeyEvent as CtKeyEvent,
    },
    execute,
};

pub fn poll_key_event() -> bool {
    println!("poll_key_event()");
    let mut ret = false;
    execute!(std::io::stdout(), EnableBracketedPaste, EnableFocusChange,).unwrap();
    if poll(Duration::from_millis(16)).unwrap() {
        println!("poll() returns true!");
        ret = true;
    }
    execute!(std::io::stdout(), DisableBracketedPaste, DisableFocusChange,).unwrap();
    println!("poll() returns false!");
    ret
}

pub fn get_key_event() -> KeyCode {
    println!("get_key_event()");
    execute!(std::io::stdout(), EnableBracketedPaste, EnableFocusChange,).unwrap();
    let ev = loop {
        match read() {
            Ok(Event::Key(CtKeyEvent {
                code,
                modifiers: _,
                kind: _,
                state: _,
            })) => {
                println!("actually got an event");
                match code {
                    CtKeyCode::Left => break KeyCode::Left,
                    CtKeyCode::Right => break KeyCode::Right,
                    CtKeyCode::Up => break KeyCode::Up,
                    CtKeyCode::Down => break KeyCode::Down,
                    CtKeyCode::Char(c) => break KeyCode::Char(c.into()),
                    CtKeyCode::Esc => break KeyCode::Esc,
                    _ => continue,
                }
            }
            Ok(_) => {
                println!("ok something else");
            }
            Err(_) => {
                println!("err");
            }
        };
    };
    execute!(std::io::stdout(), DisableBracketedPaste, DisableFocusChange,).unwrap();
    ev
}

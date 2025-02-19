use std::time::Duration;

use crate::ffi::term::KeyCode;
use crossterm::{
    event::{
        poll, read, DisableBracketedPaste, DisableFocusChange, DisableMouseCapture,
        EnableBracketedPaste, EnableFocusChange, EnableMouseCapture, Event, KeyCode as CtKeyCode,
        KeyEvent as CtKeyEvent,
    },
    execute,
    terminal::{disable_raw_mode, enable_raw_mode},
};

pub fn poll_key_event() -> bool {
    enable_raw_mode().unwrap();
    execute!(std::io::stdout(), EnableMouseCapture).unwrap();
    let mut ret = false;
    // execute!(std::io::stdout(), EnableBracketedPaste, EnableFocusChange).unwrap();
    if poll(Duration::from_millis(16)).unwrap() {
        ret = true;
    }
    // execute!(std::io::stdout(), DisableBracketedPaste, DisableFocusChange).unwrap();
    execute!(std::io::stdout(), DisableMouseCapture).unwrap();
    disable_raw_mode().unwrap();
    ret
}

pub fn get_key_event() -> KeyCode {
    enable_raw_mode().unwrap();
    execute!(std::io::stdout(), EnableMouseCapture).unwrap();
    let ev = loop {
        if let Ok(Event::Key(CtKeyEvent {
            code,
            modifiers: _,
            kind: _,
            state: _,
        })) = read()
        {
            match code {
                CtKeyCode::Left => break KeyCode::Left,
                CtKeyCode::Right => break KeyCode::Right,
                CtKeyCode::Up => break KeyCode::Up,
                CtKeyCode::Down => break KeyCode::Down,
                CtKeyCode::Char(c) => break KeyCode::Char(c.into()),
                CtKeyCode::Esc => break KeyCode::Esc,
                _ => {}
            }
        };
    };
    execute!(std::io::stdout(), DisableMouseCapture).unwrap();
    disable_raw_mode().unwrap();
    ev
}

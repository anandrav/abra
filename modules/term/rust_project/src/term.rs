use std::{
    io::{stdout, Write},
    time::Duration,
};

use crate::ffi::term::KeyCode;
use crossterm::{
    cursor,
    event::{
        poll, read, DisableBracketedPaste, DisableFocusChange, DisableMouseCapture,
        EnableBracketedPaste, EnableFocusChange, EnableMouseCapture, Event, KeyCode as CtKeyCode,
        KeyEvent as CtKeyEvent,
    },
    execute, queue,
    style::{self, Color},
    terminal::{self, Clear, ClearType},
};

pub fn enable_raw_mode() {
    terminal::enable_raw_mode().unwrap();
}

pub fn disable_raw_mode() {
    terminal::disable_raw_mode().unwrap();
}

pub fn poll_key_event() -> bool {
    // execute!(std::io::stdout(), EnableMouseCapture).unwrap();
    let mut ret = false;
    // execute!(std::io::stdout(), EnableBracketedPaste, EnableFocusChange).unwrap();
    if poll(Duration::from_millis(1)).unwrap() {
        ret = true;
    }
    // execute!(std::io::stdout(), DisableBracketedPaste, DisableFocusChange).unwrap();
    // execute!(std::io::stdout(), DisableMouseCapture).unwrap();
    ret
}

pub fn get_key_event() -> KeyCode {
    // execute!(std::io::stdout(), EnableMouseCapture).unwrap();

    // execute!(std::io::stdout(), DisableMouseCapture).unwrap();
    loop {
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
                _ => break KeyCode::Other,
            }
        };
        println!("didn't get a key event");
    }
}

pub fn clear() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::All)).unwrap();
}

pub fn mark(s: String, x: i64, y: i64) {
    let mut stdout = stdout();
    queue!(
        stdout,
        cursor::MoveToColumn(x as u16),
        cursor::MoveToRow(y as u16),
        style::Print(s)
    )
    .unwrap();
}

pub fn flush() {
    stdout().flush().unwrap();
}

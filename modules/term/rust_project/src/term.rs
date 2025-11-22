/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::io::Write;
use std::io::stdout;
use std::time::Duration;

use crate::ffi::term::KeyCode;
use abra_core::vm::AbraInt;
use crossterm::cursor;
use crossterm::event::Event;
use crossterm::event::KeyCode as CtKeyCode;
use crossterm::event::KeyEvent as CtKeyEvent;
use crossterm::event::poll;
use crossterm::event::read;
use crossterm::queue;
use crossterm::style::{self};
use crossterm::terminal::Clear;
use crossterm::terminal::ClearType;
use crossterm::terminal::size;
use crossterm::terminal::{self};

pub fn enable_raw_mode() {
    terminal::enable_raw_mode().unwrap();
}

pub fn disable_raw_mode() {
    terminal::disable_raw_mode().unwrap();
}

pub fn poll_key_event(milliseconds: AbraInt) -> bool {
    let mut ret = false;
    if poll(Duration::from_millis(milliseconds as u64)).unwrap() {
        ret = true;
    }

    ret
}

pub fn get_key_event() -> KeyCode {
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
    }
}

pub fn clear() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::All)).unwrap();
}

pub fn hide_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::Hide).unwrap();
}

pub fn show_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::Show).unwrap();
}

pub fn mark(s: String, x: AbraInt, y: AbraInt) {
    let Ok(x) = u16::try_from(x) else {
        return;
    };
    let Ok(y) = u16::try_from(y) else {
        return;
    };
    let mut stdout = stdout();
    queue!(
        stdout,
        cursor::MoveToColumn(x),
        cursor::MoveToRow(y),
        style::Print(s)
    )
    .unwrap();
}

pub fn flush() {
    stdout().flush().unwrap();
}

pub fn get_size() -> Option<(AbraInt, AbraInt)> {
    match size() {
        Ok((columns, rows)) => Some((columns as AbraInt, rows as AbraInt)),
        Err(_) => None,
    }
}

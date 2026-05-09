/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::io::Write;
use std::io::stdout;
use std::time::Duration;

use crate::ffi::ard::term::{Event, KeyCode, Modifiers, MouseButton, MouseEvent};
use abra_core::vm::AbraInt;
use crossterm::cursor;
use crossterm::event::{
    DisableMouseCapture, EnableMouseCapture, Event as CtEvent, KeyCode as CtKeyCode,
    KeyEvent as CtKeyEvent, KeyEventKind, KeyModifiers, MouseButton as CtMouseButton,
    MouseEvent as CtMouseEvent, MouseEventKind, poll, read,
};
use crossterm::queue;
use crossterm::style;
use crossterm::terminal::{
    self, Clear, ClearType, EnterAlternateScreen, LeaveAlternateScreen, SetTitle, size,
};

pub fn enable_raw_mode() {
    terminal::enable_raw_mode().unwrap();
}

pub fn disable_raw_mode() {
    terminal::disable_raw_mode().unwrap();
}

pub fn enter_alternate_screen() {
    let mut stdout = stdout();
    queue!(stdout, EnterAlternateScreen).unwrap();
}

pub fn leave_alternate_screen() {
    let mut stdout = stdout();
    queue!(stdout, LeaveAlternateScreen).unwrap();
}

pub fn enable_mouse() {
    let mut stdout = stdout();
    queue!(stdout, EnableMouseCapture).unwrap();
}

pub fn disable_mouse() {
    let mut stdout = stdout();
    queue!(stdout, DisableMouseCapture).unwrap();
}

pub fn set_title(title: String) {
    let mut stdout = stdout();
    queue!(stdout, SetTitle(title)).unwrap();
}

pub fn bell() {
    let _ = stdout().write_all(b"\x07");
}

pub fn poll_event(milliseconds: AbraInt) -> bool {
    let ms = if milliseconds < 0 { 0 } else { milliseconds as u64 };
    poll(Duration::from_millis(ms)).unwrap_or(false)
}

pub fn get_event() -> Event {
    loop {
        match read() {
            Ok(CtEvent::Key(CtKeyEvent {
                code,
                modifiers,
                kind,
                ..
            })) => {
                if kind != KeyEventKind::Press {
                    continue;
                }
                break Event::Key((key_code_from(code), modifiers_from(modifiers)));
            }
            Ok(CtEvent::Mouse(m)) => {
                let mods = modifiers_from(m.modifiers);
                if let Some(me) = mouse_event_from(&m) {
                    break Event::Mouse((me, mods));
                } else {
                    continue;
                }
            }
            Ok(CtEvent::Resize(cols, rows)) => {
                break Event::Resize((cols as AbraInt, rows as AbraInt));
            }
            Ok(_) => break Event::Other,
            Err(_) => break Event::Other,
        }
    }
}

fn modifiers_from(m: KeyModifiers) -> Modifiers {
    Modifiers {
        ctrl: m.contains(KeyModifiers::CONTROL),
        alt: m.contains(KeyModifiers::ALT),
        shift: m.contains(KeyModifiers::SHIFT),
    }
}

fn key_code_from(c: CtKeyCode) -> KeyCode {
    match c {
        CtKeyCode::Char(ch) => KeyCode::Char(ch.to_string()),
        CtKeyCode::Enter => KeyCode::Enter,
        CtKeyCode::Tab => KeyCode::Tab,
        CtKeyCode::BackTab => KeyCode::BackTab,
        CtKeyCode::Backspace => KeyCode::Backspace,
        CtKeyCode::Delete => KeyCode::Delete,
        CtKeyCode::Insert => KeyCode::Insert,
        CtKeyCode::Esc => KeyCode::Esc,
        CtKeyCode::Left => KeyCode::Left,
        CtKeyCode::Right => KeyCode::Right,
        CtKeyCode::Up => KeyCode::Up,
        CtKeyCode::Down => KeyCode::Down,
        CtKeyCode::Home => KeyCode::Home,
        CtKeyCode::End => KeyCode::End,
        CtKeyCode::PageUp => KeyCode::PageUp,
        CtKeyCode::PageDown => KeyCode::PageDown,
        CtKeyCode::F(n) => KeyCode::Function(n as AbraInt),
        _ => KeyCode::Other,
    }
}

fn mouse_event_from(m: &CtMouseEvent) -> Option<MouseEvent> {
    let x = m.column as AbraInt;
    let y = m.row as AbraInt;
    Some(match m.kind {
        MouseEventKind::Down(b) => MouseEvent::Down((mouse_button_from(b), x, y)),
        MouseEventKind::Up(b) => MouseEvent::Up((mouse_button_from(b), x, y)),
        MouseEventKind::Drag(b) => MouseEvent::Drag((mouse_button_from(b), x, y)),
        MouseEventKind::Moved => MouseEvent::Move((x, y)),
        MouseEventKind::ScrollUp => MouseEvent::ScrollUp((x, y)),
        MouseEventKind::ScrollDown => MouseEvent::ScrollDown((x, y)),
        _ => return None,
    })
}

fn mouse_button_from(b: CtMouseButton) -> MouseButton {
    match b {
        CtMouseButton::Left => MouseButton::LeftButton,
        CtMouseButton::Right => MouseButton::RightButton,
        CtMouseButton::Middle => MouseButton::MiddleButton,
    }
}

pub fn clear() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::All)).unwrap();
}

pub fn clear_line() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::CurrentLine)).unwrap();
}

pub fn clear_to_end_of_line() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::UntilNewLine)).unwrap();
}

pub fn clear_to_end_of_screen() {
    let mut stdout = stdout();
    queue!(stdout, Clear(ClearType::FromCursorDown)).unwrap();
}

pub fn hide_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::Hide).unwrap();
}

pub fn show_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::Show).unwrap();
}

pub fn move_to(x: AbraInt, y: AbraInt) {
    let Ok(x) = u16::try_from(x) else { return };
    let Ok(y) = u16::try_from(y) else { return };
    let mut stdout = stdout();
    queue!(stdout, cursor::MoveTo(x, y)).unwrap();
}

pub fn move_up(n: AbraInt) {
    let Ok(n) = u16::try_from(n) else { return };
    let mut stdout = stdout();
    queue!(stdout, cursor::MoveUp(n)).unwrap();
}

pub fn move_down(n: AbraInt) {
    let Ok(n) = u16::try_from(n) else { return };
    let mut stdout = stdout();
    queue!(stdout, cursor::MoveDown(n)).unwrap();
}

pub fn move_left(n: AbraInt) {
    let Ok(n) = u16::try_from(n) else { return };
    let mut stdout = stdout();
    queue!(stdout, cursor::MoveLeft(n)).unwrap();
}

pub fn move_right(n: AbraInt) {
    let Ok(n) = u16::try_from(n) else { return };
    let mut stdout = stdout();
    queue!(stdout, cursor::MoveRight(n)).unwrap();
}

pub fn save_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::SavePosition).unwrap();
}

pub fn restore_cursor() {
    let mut stdout = stdout();
    queue!(stdout, cursor::RestorePosition).unwrap();
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

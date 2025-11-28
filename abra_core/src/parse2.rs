/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::ast::*;
use crate::statics::{Error, StaticsContext};
use std::rc::Rc;

pub(crate) fn parse_or_err(
    ctx: &mut StaticsContext,
    file_id: FileId,
    file_data: &FileData,
) -> Option<Rc<FileAst>> {
    ctx.errors.push(Error::Parse(format!(
        "Could not parse {}",
        file_data.name()
    )));
    None
}

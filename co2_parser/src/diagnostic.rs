use std::sync::Mutex;

use chumsky::{error::Rich, span::SimpleSpan};

use crate::lexer::Token;

static ERRORS: Mutex<Vec<Rich<'static, Token, SimpleSpan>>> = Mutex::new(Vec::new());

pub fn take_errors() -> Vec<Rich<'static, Token, SimpleSpan>> {
    let mut guard = ERRORS.try_lock().unwrap();
    std::mem::take(&mut *guard)
}

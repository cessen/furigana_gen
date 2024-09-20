use std::{
    borrow::Cow,
    io::{Cursor, Read},
};

use fnv::FnvHashMap;
use lz4_flex::frame::FrameDecoder;

// Pitch accent dictionary.
const ACCENT: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/accents.tsv.lz4"));

#[derive(Debug)]
pub struct AccentDict {
    table: FnvHashMap<(Cow<'static, str>, Cow<'static, str>), Vec<u8>>,
}

pub fn build_accent_dictionary() -> AccentDict {
    let text = {
        let mut decoder = FrameDecoder::new(Cursor::new(ACCENT));
        let mut text = String::new();
        decoder.read_to_string(&mut text).unwrap();

        text
    };

    let mut table = FnvHashMap::default();
    for line in text.lines() {
        let items: Vec<_> = line.split("\t").map(|t| t.trim()).collect();

        let word = items[0];
        let kana = if items[1].is_empty() {
            items[0]
        } else {
            items[1]
        };
        let pitches = items[2]
            .split(",")
            .filter_map(|p| p.parse::<u8>().ok())
            .collect();

        table.insert(
            (
                Cow::Owned(word.into()),
                Cow::Owned(crate::hiragana_to_katakana_string(kana)),
            ),
            pitches,
        );
    }

    AccentDict { table: table }
}

impl AccentDict {
    pub fn get<'a>(&'a self, word: &'a str, kana: &'a str) -> &'a [u8] {
        if let Some(p) = self.table.get(&(Cow::from(word), Cow::from(kana))) {
            &p[..]
        } else {
            &[]
        }
    }
}

/// Computes the byte index of the character in kana that corresponds to the
/// given pitch accent number.
pub fn accent_number_to_byte_idx(kana: &str, accent_number: u8) -> Option<usize> {
    if accent_number == 0 {
        return None;
    }

    let target = accent_number - 1;
    let mut current = 0;
    let mut byte_idx = 0;

    let mut iter = kana.chars().peekable();
    while let Some(c) = iter.next() {
        if current == target {
            break;
        }

        let next_is_mod = match iter.peek() {
            Some('ゃ') | Some('ゅ') | Some('ょ') | Some('ャ') | Some('ュ') | Some('ョ') => {
                true
            }
            _ => false,
        };
        if next_is_mod {
            current += 1;
        }

        byte_idx += c.len_utf8();
    }

    return Some(byte_idx);
}

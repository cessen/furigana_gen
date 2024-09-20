mod accent;
mod learner;

use std::{
    borrow::Cow,
    io::{Cursor, Read},
};

use fnv::{FnvHashMap, FnvHashSet};
use lz4_flex::frame::FrameDecoder;
use quick_xml::events::Event;
use vibrato::{Dictionary, Tokenizer};

use accent::AccentDict;
use learner::Learner;

// Include KANJI_FREQ, a frequency-ordered array of kanji characters.
include!(concat!(env!("OUT_DIR"), "/kanji_freq_inc.rs"));

// Parsing dictionary.
const DICT: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/system.dic.lz4"));

/// A list of words that the tokenizer insists on using the less common reading
/// for, with the more common reading that should be substituted.
///
/// (surface, kana, (substitute_kana, substitute_pitch_lookup_kana))
const COMMON_SUBS: &[(&str, &str, (&str, &str))] = &[
    ("額", "ガク", ("ヒタイ", "ヒタイ")),
    ("他", "タ", ("ホカ", "ホカ")),
    ("私", "ワタクシ", ("ワタシ", "ワタシ")),
    ("等", "トー", ("ナド", "ナド")),
    ("大分", "オーイタ", ("ダイブ", "ダイブ")),
    ("日本", "ニッポン", ("ニホン", "ニホン")),
    ("日本人", "ニッポンジン", ("ニホンジン", "ニホンジン")),
];

pub struct FuriganaGenerator {
    tokenizer: Tokenizer,
    accent_dict: AccentDict,
    exclude_kanji: FnvHashSet<char>,
    subs: FnvHashMap<(Cow<'static, str>, Cow<'static, str>), (String, String)>,
    use_hiragana: bool,
    mark_accent: bool,
}

impl FuriganaGenerator {
    // `exclude_count`: exclude the N most frequent kanji from furigana.
    // Specifically, words made up *entirely* of those kanji will be excluded.
    // If a word has some kanji that aren't in that set, even if it also has
    // some that are, it will still get furigana.
    pub fn new(exclude_count: usize, use_hiragana: bool, mark_accent: bool) -> Self {
        let dict = {
            // Note: we could just pass the decoder straight to `Dictionary::read()`
            // below, and it would work.  However, that ends up being slower than
            // first decompressing the whole thing ahead of time.
            let mut decoder = FrameDecoder::new(Cursor::new(DICT));
            let mut data = Vec::new();
            decoder.read_to_end(&mut data).unwrap();

            Dictionary::read(Cursor::new(&data)).unwrap()
        };

        let exclude_kanji = {
            let mut set = FnvHashSet::default();
            for &c in KANJI_FREQ.iter().take(exclude_count) {
                set.insert(c);
            }
            set
        };

        let subs = {
            let mut map: FnvHashMap<(Cow<str>, Cow<str>), (String, String)> = FnvHashMap::default();
            for (surface, kana, (sub_kana, sub_kana_pitch_lookup)) in COMMON_SUBS.iter().copied() {
                map.insert(
                    (surface.into(), kana.into()),
                    (sub_kana.into(), sub_kana_pitch_lookup.into()),
                );
            }
            map
        };

        Self {
            tokenizer: Tokenizer::new(dict),
            accent_dict: accent::build_accent_dictionary(),
            exclude_kanji: exclude_kanji,
            subs: subs,
            use_hiragana: use_hiragana,
            mark_accent: mark_accent,
        }
    }

    pub fn new_session(&self, learn_mode: bool) -> Session<'_> {
        Session {
            tokenizer: &self.tokenizer,
            accent_dict: &self.accent_dict,
            exclude_kanji: &self.exclude_kanji,
            subs: &self.subs,
            learner: Learner::new(if learn_mode { 3 } else { usize::MAX }),
            use_hiragana: self.use_hiragana,
            mark_accent: self.mark_accent,
        }
    }
}

pub struct Session<'a> {
    tokenizer: &'a Tokenizer,
    accent_dict: &'a AccentDict,
    exclude_kanji: &'a FnvHashSet<char>,
    subs: &'a FnvHashMap<(Cow<'a, str>, Cow<'a, str>), (String, String)>,
    learner: Learner,
    use_hiragana: bool,
    mark_accent: bool,
}

impl<'a> Session<'a> {
    /// Returns (total_words_processed, Vec<(Word, distance, times_seen)>)
    pub fn word_stats(&self) -> (usize, Vec<(String, usize, usize)>) {
        let (total_words, mut stats) = self.learner.word_stats();

        (
            total_words,
            stats
                .drain(..)
                .map(|(w, s)| (w, s.max_distance, s.times_seen))
                .collect(),
        )
    }

    pub fn add_html_furigana(&mut self, text: &str) -> String {
        add_html_furigana_skip_already_ruby(
            &text,
            &self.tokenizer,
            &self.accent_dict,
            &self.exclude_kanji,
            &self.subs,
            &mut self.learner,
            self.use_hiragana,
            self.mark_accent,
        )
    }
}

fn to_str<B: std::ops::Deref<Target = [u8]>>(bytes: &B) -> &str {
    std::str::from_utf8(&bytes.deref()).unwrap()
}

/// Like `add_html_furigana()`, but skips text that already has ruby on it, to it doesn't get double-ruby.
fn add_html_furigana_skip_already_ruby(
    text: &str,
    tokenizer: &Tokenizer,
    accent_dict: &AccentDict,
    exclude_kanji: &FnvHashSet<char>,
    subs: &FnvHashMap<(Cow<str>, Cow<str>), (String, String)>,
    learner: &mut Learner,
    use_hiragana: bool,
    mark_accent: bool,
) -> String {
    let mut reader = quick_xml::Reader::from_str(text);

    let mut new_text = String::new();
    let mut rubys: i32 = 0;

    loop {
        match reader.read_event() {
            Err(_) => {
                // If we hit a parse error, just don't add furigana.
                // But still panic in debug, so we can track things down.
                debug_assert!(false);
                return text.into();
            }
            Ok(Event::Eof) => break,

            Ok(Event::Start(e)) => {
                if e.name().into_inner() == b"ruby" {
                    rubys += 1;
                }
                write_xml(&mut new_text, &Event::Start(e));
            }

            Ok(Event::End(e)) => {
                if e.name().into_inner() == b"ruby" {
                    rubys -= 1;
                }
                write_xml(&mut new_text, &Event::End(e));
            }

            Ok(Event::Text(e)) => {
                if rubys <= 0 {
                    new_text.push_str(&add_html_furigana(
                        to_str(&e),
                        tokenizer,
                        accent_dict,
                        exclude_kanji,
                        subs,
                        learner,
                        use_hiragana,
                        mark_accent,
                    ));
                } else {
                    write_xml(&mut new_text, &Event::Text(e));
                }
            }

            // All other events, just re-write them verbatim.
            Ok(e) => write_xml(&mut new_text, &e),
        }
    }

    new_text
}

/// Takes an xml event and writes it verbatim to the given string.
///
/// NOTE: really what we want is for the events to provide their byte index range
/// in the original text, so we could just write that, and even double-check that
/// we're not missing anything.  But for some reason quick_xml doesn't provide
/// that information.
fn write_xml(text: &mut String, event: &quick_xml::events::Event) {
    match event {
        Event::Start(e) => {
            text.push_str("<");
            text.push_str(to_str(e));
            text.push_str(">");
        }

        Event::End(e) => {
            text.push_str("</");
            text.push_str(to_str(e));
            text.push_str(">");
        }

        Event::Empty(e) => {
            text.push_str("<");
            text.push_str(to_str(e));
            text.push_str("/>");
        }

        Event::CData(e) => {
            text.push_str("<![CDATA[");
            text.push_str(to_str(e));
            text.push_str("]]>");
        }

        Event::Comment(e) => {
            text.push_str("<!--");
            text.push_str(to_str(e));
            text.push_str("-->");
        }

        Event::Decl(e) => {
            text.push_str("<?");
            text.push_str(to_str(e));
            text.push_str("?>");
        }

        Event::PI(e) => {
            text.push_str("<?");
            text.push_str(to_str(e));
            text.push_str("?>");
        }

        Event::DocType(e) => {
            text.push_str("<!DOCTYPE");
            text.push_str(to_str(e));
            text.push_str(">");
        }

        Event::Text(e) => text.push_str(to_str(e)),

        _ => unreachable!(),
    }
}

/// Adds furigana to Japanese text, using html ruby tags.
fn add_html_furigana(
    text: &str,
    tokenizer: &Tokenizer,
    accent_dict: &AccentDict,
    exclude_kanji: &FnvHashSet<char>,
    subs: &FnvHashMap<(Cow<str>, Cow<str>), (String, String)>,
    learner: &mut Learner,
    use_hiragana: bool,
    mark_accent: bool,
) -> String {
    let mut worker = tokenizer.new_worker();

    worker.reset_sentence(text);
    worker.tokenize();

    let mut new_text = String::new();
    for i in 0..worker.num_tokens() {
        let t = worker.token(i);
        let (surface, kana, pitches) = {
            let surface = t.surface();
            let feature = t.feature();

            let kana_1 = feature.rsplit(",").nth(0).unwrap();
            let kana_2 = feature.rsplit(",").nth(1).unwrap();
            let word = feature.rsplit(",").nth(2).unwrap();

            let (kana, pitch_kana) = if let Some((sub_kana, sub_pitch_kana)) =
                subs.get(&(Cow::from(surface), Cow::from(kana_1)))
            {
                (sub_kana.as_str(), sub_pitch_kana.as_str())
            } else {
                (kana_1, kana_2)
            };

            let pitches = if mark_accent {
                accent_dict.get(word, pitch_kana)
            } else {
                &[]
            };

            (surface, kana, pitches)
        };

        let needs_help = learner.process(surface);

        if !needs_help {
            new_text.push_str(surface);
            continue;
        }

        let kana = if use_hiragana {
            katakana_to_hiragana_string(kana)
        } else {
            kana.into()
        };

        let furigana_text = apply_furigana(surface, &kana, pitches, exclude_kanji);

        if furigana_text.is_empty() {
            new_text.push_str(surface);
        } else {
            for (surf, furi) in furigana_text.iter() {
                if furi.is_empty() {
                    new_text.push_str(surf);
                    continue;
                }

                new_text.push_str("<ruby>");
                new_text.push_str(surf);
                new_text.push_str("<rt>");
                new_text.push_str(furi);
                new_text.push_str("</rt></ruby>");
            }
        }
    }

    new_text
}

/// Returns a segmented list of (surface, furigana) pairs.
///
/// The furigana component of a pair may be empty, indicating no
/// furigana is needed for that surface element.
fn apply_furigana<'a>(
    surface: &'a str,
    kana: &'a str,
    pitches: &[u8],
    exclude_kanji: &FnvHashSet<char>,
) -> Vec<(&'a str, String)> {
    let mut out: Vec<(&str, String)> = Vec::new();

    if furigana_unneeded(surface, exclude_kanji) || !is_kana_str(kana) {
        return Vec::new();
    }

    let mut surface = surface;
    let mut kana = kana;

    // Trim any kana from the start.
    {
        let mut start_s = 0;
        let mut start_k = 0;
        for (sc, kc) in surface.chars().zip(kana.chars()) {
            if is_equivalent_kana(sc, kc) {
                start_s += sc.len_utf8();
                start_k += kc.len_utf8();
            } else {
                break;
            }
        }
        out.push((&surface[..start_s], "".into()));
        surface = &surface[start_s..];
        kana = &kana[start_k..];
    }

    // Trim any kana from the end.
    {
        let mut end_s = surface.len();
        let mut end_k = kana.len();
        for (sc, kc) in surface.chars().rev().zip(kana.chars().rev()) {
            if is_equivalent_kana(sc, kc) {
                end_s -= sc.len_utf8();
                end_k -= kc.len_utf8();
            } else {
                break;
            }
        }
        out.push((&surface[end_s..], "".into()));
        surface = &surface[..end_s];
        kana = &kana[..end_k];
    }

    // Try to uniquely match kana in the middle.
    //
    // This is just best-effort, and bails in any non-trivial cases.
    while let Some((si, sc)) = surface.char_indices().find(|(_, c)| is_kana(*c)) {
        // If there's more than one match, bail.
        let equivalent_kana_count = kana
            .chars()
            .map(|c| is_equivalent_kana(c, sc))
            .fold(0usize, |count, hit| count + hit as usize);
        if equivalent_kana_count != 1 {
            break;
        }

        // Find the one match.
        let (ki, kc) = kana
            .char_indices()
            .find(|(_, c)| is_equivalent_kana(sc, *c))
            .unwrap();

        // Insert the segments.
        out.insert(out.len() - 2, (&surface[..si], kana[..ki].into()));
        out.insert(
            out.len() - 2,
            (&surface[si..(si + sc.len_utf8())], "".into()),
        );
        surface = &surface[(si + sc.len_utf8())..];
        kana = &kana[(ki + kc.len_utf8())..];
    }

    // Left over.
    out.insert(out.len() - 1, (surface, kana.into()));
    out.retain(|(s, _)| !s.is_empty());

    // Attach pitch accent indicator(s) if we have any.
    if !pitches.is_empty() && pitches[0] <= 9 {
        let last = out.last_mut().unwrap();
        last.1.push_str("<span class=\"pitch\">");
        last.1.push(match pitches[0] {
            0 => '０',
            1 => '１',
            2 => '２',
            3 => '３',
            4 => '４',
            5 => '５',
            6 => '６',
            7 => '７',
            8 => '８',
            9 => '９',
            _ => unreachable!(),
        });
        last.1.push_str("</span>");
    }

    out
}

/// Due to the way this is used, this isn't meant to be exact, but instead
/// liberal in what it considers equivalent.
fn is_equivalent_kana(a: char, b: char) -> bool {
    const PAIRS: &[[char; 2]] = &[['は', 'わ'], ['を', 'お'], ['づ', 'ず'], ['へ', 'え']];
    const VOWELS: &[char] = &['あ', 'い', 'う', 'え', 'お', 'ぁ', 'ぃ', 'ぅ', 'ぇ', 'ぉ'];

    let (a, b) = match (normalize_kana(a), normalize_kana(b)) {
        (Some(a), Some(b)) => (a, b),
        _ => return false,
    };

    if a == b {
        return true;
    }

    if a == 'ー' && VOWELS.contains(&b) {
        return true;
    }

    if b == 'ー' && VOWELS.contains(&a) {
        return true;
    }

    for &[c, d] in PAIRS {
        if (a == c && b == d) || (a == d && b == c) {
            return true;
        }
    }

    false
}

const HIRAGANA: u32 = 0x3041;
const KATAKANA: u32 = 0x30A1;
const KANA_COUNT: u32 = 0x3097 - HIRAGANA;

pub fn is_kana(c: char) -> bool {
    if c == 'ー' {
        return true;
    }

    let c = c as u32;

    if c >= HIRAGANA && c < (HIRAGANA + KANA_COUNT) {
        return true;
    }

    if c >= KATAKANA && c < (KATAKANA + KANA_COUNT) {
        return true;
    }

    return false;
}

pub fn is_kana_str(text: &str) -> bool {
    text.chars().all(|c| is_kana(c))
}

pub fn normalize_kana(c: char) -> Option<char> {
    if !is_kana(c) {
        return None;
    }

    Some(katakana_to_hiragana(c).unwrap_or(c))
}

/// Returns true if furigana defininitely isn't needed.
pub fn furigana_unneeded(text: &str, exclude_kanji: &FnvHashSet<char>) -> bool {
    text.chars().all(|c| {
        is_kana(c) || c.is_ascii() || c.is_numeric() || c == '々' || exclude_kanji.contains(&c)
    })
}

pub fn hiragana_to_katakana(c: char) -> Option<char> {
    let c = c as u32;
    if c >= HIRAGANA && c < (HIRAGANA + KANA_COUNT) {
        char::try_from(c + KATAKANA - HIRAGANA).ok()
    } else {
        None
    }
}

pub fn katakana_to_hiragana(c: char) -> Option<char> {
    let c = c as u32;
    if c >= KATAKANA && c < (KATAKANA + KANA_COUNT) {
        char::try_from(c - KATAKANA + HIRAGANA).ok()
    } else {
        None
    }
}

pub fn katakana_to_hiragana_string(text: &str) -> String {
    let mut new_text = String::new();

    for c in text.chars() {
        new_text.push(katakana_to_hiragana(c).unwrap_or(c));
    }

    new_text
}

pub fn hiragana_to_katakana_string(text: &str) -> String {
    let mut new_text = String::new();

    for c in text.chars() {
        new_text.push(hiragana_to_katakana(c).unwrap_or(c));
    }

    new_text
}

#[cfg(test)]
mod tests {
    use super::*;

    // Share `FuriganaGenerator` among tests, since it's expensive to set up.
    pub fn get_furigana_gen() -> &'static FuriganaGenerator {
        use std::sync::OnceLock;
        static FURIGEN: OnceLock<FuriganaGenerator> = OnceLock::new();
        FURIGEN.get_or_init(|| FuriganaGenerator::new(0, false, false))
    }
    pub fn get_furigana_gen_with_accent() -> &'static FuriganaGenerator {
        use std::sync::OnceLock;
        static FURIGEN: OnceLock<FuriganaGenerator> = OnceLock::new();
        FURIGEN.get_or_init(|| FuriganaGenerator::new(0, false, true))
    }

    #[test]
    fn apply_furigana_01() {
        let surface = "へぇ";
        let kana = "ヘー";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert!(pairs.is_empty());
    }

    #[test]
    fn apply_furigana_02() {
        let surface = "へぇー";
        let kana = "ヘー";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert!(pairs.is_empty());
    }

    #[test]
    fn apply_furigana_03() {
        let surface = "へ";
        let kana = "え";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert!(pairs.is_empty());
    }

    #[test]
    fn apply_furigana_04() {
        let surface = "食べる";
        let kana = "タベル";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert_eq!(&[("食", "タ".into()), ("べる", "".into())], &pairs[..]);
    }

    #[test]
    fn apply_furigana_05() {
        let surface = "流れ出す";
        let kana = "ながれだす";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert_eq!(
            &[
                ("流", "なが".into()),
                ("れ", "".into()),
                ("出", "だ".into()),
                ("す", "".into())
            ],
            &pairs[..]
        );
    }

    #[test]
    fn apply_furigana_06() {
        let surface = "物の怪";
        let kana = "もののけ";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert_eq!(&[("物の怪", "もののけ".into())], &pairs[..]);
    }

    #[test]
    fn apply_furigana_07() {
        let surface = "ご飯";
        let kana = "ゴハン";
        let pairs = apply_furigana(surface, kana, &[], &FnvHashSet::default());

        assert_eq!(&[("ご", "".into()), ("飯", "ハン".into())], &pairs[..]);
    }

    #[test]
    fn is_equivalent_kana_01() {
        assert!(is_equivalent_kana('か', 'カ'));
        assert!(is_equivalent_kana('カ', 'か'));
        assert!(is_equivalent_kana('ぁ', 'ァ'));
        assert!(is_equivalent_kana('ァ', 'ぁ'));
        assert!(is_equivalent_kana('は', 'わ'));
        assert!(is_equivalent_kana('わ', 'は'));
        assert!(is_equivalent_kana('を', 'お'));
        assert!(is_equivalent_kana('お', 'を'));
        assert!(is_equivalent_kana('づ', 'ず'));
        assert!(is_equivalent_kana('ず', 'づ'));
        assert!(is_equivalent_kana('ー', 'あ'));
        assert!(is_equivalent_kana('あ', 'ー'));
        assert!(is_equivalent_kana('ー', 'ぁ'));
        assert!(is_equivalent_kana('ぁ', 'ー'));

        assert!(!is_equivalent_kana('は', 'ば'));
        assert!(!is_equivalent_kana('ー', 'か'));
        assert!(!is_equivalent_kana('た', '食'));
    }

    #[test]
    fn tokenize_01() {
        let mut worker = get_furigana_gen().tokenizer.new_worker();

        // General.
        worker.reset_sentence("食べている");
        worker.tokenize();

        assert_eq!(3, worker.num_tokens());
        assert_eq!("食べ", worker.token(0).surface());
        assert_eq!(
            "動詞,自立,*,*,一段,連用形,食べる,タベ,タベ",
            worker.token(0).feature()
        );
        assert_eq!("て", worker.token(1).surface());
        assert_eq!("助詞,接続助詞,*,*,*,*,て,テ,テ", worker.token(1).feature());
        assert_eq!("いる", worker.token(2).surface());
        assert_eq!(
            "動詞,非自立,*,*,一段,基本形,いる,イル,イル",
            worker.token(2).feature()
        );
    }

    #[test]
    fn tokenize_02() {
        let mut worker = get_furigana_gen().tokenizer.new_worker();

        worker.reset_sentence("そう");
        worker.tokenize();

        assert_eq!(1, worker.num_tokens());
        assert_eq!(
            "副詞,助詞類接続,*,*,*,*,そう,ソウ,ソー",
            worker.token(0).feature()
        );
    }

    #[test]
    fn add_html_furigana_01() {
        let mut gen = get_furigana_gen().new_session(false);
        let mut gen_accent = get_furigana_gen_with_accent().new_session(false);

        let text = r#"<sup class="食う">食べる</sup>のは<ruby>良</ruby>いね！<hi />"#;
        let furi_1 = gen.add_html_furigana(text);
        let furi_2 = gen_accent.add_html_furigana(text);

        assert_eq!(
            furi_1,
            r#"<sup class="食う"><ruby>食<rt>タ</rt></ruby>べる</sup>のは<ruby>良</ruby>いね！<hi />"#
        );
        assert_eq!(
            furi_2,
            r#"<sup class="食う"><ruby>食<rt>タ</rt></ruby><ruby>べる<rt><span class="pitch">２</span></rt></ruby></sup>のは<ruby>良</ruby>いね！<hi />"#
        );
    }

    // Testing custom substitutions.
    #[test]
    fn add_html_furigana_02() {
        let mut gen = get_furigana_gen().new_session(false);
        let mut gen_accent = get_furigana_gen_with_accent().new_session(false);

        assert_eq!(
            gen.add_html_furigana("額"),
            "<ruby>額<rt>ヒタイ</rt></ruby>"
        );
        assert_eq!(
            gen_accent.add_html_furigana("額"),
            "<ruby>額<rt>ヒタイ<span class=\"pitch\">０</span></rt></ruby>"
        );

        assert_eq!(gen.add_html_furigana("他"), "<ruby>他<rt>ホカ</rt></ruby>");
        assert_eq!(
            gen_accent.add_html_furigana("他"),
            "<ruby>他<rt>ホカ<span class=\"pitch\">０</span></rt></ruby>"
        );

        assert_eq!(
            gen.add_html_furigana("私"),
            "<ruby>私<rt>ワタシ</rt></ruby>"
        );
        assert_eq!(
            gen_accent.add_html_furigana("私"),
            "<ruby>私<rt>ワタシ<span class=\"pitch\">０</span></rt></ruby>"
        );

        // The added 卵 is to trigger the parse we're testing of 等.
        assert_eq!(
            gen.add_html_furigana("卵等"),
            "<ruby>卵<rt>タマゴ</rt></ruby><ruby>等<rt>ナド</rt></ruby>"
        );

        assert_eq!(
            gen.add_html_furigana("大分"),
            "<ruby>大分<rt>ダイブ</rt></ruby>"
        );

        assert_eq!(
            gen.add_html_furigana("日本"),
            "<ruby>日本<rt>ニホン</rt></ruby>"
        );

        assert_eq!(
            gen.add_html_furigana("日本人"),
            "<ruby>日本人<rt>ニホンジン</rt></ruby>"
        );
    }
}

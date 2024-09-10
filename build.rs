use std::{
    env,
    fs::File,
    io::{BufReader, Write},
    path::Path,
};

const KANJI: &str = include_str!("data/kanji_frequency.txt");

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();

    // Write frequency-ordered kanji array to rust file.
    {
        let dest_path = Path::new(&out_dir).join("kanji_freq_inc.rs");
        let mut f = File::create(&dest_path).unwrap();

        f.write_all("const KANJI_FREQ: &[char] = &[".as_bytes())
            .unwrap();

        for c in KANJI.chars() {
            if c.is_whitespace() {
                continue;
            }

            f.write_all(format!("\n'{}',", c).as_bytes()).unwrap();
        }

        f.write_all("\n];".as_bytes()).unwrap();
    }

    // Write compressed dictionary to .lz4 file.
    {
        // Read and decompress file from .xz.
        let dict_data = {
            let f = File::open("data/dictionary/system.dic.xz").unwrap();
            let mut data = Vec::new();
            lzma_rs::xz_decompress(&mut BufReader::new(f), &mut data).unwrap();

            data
        };

        // Recompress to .lz4.
        let dest_path = Path::new(&out_dir).join("system.dic.lz4");
        let f = File::create(dest_path).unwrap();
        let mut encoder = lz4_flex::frame::FrameEncoder::new(f);
        encoder.write(&dict_data).unwrap();
        encoder.finish().unwrap();
    }
}

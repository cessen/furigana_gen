use std::collections::HashMap;

const LEARN_RATE: f64 = 0.7;
const MIN_MAX_DISTANCE: usize = 10;
const MAX_MAX_DISTANCE: usize = 75000;

#[derive(Debug, Copy, Clone)]
pub(crate) struct WordStats {
    // The last position (in words processed) that this word was seen at.
    last_seen_at: usize,

    // How many times this word has been seen so far.
    pub times_seen: usize,

    // Maximum distance before helps is needed again.
    pub max_distance: usize,
}

pub struct Learner {
    stats: HashMap<String, WordStats>,
    words_processed: usize,
    times_seen_threshold: usize,
}

impl Learner {
    pub fn new(times_seen_threshold: usize) -> Self {
        Self {
            stats: HashMap::new(),
            words_processed: 0,
            times_seen_threshold: times_seen_threshold,
        }
    }

    /// Returns the word stats, sorted by how "well known" they are according
    /// to the `max_distance` metric.
    pub(crate) fn word_stats(&self) -> (usize, Vec<(String, WordStats)>) {
        let mut stats: Vec<(String, WordStats)> = self
            .stats
            .iter()
            .map(|(w, s)| (w.clone(), s.clone()))
            .collect();

        stats.sort_unstable_by_key(|(_, s)| (s.max_distance, s.times_seen));
        stats.reverse();

        (self.words_processed, stats)
    }

    pub fn record(&mut self, word: &str) {
        self.stats
            .entry(word.to_string())
            .and_modify(|stats| {
                let distance = self.words_processed - stats.last_seen_at;

                stats.last_seen_at = self.words_processed;
                stats.times_seen += 1;
                if stats.times_seen <= self.times_seen_threshold {
                    return;
                }

                stats.max_distance +=
                    distance.min((stats.max_distance as f64 * LEARN_RATE) as usize);

                stats.max_distance = stats.max_distance.min(MAX_MAX_DISTANCE);
            })
            .or_insert(WordStats {
                last_seen_at: self.words_processed,
                times_seen: 1,
                max_distance: MIN_MAX_DISTANCE,
            });
        self.words_processed += 1;
    }

    pub fn needs_help(&self, word: &str) -> bool {
        if let Some(stats) = self.stats.get(word) {
            let distance = self.words_processed - stats.last_seen_at;
            stats.times_seen <= self.times_seen_threshold || distance > stats.max_distance
        } else {
            true
        }
    }
}

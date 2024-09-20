use fnv::FnvHashMap;

const LEARN_RATE: f64 = 0.7;
const MAX_DISTANCE_FLOOR: usize = 15;
const MAX_DISTANCE_CEILING: usize = 100000;

#[derive(Debug, Copy, Clone)]
pub(crate) struct WordStats {
    // The last position (in characters processed) that this word was seen at.
    last_seen_at: usize,

    // The last position (in characters processed) that this word had help.
    last_helped_at: usize,

    // How many times this word has been seen so far.
    pub times_seen: usize,

    // Maximum distance (in characters) before help is needed again.
    pub max_distance: usize,
}

pub struct Learner {
    stats: FnvHashMap<String, WordStats>,
    chars_processed: usize,
    words_processed: usize,
    times_seen_threshold: usize,
}

impl Learner {
    pub fn new(times_seen_threshold: usize) -> Self {
        Self {
            stats: FnvHashMap::default(),
            chars_processed: 0,
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

    /// Processes a word, and returns whether it needs help or not.
    pub fn process(&mut self, word: &str) -> bool {
        if self.times_seen_threshold == usize::MAX {
            return true;
        }

        // Get word stats entry.
        let word_stats = if let Some(word_stats) = self.stats.get_mut(word) {
            word_stats
        } else {
            self.stats.insert(
                word.into(),
                WordStats {
                    last_seen_at: 0,
                    last_helped_at: 0,
                    times_seen: 0,
                    max_distance: MAX_DISTANCE_FLOOR,
                },
            );
            self.stats.get_mut(word).unwrap()
        };

        // Determine if help is needed.
        let help = {
            let help_distance = self.chars_processed - word_stats.last_helped_at;
            word_stats.times_seen <= self.times_seen_threshold
                || help_distance > word_stats.max_distance
        };

        // Update word stats.
        {
            let seen_distance = self.chars_processed - word_stats.last_seen_at;

            word_stats.last_seen_at = self.chars_processed;
            if help {
                word_stats.last_helped_at = self.chars_processed;
            }
            word_stats.times_seen += 1;

            if word_stats.times_seen > self.times_seen_threshold {
                word_stats.max_distance +=
                    seen_distance.min((word_stats.max_distance as f64 * LEARN_RATE) as usize);

                // Clamp to floor/ceiling.
                word_stats.max_distance = word_stats
                    .max_distance
                    .clamp(MAX_DISTANCE_FLOOR, MAX_DISTANCE_CEILING);
            }
        }

        // Update position.
        self.chars_processed += word.chars().count();
        self.words_processed += 1;

        return help;
    }
}

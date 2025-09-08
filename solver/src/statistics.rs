use std::time::{Duration, Instant};

/// Statistics tracking for the solver
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct Statistics {
    pub queries_processed: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub timeout_count: u64,
    pub translation_time: u64,
    pub solving_time: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub optimization_count: u64,
    // Fuzzy-side statistics pulled from the C fuzzy solver
    pub fuzzy_num_evaluate: u64,
    pub fuzzy_num_sat: u64,
    pub fuzzy_num_timeouts: u64,
    #[serde(skip)]
    pub start_time: Option<Instant>,
}

impl Statistics {
    pub fn new() -> Self {
        Self {
            start_time: Some(Instant::now()),
            ..Default::default()
        }
    }
    
    pub fn reset(&mut self) {
        *self = Self::new();
    }
    
    pub fn get_total_time(&self) -> Duration {
        self.start_time.map_or(Duration::ZERO, |start| start.elapsed())
    }
    
    pub fn get_success_rate(&self) -> f64 {
        let total = self.sat_count + self.unsat_count + self.timeout_count;
        if total == 0 {
            0.0
        } else {
            (self.sat_count + self.unsat_count) as f64 / total as f64
        }
    }
    
    pub fn get_cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }
}

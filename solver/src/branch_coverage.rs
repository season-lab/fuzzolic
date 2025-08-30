use crate::config::Config;
use anyhow::{Result, Context};
use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use xxhash_rust::xxh32::xxh32;
use log::{info, warn};

const BRANCH_BITMAP_SIZE: usize = 65536;

pub struct BranchCoverage {
    pub branch_bitmap: Vec<u8>,
    pub branch_alt_bitmap: Vec<u8>,
    pub context_bitmap: Vec<u8>,
    visited_branches: HashMap<u64, bool>,
    config: Config,
    last_branch_hash: u64,
    last_branch_inv_idx: u64,
    last_branch_is_interesting: bool,
}

impl BranchCoverage {
    pub fn new(config: &Config) -> Result<Self> {
        Ok(Self {
            branch_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            branch_alt_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            context_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            visited_branches: HashMap::new(),
            config: config.clone(),
            last_branch_hash: 0,
            last_branch_inv_idx: 0,
            last_branch_is_interesting: false,
        })
    }
    
    pub fn load_bitmaps(&mut self) -> Result<()> {
        // Load branch bitmap
        if let Some(ref branch_path) = self.config.branch_bitmap_path {
            Self::load_bitmap(branch_path, &mut self.branch_bitmap)?;
        }
        
        // Load alternative bitmap if specified
        if let Some(ref alt_path) = self.config.branch_alt_bitmap_path {
            Self::load_bitmap(alt_path, &mut self.branch_alt_bitmap)?;
        }
        
        // Load context bitmap
        if let Some(ref context_path) = self.config.context_bitmap_path {
            Self::load_bitmap(context_path, &mut self.context_bitmap)?;
        }
        
        Ok(())
    }
    
    pub fn save_bitmaps(&self) -> Result<()> {
        if let Some(ref branch_path) = self.config.branch_bitmap_path {
            self.save_bitmap(branch_path, &self.branch_bitmap)?;
        }
        
        if let Some(ref alt_path) = self.config.branch_alt_bitmap_path {
            self.save_bitmap(alt_path, &self.branch_alt_bitmap)?;
        }
        
        if let Some(ref context_path) = self.config.context_bitmap_path {
            self.save_bitmap(context_path, &self.context_bitmap)?;
        }
        
        Ok(())
    }
    
    fn load_bitmap<P: AsRef<Path>>(path: P, bitmap: &mut Vec<u8>) -> Result<()> {
        let path = path.as_ref();
        
        match File::open(path) {
            Ok(mut file) => {
                let mut buffer = Vec::new();
                file.read_to_end(&mut buffer)
                    .with_context(|| format!("Failed to read bitmap from {}", path.display()))?;
                
                if buffer.len() == BRANCH_BITMAP_SIZE {
                    bitmap.copy_from_slice(&buffer);
                    info!("Loaded bitmap from {}", path.display());
                } else {
                    warn!("Invalid bitmap size in {}, resetting", path.display());
                    bitmap.fill(0);
                }
            }
            Err(_) => {
                info!("Bitmap {} does not exist, initializing", path.display());
                bitmap.fill(0);
            }
        }
        
        Ok(())
    }
    
    fn save_bitmap<P: AsRef<Path>>(&self, path: P, bitmap: &[u8]) -> Result<()> {
        let path = path.as_ref();
        info!("Saving bitmap to {}", path.display());
        
        let mut file = File::create(path)
            .with_context(|| format!("Failed to create bitmap file {}", path.display()))?;
        
        file.write_all(bitmap)
            .with_context(|| format!("Failed to write bitmap to {}", path.display()))?;
        
        Ok(())
    }
    
    /// Update branch coverage for a given address
    pub fn update_branch_coverage(&mut self, address: usize, taken: bool, is_lib: bool) -> bool {
        self.is_interesting_branch(address as u64, taken, is_lib)
    }
    
    /// Check if a branch is interesting (similar to QSYM/AFL approach)
    pub fn is_interesting_branch(&mut self, pc: u64, taken: bool, _is_lib: bool) -> bool {
        let hash = self.hash_pc(pc, taken);
        let idx = (hash % BRANCH_BITMAP_SIZE as u64) as usize;
        
        let current_count = self.branch_bitmap[idx];
        let new_count = if current_count == 255 { 255 } else { current_count + 1 };
        
        // Update bitmap
        self.branch_bitmap[idx] = new_count;
        
        // Check if this creates new coverage
        let is_interesting = match current_count {
            0 => true, // First time seeing this branch
            1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 => {
                // Power of 2 transitions are interesting
                Self::is_power_of_two(new_count as u32)
            }
            _ => false,
        };
        
        if is_interesting {
            self.visited_branches.insert(hash, true);
        }
        
        self.last_branch_hash = hash;
        self.last_branch_is_interesting = is_interesting;
        
        is_interesting
    }
    
    /// Fuzzolic-style branch coverage check
    pub fn is_interesting_branch_fuzzolic(
        &mut self,
        idx: u16,
        local_count_idx: u16,
        idx_inv: u16,
        local_count_idx_inv: u16,
        addr: u64,
    ) -> bool {
        // This would implement the Fuzzolic-specific branch coverage logic
        // For now, fall back to the standard approach
        self.is_interesting_branch(addr, idx != idx_inv, false)
    }
    
    pub fn is_interesting_memory(&self, addr: u64) -> bool {
        // Simple memory access tracking
        let hash = xxh32(&addr.to_le_bytes(), 0) as usize % BRANCH_BITMAP_SIZE;
        self.branch_bitmap[hash] == 0
    }
    
    pub fn mark_sat_branch(&mut self) {
        // Mark that we found a satisfiable branch
        if self.last_branch_is_interesting {
            info!("Marked SAT branch at hash {}", self.last_branch_hash);
        }
    }
    
    fn hash_pc(&self, pc: u64, taken: bool) -> u64 {
        let taken_byte = if taken { 1u8 } else { 0u8 };
        let mut data = Vec::with_capacity(9);
        data.extend_from_slice(&pc.to_le_bytes());
        data.push(taken_byte);
        xxh32(&data, 0) as u64
    }
    
    fn is_power_of_two(x: u32) -> bool {
        x != 0 && (x & (x - 1)) == 0
    }
}

// Count class lookup table (from AFL)
const COUNT_CLASS_BINARY: [u8; 257] = [
    0, 1, 2, 4, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 16,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
    128,
];

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    
    #[test]
    fn test_branch_coverage_creation() {
        let config = Config {
            testcase_path: Some("test.dat".into()),
            testcase_dir: Some("test_dir".into()),
            output_dir: Some("output".into()),
            memory_bitmap_path: Some("memory.bitmap".into()),
            branch_bitmap_path: Some("test_branch.bitmap".into()),
            context_bitmap_path: Some("test_branch_context.bitmap".into()),
            ..Default::default()
        };
        
        let coverage = BranchCoverage::new(&config).unwrap();
        assert_eq!(coverage.branch_bitmap.len(), BRANCH_BITMAP_SIZE);
    }
    
    #[test]
    fn test_interesting_branch() {
        let config = Config {
            branch_bitmap_path: Some("test_branch.bitmap".into()),
            context_bitmap_path: Some("test_branch_context.bitmap".into()),
            testcase_path: Some("test.dat".into()),
            testcase_dir: Some("test_dir".into()),
            output_dir: Some("output".into()),
            memory_bitmap_path: Some("memory.bitmap".into()),
            ..Default::default()
        };
        
        let mut coverage = BranchCoverage::new(&config).unwrap();
        
        // First time should be interesting (count 0 -> 1)
        assert!(coverage.is_interesting_branch(0x1000, true, false));
        
        // Second time should also be interesting (count 1 -> 2, power of 2)
        assert!(coverage.is_interesting_branch(0x1000, true, false));
        
        // Third time should not be interesting (count 2 -> 3, not power of 2)
        assert!(!coverage.is_interesting_branch(0x1000, true, false));
    }
}

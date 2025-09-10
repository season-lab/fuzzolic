use crate::utils::config::Config;
use anyhow::{Result, Context};
use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use xxhash_rust::xxh32::xxh32;
use log::{info, warn};

pub const BRANCH_BITMAP_SIZE: usize = 65536;

pub struct BranchCoverage {
    pub branch_bitmap: Vec<u8>,
    pub branch_alt_bitmap: Vec<u8>,
    pub context_bitmap: Vec<u8>,
    pub branch_neg_bitmap: Vec<u8>,
    visited_branches: HashMap<u64, bool>,
    config: Config,
    last_branch_hash: u64,
    last_branch_inv_idx: u64,
    last_branch_is_interesting: i32,
}

impl BranchCoverage {
    pub fn new(config: &Config) -> Result<Self> {
        Ok(Self {
            branch_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            branch_alt_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            context_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            branch_neg_bitmap: vec![0; BRANCH_BITMAP_SIZE],
            visited_branches: HashMap::new(),
            config: config.clone(),
            last_branch_hash: 0,
            last_branch_inv_idx: 0,
            last_branch_is_interesting: 0,
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
        self.record_branch(address as u64, taken, is_lib)
    }
    
    /// Check if a branch is interesting (similar to QSYM/AFL approach)
    pub fn record_branch(&mut self, addr: u64, taken: bool, _is_indirect: bool) -> bool {
        let hash = xxh32(&addr.to_le_bytes(), 0) as u64;
        let idx = (hash ^ (taken as u64)) % (BRANCH_BITMAP_SIZE as u64);
        
        // Check if this branch transition is new
        let current_count = self.branch_bitmap[idx as usize];
        
        // Branch is interesting if:
        // 1. It's the first time we see this transition
        // 2. The hit count is a power of 2 (exponential backoff)
        current_count == 0 || Self::is_power_of_two(current_count as u32)
    }
    
    /// Record a branch execution with bitmap update
    pub fn record_branch_execution(&mut self, addr: u64, taken: bool) -> Result<()> {
        let hash = xxh32(&addr.to_le_bytes(), 0) as u64;
        let idx = (hash ^ (taken as u64)) % (BRANCH_BITMAP_SIZE as u64);
        
        // Update branch bitmap with hit count
        let current_count = self.branch_bitmap[idx as usize];
        if current_count < 255 {
            self.branch_bitmap[idx as usize] = current_count + 1;
        }
        
        // Track this branch in visited set
        self.visited_branches.insert(addr, taken);
        
        // Update last branch tracking
        self.last_branch_hash = hash;
        self.last_branch_inv_idx = idx;
        self.last_branch_is_interesting = if self.record_branch(addr, taken, false) { 1 } else { 0 };
        
        Ok(())
    }
    
    /// Fuzzolic-style branch coverage check
    pub fn is_interesting_branch_fuzzolic(
        &mut self,
        idx: u16,
        _local_count_idx: u16,
        idx_inv: u16,
        _local_count_idx_inv: u16,
        addr: u64,
    ) -> bool {
        // This would implement the Fuzzolic-specific branch coverage logic
        // For now, fall back to the standard approach
        if self.record_branch(addr, idx != idx_inv, false) {
            true
        } else {
            false
        }
    }
    
    pub fn is_interesting_memory(&self, addr: u64) -> bool {
        // Simple memory access tracking
        let hash = xxh32(&addr.to_le_bytes(), 0) as usize % BRANCH_BITMAP_SIZE;
        self.branch_bitmap[hash] == 0
    }
    
    pub fn mark_sat_branch(&mut self) {
        // Mark that we found a satisfiable branch - from C implementation
        self.branch_neg_bitmap[self.last_branch_inv_idx as usize] += 1;
        self.branch_bitmap[self.last_branch_inv_idx as usize] |= self.branch_neg_bitmap[self.last_branch_inv_idx as usize];
        self.branch_neg_bitmap[self.last_branch_inv_idx as usize] -= 1;
    }
    
    /// QSYM-style branch coverage (from C implementation)
    pub fn is_interesting_branch_qsym(&mut self, pc: u64, taken: bool, is_lib: bool) -> i32 {
        let h = self.hash_pc(pc, taken);
        let idx = self.get_index(h);
        
        self.branch_neg_bitmap[idx as usize] = self.branch_neg_bitmap[idx as usize].wrapping_add(1);
        
        let ret = if (self.branch_neg_bitmap[idx as usize] | self.branch_bitmap[idx as usize]) != self.branch_bitmap[idx as usize] {
            let inv_h = self.hash_pc(pc, !taken);
            let inv_idx = self.get_index(inv_h);
            
            let result = if !is_lib && self.branch_bitmap[idx as usize] == 0 { 2 } else { 1 };
            
            self.branch_bitmap[idx as usize] |= self.branch_neg_bitmap[idx as usize];
            
            self.branch_neg_bitmap[inv_idx as usize] = self.branch_neg_bitmap[inv_idx as usize].wrapping_add(1);
            self.branch_bitmap[inv_idx as usize] |= self.branch_neg_bitmap[inv_idx as usize];
            self.branch_neg_bitmap[inv_idx as usize] = self.branch_neg_bitmap[inv_idx as usize].wrapping_sub(1);
            
            result
        } else {
            0
        };
        
        self.branch_neg_bitmap[idx as usize] = self.branch_neg_bitmap[idx as usize].wrapping_sub(1);
        self.last_branch_inv_idx = self.get_index(self.hash_pc(pc, !taken));
        
        ret
    }
    
    /// Fuzzolic-style branch coverage (from C implementation)
    pub fn is_interesting_branch_fuzzolic_impl(&mut self, idx: u16, count: u16, idx_inv: u16, count_inv: u16, addr: u64) -> i32 {
        let normalized_hit_count = COUNT_CLASS_BINARY[(count + 1) as usize];
        
        if (normalized_hit_count | self.branch_bitmap[idx as usize]) != self.branch_bitmap[idx as usize] {
            let ret = if addr < 0x10000000 && self.branch_bitmap[idx as usize] == 0 { 2 } else { 1 };
            
            // Update bitmap
            self.branch_bitmap[idx as usize] |= normalized_hit_count;
            
            // Update inverse bitmap
            let normalized_hit_count_inv = COUNT_CLASS_BINARY[(count_inv + 1) as usize];
            self.branch_bitmap[idx_inv as usize] |= normalized_hit_count_inv;
            
            self.last_branch_is_interesting = ret;
            ret
        } else {
            self.last_branch_is_interesting = 0;
            0
        }
    }
    
    fn hash_pc(&self, pc: u64, taken: bool) -> u64 {
        let taken_byte = if taken { 1u8 } else { 0u8 };
        let mut data = Vec::with_capacity(9);
        data.extend_from_slice(&pc.to_le_bytes());
        data.push(taken_byte);
        (xxh32(&data, 0) as u64) % (BRANCH_BITMAP_SIZE as u64)
    }
    
    fn get_index(&self, h: u64) -> u64 {
        ((self.last_branch_hash >> 1) ^ h) % (BRANCH_BITMAP_SIZE as u64)
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


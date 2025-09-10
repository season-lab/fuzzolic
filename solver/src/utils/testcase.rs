use anyhow::{Result, Context};
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use serde::{Serialize, Deserialize};
use std::sync::atomic::{AtomicU64, Ordering};

static TESTCASE_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MutationType {
    NoMutation,
    Trim,
    TrimDel,
    Extend,
    ExtendWithA,
    Replace,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestcaseMutation {
    pub mutation_type: MutationType,
    pub offset: usize,
    pub len: usize,
    pub data: Option<Vec<u8>>,
}

impl TestcaseMutation {
    pub fn new_trim(offset: usize, len: usize) -> Self {
        Self {
            mutation_type: MutationType::Trim,
            offset,
            len,
            data: None,
        }
    }
    
    pub fn new_replace(offset: usize, data: Vec<u8>) -> Self {
        let len = data.len();
        Self {
            mutation_type: MutationType::Replace,
            offset,
            len,
            data: Some(data),
        }
    }
    
    pub fn new_extend(offset: usize, data: Vec<u8>) -> Self {
        let len = data.len();
        Self {
            mutation_type: MutationType::Extend,
            offset,
            len,
            data: Some(data),
        }
    }
    
    pub fn new_bit_flip(byte_idx: usize, bit_idx: usize) -> Self {
        Self {
            mutation_type: MutationType::Replace,
            offset: byte_idx,
            len: 1,
            data: Some(vec![1u8 << bit_idx]), // Will be XORed with original
        }
    }
    
    pub fn new_arithmetic(offset: usize, delta: i32) -> Self {
        Self {
            mutation_type: MutationType::Replace,
            offset,
            len: 1,
            data: Some(vec![delta as u8]), // Will be added to original
        }
    }
    
    pub fn new_overwrite(offset: usize, data: Vec<u8>) -> Self {
        let len = data.len();
        Self {
            mutation_type: MutationType::Replace,
            offset,
            len,
            data: Some(data),
        }
    }
    
    pub fn new_delete(offset: usize, len: usize) -> Self {
        Self {
            mutation_type: MutationType::Trim,
            offset,
            len,
            data: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Testcase {
    pub data: Vec<u8>,
    pub mutations: Vec<TestcaseMutation>,
    id: u64,
}

impl Testcase {
    pub fn new(data: Vec<u8>) -> Self {
        Self {
            data,
            mutations: Vec::new(),
            id: TESTCASE_ID_COUNTER.fetch_add(1, Ordering::SeqCst),
        }
    }
    
    pub fn id(&self) -> u64 {
        self.id
    }
    
    pub fn data(&self) -> &[u8] {
        &self.data
    }
    
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let data = std::fs::read(path.as_ref())
            .with_context(|| format!("Failed to read testcase from {}", path.as_ref().display()))?;
        Ok(Self::new(data))
    }
    
    pub fn size(&self) -> usize {
        self.data.len()
    }
    
    pub fn add_mutation(&mut self, mutation: TestcaseMutation) {
        self.mutations.push(mutation);
    }
    
    pub fn save_to_file(&self, output_dir: &Path) -> Result<Vec<PathBuf>> {
        let mut saved_files = Vec::new();
        
        // Save the main testcase
        let main_path = output_dir.join("testcase.dat");
        self.write_data_to_file(&main_path, &self.data)?;
        saved_files.push(main_path);
        
        // Apply and save mutations
        for (i, mutation) in self.mutations.iter().enumerate() {
            let mutated_data = self.apply_mutation(mutation)?;
            let mutation_path = output_dir.join(format!("testcase_mut_{}.dat", i));
            self.write_data_to_file(&mutation_path, &mutated_data)?;
            saved_files.push(mutation_path);
        }
        
        Ok(saved_files)
    }
    
    fn write_data_to_file(&self, path: &Path, data: &[u8]) -> Result<()> {
        let mut file = File::create(path)
            .with_context(|| format!("Failed to create file {}", path.display()))?;
        file.write_all(data)
            .with_context(|| format!("Failed to write data to {}", path.display()))?;
        Ok(())
    }
    
    pub fn apply_mutation(&self, mutation: &TestcaseMutation) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        
        match mutation.mutation_type {
            MutationType::NoMutation => {
                result.extend_from_slice(&self.data);
            }
            MutationType::Trim => {
                // Remove bytes from offset to offset+len
                for (i, &byte) in self.data.iter().enumerate() {
                    if i < mutation.offset || i >= mutation.offset + mutation.len {
                        result.push(byte);
                    }
                }
            }
            MutationType::TrimDel => {
                // Replace byte at offset with 0
                for (i, &byte) in self.data.iter().enumerate() {
                    if i == mutation.offset {
                        result.push(0);
                    } else {
                        result.push(byte);
                    }
                }
            }
            MutationType::Replace => {
                // Replace bytes starting at offset with new data
                if let Some(ref new_data) = mutation.data {
                    for (i, &byte) in self.data.iter().enumerate() {
                        if i == mutation.offset {
                            result.extend_from_slice(new_data);
                            // Skip the original bytes that are being replaced
                            continue;
                        } else if i > mutation.offset && i < mutation.offset + mutation.len {
                            // Skip bytes being replaced
                            continue;
                        } else {
                            result.push(byte);
                        }
                    }
                } else {
                    anyhow::bail!("Replace mutation requires data");
                }
            }
            MutationType::Extend => {
                // Insert new data at offset
                if let Some(ref new_data) = mutation.data {
                    for (i, &byte) in self.data.iter().enumerate() {
                        if i == mutation.offset {
                            result.extend_from_slice(new_data);
                        }
                        result.push(byte);
                    }
                } else {
                    anyhow::bail!("Extend mutation requires data");
                }
            }
            MutationType::ExtendWithA => {
                // Insert 'A' bytes at offset
                for (i, &byte) in self.data.iter().enumerate() {
                    if i == mutation.offset {
                        for _ in 0..mutation.len {
                            result.push(b'A');
                        }
                    }
                    result.push(byte);
                }
            }
        }
        
        Ok(result)
    }
}


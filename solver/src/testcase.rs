use anyhow::{Result, Context};
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use serde::{Serialize, Deserialize};

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
}

#[derive(Debug, Clone)]
pub struct Testcase {
    pub data: Vec<u8>,
    pub mutations: Vec<TestcaseMutation>,
}

impl Testcase {
    pub fn new(data: Vec<u8>) -> Self {
        Self {
            data,
            mutations: Vec::new(),
        }
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
    
    fn apply_mutation(&self, mutation: &TestcaseMutation) -> Result<Vec<u8>> {
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

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_testcase_creation() {
        let data = vec![1, 2, 3, 4, 5];
        let testcase = Testcase::new(data.clone());
        assert_eq!(testcase.data, data);
        assert_eq!(testcase.size(), 5);
    }
    
    #[test]
    fn test_trim_mutation() {
        let testcase = Testcase::new(vec![1, 2, 3, 4, 5]);
        let mutation = TestcaseMutation::new_trim(1, 2); // Remove bytes 1 and 2
        let result = testcase.apply_mutation(&mutation).unwrap();
        assert_eq!(result, vec![1, 4, 5]);
    }
    
    #[test]
    fn test_replace_mutation() {
        let testcase = Testcase::new(vec![1, 2, 3, 4, 5]);
        let mutation = TestcaseMutation::new_replace(1, vec![10, 11]);
        let result = testcase.apply_mutation(&mutation).unwrap();
        assert_eq!(result, vec![1, 10, 11, 4, 5]);
    }
    
    #[test]
    fn test_extend_mutation() {
        let testcase = Testcase::new(vec![1, 2, 3]);
        let mutation = TestcaseMutation::new_extend(1, vec![10, 11]);
        let result = testcase.apply_mutation(&mutation).unwrap();
        assert_eq!(result, vec![1, 10, 11, 2, 3]);
    }
}

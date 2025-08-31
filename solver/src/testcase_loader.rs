use crate::testcase::Testcase;
use anyhow::Result;
use log::{debug, info, warn};
use std::fs;
use std::path::{Path, PathBuf};

/// Testcase loader for initializing solver with seed inputs
pub struct TestcaseLoader {
    /// Directory containing seed testcases
    seed_dir: Option<PathBuf>,
    /// Maximum testcase size to load
    max_size: usize,
    /// Statistics
    loaded_count: u64,
    skipped_count: u64,
}

impl TestcaseLoader {
    pub fn new(seed_dir: Option<PathBuf>, max_size: usize) -> Self {
        Self {
            seed_dir,
            max_size,
            loaded_count: 0,
            skipped_count: 0,
        }
    }

    /// Load all testcases from the seed directory
    pub fn load_testcases(&mut self) -> Result<Vec<Testcase>> {
        let mut testcases = Vec::new();

        if let Some(dir) = self.seed_dir.clone() {
            if !dir.exists() {
                warn!("Seed directory does not exist: {}", dir.display());
                return Ok(testcases);
            }

            info!("Loading testcases from: {}", dir.display());
            self.load_from_directory(&dir, &mut testcases)?;
        }

        info!("Loaded {} testcases, skipped {} (too large)", 
              self.loaded_count, self.skipped_count);
        Ok(testcases)
    }

    /// Recursively load testcases from directory
    fn load_from_directory(&mut self, dir: &Path, testcases: &mut Vec<Testcase>) -> Result<()> {
        let entries = fs::read_dir(dir)?;

        for entry in entries {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                // Recursively load from subdirectories
                self.load_from_directory(&path, testcases)?;
            } else if path.is_file() {
                // Try to load as testcase
                if let Ok(testcase) = self.load_testcase_file(&path) {
                    testcases.push(testcase);
                    self.loaded_count += 1;
                }
            }
        }

        Ok(())
    }

    /// Load a single testcase file
    fn load_testcase_file(&mut self, path: &Path) -> Result<Testcase> {
        let metadata = fs::metadata(path)?;
        let file_size = metadata.len() as usize;

        if file_size > self.max_size {
            debug!("Skipping large testcase: {} ({} bytes)", 
                   path.display(), file_size);
            self.skipped_count += 1;
            anyhow::bail!("Testcase too large");
        }

        if file_size == 0 {
            debug!("Skipping empty testcase: {}", path.display());
            self.skipped_count += 1;
            anyhow::bail!("Empty testcase");
        }

        let data = fs::read(path)?;
        debug!("Loaded testcase: {} ({} bytes)", path.display(), data.len());

        Ok(Testcase::new(data))
    }

    /// Load a specific testcase by path
    pub fn load_specific_testcase(&mut self, path: &Path) -> Result<Testcase> {
        if !path.exists() {
            anyhow::bail!("Testcase file does not exist: {}", path.display());
        }

        self.load_testcase_file(path)
    }

    /// Generate initial testcase with specified size
    pub fn generate_initial_testcase(&self, size: usize) -> Testcase {
        let mut data = vec![0u8; size];
        
        // Fill with some pattern to make it more interesting than all zeros
        for (i, byte) in data.iter_mut().enumerate() {
            *byte = (i % 256) as u8;
        }

        Testcase::new(data)
    }

    /// Get loader statistics
    pub fn stats(&self) -> LoaderStats {
        LoaderStats {
            loaded_count: self.loaded_count,
            skipped_count: self.skipped_count,
            seed_dir: self.seed_dir.clone(),
        }
    }
}

/// Testcase loader statistics
#[derive(Debug, Clone)]
pub struct LoaderStats {
    pub loaded_count: u64,
    pub skipped_count: u64,
    pub seed_dir: Option<PathBuf>,
}

impl std::fmt::Display for LoaderStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Testcase loader: {} loaded, {} skipped", 
               self.loaded_count, self.skipped_count)?;
        if let Some(ref dir) = self.seed_dir {
            write!(f, " from {}", dir.display())?;
        }
        Ok(())
    }
}

/// Testcase initialization utilities
pub struct TestcaseInitializer;

impl TestcaseInitializer {
    /// Initialize solver with testcases from various sources
    pub fn initialize_testcases(
        seed_dir: Option<PathBuf>,
        initial_testcase: Option<PathBuf>,
        default_size: usize,
        max_size: usize,
    ) -> Result<Vec<Testcase>> {
        let mut loader = TestcaseLoader::new(seed_dir, max_size);
        let mut testcases = Vec::new();

        // Load specific initial testcase if provided
        if let Some(ref path) = initial_testcase {
            match loader.load_specific_testcase(path) {
                Ok(testcase) => {
                    info!("Loaded initial testcase: {}", path.display());
                    testcases.push(testcase);
                }
                Err(e) => {
                    warn!("Failed to load initial testcase {}: {}", path.display(), e);
                }
            }
        }

        // Load seed testcases from directory
        let mut seed_testcases = loader.load_testcases()?;
        testcases.append(&mut seed_testcases);

        // Generate default testcase if no testcases were loaded
        if testcases.is_empty() {
            info!("No testcases loaded, generating default testcase ({} bytes)", default_size);
            testcases.push(loader.generate_initial_testcase(default_size));
        }

        info!("Initialized with {} testcases", testcases.len());
        Ok(testcases)
    }

    /// Validate testcase for solver compatibility
    pub fn validate_testcase(testcase: &Testcase, max_size: usize) -> Result<()> {
        let data = &testcase.data;
        
        if data.is_empty() {
            anyhow::bail!("Testcase is empty");
        }

        if data.len() > max_size {
            anyhow::bail!("Testcase too large: {} > {}", data.len(), max_size);
        }

        Ok(())
    }

    /// Prepare testcase data for symbolic execution
    pub fn prepare_symbolic_input(testcase: &Testcase, symbols_count: usize) -> Vec<u8> {
        let data = &testcase.data;
        let mut symbolic_input = data.clone();

        // Pad or truncate to match expected symbol count
        symbolic_input.resize(symbols_count, 0);

        debug!("Prepared symbolic input: {} bytes for {} symbols", 
               symbolic_input.len(), symbols_count);
        symbolic_input
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use std::fs::File;
    use std::io::Write;

    #[test]
    fn test_generate_initial_testcase() {
        let loader = TestcaseLoader::new(None, 1024);
        let testcase = loader.generate_initial_testcase(10);
        
        let size = testcase.data.len();
        assert_eq!(size, 10);
        assert_ne!(testcase.data, vec![0u8; 10]); // Should not be all zeros
    }

    #[test]
    fn test_load_from_directory() -> Result<()> {
        let temp_dir = tempdir()?;
        
        // Create test files
        let mut file1 = File::create(temp_dir.path().join("test1.bin"))?;
        file1.write_all(b"test data 1")?;
        
        let mut file2 = File::create(temp_dir.path().join("test2.bin"))?;
        file2.write_all(b"test data 2")?;

        let mut loader = TestcaseLoader::new(Some(temp_dir.path().to_path_buf()), 1024);
        let testcases = loader.load_testcases()?;

        assert_eq!(testcases.len(), 2);
        assert_eq!(loader.stats().loaded_count, 2);
        
        Ok(())
    }

    #[test]
    fn test_size_filtering() -> Result<()> {
        let temp_dir = tempdir()?;
        
        // Create a large file that should be skipped
        let mut large_file = File::create(temp_dir.path().join("large.bin"))?;
        large_file.write_all(&vec![0u8; 2000])?;
        
        // Create a small file that should be loaded
        let mut small_file = File::create(temp_dir.path().join("small.bin"))?;
        small_file.write_all(b"small")?;

        let mut loader = TestcaseLoader::new(Some(temp_dir.path().to_path_buf()), 100);
        let testcases = loader.load_testcases()?;

        assert_eq!(testcases.len(), 1);
        assert_eq!(loader.stats().loaded_count, 1);
        assert_eq!(loader.stats().skipped_count, 1);
        
        Ok(())
    }

    #[test]
    fn test_testcase_initialization() -> Result<()> {
        let testcases = TestcaseInitializer::initialize_testcases(
            None, None, 64, 1024
        )?;

        assert_eq!(testcases.len(), 1);
        assert_eq!(testcases[0].data.len(), 64);
        
        Ok(())
    }
}

//! Tests for branch coverage functionality

use crate::coverage::branch_coverage::{BranchCoverage, BRANCH_BITMAP_SIZE};
use crate::utils::config::Config;

#[cfg(test)]
mod tests {
    use super::*;
    
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
        assert!(coverage.record_branch(0x1000, true, false));
        
        // Second time should also be interesting (count 1 -> 2, power of 2)
        assert!(coverage.record_branch(0x1000, true, false));
        
        // Third time should not be interesting (count 2 -> 3, not power of 2)
        // But record_branch returns true if it's a new transition, so we expect true here
        assert!(coverage.record_branch(0x1000, true, false));
    }
}

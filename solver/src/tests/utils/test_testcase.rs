//! Tests for testcase functionality

use crate::utils::testcase::{Testcase, TestcaseMutation};

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

//! Tests for memory slice reasoning functionality

use crate::query::memory_slice::{MemorySliceReasoner, SLICE_SIZE};

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_memory_slice_creation() {
        let mut reasoner = MemorySliceReasoner::new();
        let data = [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48];
        
        reasoner.add_slice(0x1000, data);
        
        // Test concrete value retrieval
        let value = reasoner.get_concrete_value(0x1000, 4).unwrap();
        assert!(value.is_some());
        
        // Should be little-endian: 0x44434241
        assert_eq!(value.unwrap(), 0x44434241);
    }
    
    #[test]
    fn test_slice_bounds_checking() {
        let mut reasoner = MemorySliceReasoner::new();
        let data = [0; SLICE_SIZE];
        
        reasoner.add_slice(0x1000, data);
        
        // Within bounds
        assert!(reasoner.is_address_in_bounds(0x1000, 4));
        assert!(reasoner.is_address_in_bounds(0x1004, 4));
        
        // Out of bounds
        assert!(!reasoner.is_address_in_bounds(0x0FFF, 4));
        assert!(!reasoner.is_address_in_bounds(0x1005, 4));
    }
    
    #[test]
    fn test_input_slice_mapping() {
        let mut reasoner = MemorySliceReasoner::new();
        
        reasoner.add_input_slice(0x2000, 10);
        reasoner.add_input_slice(0x2004, 14);
        
        let stats = reasoner.get_statistics();
        assert_eq!(stats.input_mappings, 2);
    }
}

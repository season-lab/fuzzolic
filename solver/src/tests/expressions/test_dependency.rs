//! Tests for expression dependency graph functionality

use crate::expressions::dependency::DependencyGraph;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dependency_creation() {
        let mut graph = DependencyGraph::new(100);
        
        let inputs = [1, 2, 3].iter().cloned().collect();
        let dep_id = graph.add_expression(&inputs, 10).unwrap();
        
        assert_eq!(dep_id, 0);
        assert_eq!(graph.dependencies.len(), 1);
        
        let dep = graph.get_dependency(dep_id).unwrap();
        assert_eq!(dep.inputs.len(), 3);
        assert_eq!(dep.exprs.len(), 1);
        assert!(dep.has_expr(10));
    }
    
    #[test]
    fn test_dependency_merging() {
        let mut graph = DependencyGraph::new(100);
        
        // Create first dependency
        let inputs1 = [1, 2].iter().cloned().collect();
        let dep_id1 = graph.add_expression(&inputs1, 10).unwrap();
        
        // Create second dependency with overlapping inputs
        let inputs2 = [2, 3].iter().cloned().collect();
        let dep_id2 = graph.add_expression(&inputs2, 11).unwrap();
        
        // Should merge into the same dependency
        assert_eq!(dep_id1, dep_id2);
        
        let dep = graph.get_dependency(dep_id1).unwrap();
        assert_eq!(dep.inputs.len(), 3); // 1, 2, 3
        assert_eq!(dep.exprs.len(), 2); // 10, 11
    }
    
    #[test]
    fn test_expression_input_lookup() {
        let mut graph = DependencyGraph::new(100);
        
        let inputs = [5, 10, 15].iter().cloned().collect();
        graph.add_expression(&inputs, 100).unwrap();
        
        let result_inputs = graph.get_expression_inputs(100);
        assert_eq!(result_inputs, inputs);
        
        let empty_inputs = graph.get_expression_inputs(999);
        assert!(empty_inputs.is_empty());
    }
}

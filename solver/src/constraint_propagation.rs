use anyhow::Result;
use log::{debug, info, warn};
use std::collections::{HashMap, HashSet, VecDeque};
use crate::expression::{Expr, OpKind};
use crate::dependency_graph::{DependencyGraph, DependencyNode, DependencyNodeType};

/// Constraint propagation engine for preprocessing expressions
pub struct ConstraintPropagator {
    constraints: Vec<Constraint>,
    variable_domains: HashMap<u64, Domain>,
    propagation_queue: VecDeque<PropagationEvent>,
    dependency_graph: DependencyGraph,
    max_iterations: usize,
}

impl ConstraintPropagator {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            variable_domains: HashMap::new(),
            propagation_queue: VecDeque::new(),
            dependency_graph: DependencyGraph::new(10000),
            max_iterations: 1000,
        }
    }
    
    /// Add constraint to the propagation system
    pub fn add_constraint(&mut self, expr: &Expr) -> Result<usize> {
        let constraint_id = self.constraints.len();
        let constraint = Constraint::from_expression(constraint_id, expr)?;
        
        // Add to dependency graph
        let node = DependencyNode::new(constraint_id, DependencyNodeType::Constraint);
        self.dependency_graph.add_node(constraint_id, node)?;
        
        // Extract variables and add dependencies
        let variables = self.extract_variables(expr);
        for var_id in variables {
            self.dependency_graph.add_dependency(constraint_id, var_id as usize)?;
            
            // Initialize domain if not exists
            if !self.variable_domains.contains_key(&var_id) {
                self.variable_domains.insert(var_id, Domain::new_unbounded());
            }
        }
        
        self.constraints.push(constraint);
        
        // Queue initial propagation
        self.propagation_queue.push_back(PropagationEvent::ConstraintAdded(constraint_id));
        
        Ok(constraint_id)
    }
    
    /// Perform constraint propagation until fixpoint
    pub fn propagate(&mut self) -> Result<PropagationResult> {
        let mut iterations = 0;
        let mut changes_made = true;
        let mut total_reductions = 0;
        
        info!("Starting constraint propagation with {} constraints", self.constraints.len());
        
        while changes_made && iterations < self.max_iterations && !self.propagation_queue.is_empty() {
            changes_made = false;
            iterations += 1;
            
            let batch_size = std::cmp::min(self.propagation_queue.len(), 100);
            for _ in 0..batch_size {
                if let Some(event) = self.propagation_queue.pop_front() {
                    match self.process_propagation_event(event)? {
                        PropagationEventResult::DomainReduced(var_id) => {
                            changes_made = true;
                            total_reductions += 1;
                            self.queue_dependent_constraints(var_id)?;
                        }
                        PropagationEventResult::Inconsistency => {
                            return Ok(PropagationResult::Inconsistent);
                        }
                        PropagationEventResult::NoChange => {}
                    }
                }
            }
            
            debug!("Propagation iteration {}: {} reductions", iterations, total_reductions);
        }
        
        if iterations >= self.max_iterations {
            warn!("Constraint propagation reached maximum iterations");
            return Ok(PropagationResult::MaxIterationsReached);
        }
        
        info!("Constraint propagation completed in {} iterations with {} reductions", 
              iterations, total_reductions);
        
        Ok(PropagationResult::Success { 
            iterations, 
            reductions: total_reductions 
        })
    }
    
    /// Process a single propagation event
    fn process_propagation_event(&mut self, event: PropagationEvent) -> Result<PropagationEventResult> {
        match event {
            PropagationEvent::ConstraintAdded(constraint_id) => {
                self.propagate_constraint(constraint_id)
            }
            PropagationEvent::DomainChanged(var_id) => {
                // Find all constraints that depend on this variable
                let dependents = self.dependency_graph.get_dependents(var_id as usize);
                for &constraint_id in &dependents {
                    match self.propagate_constraint(constraint_id)? {
                        PropagationEventResult::DomainReduced(_) => {
                            return Ok(PropagationEventResult::DomainReduced(var_id));
                        }
                        PropagationEventResult::Inconsistency => {
                            return Ok(PropagationEventResult::Inconsistency);
                        }
                        PropagationEventResult::NoChange => {}
                    }
                }
                Ok(PropagationEventResult::NoChange)
            }
        }
    }
    
    /// Propagate a specific constraint
    fn propagate_constraint(&mut self, constraint_id: usize) -> Result<PropagationEventResult> {
        if constraint_id >= self.constraints.len() {
            return Ok(PropagationEventResult::NoChange);
        }
        
        let constraint = &self.constraints[constraint_id].clone();
        
        match constraint.constraint_type {
            ConstraintType::Equality => {
                self.propagate_equality_constraint(constraint)
            }
            ConstraintType::Inequality => {
                self.propagate_inequality_constraint(constraint)
            }
            ConstraintType::Range => {
                self.propagate_range_constraint(constraint)
            }
            ConstraintType::Arithmetic => {
                self.propagate_arithmetic_constraint(constraint)
            }
            ConstraintType::Boolean => {
                self.propagate_boolean_constraint(constraint)
            }
            ConstraintType::Bitvector => {
                self.propagate_bitvector_constraint(constraint)
            }
        }
    }
    
    /// Propagate equality constraint (x = y)
    fn propagate_equality_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        if constraint.variables.len() != 2 {
            return Ok(PropagationEventResult::NoChange);
        }
        
        let var1 = constraint.variables[0];
        let var2 = constraint.variables[1];
        
        let domain1 = self.variable_domains.get(&var1).cloned().unwrap_or(Domain::new_unbounded());
        let domain2 = self.variable_domains.get(&var2).cloned().unwrap_or(Domain::new_unbounded());
        
        // Intersect domains
        let intersection = domain1.intersect(&domain2);
        
        if intersection.is_empty() {
            return Ok(PropagationEventResult::Inconsistency);
        }
        
        let mut changed = false;
        
        // Update domain1 if it changed
        if !domain1.equals(&intersection) {
            self.variable_domains.insert(var1, intersection.clone());
            changed = true;
        }
        
        // Update domain2 if it changed
        if !domain2.equals(&intersection) {
            self.variable_domains.insert(var2, intersection);
            changed = true;
        }
        
        if changed {
            Ok(PropagationEventResult::DomainReduced(var1))
        } else {
            Ok(PropagationEventResult::NoChange)
        }
    }
    
    /// Propagate inequality constraint (x < y, x <= y, etc.)
    fn propagate_inequality_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        if constraint.variables.len() != 2 {
            return Ok(PropagationEventResult::NoChange);
        }
        
        let var1 = constraint.variables[0];
        let var2 = constraint.variables[1];
        
        let domain1 = self.variable_domains.get(&var1).cloned().unwrap_or(Domain::new_unbounded());
        let domain2 = self.variable_domains.get(&var2).cloned().unwrap_or(Domain::new_unbounded());
        
        // For x < y: x.max < y.min should be possible
        // Adjust domains accordingly
        let mut new_domain1 = domain1.clone();
        let mut new_domain2 = domain2.clone();
        let mut changed = false;
        
        match constraint.operator {
            Some(ConstraintOperator::LessThan) => {
                // x < y: x.max < y.min
                if let (Some(max1), Some(min2)) = (domain1.max, domain2.min) {
                    if max1 >= min2 {
                        new_domain1.max = Some(min2 - 1);
                        new_domain2.min = Some(max1 + 1);
                        changed = true;
                    }
                }
            }
            Some(ConstraintOperator::LessThanOrEqual) => {
                // x <= y: x.max <= y.min
                if let (Some(max1), Some(min2)) = (domain1.max, domain2.min) {
                    if max1 > min2 {
                        new_domain1.max = Some(min2);
                        new_domain2.min = Some(max1);
                        changed = true;
                    }
                }
            }
            _ => {}
        }
        
        if new_domain1.is_empty() || new_domain2.is_empty() {
            return Ok(PropagationEventResult::Inconsistency);
        }
        
        if changed {
            self.variable_domains.insert(var1, new_domain1);
            self.variable_domains.insert(var2, new_domain2);
            Ok(PropagationEventResult::DomainReduced(var1))
        } else {
            Ok(PropagationEventResult::NoChange)
        }
    }
    
    /// Propagate range constraint (x in [a, b])
    fn propagate_range_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        if constraint.variables.len() != 1 {
            return Ok(PropagationEventResult::NoChange);
        }
        
        let var_id = constraint.variables[0];
        let current_domain = self.variable_domains.get(&var_id).cloned().unwrap_or(Domain::new_unbounded());
        
        // Create range domain from constraint
        let range_domain = Domain {
            min: constraint.range_min,
            max: constraint.range_max,
        };
        
        let intersection = current_domain.intersect(&range_domain);
        
        if intersection.is_empty() {
            return Ok(PropagationEventResult::Inconsistency);
        }
        
        if !current_domain.equals(&intersection) {
            self.variable_domains.insert(var_id, intersection);
            Ok(PropagationEventResult::DomainReduced(var_id))
        } else {
            Ok(PropagationEventResult::NoChange)
        }
    }
    
    /// Propagate arithmetic constraint (x + y = z, etc.)
    fn propagate_arithmetic_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        // Simplified arithmetic propagation
        // In full implementation, would handle various arithmetic operations
        Ok(PropagationEventResult::NoChange)
    }
    
    /// Propagate boolean constraint
    fn propagate_boolean_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        // Simplified boolean propagation
        // In full implementation, would handle boolean satisfiability
        Ok(PropagationEventResult::NoChange)
    }
    
    /// Propagate bitvector constraint
    fn propagate_bitvector_constraint(&mut self, constraint: &Constraint) -> Result<PropagationEventResult> {
        // Simplified bitvector propagation
        // In full implementation, would handle bitwise operations
        Ok(PropagationEventResult::NoChange)
    }
    
    /// Queue constraints that depend on a variable
    fn queue_dependent_constraints(&mut self, var_id: u64) -> Result<()> {
        let dependents = self.dependency_graph.get_dependents(var_id as usize);
        for &constraint_id in &dependents {
            self.propagation_queue.push_back(PropagationEvent::DomainChanged(var_id));
        }
        Ok(())
    }
    
    /// Extract variable IDs from expression
    fn extract_variables(&self, expr: &Expr) -> Vec<u64> {
        let mut variables = Vec::new();
        
        // In a full implementation, would recursively traverse expression tree
        // For now, use a simplified approach
        if expr.op1_is_const == 0 && !expr.op1.is_null() {
            variables.push(expr.op1 as u64);
        }
        if expr.op2_is_const == 0 && !expr.op2.is_null() {
            variables.push(expr.op2 as u64);
        }
        if expr.op3_is_const == 0 && !expr.op3.is_null() {
            variables.push(expr.op3 as u64);
        }
        
        variables
    }
    
    /// Get final domains after propagation
    pub fn get_domains(&self) -> &HashMap<u64, Domain> {
        &self.variable_domains
    }
    
    /// Check if system is consistent
    pub fn is_consistent(&self) -> bool {
        self.variable_domains.values().all(|domain| !domain.is_empty())
    }
    
    /// Get propagation statistics
    pub fn get_statistics(&self) -> PropagationStatistics {
        PropagationStatistics {
            constraint_count: self.constraints.len(),
            variable_count: self.variable_domains.len(),
            queue_size: self.propagation_queue.len(),
            dependency_edges: self.dependency_graph.edge_count(),
        }
    }
}

/// Represents a constraint in the system
#[derive(Debug, Clone)]
pub struct Constraint {
    pub id: usize,
    pub constraint_type: ConstraintType,
    pub variables: Vec<u64>,
    pub operator: Option<ConstraintOperator>,
    pub range_min: Option<i64>,
    pub range_max: Option<i64>,
}

impl Constraint {
    pub fn from_expression(id: usize, expr: &Expr) -> Result<Self> {
        let constraint_type = match expr.opkind {
            30..=35 => ConstraintType::Equality,
            36..=41 => ConstraintType::Inequality,
            1..=5 => ConstraintType::Arithmetic,
            20..=25 => ConstraintType::Boolean,
            10..=15 => ConstraintType::Bitvector,
            _ => ConstraintType::Range,
        };
        
        let operator = match expr.opkind {
            36 => Some(ConstraintOperator::LessThan),
            37 => Some(ConstraintOperator::LessThanOrEqual),
            38 => Some(ConstraintOperator::GreaterThan),
            39 => Some(ConstraintOperator::GreaterThanOrEqual),
            30 => Some(ConstraintOperator::Equal),
            31 => Some(ConstraintOperator::NotEqual),
            _ => None,
        };
        
        Ok(Self {
            id,
            constraint_type,
            variables: Vec::new(), // Would be populated by extract_variables
            operator,
            range_min: None,
            range_max: None,
        })
    }
}

/// Types of constraints
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintType {
    Equality,
    Inequality,
    Range,
    Arithmetic,
    Boolean,
    Bitvector,
}

/// Constraint operators
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintOperator {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

/// Variable domain representation
#[derive(Debug, Clone)]
pub struct Domain {
    pub min: Option<i64>,
    pub max: Option<i64>,
}

impl Domain {
    pub fn new_unbounded() -> Self {
        Self { min: None, max: None }
    }
    
    pub fn new_range(min: i64, max: i64) -> Self {
        Self { min: Some(min), max: Some(max) }
    }
    
    pub fn intersect(&self, other: &Domain) -> Domain {
        let new_min = match (self.min, other.min) {
            (Some(a), Some(b)) => Some(std::cmp::max(a, b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };
        
        let new_max = match (self.max, other.max) {
            (Some(a), Some(b)) => Some(std::cmp::min(a, b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };
        
        Domain { min: new_min, max: new_max }
    }
    
    pub fn is_empty(&self) -> bool {
        match (self.min, self.max) {
            (Some(min), Some(max)) => min > max,
            _ => false,
        }
    }
    
    pub fn equals(&self, other: &Domain) -> bool {
        self.min == other.min && self.max == other.max
    }
}

/// Propagation events
#[derive(Debug, Clone)]
pub enum PropagationEvent {
    ConstraintAdded(usize),
    DomainChanged(u64),
}

/// Results of processing propagation events
#[derive(Debug, Clone)]
pub enum PropagationEventResult {
    DomainReduced(u64),
    Inconsistency,
    NoChange,
}

/// Overall propagation results
#[derive(Debug, Clone)]
pub enum PropagationResult {
    Success { iterations: usize, reductions: usize },
    Inconsistent,
    MaxIterationsReached,
}

/// Propagation statistics
#[derive(Debug, Clone)]
pub struct PropagationStatistics {
    pub constraint_count: usize,
    pub variable_count: usize,
    pub queue_size: usize,
    pub dependency_edges: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_domain_intersection() {
        let domain1 = Domain::new_range(0, 10);
        let domain2 = Domain::new_range(5, 15);
        let intersection = domain1.intersect(&domain2);
        
        assert_eq!(intersection.min, Some(5));
        assert_eq!(intersection.max, Some(10));
        assert!(!intersection.is_empty());
    }
    
    #[test]
    fn test_empty_domain() {
        let domain1 = Domain::new_range(0, 5);
        let domain2 = Domain::new_range(10, 15);
        let intersection = domain1.intersect(&domain2);
        
        assert!(intersection.is_empty());
    }
    
    #[test]
    fn test_constraint_propagator() {
        let mut propagator = ConstraintPropagator::new();
        
        // Test basic functionality
        assert_eq!(propagator.constraints.len(), 0);
        assert!(propagator.is_consistent());
    }
}

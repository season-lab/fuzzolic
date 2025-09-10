use std::collections::{HashMap, HashSet};
use anyhow::Result;
use log::debug;

/// Represents a dependency node that tracks relationships between inputs and expressions
#[derive(Debug, Clone)]
pub struct Dependency {
    /// Set of input indices that this dependency depends on
    pub inputs: HashSet<usize>,
    /// Set of expression indices that belong to this dependency
    pub exprs: HashSet<usize>,
}

impl Dependency {
    pub fn new() -> Self {
        Self {
            inputs: HashSet::new(),
            exprs: HashSet::new(),
        }
    }
    
    pub fn with_input(input_idx: usize) -> Self {
        let mut dep = Self::new();
        dep.inputs.insert(input_idx);
        dep
    }
    
    pub fn add_input(&mut self, input_idx: usize) {
        self.inputs.insert(input_idx);
    }
    
    pub fn add_expr(&mut self, expr_idx: usize) {
        self.exprs.insert(expr_idx);
    }
    
    pub fn merge(&mut self, other: &Dependency) {
        self.inputs.extend(&other.inputs);
        self.exprs.extend(&other.exprs);
    }
    
    pub fn has_input(&self, input_idx: usize) -> bool {
        self.inputs.contains(&input_idx)
    }
    
    pub fn has_expr(&self, expr_idx: usize) -> bool {
        self.exprs.contains(&expr_idx)
    }
    
    pub fn input_count(&self) -> usize {
        self.inputs.len()
    }
    
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }
}

/// Manages the dependency graph for expressions and inputs
#[derive(Debug)]
pub struct DependencyGraph {
    /// Maps input indices to their dependency nodes
    input_to_dependency: HashMap<usize, usize>,
    /// Storage for dependency nodes
    pub dependencies: Vec<Dependency>,
    /// Next available dependency ID
    next_dependency_id: usize,
    /// Maximum number of inputs supported
    max_inputs: usize,
}

impl DependencyGraph {
    pub fn new(max_inputs: usize) -> Self {
        Self {
            input_to_dependency: HashMap::new(),
            dependencies: Vec::new(),
            next_dependency_id: 0,
            max_inputs,
        }
    }
    
    /// Clear all dependencies
    pub fn clear(&mut self) {
        self.input_to_dependency.clear();
        self.dependencies.clear();
        self.next_dependency_id = 0;
    }
    
    /// Get or create a dependency for the given inputs and add the expression
    pub fn add_expression(&mut self, inputs: &HashSet<usize>, expr_idx: usize) -> Result<usize> {
        if inputs.is_empty() {
            return Ok(0); // No dependencies
        }
        
        // Find existing dependencies for these inputs
        let mut existing_deps: HashSet<usize> = HashSet::new();
        for &input_idx in inputs {
            if input_idx >= self.max_inputs {
                anyhow::bail!("Input index {} exceeds maximum {}", input_idx, self.max_inputs);
            }
            
            if let Some(&dep_id) = self.input_to_dependency.get(&input_idx) {
                existing_deps.insert(dep_id);
            }
        }
        
        let target_dep_id = if existing_deps.is_empty() {
            // Create new dependency
            let dep_id = self.next_dependency_id;
            self.next_dependency_id += 1;
            
            let mut new_dep = Dependency::new();
            for &input_idx in inputs {
                new_dep.add_input(input_idx);
                self.input_to_dependency.insert(input_idx, dep_id);
            }
            new_dep.add_expr(expr_idx);
            
            self.dependencies.push(new_dep);
            debug!("Created new dependency {} for expression {}", dep_id, expr_idx);
            dep_id
        } else if existing_deps.len() == 1 {
            // Use existing dependency
            let dep_id = *existing_deps.iter().next().unwrap();
            
            // Add any new inputs to the existing dependency
            for &input_idx in inputs {
                if !self.input_to_dependency.contains_key(&input_idx) {
                    self.input_to_dependency.insert(input_idx, dep_id);
                    if let Some(dep) = self.dependencies.get_mut(dep_id) {
                        dep.add_input(input_idx);
                    }
                }
            }
            
            // Add expression to dependency
            if let Some(dep) = self.dependencies.get_mut(dep_id) {
                dep.add_expr(expr_idx);
            }
            
            debug!("Added expression {} to existing dependency {}", expr_idx, dep_id);
            dep_id
        } else {
            // Merge multiple dependencies
            let primary_dep_id = *existing_deps.iter().next().unwrap();
            let mut deps_to_merge: Vec<usize> = existing_deps.into_iter().collect();
            deps_to_merge.sort();
            
            // Collect all data from dependencies to merge
            let mut merged_inputs = HashSet::new();
            let mut merged_exprs = HashSet::new();
            
            for &dep_id in &deps_to_merge {
                if let Some(dep) = self.dependencies.get(dep_id) {
                    merged_inputs.extend(&dep.inputs);
                    merged_exprs.extend(&dep.exprs);
                }
            }
            
            // Add new inputs and expression
            merged_inputs.extend(inputs);
            merged_exprs.insert(expr_idx);
            
            // Update primary dependency
            if let Some(primary_dep) = self.dependencies.get_mut(primary_dep_id) {
                primary_dep.inputs = merged_inputs.clone();
                primary_dep.exprs = merged_exprs;
            }
            
            // Update input mappings to point to primary dependency
            for &input_idx in &merged_inputs {
                self.input_to_dependency.insert(input_idx, primary_dep_id);
            }
            
            // Mark other dependencies as invalid (we'll clean them up later)
            for &dep_id in &deps_to_merge {
                if dep_id != primary_dep_id {
                    if let Some(dep) = self.dependencies.get_mut(dep_id) {
                        dep.inputs.clear();
                        dep.exprs.clear();
                    }
                }
            }
            
            debug!("Merged {} dependencies into {} for expression {}", 
                   deps_to_merge.len(), primary_dep_id, expr_idx);
            primary_dep_id
        };
        
        Ok(target_dep_id)
    }
    
    /// Get dependency for a specific input
    pub fn get_dependency_for_input(&self, input_idx: usize) -> Option<&Dependency> {
        if let Some(&dep_id) = self.input_to_dependency.get(&input_idx) {
            self.dependencies.get(dep_id)
        } else {
            None
        }
    }
    
    /// Get dependency by ID
    pub fn get_dependency(&self, dep_id: usize) -> Option<&Dependency> {
        self.dependencies.get(dep_id)
    }
    
    /// Get all expressions that depend on the given inputs
    pub fn get_dependent_expressions(&self, inputs: &HashSet<usize>) -> HashSet<usize> {
        let mut result = HashSet::new();
        
        for &input_idx in inputs {
            if let Some(dep) = self.get_dependency_for_input(input_idx) {
                result.extend(&dep.exprs);
            }
        }
        
        result
    }
    
    /// Get all inputs that the given expression depends on
    pub fn get_expression_inputs(&self, expr_idx: usize) -> HashSet<usize> {
        for dep in &self.dependencies {
            if dep.has_expr(expr_idx) {
                return dep.inputs.clone();
            }
        }
        HashSet::new()
    }
    
    /// Check if two expressions share any input dependencies
    pub fn expressions_share_inputs(&self, expr1_idx: usize, expr2_idx: usize) -> bool {
        let inputs1 = self.get_expression_inputs(expr1_idx);
        let inputs2 = self.get_expression_inputs(expr2_idx);
        
        !inputs1.is_disjoint(&inputs2)
    }
    
    /// Get statistics about the dependency graph
    pub fn get_stats(&self) -> DependencyStats {
        let active_deps = self.dependencies.iter()
            .filter(|dep| !dep.inputs.is_empty())
            .count();
        
        let total_inputs = self.input_to_dependency.len();
        let total_exprs = self.dependencies.iter()
            .map(|dep| dep.exprs.len())
            .sum();
        
        DependencyStats {
            active_dependencies: active_deps,
            total_inputs,
            total_expressions: total_exprs,
            max_inputs_per_dependency: self.dependencies.iter()
                .map(|dep| dep.inputs.len())
                .max()
                .unwrap_or(0),
            max_exprs_per_dependency: self.dependencies.iter()
                .map(|dep| dep.exprs.len())
                .max()
                .unwrap_or(0),
        }
    }
    
    /// Cleanup empty dependencies
    pub fn cleanup(&mut self) {
        // Remove empty dependencies and compact the vector
        let mut new_dependencies = Vec::new();
        let mut id_mapping = HashMap::new();
        
        for (old_id, dep) in self.dependencies.iter().enumerate() {
            if !dep.inputs.is_empty() {
                let _new_id = new_dependencies.len();
                new_dependencies.push(dep.clone());
                id_mapping.insert(old_id, new_dependencies.len() - 1);
            }
        }
        
        // Update input_to_dependency mapping with new IDs
        let updates: Vec<(usize, usize)> = self.input_to_dependency
            .iter()
            .filter_map(|(input_idx, old_dep_id)| {
                id_mapping.get(old_dep_id).map(|&new_dep_id| (*input_idx, new_dep_id))
            })
            .collect();
        
        for (input_idx, new_dep_id) in updates {
            self.input_to_dependency.insert(input_idx, new_dep_id);
        }
        
        self.dependencies = new_dependencies;
        self.next_dependency_id = self.dependencies.len();
        
        debug!("Cleaned up dependency graph, {} active dependencies remain", 
               self.dependencies.len());
    }
}

#[derive(Debug, Clone)]
pub struct DependencyStats {
    pub active_dependencies: usize,
    pub total_inputs: usize,
    pub total_expressions: usize,
    pub max_inputs_per_dependency: usize,
    pub max_exprs_per_dependency: usize,
}

impl std::fmt::Display for DependencyStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, 
            "Dependencies: {} active, {} inputs, {} expressions (max {}/{} per dep)",
            self.active_dependencies,
            self.total_inputs,
            self.total_expressions,
            self.max_inputs_per_dependency,
            self.max_exprs_per_dependency
        )
    }
}


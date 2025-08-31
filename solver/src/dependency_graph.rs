use anyhow::Result;
use std::collections::{HashMap, HashSet, VecDeque};

/// Dependency graph for tracking expression dependencies
pub struct DependencyGraph {
    nodes: HashMap<usize, DependencyNode>,
    edges: HashMap<usize, HashSet<usize>>,
    reverse_edges: HashMap<usize, HashSet<usize>>,
    max_size: usize,
}

impl DependencyGraph {
    pub fn new(max_size: usize) -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            reverse_edges: HashMap::new(),
            max_size,
        }
    }
    
    /// Add a node to the dependency graph
    pub fn add_node(&mut self, id: usize, node: DependencyNode) -> Result<()> {
        if self.nodes.len() >= self.max_size {
            self.evict_oldest_node();
        }
        
        self.nodes.insert(id, node);
        self.edges.entry(id).or_insert_with(HashSet::new);
        self.reverse_edges.entry(id).or_insert_with(HashSet::new);
        
        Ok(())
    }
    
    /// Add a dependency edge between two nodes
    pub fn add_dependency(&mut self, from: usize, to: usize) -> Result<()> {
        self.edges.entry(from).or_insert_with(HashSet::new).insert(to);
        self.reverse_edges.entry(to).or_insert_with(HashSet::new).insert(from);
        Ok(())
    }
    
    /// Get dependencies of a node
    pub fn get_dependencies(&self, id: usize) -> Vec<usize> {
        self.edges.get(&id).map_or(Vec::new(), |deps| deps.iter().copied().collect())
    }
    
    /// Get reverse dependencies (dependents) of a node
    pub fn get_dependents(&self, id: usize) -> Vec<usize> {
        self.reverse_edges.get(&id).map_or(Vec::new(), |deps| deps.iter().copied().collect())
    }
    
    /// Perform topological sort
    pub fn topological_sort(&self) -> Result<Vec<usize>> {
        let mut in_degree: HashMap<usize, usize> = HashMap::new();
        let mut queue = VecDeque::new();
        let mut result = Vec::new();
        
        // Calculate in-degrees
        for &node_id in self.nodes.keys() {
            in_degree.insert(node_id, 0);
        }
        
        for deps in self.edges.values() {
            for &dep in deps {
                *in_degree.entry(dep).or_insert(0) += 1;
            }
        }
        
        // Find nodes with no incoming edges
        for (&node_id, &degree) in &in_degree {
            if degree == 0 {
                queue.push_back(node_id);
            }
        }
        
        // Process nodes
        while let Some(node_id) = queue.pop_front() {
            result.push(node_id);
            
            if let Some(deps) = self.edges.get(&node_id) {
                for &dep in deps {
                    if let Some(degree) = in_degree.get_mut(&dep) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(dep);
                        }
                    }
                }
            }
        }
        
        if result.len() != self.nodes.len() {
            anyhow::bail!("Cycle detected in dependency graph");
        }
        
        Ok(result)
    }
    
    /// Find strongly connected components
    pub fn find_sccs(&self) -> Vec<Vec<usize>> {
        let mut visited = HashSet::new();
        let mut finish_stack = Vec::new();
        let mut sccs = Vec::new();
        
        // First DFS to get finish times
        for &node_id in self.nodes.keys() {
            if !visited.contains(&node_id) {
                self.dfs_finish(&node_id, &mut visited, &mut finish_stack);
            }
        }
        
        // Second DFS on transpose graph
        visited.clear();
        while let Some(node_id) = finish_stack.pop() {
            if !visited.contains(&node_id) {
                let mut scc = Vec::new();
                self.dfs_transpose(&node_id, &mut visited, &mut scc);
                if !scc.is_empty() {
                    sccs.push(scc);
                }
            }
        }
        
        sccs
    }
    
    /// DFS for finish times
    fn dfs_finish(&self, node_id: &usize, visited: &mut HashSet<usize>, finish_stack: &mut Vec<usize>) {
        visited.insert(*node_id);
        
        if let Some(deps) = self.edges.get(node_id) {
            for &dep in deps {
                if !visited.contains(&dep) {
                    self.dfs_finish(&dep, visited, finish_stack);
                }
            }
        }
        
        finish_stack.push(*node_id);
    }
    
    /// DFS on transpose graph
    fn dfs_transpose(&self, node_id: &usize, visited: &mut HashSet<usize>, scc: &mut Vec<usize>) {
        visited.insert(*node_id);
        scc.push(*node_id);
        
        if let Some(deps) = self.reverse_edges.get(node_id) {
            for &dep in deps {
                if !visited.contains(&dep) {
                    self.dfs_transpose(&dep, visited, scc);
                }
            }
        }
    }
    
    /// Evict oldest node to maintain size limit
    fn evict_oldest_node(&mut self) {
        if let Some(&oldest_id) = self.nodes.keys().next() {
            self.remove_node(oldest_id);
        }
    }
    
    /// Remove a node and its edges
    fn remove_node(&mut self, id: usize) {
        self.nodes.remove(&id);
        
        // Remove outgoing edges
        if let Some(deps) = self.edges.remove(&id) {
            for dep in deps {
                if let Some(reverse_deps) = self.reverse_edges.get_mut(&dep) {
                    reverse_deps.remove(&id);
                }
            }
        }
        
        // Remove incoming edges
        if let Some(reverse_deps) = self.reverse_edges.remove(&id) {
            for dep in reverse_deps {
                if let Some(deps) = self.edges.get_mut(&dep) {
                    deps.remove(&id);
                }
            }
        }
    }
    
    /// Get node count
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    
    /// Get edge count
    pub fn edge_count(&self) -> usize {
        self.edges.values().map(|deps| deps.len()).sum()
    }
}

/// Dependency node information
#[derive(Debug, Clone)]
pub struct DependencyNode {
    pub id: usize,
    pub node_type: DependencyNodeType,
    pub metadata: HashMap<String, String>,
}

impl DependencyNode {
    pub fn new(id: usize, node_type: DependencyNodeType) -> Self {
        Self {
            id,
            node_type,
            metadata: HashMap::new(),
        }
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }
}

/// Types of dependency nodes
#[derive(Debug, Clone)]
pub enum DependencyNodeType {
    Expression,
    Symbol,
    Constraint,
    Query,
}

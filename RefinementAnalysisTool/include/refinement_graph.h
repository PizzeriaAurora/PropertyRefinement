#pragma once
#include "property.h"
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <memory>
#include <stack>
#include <iostream>

namespace ctl {
// Graph structure for refinement relationships
class RefinementGraph {
    friend class Analyzer; // Allow Analyzer to access private members
    
public:
    struct Edge {
        size_t from;
        size_t to;
        
        Edge(size_t f, size_t t) : from(f), to(t) {}
    };
    
private:
    std::vector<std::shared_ptr<CTLProperty>> nodes_;
    std::vector<Edge> edges_;
    std::unordered_map<size_t, std::vector<size_t>> adjacency_list_;
    
    // For transitive optimization access
    std::vector<std::vector<size_t>> adjacency_; // Direct adjacency matrix access
    
public:
    void addNode(std::shared_ptr<CTLProperty> property);
    void addEdge(size_t from, size_t to);
    bool hasEdge(size_t from, size_t to) const;
    
    const std::vector<std::shared_ptr<CTLProperty>>& getNodes() const { return nodes_; }
    const std::vector<Edge>& getEdges() const { return edges_; }
    const std::unordered_map<size_t, std::vector<size_t>>& getAdjacencyList() const { 
        return adjacency_list_; 
    }
    
    // Graph algorithms
    std::vector<size_t> topologicalSort() const;
    std::vector<std::vector<size_t>> findStronglyConnectedComponents() const;
    bool hasPath(size_t from, size_t to) const;
    
    // Visualization
    void toDot(const std::string& filename, const std::string& title = "Refinement Graph") const;
    void toPNG(const std::string& filename, const std::string& title = "Refinement Graph") const;
    
    // Statistics
    size_t getNodeCount() const { return nodes_.size(); }
    size_t getEdgeCount() const { return edges_.size(); }
    double getDensity() const;
    std::vector<size_t> getInDegrees() const;
    std::vector<size_t> getOutDegrees() const;
};

} // namespace ctl
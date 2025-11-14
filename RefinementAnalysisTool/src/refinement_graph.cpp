
#include "refinement_graph.h"
#include <filesystem>
#include <fstream>
#include <sstream>
#include <chrono>
#include <iomanip>
#include <thread>
#include <execution>
#include <queue>
#include <stack>
#include <numeric>
namespace ctl {

// RefinementGraph implementation
void RefinementGraph::addNode(std::shared_ptr<CTLProperty> property) {
    nodes_.push_back(std::move(property));
    adjacency_.resize(nodes_.size()); // Maintain adjacency_ matrix size
}

void RefinementGraph::addEdge(size_t from, size_t to) {
    if (from >= nodes_.size() || to >= nodes_.size()) {
        throw std::out_of_range("Edge indices out of range");
    }
    
    edges_.emplace_back(from, to);
    adjacency_list_[from].push_back(to);
    adjacency_[from].push_back(to); // Also maintain adjacency_ for optimization access
}

bool RefinementGraph::hasEdge(size_t from, size_t to) const {
    if (from >= nodes_.size() || to >= nodes_.size()) {
        return false;
    }
    
    // Check in adjacency_ matrix (more efficient for transitive closure)
    if (from < adjacency_.size()) {
        const auto& adj = adjacency_[from];
        return std::find(adj.begin(), adj.end(), to) != adj.end();
    }
    
    return false;
}

std::vector<size_t> RefinementGraph::topologicalSort() const {
    std::vector<size_t> in_degree(nodes_.size(), 0);
    std::vector<size_t> result;
    std::queue<size_t> queue;
    
    // Calculate in-degrees
    for (const auto& edge : edges_) {
        in_degree[edge.to]++;
    }
    
    // Find all nodes with in-degree 0
    for (size_t i = 0; i < nodes_.size(); ++i) {
        if (in_degree[i] == 0) {
            queue.push(i);
        }
    }
    
    // Process nodes
    while (!queue.empty()) {
        size_t current = queue.front();
        queue.pop();
        result.push_back(current);
        
        auto it = adjacency_list_.find(current);
        if (it != adjacency_list_.end()) {
            for (size_t neighbor : it->second) {
                in_degree[neighbor]--;
                if (in_degree[neighbor] == 0) {
                    queue.push(neighbor);
                }
            }
        }
    }
    
    return result;
}

std::vector<std::vector<size_t>> RefinementGraph::findStronglyConnectedComponents() const {
    // Tarjan's algorithm for finding strongly connected components
    std::vector<std::vector<size_t>> sccs;
    std::vector<int> index(nodes_.size(), -1);
    std::vector<int> lowlink(nodes_.size(), -1);
    std::vector<bool> on_stack(nodes_.size(), false);
    std::stack<size_t> stack;
    int current_index = 0;
    
    // Helper function for DFS
    std::function<void(size_t)> strongconnect = [&](size_t v) {
        index[v] = current_index;
        lowlink[v] = current_index;
        current_index++;
        stack.push(v);
        on_stack[v] = true;
        
        // Consider successors of v
        auto it = adjacency_list_.find(v);
        if (it != adjacency_list_.end()) {
            for (size_t w : it->second) {
                if (index[w] == -1) {
                    // Successor w has not yet been visited; recurse on it
                    strongconnect(w);
                    lowlink[v] = std::min(lowlink[v], lowlink[w]);
                } else if (on_stack[w]) {
                    // Successor w is in stack S and hence in the current SCC
                    lowlink[v] = std::min(lowlink[v], index[w]);
                }
            }
        }
        
        // If v is a root node, pop the stack and generate an SCC
        if (lowlink[v] == index[v]) {
            std::vector<size_t> scc;
            size_t w;
            do {
                w = stack.top();
                stack.pop();
                on_stack[w] = false;
                scc.push_back(w);
            } while (w != v);
            sccs.push_back(scc);
        }
    };
    
    // Call the recursive helper function for all vertices
    for (size_t v = 0; v < nodes_.size(); ++v) {
        if (index[v] == -1) {
            strongconnect(v);
        }
    }
    
    return sccs;
}

double RefinementGraph::getDensity() const {
    size_t n = nodes_.size();
    if (n <= 1) return 0.0;
    return static_cast<double>(edges_.size()) / (n * (n - 1));
}

void RefinementGraph::toDot(const std::string& filename, const std::string& title) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "digraph RefinementGraph {\n";
    file << "  label=\"" << title << "\";\n";
    file << "  labelloc=\"t\";\n";
    file << "  rankdir=TB;\n";
    file << "  node [shape=box, style=rounded];\n\n";
    
    // Add nodes
    for (size_t i = 0; i < nodes_.size(); ++i) {
        std::string label = nodes_[i]->toString();
        // Escape quotes and limit length
        if (label.length() > 50) {
            label = label.substr(0, 47) + "...";
        }
        
        // Replace quotes with escaped quotes
        size_t pos = 0;
        while ((pos = label.find('"', pos)) != std::string::npos) {
            label.replace(pos, 1, "\\\"");
            pos += 2;
        }
        
        file << "  n" << i << " [label=\"" << label << "\"];\n";
    }
    
    file << "\n";
    
    // Add edges
    for (const auto& edge : edges_) {
        file << "  n" << edge.from << " -> n" << edge.to << ";\n";
    }
    
    file << "}\n";
    file.close();
}


}
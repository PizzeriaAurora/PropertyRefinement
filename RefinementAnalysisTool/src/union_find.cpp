
#include "union_find.h"
namespace ctl{
    // UnionFind implementation
size_t UnionFind::find(size_t x) const {
    auto it = parent_.find(x);
    if (it == parent_.end()) {
        parent_[x] = x;
        return x;
    }
    
    if (it->second != x) {
        parent_[x] = find(it->second); // Path compression
    }
    return parent_[x];
}

void UnionFind::unite(size_t x, size_t y) {
    size_t root_x = find(x);
    size_t root_y = find(y);
    
    if (root_x == root_y) return;
    
    // Union by rank
    auto rank_x_it = rank_.find(root_x);
    auto rank_y_it = rank_.find(root_y);
    
    size_t rank_x = (rank_x_it != rank_.end()) ? rank_x_it->second : 0;
    size_t rank_y = (rank_y_it != rank_.end()) ? rank_y_it->second : 0;
    
    if (rank_x < rank_y) {
        parent_[root_x] = root_y;
    } else if (rank_x > rank_y) {
        parent_[root_y] = root_x;
    } else {
        parent_[root_y] = root_x;
        rank_[root_x] = rank_x + 1;
    }
}

bool UnionFind::connected(size_t x, size_t y) const {
    return find(x) == find(y);
}

std::vector<std::vector<size_t>> UnionFind::getEquivalenceClasses() const {
    std::unordered_map<size_t, std::vector<size_t>> class_map;
    
    // Group elements by their root
    for (const auto& [element, _] : parent_) {
        size_t root = find(element);
        class_map[root].push_back(element);
    }
    
    std::vector<std::vector<size_t>> classes;
    for (const auto& [root, elements] : class_map) {
        classes.push_back(elements);
    }
    
    return classes;
}

} // namespace name

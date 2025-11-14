# pragma once

#include "property.h"
#include "refinement_graph.h"

#include <vector>
#include <unordered_map>
#include <thread>
#include <future>
#include <functional>


namespace ctl {

// Union-Find data structure for equivalence classes
class UnionFind {
private:
    mutable std::unordered_map<size_t, size_t> parent_;
    std::unordered_map<size_t, size_t> rank_;
    
public:
    size_t find(size_t x) const;
    void unite(size_t x, size_t y);
    bool connected(size_t x, size_t y) const;
    std::vector<std::vector<size_t>> getEquivalenceClasses() const;
};

} // namespace ctl
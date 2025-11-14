#include "CTLautomaton.h"
#include <queue>
#include <algorithm>
#include <iostream>
#include <unordered_map>
#include <stack>


#ifdef USE_ON_THE_FLY_PRODUCT

// ============================================================================
// ON-THE-FLY PRODUCT CONSTRUCTION FOR LANGUAGE INCLUSION
// ============================================================================
// This file implements L(B) ⊆ L(A) as emptiness of L(B) ∩ L(¬A)
// using on-the-fly product automaton construction.
// ============================================================================
namespace ctl {
namespace {
    // Product state: pair of (state_from_B, state_from_notA)
    struct ProductState {
        std::string state_B;
        std::string state_notA;
        
        bool operator==(const ProductState& other) const {
            return state_B == other.state_B && state_notA == other.state_notA;
        }
        
        bool operator<(const ProductState& other) const {
            if (state_B != other.state_B) return state_B < other.state_B;
            return state_notA < other.state_notA;
        }
        
        std::string toString() const {
            return "(" + state_B + "," + state_notA + ")";
        }
    };
    
    struct ProductStateHash {
        size_t operator()(const ProductState& ps) const {
            return std::hash<std::string>()(ps.state_B) ^ 
                   (std::hash<std::string>()(ps.state_notA) << 1);
        }
    };
} // end anonymous namespace

// ============================================================================
// Helper: Combine moves from B and ¬A into a product move
// ============================================================================
static bool combineMoves(
    const Move& move_B,
    const Move& move_notA,
    Move& result,
    const CTLAutomaton& automaton_B,
    const CTLAutomaton& automaton_notA
) {
    // Step 1: Merge atomic guards
    result.atoms = move_B.atoms;
    result.atoms.insert(move_notA.atoms.begin(), move_notA.atoms.end());
    
    // Step 2: Check if combined atoms are satisfiable
    if (!automaton_B.isSatisfiable(result.atoms)) {
        return false; // Inconsistent combination, discard
    }
    
    // Step 3: Synchronize next-states by direction
    // Both automata must agree on the directions they use
    
    // If both have no next states (terminal), this is valid
    if (move_B.next_states.empty() && move_notA.next_states.empty()) {
        return true;
    }
    
    // Collect directions from both moves
    std::unordered_map<int, std::unordered_set<std::string_view>> dirs_B;
    std::unordered_map<int, std::unordered_set<std::string_view>> dirs_notA;
    
    for (const auto& ns : move_B.next_states) {
        dirs_B[ns.dir].insert(ns.state);
    }
    
    for (const auto& ns : move_notA.next_states) {
        dirs_notA[ns.dir].insert(ns.state);
    }
    
    // Get all unique directions
    std::unordered_set<int> all_dirs;
    for (const auto& [dir, _] : dirs_B) all_dirs.insert(dir);
    for (const auto& [dir, _] : dirs_notA) all_dirs.insert(dir);
    
    // For each direction, both automata must have transitions (synchronization)
    for (int dir : all_dirs) {
        if (dirs_B.find(dir) == dirs_B.end() || dirs_notA.find(dir) == dirs_notA.end()) {
            // Direction mismatch - cannot synchronize
            return false;
        }
        
        // Create product states for all combinations at this direction
        for (auto sb : dirs_B[dir]) {
            for (auto sna : dirs_notA[dir]) {
                ProductState ps{std::string(sb), std::string(sna)};
                result.next_states.insert({dir, ps.toString()});
            }
        }
    }
    
    return true; // Successfully combined
}

// ============================================================================
// On-the-fly product automaton construction with SCC computation
// ============================================================================
static void buildProductAutomaton(
    const CTLAutomaton& automaton_B,
    const CTLAutomaton& automaton_notA,
    std::unordered_map<ProductState, std::vector<Move>, ProductStateHash>& product_transitions,
    std::unordered_set<ProductState, ProductStateHash>& product_states,
    std::unordered_map<ProductState, std::unordered_set<ProductState, ProductStateHash>, ProductStateHash>& product_successors,
    ProductState& initial_product_state
) {
    // Initial product state
    initial_product_state = ProductState{
        std::string(automaton_B.getInitialState()), 
        std::string(automaton_notA.getInitialState())
    };
    
    std::queue<ProductState> worklist;
    worklist.push(initial_product_state);
    product_states.insert(initial_product_state);
    
    std::unordered_map<std::string_view, std::vector<Move>> moves_cache_B;
    std::unordered_map<std::string_view, std::vector<Move>> moves_cache_notA;
    
    while (!worklist.empty()) {
        ProductState current = worklist.front();
        worklist.pop();
        
        // Get moves from both component automata
        auto moves_B = automaton_B.getMoves(current.state_B, moves_cache_B);
        auto moves_notA = automaton_notA.getMoves(current.state_notA, moves_cache_notA);
        
        std::vector<Move> combined_moves;
        
        // Try all combinations of moves from both automata
        for (const auto& move_B : moves_B) {
            for (const auto& move_notA : moves_notA) {
                Move product_move;
                
                if (combineMoves(move_B, move_notA, product_move, automaton_B, automaton_notA)) {
                    combined_moves.push_back(product_move);
                    
                    // Track successors for SCC computation
                    for (const auto& ns : product_move.next_states) {
                        // Parse the product state name "(qB,qNotA)"
                        std::string state_str(ns.state);
                        size_t comma_pos = state_str.find(',');
                        if (comma_pos != std::string::npos && state_str.front() == '(' && state_str.back() == ')') {
                            std::string sb = state_str.substr(1, comma_pos - 1);
                            std::string sna = state_str.substr(comma_pos + 1, state_str.length() - comma_pos - 2);
                            
                            ProductState next_product{sb, sna};
                            
                            // Add to successor relation
                            product_successors[current].insert(next_product);
                            
                            // Add to worklist if not yet visited
                            if (product_states.find(next_product) == product_states.end()) {
                                product_states.insert(next_product);
                                worklist.push(next_product);
                            }
                        }
                    }
                }
            }
        }
        
        product_transitions[current] = std::move(combined_moves);
    }
}

// ============================================================================
// Compute SCCs of the product automaton using Tarjan's algorithm
// ============================================================================
static std::vector<std::vector<ProductState>> computeProductSCCs(
    const std::unordered_set<ProductState, ProductStateHash>& product_states,
    const std::unordered_map<ProductState, std::unordered_set<ProductState, ProductStateHash>, ProductStateHash>& product_successors
) {
    std::unordered_map<ProductState, int, ProductStateHash> index_map;
    std::unordered_map<ProductState, int, ProductStateHash> lowlink_map;
    std::unordered_set<ProductState, ProductStateHash> on_stack;
    std::stack<ProductState> stack;
    int index = 0;
    std::vector<std::vector<ProductState>> sccs;
    
    std::function<void(const ProductState&)> strongConnect = [&](const ProductState& v) {
        index_map[v] = index;
        lowlink_map[v] = index;
        index++;
        stack.push(v);
        on_stack.insert(v);
        
        // Process successors
        auto it = product_successors.find(v);
        if (it != product_successors.end()) {
            for (const auto& w : it->second) {
                if (index_map.find(w) == index_map.end()) {
                    // Successor w has not yet been visited; recurse
                    strongConnect(w);
                    lowlink_map[v] = std::min(lowlink_map[v], lowlink_map[w]);
                } else if (on_stack.count(w) > 0) {
                    // Successor w is on the stack and hence in the current SCC
                    lowlink_map[v] = std::min(lowlink_map[v], index_map[w]);
                }
            }
        }
        
        // If v is a root node, pop the stack and create an SCC
        if (lowlink_map[v] == index_map[v]) {
            std::vector<ProductState> scc;
            ProductState w;
            do {
                w = stack.top();
                stack.pop();
                on_stack.erase(w);
                scc.push_back(w);
            } while (!(w == v));
            
            sccs.push_back(scc);
        }
    };
    
    // Run Tarjan's algorithm on all unvisited states
    for (const auto& ps : product_states) {
        if (index_map.find(ps) == index_map.end()) {
            strongConnect(ps);
        }
    }
    
    return sccs;
}

// ============================================================================
// Determine if a product SCC is accepting
// ============================================================================
static bool isProductSCCAccepting(
    const std::vector<ProductState>& scc,
    const CTLAutomaton& automaton_B,
    const CTLAutomaton& automaton_notA
) {
    // An SCC in the product is accepting if it satisfies the acceptance
    // condition from both component automata
    
    // For CTL automata with ν/μ fixpoints:
    // - The product inherits acceptance from both components
    // - Typically, we need at least one accepting state from each component
    
    for (const auto& ps : scc) {
        bool b_accepting = automaton_B.isAccepting(ps.state_B);
        bool nota_accepting = automaton_notA.isAccepting(ps.state_notA);
        
        // Both must be accepting for the product state to be accepting
        if (b_accepting && nota_accepting) {
            return true;
        }
    }
    
    return false;
}

// ============================================================================
// Check if there's a path from initial state to an accepting SCC
// ============================================================================
static bool hasPathToAcceptingSCC(
    const ProductState& initial,
    const std::vector<std::vector<ProductState>>& sccs,
    const std::unordered_map<ProductState, std::unordered_set<ProductState, ProductStateHash>, ProductStateHash>& product_successors,
    const CTLAutomaton& automaton_B,
    const CTLAutomaton& automaton_notA
) {
    // Find accepting SCCs
    std::unordered_set<ProductState, ProductStateHash> accepting_states;
    for (const auto& scc : sccs) {
        if (isProductSCCAccepting(scc, automaton_B, automaton_notA)) {
            for (const auto& ps : scc) {
                accepting_states.insert(ps);
            }
        }
    }
    
    if (accepting_states.empty()) {
        return false; // No accepting SCCs
    }
    
    // BFS to check reachability from initial to any accepting state
    std::unordered_set<ProductState, ProductStateHash> visited;
    std::queue<ProductState> queue;
    queue.push(initial);
    visited.insert(initial);
    
    while (!queue.empty()) {
        ProductState current = queue.front();
        queue.pop();
        
        // Check if we reached an accepting state
        if (accepting_states.count(current) > 0) {
            return true;
        }
        
        // Explore successors
        auto it = product_successors.find(current);
        if (it != product_successors.end()) {
            for (const auto& succ : it->second) {
                if (visited.find(succ) == visited.end()) {
                    visited.insert(succ);
                    queue.push(succ);
                }
            }
        }
    }
    
    return false; // No path to accepting SCC
}

// ============================================================================
// Helper wrapper for language inclusion checking from member function
// ============================================================================
static bool checkLanguageInclusionOTF(
    const CTLAutomaton& automaton_B,
    const CTLAutomaton& automaton_notA
) {
    std::unordered_map<ProductState, std::vector<Move>, ProductStateHash> product_transitions;
    std::unordered_set<ProductState, ProductStateHash> product_states;
    std::unordered_map<ProductState, std::unordered_set<ProductState, ProductStateHash>, ProductStateHash> product_successors;
    ProductState initial_product_state;
    
    buildProductAutomaton(automaton_B, automaton_notA, product_transitions, product_states, product_successors, initial_product_state);
    
    auto sccs = computeProductSCCs(product_states, product_successors);
    
    bool has_accepting_path = hasPathToAcceptingSCC(initial_product_state, sccs, product_successors, automaton_B, automaton_notA);
    
    return !has_accepting_path;
}




// ============================================================================
// Language inclusion checking L(this) ⊇ L(other)
// ============================================================================
bool CTLAutomaton::languageIncludes(const CTLAutomaton& other) const {
    // Implementation: checking whether L(this) ⊇ L(other) = L(other & !this) is empty
    if (this->getFormula()->hash() == CTLAutomaton::TRUE_HASH) return true;
    if (other.getFormula()->hash() == CTLAutomaton::FALSE_HASH) return true;

    // Using on-the-fly product construction
    // Build product automaton for L(other) ∩ L(¬this)
    
    // Create negated automaton for L(¬this)
    auto this_neg = this->getNegatedFormula();
    CTLAutomaton automaton_notA(*this_neg);
    
    // Check if L(other) ∩ L(¬this) is empty using OTF product
    return checkLanguageInclusionOTF(other, automaton_notA);
}
} // namespace ctl
#endif // USE_ON_THE_FLY_PRODUCT


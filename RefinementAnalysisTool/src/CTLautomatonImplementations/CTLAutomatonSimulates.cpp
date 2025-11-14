#include "CTLautomaton.h"
#include <queue>
#include <unordered_set>
#include <unordered_map>

namespace ctl {

#ifdef USE_Z3
    
    

    // Check if atoms of phi_prime imply atoms of phi (Atomic Entailment)
    // atoms(φ') => atoms(φ)
    bool atomicEntailment(const std::unordered_set<std::string>& atoms_phi_prime, 
                         const std::unordered_set<std::string>& atoms_phi,
                         z3::context& ctx) {
        
        if (atoms_phi.empty()) {
            return true; // Empty conclusion is always implied
        }
        
        try {
            // Build conjunction of atoms_phi_prime
            z3::expr_vector premise_exprs(ctx);
            for (const auto& atom : atoms_phi_prime) {
                premise_exprs.push_back(formula_utils::parseStringToZ3(atom, ctx));
            }
            
            // Build conjunction of atoms_phi  
            z3::expr_vector conclusion_exprs(ctx);
            for (const auto& atom : atoms_phi) {
                conclusion_exprs.push_back(formula_utils::parseStringToZ3(atom, ctx));
            }
            
            // Check if premise => conclusion
            // This is equivalent to checking if (premise && !conclusion) is unsat
            z3::solver s(ctx);
            if (premise_exprs.size() > 0) {
                if (premise_exprs.size() == 1) {
                    s.add(premise_exprs[0]);
                } else {
                    s.add(z3::mk_and(premise_exprs));
                }
            }
            
            if (conclusion_exprs.size() > 0) {
                if (conclusion_exprs.size() == 1) {
                    s.add(!conclusion_exprs[0]);
                } else {
                    s.add(!z3::mk_and(conclusion_exprs));
                }
            }
            
            return s.check() == z3::unsat;
        } catch (...) {
            // If we can't parse or check, be conservative
            return false;
        }
    }
    
    // Check Successor Consistency for a move (Python-style)
    // For each next state requirement in move_phi, there must be a corresponding 
    // requirement in move_phi_prime with the same direction and the pair of 
    // successor states must be in R
    bool successorConsistency(const Move& move_phi_prime, const Move& move_phi,
                              const std::unordered_set<SimPair, SimPairHash>& R) {
        // For each successor obligation in move_phi (Spoiler's move)
        for (const auto& pair_phi : move_phi.next_states) {
            // Find a corresponding successor in move_phi_prime (Duplicator's move)

            bool found = false;
            for (const auto& pair_phi_prime : move_phi_prime.next_states) {
                // Same direction and the pair of states must be in R
                if (pair_phi.dir == pair_phi_prime.dir) {
                    if (R.count({pair_phi.state, pair_phi_prime.state}) > 0 || R.count({pair_phi_prime.state, pair_phi.state}) > 0) {
                        found = true;
                        break;
                    }
                }
            }
            if (!found) {
                return false;
            }
        }
        return true;
    }
    
    
    // Check if there's a matching move for move_spoiler in the moves of duplicator
    // Returns true if a matching move is found
    // Uses Python-style algorithm logic
    bool hasMatchingMove(const Move& move_spoiler,
                        const std::vector<Move>& moves_duplicator,
                        const std::unordered_set<SimPair, SimPairHash>& R,
                        z3::context& ctx) {

        // For each move from the Duplicator
        for (const auto& move_duplicator : moves_duplicator) {
            // Check (1) Atomic Entailment: atoms(spoiler) => atoms(duplicator)
            // The Spoiler's requirements must be implied by the Duplicator's requirements
            // This means the Duplicator must be "at least as permissive" as the Spoiler
            if (!atomicEntailment(move_spoiler.atoms, move_duplicator.atoms, ctx)) {
                continue; // This move doesn't satisfy atomic entailment
            }
            
            // Check (2) Successor Consistency
            if (successorConsistency(move_spoiler, move_duplicator, R)) {
                return true; // Found a matching move!
            }
        }
        
        return false; // No matching move found
    }

    bool CTLAutomaton::simulates(const CTLAutomaton& other) const{
        return other.isSimulatedBy(*this);
    }

    
    bool CTLAutomaton::isSimulatedBy(const CTLAutomaton& other) const {
        // Python-style simulation algorithm
        // this.isSimulatedBy(other) checks if 'other' can simulate 'this'
        // Meaning: L(other) ⊇ L(this), so other is more general/weaker
        // 'this' is the Spoiler, 'other' is the Duplicator
        
        // Check if automata are equal first
        if (this->getFormula()->hash() == other.getFormula()->hash() && 
            this->getFormula()->equals(*other.getFormula())) {
            return true;
        }
        
        // Special cases for empty automata
        if (this->v_states_.empty()) {
            // this is empty (false formula) - can be simulated by anything
            return true;
        }
        if (other.v_states_.empty()) {
            // other is empty (false) but this isn't - cannot simulate
            return false;
        }
        
        // Create Z3 context for guard checking
        z3::context ctx;
        
        // Pre-compute DNF for all states in both automata (Python approach)
        auto dnf_self = this->getExpandedTransitions();
        auto dnf_other = other.getExpandedTransitions();
        
        // Initialize R with all valid pairs (Python approach)
        // A pair (q_s, q_o) is invalid if q_s is accepting but q_o is not
        std::unordered_set<SimPair, SimPairHash> R;
        
        for (const auto& state_this : v_states_) {
            for (const auto& state_other : other.v_states_) {
                bool this_accepting = isAccepting(state_this->name);
                bool other_accepting = other.isAccepting(state_other->name);
                
                // Fix the acceptance condition: only exclude if this is accepting but other is not
                if (!(this_accepting && !other_accepting)) {
                    SimPair pair{state_this->name, state_other->name};
                    R.insert(pair);
                }
            }
        }


        
        // Iteratively refine the simulation relation R until fixed point (Python approach)
        while (true) {
            std::unordered_set<SimPair, SimPairHash> R_prime;
            
            // For each pair currently in the relation
            for (const auto& pair : R) {
                bool is_pair_good = true; // Assume valid until proven otherwise
                
                const auto& moves_self = dnf_self[pair.q_phi];   // Spoiler's moves
                const auto& moves_other = dnf_other[pair.q_phi_prime]; // Duplicator's moves
                
                // For EVERY move the Spoiler makes...
                for (const auto& move_spoiler : moves_self) {
                    // ...the Duplicator must have AT LEAST ONE valid response
                    if (!hasMatchingMove(move_spoiler, moves_other, R, ctx)) {
                        // If the Duplicator has no response to this Spoiler move,
                        // the pair is not in the simulation
                        is_pair_good = false;
                        break; // No need to check other moves from the Spoiler
                    }
                }
                
                // If the Duplicator could counter all of the Spoiler's moves...
                if (is_pair_good) {
                    R_prime.insert(pair); // ...keep the pair for the next iteration
                }
            }
            
            // If the relation did not shrink, we have reached the fixed point
            if (R == R_prime) {
                break;
            }
            
            // Otherwise, update R and continue refining
            R = std::move(R_prime);
        }
        
        // The overall simulation holds if the pair of initial states is in the final relation
        SimPair initial_pair{this->initial_state_, other.initial_state_};
        bool result = R.count(initial_pair) > 0;

        
        return result;
    }

}

#else // USE_CVC5 or other solver

    // Stub implementation when not using Z3
    // Simulation checking requires Z3 for the atomic entailment checks
    bool CTLAutomaton::simulates(const CTLAutomaton& other) const {
        // Conservative: return false (simulation not supported without Z3)
        throw std::runtime_error("Simulation checking requires Z3 solver");
    }

    bool CTLAutomaton::isSimulatedBy(const CTLAutomaton& other) const {
        throw std::runtime_error("Simulation checking requires Z3 solver");
    }

#endif // USE_Z3




#include "CTLautomaton.h"
#include <queue>
#include <algorithm>
#include <iostream>

namespace ctl {

    
      bool CTLAutomaton::isEmpty() const {
        if (this->getFormula()->hash() == FALSE_HASH) return true;
        if (this->getFormula()->hash() == TRUE_HASH)  return false;

        //local_guard_cache_.clear();
        if (!blocks_) {
            std::cerr << "Warning: SCC blocks not computed yet. Computing now.\n";
            auto p = std::make_unique<SCCBlocks>(__computeSCCs());
            blocks_ = std::move(p);
            __decideBlockTypes();
        }

        auto topo = __getTopologicalOrder();
        std::reverse(topo.begin(), topo.end());

        std::unordered_map<std::string_view, std::vector<Move>> state_to_moves;
        // Pre-allocate space to avoid rehashing
        state_to_moves.reserve(v_states_.size());

        std::vector<std::unordered_set<std::string_view>> Good(blocks_->size());

        for (int B : topo) {
            const auto& info = blocks_->getBlockInfo(B);
            const auto& statesInB = blocks_->blocks[B];
            bool isNu = info.isGreatestFixedPoint();
            bool isMu = info.isLeastFixedPoint();

            std::unordered_set<std::string_view> S;

            auto block_info = blocks_->getBlockInfo(B);
            bool block_is_universal = block_info.isUniversal();
            if (block_info.isSimple()) {
                //We need to identify what the other blocks are. 
                // We first check the order
                auto& pred = __getDAG()[B];
                bool total_existential_blocks = true;
                if (!pred.empty()) {
                    for (auto p : pred) {
                        if (blocks_->getBlockInfo(p).isUniversal()) {
                            total_existential_blocks = false;
                            break;
                        }
                    }
                }
                block_is_universal = !total_existential_blocks;

            }

            // --- ν-block: start full and shrink
            if (isNu) {
                S.insert(statesInB.begin(), statesInB.end());
                bool changed = true;
                while (changed) {
                    std::unordered_set<std::string_view> Snext;
                    for (auto q : statesInB)
                        if (__existsSatisfyingTransition(q, B, S, Good, block_is_universal, state_to_moves))
                            Snext.insert(q);
                    changed = (Snext != S);
                    S = std::move(Snext);
                }
            }

            // --- μ-block: start empty and grow
            else if (isMu) {
                S.clear();
                bool changed = true;
                while (changed) {
                    std::unordered_set<std::string_view> Snext = S;
                    for (auto q : statesInB)
                        if (__existsSatisfyingTransition(q, B, S, Good, block_is_universal, state_to_moves))
                            Snext.insert(q);
                    changed = (Snext != S);
                    S = std::move(Snext);
                }
            }

            // --- simple block: one-shot evaluation (no iteration)
            else {
                for (auto q : statesInB)
                    if (__existsSatisfyingTransition(q, B, {}, Good, block_is_universal, state_to_moves))
                        S.insert(q);
            }

            Good[B] = S;

        }

        int b0 = blocks_->getBlockId(initial_state_);
        bool nonempty = Good[b0].count(initial_state_) > 0;
        return !nonempty;
    }


bool CTLAutomaton::__existsSatisfyingTransition(
    std::string_view q,
    int curBlock,
    const std::unordered_set<std::string_view>& in_block_ok,
    const std::vector<std::unordered_set<std::string_view>>& goodStates,
    bool block_is_universal,
    std::unordered_map<std::string_view, std::vector<Move>>& state_to_moves
) const {

    auto base_moves = __getMovesInternal(q, state_to_moves);

    // For each move, check if it's satisfiable AND its next-states are acceptable
    //std::cout << "Dealing with "<< base_moves.size() <<" moves for state "<< std::string(q) << "\n";
    int moves_done = 0;
    for (const auto& move : base_moves) {
        //std::cout << "  Move " << (++moves_done) << "/" << base_moves.size() << "\n";
        // Step 1: Check if atoms are satisfiable
        if (!__isSatisfiable(move.atoms)) {
            continue;
        }
        // Step 2: Handle terminal moves (no next states) - these are always OK if atoms are SAT
        if (move.next_states.empty()) {
            return true;
        }

        // Step 3: Check next-states based on block type (universal vs existential)
        bool next_states_ok = false;
        
        if (block_is_universal) {
            //std::cout << "   \n";
            // UNIVERSAL (A / AND): ALL next states must be in good sets
            next_states_ok = true; // assume all are good until proven otherwise
            // we group states by the direction
            std::array<std::vector<std::string_view>, 2> dir_to_states;
            for (const auto& ns : move.next_states) {
                if(ns.dir==-1) continue;
                dir_to_states[ns.dir].push_back(ns.state);
            }
            // for each direction, we must ensure that
            // 1. both states are in good blocks
            // 2. the atoms from those states (-1) are conjunction compatible
            for (const auto& statesAtDir : dir_to_states) {
                if (statesAtDir.empty()) continue;
                std::unordered_set<std::string> accumGuard;
                for (const auto& s : statesAtDir) {
                    auto it = state_to_moves.find(s);
                    if (it == state_to_moves.end()) {
                        continue;
                    }
                    for (const auto& mv : it->second) {
                        // (a) check obligations of this move
                        bool obligationsOK = true;
                        for (const auto& ns : mv.next_states) {
                            if (ns.dir == -1) continue; // local handled elsewhere
                            int tb = blocks_->getBlockId(ns.state);
                            if (tb == curBlock) {
                                bool isNu = blocks_->isGreatestFixedPoint(curBlock);
                                if (isNu && !in_block_ok.count(ns.state))
                                    { obligationsOK = false; break; }
                            } else {
                                if (tb < 0 || tb >= (int)goodStates.size() ||
                                    !goodStates[tb].count(ns.state))
                                    { obligationsOK = false; break; }
                            }
                        }
                        if (!obligationsOK) return false;
                        __appendGuard(accumGuard, mv.atoms);
                    }
                }
                if (!__isSatisfiable(accumGuard)) {
                    return false;
                }
            }

            

            
            //for (const auto& ns : move.next_states) {
            //    bool this_state_ok = false;
            //    
            //    int target_block = blocks_->getBlockId(ns.state);
            //    
            //    if (target_block == curBlock) {
            //        // Within same block: check if it's in the current fixpoint set
            //        bool isNu = blocks_->isGreatestFixedPoint(curBlock);
            //        if (isNu) {
            //            // ν-block: must be in current approximation
            //            this_state_ok = in_block_ok.count(ns.state) > 0;
            //        } else {
            //            // μ-block: optimistic (assume it will be added)
            //            this_state_ok = true;
            //        }
            //    } else {
            //        // Different block: check if it's in the already-computed good set
            //        if (target_block >= 0 && target_block < (int)goodStates.size()) {
            //            this_state_ok = goodStates[target_block].count(ns.state) > 0;
            //        }
            //    }
            //    
            //    if (!this_state_ok) {
            //        next_states_ok = false;
            //        break; // One bad state means the whole move fails
            //    }
            //}
            
        } else {
            // EXISTENTIAL (E / OR): AT LEAST ONE next state must be in good sets
            next_states_ok = false; // assume none are good until we find one
            
            for (const auto& ns : move.next_states) {
                bool this_state_ok = false;
                
                int target_block = blocks_->getBlockId(ns.state);
                
                if (target_block == curBlock) {
                    // Within same block
                    bool isNu = blocks_->isGreatestFixedPoint(curBlock);
                    if (isNu) {
                        this_state_ok = in_block_ok.count(ns.state) > 0;
                    } else {
                        // μ-block: optimistic
                        this_state_ok = true;
                    }
                } else {
                    // Different block
                    if (target_block >= 0 && target_block < (int)goodStates.size()) {
                        this_state_ok = goodStates[target_block].count(ns.state) > 0;
                    }
                }
                
                if (this_state_ok) {
                    next_states_ok = true;
                    break; // Found one good state, that's enough for existential
                }
            }
        }

        // If this move is satisfiable AND its next-states are OK, we found a valid transition
        if (next_states_ok) {
            return true;
        }
    }

    // No satisfying transition found
    return false;
}

// Helper functions for per-child joint realizability
bool CTLAutomaton::__isSatisfiableUnion(const std::unordered_set<std::string>& base, const std::unordered_set<std::string>& add) const {
    std::unordered_set<std::string> combined = base;
    combined.insert(add.begin(), add.end());
    return __isSatisfiable(combined);
}

void CTLAutomaton::__appendGuard(std::unordered_set<std::string>& base, const std::unordered_set<std::string>& add) const {
    base.insert(add.begin(), add.end());
}




/*

bool CTLAutomaton::__childConjunctionEnabled(
    const std::vector<std::string_view>& statesAtChild,
    int curBlock,
    const std::unordered_set<std::string_view>& in_block_ok,
    const std::vector<std::unordered_set<std::string_view>>& goodStates
) const {
    
    

     // Multiple required states at one child
    std::unordered_set<std::string> accumGuard;
    //if (block_is_universal) {
    for (const auto& s : statesAtChild) {
        auto it = m_expanded_transitions_.find(s);
        if (it == m_expanded_transitions_.end()) {
            continue;
        }
        for (const auto& mv : it->second) {
            // (a) check obligations of this move
            bool obligationsOK = true;
            for (const auto& ns : mv.next_states) {
                if (ns.dir == -1) continue; // local handled elsewhere
                int tb = blocks_->getBlockId(ns.state);
                if (tb == curBlock) {
                    bool isNu = blocks_->isGreatestFixedPoint(curBlock);
                    if (isNu && !in_block_ok.count(ns.state))
                        { obligationsOK = false; break; }
                } else {
                    if (tb < 0 || tb >= (int)goodStates.size() ||
                        !goodStates[tb].count(ns.state))
                        { obligationsOK = false; break; }
                }
            }
            if (!obligationsOK) return false;
            __appendGuard(accumGuard, mv.atoms);
        }
    }
    if (!__isSatisfiable(accumGuard)) {
        return false;
    }
    return true;

    
}



*/



std::vector<std::unordered_set<int>>& CTLAutomaton::__getDAG() const
{
    if (!block_edges_.empty()) {
        return block_edges_;
    }

    std::vector<std::unordered_set<int>> block_edges(blocks_->size());
    for (int i = 0; i < (int)blocks_->size(); ++i) {
        for (const auto& st : blocks_->blocks[i]) {
            auto it = state_successors_.find(st);
            if (it == state_successors_.end()) {
                block_edges[i] = {};
                continue;
            }
            //block_edges[i] = {};
            for (const auto& succ : it->second) {
                int bj = blocks_->getBlockId(succ);
                if (bj != i) block_edges[i].insert(bj);
            }
        }
    }
    block_edges_ = std::move(block_edges);
    return block_edges_;

}
}
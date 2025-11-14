

#include "CTLautomaton.h"


#include <sstream>
#include <algorithm>
#include <queue>
#include <stack>

namespace ctl {

  void CTLAutomaton::buildFromFormula(const CTLFormula& formula, bool symbolic) {
    p_original_formula_ = std::move(formula_utils::preprocessFormula(formula));
    p_negated_formula_ = std::move(formula_utils::negateFormula(formula));
    smt_interface_ = createDefaultSMTInterface();
    __buildFromFormula( false);
    blocks_ = std::make_unique<SCCBlocks>(__computeSCCs());

    
    __decideBlockTypes();
    //blocks_->print();
    m_expanded_transitions_ = getMoves();
  }







  void CTLAutomaton::__buildFromFormula(bool symbolic) {
      // Implementation of the actual building logic goes here
      s_accepting_states_.clear();
      state_successors_.clear();
      m_transitions_.clear();
      v_states_.clear();

    if(p_original_formula_->hash() == TRUE_HASH){
        auto state = std::make_shared<CTLState>();
        state->name = "q0";
        state->formula = p_original_formula_->clone();
        v_states_.push_back(state);
        initial_state_ = state->name;
        formula_hash_to_state_cache_[p_original_formula_->hash()] = state->name;
        addDNF(state->name, GTrue, { Conj{ { /* empty */ } } });
        return;
    }


    if (p_original_formula_->hash() == FALSE_HASH)
    {
        auto state = std::make_shared<CTLState>();
        state->name = "q0";
        state->formula = p_original_formula_->clone();
        v_states_.push_back(state);
        initial_state_ = state->name;
        formula_hash_to_state_cache_[p_original_formula_->hash()] = state->name;
        addDNF(state->name, GFalse, { Conj{ { /* empty */ } } });
        return;
    }

    std::unordered_map<formula_utils::FormulaKey, const CTLFormula*, formula_utils::FormulaKeyHash> seen;
    std::vector<const CTLFormula*> topo;
    collectClosureDFS(*p_original_formula_, seen, topo);
    //std::cout << "Total subformulas collected: " << topo.size() << std::endl;
    // Create one state per subformula
    for (const CTLFormula* sf : topo) {
        auto state = std::make_shared<CTLState>();
        state->name = "q" + std::to_string(v_states_.size());
        state->formula = sf->clone();
        v_states_.push_back(state);
        formula_hash_to_state_cache_[sf->hash()] = state->name;
        if (sf->getType() == FormulaType::BINARY) {
            //m_state_operator_[state->name] = static_cast<const BinaryFormula*>(sf)->operator_;
            m_state_operator_[state->name] = static_cast<const BinaryFormula*>(sf)->operator_;
        }
    }

    // 3) Handle state transitions
    __handleStatesAndTransitions(symbolic);


    initial_state_ = getStateOfFormula(*p_original_formula_);
    
    
  }



void CTLAutomaton::__clean() {
    throw std::runtime_error("CTLAutomaton::__clean not implemented yet.");
}

bool CTLAutomaton::__isSatisfiable(const std::string& g) const {
    if (!smt_interface_) {
        throw std::runtime_error("SMT interface not initialized");
    }
    return smt_interface_->isSatisfiable(g);
}


bool CTLAutomaton::__isSatisfiable(const std::unordered_set<std::string>& g) const {
    if (!smt_interface_) {
        throw std::runtime_error("SMT interface not initialized");
    }
    return smt_interface_->isSatisfiable(g);
}



  std::string CTLAutomaton::__handleProp (const std::string& proposition, bool symbolic){
        // If symbolic=true we can decide satisfiability now; else keep the prop (or "true") per your needs
        //if (!symbolic) return proposition.empty() ? "true" : proposition;
        //return proposition.empty() ? "" : proposition;
        bool sat = __isSatisfiable(proposition);
        if (!sat) return "false";
        return proposition.empty() ? "" : proposition;
        //else return (symbolic ? "true" : proposition);
        //return sat ? "true" : "false";
    };




    void CTLAutomaton::__decideBlockTypes() const {
        // loop through each block, get the state and decide its type
        for (size_t i = 0; i < blocks_->blocks.size(); ++i) {
            // Check for μ/ν
            bool acceptance_for_this_block = false;
            std::vector<SCCAcceptanceType> acceptance_in_block; // refers to SCCAcceptanceType enum, which is nu or mu
            std::vector<SCCBlockType> block_types_in_block;
            //std::vector<SCCAcceptanceType> acceptance_in_block;

            
            for (size_t j = 0; j < blocks_->blocks[i].size(); ++j) {
                const auto& state_name = blocks_->blocks[i][j];
                auto it = std::find_if(v_states_.begin(), v_states_.end(),
                                       [&state_name](const CTLStatePtr& s) {
                                           return s->name == state_name;
                                       });
                if (it != v_states_.end()) {
                    acceptance_in_block.push_back(formula_utils::getBlockAcceptanceTypeFromFormula((*it)->formula));
                    block_types_in_block.push_back(formula_utils::getSCCBlockTypeFromFormula((*it)->formula));
                }
                
            }


            // Decide block type
            SCCAcceptanceType final_acceptance_type = SCCAcceptanceType::UNDEFINED;
            SCCBlockType final_block_type = SCCBlockType::UNDEFINED;
            // if types are the same, assign that type
            if (!acceptance_in_block.empty()) {
                final_acceptance_type = acceptance_in_block[0];
                bool all_same = std::all_of(acceptance_in_block.begin(), acceptance_in_block.end(),
                                            [final_acceptance_type](SCCAcceptanceType t) { return t == final_acceptance_type; });
                if (!all_same) std::cerr << "Warning: Mixed block types in block " << i << "\n";
                final_block_type = block_types_in_block[0];
                all_same = std::all_of(block_types_in_block.begin(), block_types_in_block.end(),
                                            [final_block_type](SCCBlockType t) { return t == final_block_type; });
                if (!all_same) std::cerr << "Warning: Mixed existential/universal types in block " << i << "\n";
            }else throw std::runtime_error("Error: Empty block found when deciding block types.");
            // Check for acceptance
            
            blocks_->setInfoAt(i, final_acceptance_type, final_block_type);
            if(blocks_->isGreatestFixedPoint(i))
                s_accepting_states_.insert(blocks_->blocks[i].begin(), blocks_->blocks[i].end());
        }
    }


  void CTLAutomaton::addEdge(const std::string_view from, const std::string_view to) {
        state_successors_[from].insert(to);
        
    };

    // Record graph edges and store exactly ONE transition (guard + disjuncts).
  void CTLAutomaton::addDNF(const std::string_view from,
                             const std::string& guard,
                             const std::vector<Conj>& disjuncts) {
      // Record edges for SCCs
      auto& succs = state_successors_[from];
      for (const auto& c : disjuncts) {
          for (const auto& a : c.atoms) {
              succs.insert(a.qnext); // ok if duplicates; SCC code can tolerate or you can dedup
          }
      }
      // Single transition object for the whole DNF clause
      CTLTransitionPtr t = std::make_shared<CTLTransition>();
      t->guard     = std::string(guard);
      t->disjuncts = disjuncts;
      t->from      = from;
      m_transitions_[from].push_back(std::move(t));
  };



  void CTLAutomaton::__handleStatesAndTransitions(bool symbolic)
  {
    for (auto state : v_states_) {
        FormulaType t = state->formula->getType();
        
        
        switch (t) {
            case FormulaType::BOOLEAN_LITERAL: {
                auto b = std::dynamic_pointer_cast<BooleanLiteral>(state->formula);
                if (b->value) {
                    // δ(q) := true   (disjuncts may be empty; treat as one empty conj under guard=true)
                    addDNF(state->name, GTrue, { Conj{ { /* empty */ } } });
                } else {
                    // false: no satisfiable transition, or guard=false
                    addDNF(state->name, GFalse, {}); // harmless; existsSatisfyingTransition will skip
                }
                break;
            }
            case FormulaType::ATOMIC: 
            {
                auto a = std::dynamic_pointer_cast<AtomicFormula>(state->formula);
                // δ(q) := proposition as guard, with no spawned copies
                std::string g = __handleProp(a->proposition, symbolic);
                //if (g != "false") 
                    addDNF(state->name, g, { Conj{ {} } });
                break;
            }
            case FormulaType::NEGATION: 
              {
                  auto n = std::dynamic_pointer_cast<NegationFormula>(state->formula);
                  if (auto atom = std::dynamic_pointer_cast<AtomicFormula>(n->operand)) {
                      std::string g = __handleProp("!" + atom->proposition, symbolic);
                      //if (g == "false") m_rejecting_states_.insert(s);
                      //if (g != "false")  
                      addDNF(state->name, g, { Conj{ {} } });
                      break;
                  }
                  // Handle other negations if needed
                  throw std::runtime_error("Unhandled negation formula in builder: " + state->name + " : " + state->formula->toString());
                  break;
              }

            case FormulaType::BINARY: 
              {
                auto bin =  std::dynamic_pointer_cast<BinaryFormula>(state->formula);
                switch (bin->operator_) {
                    case BinaryOperator::AND: {
                        auto leftType  = bin->left->getType();
                        auto rightType = bin->right->getType();

                        // true/false simplifications
                        if (leftType == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(bin->left);
                            if (!b->value) {
                                // left = false → whole conj = false
                                addDNF(state->name, GFalse, {}); 
                                break;
                            } // if true → skip left, use right only
                        }

                        if (rightType == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(bin->right);
                            if (!b->value) {
                                addDNF(state->name, GFalse, {});
                                break;
                            }
                        }

                        // If either side is 'true', drop it (q ∧ true = q)
                        std::string_view s_left, s_right;
                        if (!(leftType == FormulaType::BOOLEAN_LITERAL &&
                            std::dynamic_pointer_cast<BooleanLiteral>(bin->left)->value)) {
                            s_left = getStateOfFormula(*bin->left);
                        }
                        if (!(rightType == FormulaType::BOOLEAN_LITERAL &&
                            std::dynamic_pointer_cast<BooleanLiteral>(bin->right)->value)) {
                            s_right = getStateOfFormula(*bin->right);
                        }

                        // If both sides reduced away (true ∧ true)
                        if (s_left.empty() && s_right.empty()) {
                            addDNF(state->name, GTrue, { Conj{ {} } }); // δ = true
                        } else if (s_left.empty()) {
                            // only right remains: φ ∧ true = φ
                            // get the disjuncts from right only
                            //auto right_conj = m_transitions_.find(s_right);
                            //if (right_conj != m_transitions_.end()) {
                            //    for (const auto& t : right_conj->second) {
                            //        addDNF(state->name, t->guard, t->disjuncts);
                            //    }
                            //}
                            addDNF(state->name, GTrue, { Conj{ { { -1, s_right } } } });
                        } else if (s_right.empty()) {
                            addDNF(state->name, GTrue, { Conj{ { { -1, s_left } } } });
                            // only left remains: true ∧ φ = φ
                            //auto left_conj = m_transitions_.find(s_left);
                            //if (left_conj != m_transitions_.end()) {
                            //    for (const auto& t : left_conj->second) {
                            //        addDNF(state->name, t->guard, t->disjuncts);
                            //    }
                            //}

                        } else {
                            // normal case: φ ∧ ψ
                            addDNF(state->name, GTrue,
                                { Conj{ { { -1, s_left }, { -1, s_right } } } });
                            // DNF of (A ∧ B) is the pairwise combination of clauses from DNF(A) and DNF(B).
                            // This is the most complex part of the conversion.
                            // auto left_conj = m_transitions_.find(s_left);
                            //    auto right_conj = m_transitions_.find(s_right);
                            //for (const auto& conj_left : left_conj->second) {
                            //    for (const auto& conj_right : right_conj->second) {
                            //        // Combine guards (AND)
                            //        std::string combined_guard;
                            //        if (conj_left->guard == GFalse || conj_right->guard == GFalse) {
                            //            combined_guard = GFalse;
                            //        } else if (conj_left->guard == GTrue) {
                            //            combined_guard = conj_right->guard;
                            //        } else if (conj_right->guard == GTrue) {
                            //            combined_guard = conj_left->guard;
                            //        } else {
                            //            combined_guard = "(" + conj_left->guard + ") & (" + conj_right->guard + ")";
                            //        }
//
                            //        // Combine disjuncts (cross product)
                            //        std::vector<Conj> combined_disjuncts;
                            //        for (const auto& d_left : conj_left->disjuncts) {
                            //            for (const auto& d_right : conj_right->disjuncts) {
                            //                Conj combined_conj;
                            //                combined_conj.atoms.insert(combined_conj.atoms.end(),
                            //                    d_left.atoms.begin(), d_left.atoms.end());
                            //                combined_conj.atoms.insert(combined_conj.atoms.end(),
                            //                    d_right.atoms.begin(), d_right.atoms.end());
                            //                combined_disjuncts.push_back(std::move(combined_conj));
                            //            }
                            //        }
//
                            //        addDNF(state->name, combined_guard, combined_disjuncts);
                            //    }
                            //}
                        }//
                        break;
                    }


                    case BinaryOperator::OR: {
                        auto leftType  = bin->left->getType();
                        auto rightType = bin->right->getType();

                        // false/true simplifications
                        if (leftType == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(bin->left);
                            if (b->value) {
                                // true ∨ x = true
                                addDNF(state->name, GTrue, { Conj{ {} } });
                                break;
                            } // if false → skip left
                        }

                        if (rightType == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(bin->right);
                            if (b->value) {
                                addDNF(state->name, GTrue, { Conj{ {} } });
                                break;
                            }
                        }

                        // If either side is 'false', drop it (q ∨ false = q)
                        std::vector<Conj> disjuncts;
                        if (!(leftType == FormulaType::BOOLEAN_LITERAL &&
                            !std::dynamic_pointer_cast<BooleanLiteral>(bin->left)->value)) {
                            std::string_view s_left = getStateOfFormula(*bin->left);
                            disjuncts.push_back(Conj{ { { -1, s_left } } });
                        }
                        if (!(rightType == FormulaType::BOOLEAN_LITERAL &&
                            !std::dynamic_pointer_cast<BooleanLiteral>(bin->right)->value)) {
                            std::string_view s_right = getStateOfFormula(*bin->right);
                            disjuncts.push_back(Conj{ { { -1, s_right } } });
                        }

                        if (disjuncts.empty()) {
                            // both sides false → δ = false
                            addDNF(state->name, GFalse, {});
                        } else {
                            addDNF(state->name, GTrue, disjuncts);
                        }
                        break;
                    }

                    default:
                        throw std::runtime_error("Unsupported binary operator in builder");
                }
    
              }
              break;
              // Temporal core
            case FormulaType::TEMPORAL: 
              {
                using Op = TemporalOperator;
                auto t = std::dynamic_pointer_cast<TemporalFormula>(state->formula);
                switch (t->operator_) {
                    // AX φ  :  ∧_{c∈{L,R}} next(c, φ)
                    case Op::AX: {
                        if (t->operand->getType() == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(t->operand);
                            if (!b->value) {
                                // AX false = false
                                addDNF(state->name, GFalse, {});
                                break;
                            } else {
                                // AX true = true
                                addDNF(state->name, GTrue, { Conj{ {} } });
                                break;
                            }
                        }
                        std::string_view sub = getStateOfFormula(*t->operand);
                        addDNF(state->name, GTrue, { Conj{ { { L, sub }, { R, sub } } } });
                        break;
                    }
                    // EX φ  :  ∨_{c∈{L,R}} next(c, φ)
                    case Op::EX: {
                        if (t->operand->getType() == FormulaType::BOOLEAN_LITERAL) {
                            auto b = std::dynamic_pointer_cast<BooleanLiteral>(t->operand);
                            if (!b->value) {
                                // AX false = false
                                addDNF(state->name, GFalse, {});
                                break;
                            } else {
                                // AX true = true
                                addDNF(state->name, GTrue, { Conj{ {} } });
                                break;
                            }
                        }
                        std::string_view sub = getStateOfFormula(*t->operand);
                        addDNF(state->name, GTrue, { Conj{ { { L, sub } } }, Conj{ { { R, sub } } } });
                        break;
                    }
                    // A(φ U ψ) : ψ  ∨  (φ ∧ AX self)
                    case Op::AU: {
                        std::vector<Conj> disjuncts;

                        const auto& phi = *t->operand;
                        const auto& psi = *t->second_operand;

                        bool phi_true  = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool phi_false = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool psi_true  = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);
                        bool psi_false = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);

                        // Simplify trivial cases
                        if (psi_true) {
                            // A(φ U true) = true
                            addDNF(state->name, GTrue, { Conj{ {} } });
                            break;
                        }
                        if (psi_false && phi_false) {
                            // A(false U false) = false
                            addDNF(state->name, GFalse, {});
                            break;
                        }

                        // (1) Immediate satisfaction: ψ
                        if (!psi_false) {
                            std::string_view s_psi = getStateOfFormula(psi);
                            disjuncts.push_back(Conj{ { { -1, s_psi } } });
                        }

                        // (2) Continue case: φ ∧ AX self  (universal next)
                        if (!phi_false) {
                            Conj cont;
                            if (!phi_true) {
                                std::string_view s_phi = getStateOfFormula(phi);
                                cont.atoms.push_back({ -1, s_phi });
                            }
                            // universal next: both branches must satisfy A(φ U ψ)
                            cont.atoms.push_back({ L, state->name });
                            cont.atoms.push_back({ R, state->name });
                            disjuncts.push_back(std::move(cont));
                        }

                        if (disjuncts.empty())
                            addDNF(state->name, GFalse, {});
                        else
                            addDNF(state->name, GTrue, disjuncts);
                        break;
                    }

                    // E(φ U ψ) : ψ  ∨  (φ ∧ EX self)  = ψ  ∨  (φ ∧ next(L,self)) ∨ (φ ∧ next(R,self))
                    case Op::EU: {
                        std::vector<Conj> disjuncts;

                        const auto& phi = *t->operand;
                        const auto& psi = *t->second_operand;

                        bool phi_true  = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool phi_false = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool psi_true  = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);
                        bool psi_false = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);
                        
                        // Simplify special cases
                        if (psi_true) {  // E(φ U true) = true
                            addDNF(state->name, GTrue, { Conj{ {} } });
                            break;
                        }
                        if (psi_false && phi_false) {  // E(false U false) = false
                            addDNF(state->name, GFalse, {});
                            break;
                        }

                        // (1) Immediate satisfaction: ψ
                        if (!psi_false) {
                            std::string_view s_psi = getStateOfFormula(psi);
                            disjuncts.push_back(Conj{ { { -1, s_psi } } });
                        }

                        // (2) Continuation: φ ∧ EX self
                        if (!phi_false) {
                            if (phi_true) {
                                // true ∧ EX self = EX self
                                disjuncts.push_back(Conj{ { { L, state->name } } });
                                disjuncts.push_back(Conj{ { { R, state->name } } });
                            } else {
                                std::string_view s_phi = getStateOfFormula(phi);
                                disjuncts.push_back(Conj{ { { -1, s_phi }, { L, state->name } } });
                                disjuncts.push_back(Conj{ { { -1, s_phi }, { R, state->name } } });
                            }
                        }

                        if (disjuncts.empty())
                            addDNF(state->name, GFalse, {});
                        else
                            addDNF(state->name, GTrue, disjuncts);
                        break;
                    }

                    case Op::AU_TILDE: {
                        // A(φ Ũ ψ) = ψ ∧ (φ ∨ AX self)
                        std::vector<Conj> disjuncts;

                        const auto& phi = *t->operand;
                        const auto& psi = *t->second_operand;

                        bool phi_true  = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool phi_false = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool psi_true  = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);
                        bool psi_false = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);

                        if (psi_false) {
                            // ψ must hold now; if false, unsatisfiable
                            addDNF(state->name, GFalse, {});
                            break;
                        }
                        if (psi_true && phi_true) {
                            // ψ ∧ φ = true, so A(true Ũ true) = true
                            addDNF(state->name, GTrue, { Conj{ {} } });
                            break;
                        }

                        // (ψ ∧ φ)
                        if (!psi_false && !phi_false) {
                            Conj conj1;
                            if (!psi_true) {
                                std::string_view s_psi = getStateOfFormula(psi);
                                conj1.atoms.push_back({ -1, s_psi });
                            }
                            if (!phi_true) {
                                std::string_view s_phi = getStateOfFormula(phi);
                                conj1.atoms.push_back({ -1, s_phi });
                            }
                            disjuncts.push_back(std::move(conj1));
                        }

                        // (ψ ∧ AX self)
                        if (!psi_false) {
                            Conj conj2;
                            if (!psi_true) {
                                std::string_view s_psi = getStateOfFormula(psi);
                                conj2.atoms.push_back({ -1, s_psi });
                            }
                            conj2.atoms.push_back({ L, state->name });
                            conj2.atoms.push_back({ R, state->name });
                            disjuncts.push_back(std::move(conj2));
                        }

                        if (disjuncts.empty())
                            addDNF(state->name, GFalse, {});
                        else
                            addDNF(state->name, GTrue, disjuncts);

                        break;
                    }

                    // E(φ Ũ ψ) : ψ ∧ (φ ∨ EX self) = (ψ ∧ φ) ∨ (ψ ∧ next(L,self)) ∨ (ψ ∧ next(R,self))
                    case Op::EU_TILDE: {
                        // E(φ Ũ ψ) = ψ ∧ (φ ∨ EX self)
                        std::vector<Conj> disjuncts;
                        
                        const auto& phi = *t->operand;
                        const auto& psi = *t->second_operand;

                        bool phi_true  = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool phi_false = (phi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->operand)->value);
                        bool psi_true  = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);
                        bool psi_false = (psi.getType() == FormulaType::BOOLEAN_LITERAL &&
                                        !std::dynamic_pointer_cast<BooleanLiteral>(t->second_operand)->value);

                        if (psi_false) {
                            addDNF(state->name, GFalse, {});
                            break;
                        }
                        if (psi_true && phi_true) {
                            addDNF(state->name, GTrue, { Conj{ {} } });
                            break;
                        }

                        // (ψ ∧ φ)
                        if (!psi_false && !phi_false) {
                            Conj conj1;
                            if (!psi_true) {
                                
                                std::string_view s_psi = getStateOfFormula(psi);
                                conj1.atoms.push_back({ -1, s_psi });
                            }
                            if (!phi_true) {
                                
                                std::string_view s_phi = getStateOfFormula(phi);
                                conj1.atoms.push_back({ -1, s_phi });
                            }
                            disjuncts.push_back(std::move(conj1));
                        }

                        // (ψ ∧ EX self)
                        if (!psi_false) {
                            if (psi_true) {
                                disjuncts.push_back(Conj{ { { L, state->name } } });
                                disjuncts.push_back(Conj{ { { R, state->name } } });
                            } else {
                                std::string_view s_psi = getStateOfFormula(psi);
                                disjuncts.push_back(Conj{ { { -1, s_psi }, { L, state->name } } });
                                disjuncts.push_back(Conj{ { { -1, s_psi }, { R, state->name } } });
                            }
                        }

                        if (disjuncts.empty())
                            addDNF(state->name, GFalse, {});
                        else
                            addDNF(state->name, GTrue, disjuncts);

                        break;
                    }

                    default:
                        throw std::runtime_error("Non-core temporal op in builder: " + state->name + " : " + state->formula->toString());
                }
            
                break;
              }

            default:
                throw std::runtime_error("Unhandled node in builder: " + state->name + " of type " + formula_utils::formulaTypeToString(t));
                break; // continue to the error below
        }

    }
  }




  std::vector<std::vector<std::string_view>> CTLAutomaton::__computeSCCs() const {

      std::vector<std::string_view> V; V.reserve(state_successors_.size());
      std::unordered_map<std::string_view, int> idx; idx.reserve(state_successors_.size());

      V.reserve(state_successors_.size());
      for (const auto& kv : state_successors_) {
          idx.emplace(kv.first, static_cast<int>(V.size()));
          V.push_back(kv.first);
      }
      if (!idx.count(initial_state_)) {
          // In case the initial state has no registered successors yet
          idx.emplace(initial_state_, static_cast<int>(V.size()));
          V.push_back(initial_state_);
      }

      const int n = static_cast<int>(V.size());
      std::vector<int> index(n, -1), low(n, 0);
      std::vector<char> onstack(n, 0);
      std::stack<int> st;
      int timer = 0;
      std::vector<std::vector<std::string_view>> sccs;

      std::function<void(int)> dfs = [&](int v){
          index[v] = low[v] = timer++;
          st.push(v); onstack[v] = 1;

          const std::string_view sv = V[v];
          auto it = state_successors_.find(sv);
          if (it != state_successors_.end()) {
              for (const auto& succ : it->second) {
                  auto jt = idx.find(succ);
                  if (jt == idx.end()) continue; // unknown state (shouldn't happen)
                  int w = jt->second;
                  if (index[w] == -1) {
                      dfs(w);
                      low[v] = std::min(low[v], low[w]);
                  } else if (onstack[w]) {
                      low[v] = std::min(low[v], index[w]);
                  }
              }
          }

          if (low[v] == index[v]) {
              // root of SCC
              std::vector<std::string_view> comp;
              while (true) {
                  int w = st.top(); st.pop(); onstack[w] = 0;
                  comp.push_back(std::string_view(V[w]));
                  if (w == v) break;
              }

              sccs.push_back(comp);
          }
      };

      for (int v = 0; v < n; ++v) {
          if (index[v] == -1) dfs(v);
      }
      return sccs;
  }




    // Convert C++ transitions to Python-style DNF format
    std::vector<Move> CTLAutomaton::transitionToDNF(const std::vector<CTLTransitionPtr>& transitions, bool with_atom_collection) const {
        std::vector<Move> dnf_moves;
        
        for (const auto& transition : transitions) {
            // Skip transitions with false guard
            //if (transition->guard == "false") {
            //    continue;
            //}
            
            // Each disjunct becomes a separate move
            for (const auto& conj : transition->disjuncts) {
                Move move;
                
                // Add the guard as an atomic proposition if it's not "true"
                if (transition->guard != "true" && !transition->guard.empty()) {
                    move.atoms.insert(transition->guard);
                }
                
                // Process atoms from the conjunction
                for (const auto& atom : conj.atoms) {
                    
                        // Directions 0/1 (L/R) are temporal requirements (next state moves)
                        move.next_states.insert({atom.dir, atom.qnext});
                    
                }
                
                dnf_moves.push_back(std::move(move));
            }
        }
        

        return dnf_moves;
    }
    
    

    
    std::vector<Move> CTLAutomaton::__getMovesInternal(const std::string_view state_name,
        std::unordered_map<std::string_view, std::vector<Move>>& state_to_moves) const {
        // Check if already memoized
        auto memo_it = state_to_moves.find(state_name);
        if (memo_it != state_to_moves.end()) {
            return memo_it->second;
        }
        // Get raw transitions for this state
        auto it = m_transitions_.find(state_name);
        if (it == m_transitions_.end() || it->second.empty()) {
            state_to_moves[state_name] = {};
            return {};
        }
        // Convert raw transitions to base DNF moves
        auto base_moves = transitionToDNF(it->second);
        std::vector<Move> fully_expanded_moves;
        for (const auto& base_move : base_moves) {
            // Recursively expand each base move (since transitions are already DNF, each expands to one move)
            expandMoveRevisited(base_move, state_name, state_to_moves, &fully_expanded_moves);
            
        }
        
        
        std::unordered_set<Move> seen_moves;
        std::vector<Move> unique_moves;
        
        for (const auto& move : fully_expanded_moves) {
            if (seen_moves.find(move) == seen_moves.end()) {
                seen_moves.insert(move);
                unique_moves.push_back(move);
            }
        }
        
        state_to_moves[state_name] = unique_moves;
        return unique_moves;
    }




    
    void CTLAutomaton::expandMoveRevisited(const Move& move, 
                                   const std::string_view current_state,
                                   std::unordered_map<std::string_view, std::vector<Move>>& state_to_moves,
                                   std::vector<Move>* fully_expanded_moves) const 
    {
        // Gather expansion options for each referenced next state
        std::vector<std::vector<Move>> expansion_options;
        
        for (const auto& pair : move.next_states) {
            const int dir = pair.dir;
            const std::string_view next_state = pair.state;
            
            std::vector<Move> options_for_this_pair;
            
            // Self-reference: stop expansion, keep it as-is
            if (next_state == current_state) {
                Move self_move;
                self_move.atoms = move.atoms;
                self_move.next_states.insert(pair);
                options_for_this_pair.push_back(self_move);
            }
            // Expand via already memoized state moves
            else {
                auto it = state_to_moves.find(next_state);
                if (it != state_to_moves.end() && !it->second.empty()) {
                    const auto& next_moves = it->second;
                    
                    for (const auto& next_move : next_moves) {
                        Move expanded;
                        expanded.atoms = move.atoms; // Start with current atoms
                        
                        // Merge atoms from the next move
                        expanded.atoms.insert(next_move.atoms.begin(), next_move.atoms.end());
                        
                        if (next_move.next_states.empty()) {
                            // Terminal move: no further next states, just atoms
                            // Don't add any next_states
                        } else {
                            // Merge next-states from referenced state
                            for (const auto& np : next_move.next_states) {
                                expanded.next_states.insert(np);
                            }
                        }
                        options_for_this_pair.push_back(std::move(expanded));
                    }
                } else {
                    // No info for that state: keep as symbolic reference
                    Move fallback;
                    fallback.atoms = move.atoms;
                    fallback.next_states.insert(pair);
                    options_for_this_pair.push_back(std::move(fallback));
                }
            }
            
            expansion_options.push_back(std::move(options_for_this_pair));
        }
        
        // Handle terminal (no next-states)
        if (expansion_options.empty()) {
            Move terminal;
            terminal.atoms = move.atoms;
            fully_expanded_moves->push_back(std::move(terminal));
            return;
        }
        
        // Determine expansion type (conjunctive vs disjunctive)
        // Check if current state represents AND/universal or OR/existential operator
        bool is_conjunctive = false;
        
        // Look up the operator for this state
        auto op_it = m_state_operator_.find(current_state);
        if (op_it != m_state_operator_.end()) {
            // If it's an AND operator, use conjunctive expansion (Cartesian product)
            is_conjunctive = (op_it->second == BinaryOperator::AND);
        } else {
            // For temporal operators, check the formula type
            auto state_it = std::find_if(v_states_.begin(), v_states_.end(),
                                        [&](const CTLStatePtr& s) { return s->name == current_state; });
            if (state_it != v_states_.end()) {
                const auto& formula = (*state_it)->formula;
                auto temporal = std::dynamic_pointer_cast<TemporalFormula>(formula);
                if (temporal) {
                    // Universal operators (AX, AU, AU~) use conjunctive expansion
                    is_conjunctive = (temporal->operator_ == TemporalOperator::AX ||
                                    temporal->operator_ == TemporalOperator::AU ||
                                    temporal->operator_ == TemporalOperator::AU_TILDE);
                }
                // Binary AND also uses conjunctive
                auto binary = std::dynamic_pointer_cast<BinaryFormula>(formula);
                if (binary && binary->operator_ == BinaryOperator::AND) {
                    is_conjunctive = true;
                }
            }
        }
        
        Move base_move;
        base_move.atoms = move.atoms;
        
        // Perform expansion based on type
        if (is_conjunctive) {
            // ---- Cartesian product (AND) ----
            // All combinations: one option from each position
            std::function<void(size_t, Move)> generate = [&](size_t i, Move acc) {
                if (i == expansion_options.size()) {
                    fully_expanded_moves->push_back(acc);
                    return;
                }
                for (const auto& opt : expansion_options[i]) {
                    Move combined = acc;
                    combined.atoms.insert(opt.atoms.begin(), opt.atoms.end());
                    combined.next_states.insert(opt.next_states.begin(), opt.next_states.end());
                    generate(i + 1, std::move(combined));
                }
            };
            generate(0, base_move);
        } else {
            // ---- Union (OR) ----
            // Each option becomes a separate move
            for (const auto& opts : expansion_options) {
                for (const auto& opt : opts) {
                    Move combined = base_move;
                    combined.atoms.insert(opt.atoms.begin(), opt.atoms.end());
                    combined.next_states.insert(opt.next_states.begin(), opt.next_states.end());
                    fully_expanded_moves->push_back(std::move(combined));
                }
            }
        }
        
        return;
    }



    //std::function<void(size_t, Move)> cross_product = [&](size_t option_index, Move current_combination) {
    //        if (option_index == expansion_options.size()) {
    //            // We've chosen one option from each position - this is a complete combination
    //            fully_expanded_moves->push_back(current_combination);
    //            return;
    //        }
    //        
    //        // Try each option at the current position
    //        for (const auto& option : expansion_options[option_index]) {
    //            Move combined = current_combination;
    //            
    //            // Merge atoms from this option
    //            combined.atoms.insert(option.atoms.begin(), option.atoms.end());
    //            
    //            // Merge next_states from this option
    //            combined.next_states.insert(option.next_states.begin(), option.next_states.end());
    //            
    //            // Recurse to next position in expansion_options
    //            cross_product(option_index + 1, combined);
    //        }
    //    };




}
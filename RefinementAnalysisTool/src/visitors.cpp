#include "visitors.h"
#include "formula_utils.h"
#include <regex>
#include <cctype>
#include <algorithm>

namespace ctl {

// Helper function to extract variable names from arithmetic expressions
std::vector<std::string> extractVariablesFromExpression(const std::string& expr) {
    std::vector<std::string> variables;
    std::string trimmed = expr;
    
    // Remove whitespace
    trimmed.erase(std::remove_if(trimmed.begin(), trimmed.end(), ::isspace), trimmed.end());
    
    // Use regex to find variable names (sequences of letters, digits, underscore starting with letter or underscore)
    std::regex var_regex(R"([a-zA-Z_][a-zA-Z0-9_]*)");
    std::sregex_iterator iter(trimmed.begin(), trimmed.end(), var_regex);
    std::sregex_iterator end;
    
    for (; iter != end; ++iter) {
        std::string var = iter->str();
        // Check if it's not a number (variables shouldn't be pure numbers)
        if (!var.empty() && !std::isdigit(var[0])) {
            // Avoid duplicates
            if (std::find(variables.begin(), variables.end(), var) == variables.end()) {
                variables.push_back(var);
            }
        }
    }
    
    return variables;
}

// Visitor implementations
void AtomCollectorVisitor::visit(const AtomicFormula& formula) {
    // Instead of adding the whole proposition, extract individual variables
    std::vector<std::string> vars = extractVariablesFromExpression(formula.proposition);
    for (const auto& var : vars) {
            atoms_.insert(var);
        
    }
}

void AtomCollectorVisitor::visit(const ComparisonFormula& formula) {
    // Extract variables from the variable field (might be a complex expression)
    std::vector<std::string> left_vars = extractVariablesFromExpression(formula.variable);
    for (const auto& var : left_vars) {
        atoms_.insert(var);
    }
    
    // If the value side is also a variable expression (not a number), extract variables from it too
    try {
        std::stod(formula.value); // Try to parse as number
        // It's a number, don't add it
    } catch (...) {
        // It's a variable expression, extract variables from it
        std::vector<std::string> right_vars = extractVariablesFromExpression(formula.value);
        for (const auto& var : right_vars) {
            atoms_.insert(var);
        }
    }
}

void AtomCollectorVisitor::visit(const BooleanLiteral& formula) {
    // Boolean literals are not atomic propositions
}

void AtomCollectorVisitor::visit(const NegationFormula& formula) {
    formula.operand->accept(*this);
}

void AtomCollectorVisitor::visit(const BinaryFormula& formula) {
    formula.left->accept(*this);
    formula.right->accept(*this);
}

void AtomCollectorVisitor::visit(const TemporalFormula& formula) {
    formula.operand->accept(*this);
    if (formula.second_operand) {
        formula.second_operand->accept(*this);
    }
}



void NNFConverterVisitor::visit(const AtomicFormula& formula) {
    if (negate_) {
        result_ = std::make_shared<AtomicFormula>("!" + formula.toString());
    } else {
        result_ = formula.clone();
    }
}

void NNFConverterVisitor::visit(const ComparisonFormula& formula) {
    if (negate_) {
        result_ = std::make_shared<AtomicFormula>("!(" + formula.toString() + ")");
    } else {
        result_ = formula.clone();
    }
}

void NNFConverterVisitor::visit(const BooleanLiteral& formula) {
    if (negate_) {
        result_ = std::make_shared<BooleanLiteral>(!formula.value);
    } else {
        result_ = formula.clone();
    }
}

void NNFConverterVisitor::visit(const NegationFormula& formula) {
    // Push negation inward
    result_ = convert(*formula.operand, !negate_);
}

void NNFConverterVisitor::visit(const BinaryFormula& formula) {
    auto left_nnf = convert(*formula.left, negate_);
    auto right_nnf = convert(*formula.right, negate_);


    if (negate_) {
        // Apply De Morgan's laws
        switch (formula.operator_) {
            case BinaryOperator::AND:
                // ¬(φ ∧ ψ) → ¬φ ∨ ¬ψ
                result_ = std::make_shared<BinaryFormula>(
                    convert(*formula.left, true), 
                    BinaryOperator::OR, 
                    convert(*formula.right, true));
                break;
            case BinaryOperator::OR:
                // ¬(φ ∨ ψ) → ¬φ ∧ ¬ψ
                result_ = std::make_shared<BinaryFormula>(
                    convert(*formula.left, true), 
                    BinaryOperator::AND, 
                    convert(*formula.right, true));
                break;
            case BinaryOperator::IMPLIES:
                // ¬(φ → ψ) → φ ∧ ¬ψ
                result_ = std::make_shared<BinaryFormula>(
                    convert(*formula.left, false), 
                    BinaryOperator::AND, 
                    convert(*formula.right, true));
                break;
        }
    } else {
        if (formula.operator_ == BinaryOperator::IMPLIES) {
            // φ → ψ ≡ ¬φ ∨ ψ
            result_ = std::make_shared<BinaryFormula>(
                convert(*formula.left, true), 
                BinaryOperator::OR, 
                convert(*formula.right, false));
        } else {
            result_ = std::make_shared<BinaryFormula>(left_nnf, formula.operator_, right_nnf);
        }
    }
}

void NNFConverterVisitor::visit(const TemporalFormula& formula) {
    if (negate_) {
        // Apply temporal duals with FULL coverage of all CTL operators
        switch (formula.operator_) {
            case TemporalOperator::EF: {
                // ¬EF φ ≡ AG ¬φ
                auto negated_operand = convert(*formula.operand, true);
                result_ = std::make_shared<TemporalFormula>(TemporalOperator::AG,  negated_operand);
                break;
            }
            case TemporalOperator::AF: {
                // ¬AF φ ≡ EG ¬φ
                auto negated_operand = convert(*formula.operand, true);
                result_ = std::make_shared<TemporalFormula>(TemporalOperator::EG,  negated_operand);
                break;
            }
            case TemporalOperator::EG: {
                // ¬EG φ ≡ AF ¬φ
                auto negated_operand = convert(*formula.operand, true);
                result_ = std::make_shared<TemporalFormula>(TemporalOperator::AF,  negated_operand);
                break;
            }
            case TemporalOperator::AG: {
                // ¬AG φ ≡ EF ¬φ
                auto negated_operand = convert(*formula.operand, true);
                result_ = std::make_shared<TemporalFormula>(TemporalOperator::EF,  negated_operand);
                break;
            }
            case TemporalOperator::EU: {
                // ¬E[φ U ψ] ≡ A[¬ψ W (¬φ ∧ ¬ψ)] ≡ A[¬ψ U (¬φ ∧ ¬ψ)] ∨ AG ¬ψ
                // Simpler: ¬E[φ U ψ] ≡ (AG ¬ψ) ∨ A[¬ψ U (¬φ ∧ ¬ψ)]
                // Even simpler for NNF: Use the fact that ¬E[φ U ψ] means "ψ never holds, or ¬φ holds when ψ first holds"
                // Standard translation: ¬E[φ U ψ] ≡ A[¬ψ W (¬φ ∧ ¬ψ)] ≡ 
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    auto neg_phi_and_neg_psi = std::make_shared<BinaryFormula>(neg_phi, BinaryOperator::AND, neg_psi);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::AW, neg_psi, neg_phi_and_neg_psi);
                }
                else {
                    throw std::runtime_error("NNFConverterVisitor::visit(EU): missing second operand");
                }
                break;
            }
            case TemporalOperator::AU: {
                // ¬A[φ U ψ] ≡ E[¬ψ W (¬φ ∧ ¬ψ)]
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    auto neg_phi_and_neg_psi = std::make_shared<BinaryFormula>(neg_phi, BinaryOperator::AND, neg_psi);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::EW, neg_psi, neg_phi_and_neg_psi);
                }
                else {
                    throw std::runtime_error("NNFConverterVisitor::visit(AU): missing second operand");
                }
                break;
            }
            case TemporalOperator::EW: {
                // ¬E[φ W ψ] ≡ A[¬φ U ¬ψ]
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::AU, neg_phi, neg_psi);
                }
                else {
                    throw std::runtime_error("NNFConverterVisitor::visit(EW): missing second operand");
                }
                break;
            }
            case TemporalOperator::AW: {
                // ¬A[φ W ψ] ≡ E[¬φ U ¬ψ]
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::EU, neg_phi, neg_psi);
                }
                else {
                    throw std::runtime_error("NNFConverterVisitor::visit(AW): missing second operand");
                }
                break;
            }

            case TemporalOperator::EU_TILDE: {
                // ¬Ẽ[φ Ũ ψ] ≡ A[¬ψ W (¬φ ∧ ¬ψ)]
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    auto neg_phi_and_neg_psi = std::make_shared<BinaryFormula>(neg_phi, BinaryOperator::AND, neg_psi);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::AW, neg_psi, neg_phi_and_neg_psi);
                }
                else{
                    throw std::runtime_error("ENFConverterVisitor::visit(EU_TILDE): missing second operand");
                }
                break;
            }

            case TemporalOperator::AU_TILDE: {
                // ¬Ã[φ Ũ ψ] ≡ E[¬ψ W (¬φ ∧ ¬ψ)]
                if (formula.second_operand) {
                    auto neg_phi = convert(*formula.operand, true);
                    auto neg_psi = convert(*formula.second_operand, true);
                    auto neg_phi_and_neg_psi = std::make_shared<BinaryFormula>(neg_phi, BinaryOperator::AND, neg_psi);
                    result_ = std::make_shared<TemporalFormula>(TemporalOperator::EW, neg_psi, neg_phi_and_neg_psi);
                }else{
                    throw std::runtime_error("ENFConverterVisitor::visit(AU_TILDE): missing second operand");
                }
                
                break;
            }

            default:
                // EX, AX - if we ever add them
                // For now, shouldn't reach here
                throw std::runtime_error("Unsupported temporal operator in NNF conversion: " + temporalOperatorToString(formula.operator_));
        }
    } else {
        // Not negated - just convert operands to NNF
        auto operand_nnf = convert(*formula.operand, false);
        if (formula.second_operand) {
            auto second_nnf = convert(*formula.second_operand, false);
            result_ = std::make_shared<TemporalFormula>(formula.operator_, operand_nnf, second_nnf);
        } else {
            result_ = std::make_shared<TemporalFormula>(formula.operator_,  operand_nnf);
        }
    }

}



static CTLFormulaPtr make_shared_clone(const CTLFormulaPtr& f) {
    return f->clone();
}

// --- helpers ---
CTLFormulaPtr ENFConverterVisitor::neg(const CTLFormulaPtr& f) {
    ENFConverterVisitor inner_v;
    f->accept(inner_v);
    auto inner = inner_v.getResult();

    if (auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(inner)) {
        return std::make_shared<BooleanLiteral>(!bool_lit->value);
    }
    if (auto neg_lit = std::dynamic_pointer_cast<NegationFormula>(inner)) {
        return neg_lit->operand->clone();
    }
    return std::make_shared<NegationFormula>(inner);
}

CTLFormulaPtr ENFConverterVisitor::t_true() {
    return std::make_shared<BooleanLiteral>(true);
}

CTLFormulaPtr ENFConverterVisitor::t_false() {
    return std::make_shared<BooleanLiteral>(false);
}

// --- atomic / literal visitors ---
void ENFConverterVisitor::visit(const AtomicFormula& f) {
    result_ = std::make_shared<AtomicFormula>(f);
}

void ENFConverterVisitor::visit(const ComparisonFormula& f) {
    result_ = std::make_shared<ComparisonFormula>(f);
}

void ENFConverterVisitor::visit(const BooleanLiteral& f) {
    result_ = std::make_shared<BooleanLiteral>(f);
}

void ENFConverterVisitor::visit(const NegationFormula& f) {
    // NNF guarantees negations are on atoms, so just clone
    result_ = std::make_shared<NegationFormula>(f);
}

void ENFConverterVisitor::visit(const BinaryFormula& f) {
    ENFConverterVisitor left_v, right_v;
    f.left->accept(left_v);
    f.right->accept(right_v);

    result_ = std::make_shared<BinaryFormula>(
        left_v.getResult(),
        f.operator_,
        right_v.getResult()
    );
}

// --- main temporal conversion logic ---
void ENFConverterVisitor::visit(const TemporalFormula& f) {
    switch (f.operator_) {

        // Existential operators stay as is
        case TemporalOperator::EX:
        case TemporalOperator::EU:
        
        case TemporalOperator::EG: {
            ENFConverterVisitor op1_v;
            f.operand->accept(op1_v);
            CTLFormulaPtr op1 = op1_v.getResult();

            if (f.second_operand) {
                ENFConverterVisitor op2_v;
                f.second_operand->accept(op2_v);
                CTLFormulaPtr op2 = op2_v.getResult();
                result_ = std::make_shared<TemporalFormula>(
                    f.operator_, op1, op2);
            } else {
                result_ = std::make_shared<TemporalFormula>(
                    f.operator_, op1);
            }
            break;
        }

        case TemporalOperator::EF:
        // E(true U φ) ≡ EF φ
        {
            ENFConverterVisitor op1_v;
            f.operand->accept(op1_v);
            CTLFormulaPtr op1 = op1_v.getResult();

            auto true_formula = t_true();
            result_ = std::make_shared<TemporalFormula>(
                TemporalOperator::EU,
                true_formula,
                op1);
            break;
        }

        case TemporalOperator::EW: {
            if (!f.second_operand) {
                throw std::runtime_error("ENFConverterVisitor::visit(EW): missing second operand");
            }

            ENFConverterVisitor phi_v;
            f.operand->accept(phi_v);
            CTLFormulaPtr phi = phi_v.getResult();

            ENFConverterVisitor psi_v;
            f.second_operand->accept(psi_v);
            CTLFormulaPtr psi = psi_v.getResult();

            auto eu = std::make_shared<TemporalFormula>(
                TemporalOperator::EU,
                phi->clone(),
                psi);
            auto eg = std::make_shared<TemporalFormula>(
                TemporalOperator::EG,
                phi);

            result_ = std::make_shared<BinaryFormula>(
                eu,
                BinaryOperator::OR,
                eg);
            break;
        }

        // --- UNIVERSAL -> EXISTENTIAL dualities ---
        case TemporalOperator::AX: {
            auto inner = std::make_shared<TemporalFormula>(
                TemporalOperator::EX,
                neg(make_shared_clone(f.operand))
            );
            result_ = neg(inner);
            break;
        }
        case TemporalOperator::AF: {
            // AF φ ≡ ¬EG ¬φ
            auto not_phi = neg(make_shared_clone(f.operand));
            auto eg_not_phi = std::make_shared<TemporalFormula>(
                TemporalOperator::EG, not_phi);
            result_ = neg(eg_not_phi);
            break;
        }

        //case TemporalOperator::AF: {
        //    auto e_until = std::make_shared<TemporalFormula>(
        //        TemporalOperator::EU,
        //        t_true(),
        //        make_shared_clone(f.operand)
        //    );
        //    result_ = e_until;
        //    break;
        //}

        case TemporalOperator::AG: {
            ENFConverterVisitor op_v;
            f.operand->accept(op_v);
            CTLFormulaPtr op = op_v.getResult();

            if (auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(op)) {
                result_ = bool_lit->value ? t_true() : t_false();
                break;
            }

            auto ef = std::make_shared<TemporalFormula>(
                TemporalOperator::EF,
                neg(op)
            );
            result_ = neg(ef);
            break;
        }

        case TemporalOperator::AU: {
            // A(φ U ψ) ≡ ¬E[(¬ψ) U (¬φ ∧ ¬ψ)] ∧ ¬EG(¬ψ)
            auto not_psi = neg(make_shared_clone(f.second_operand));
            auto not_phi = neg(make_shared_clone(f.operand));
            auto and_inner = std::make_shared<BinaryFormula>(
                not_phi, BinaryOperator::AND, not_psi);

            auto e_until = std::make_shared<TemporalFormula>(
                TemporalOperator::EU,
                not_psi,
                and_inner);

            auto eg_not_psi = std::make_shared<TemporalFormula>(
                TemporalOperator::EG,
                not_psi);

            auto left = neg(e_until);
            auto right = neg(eg_not_psi);
            result_ = std::make_shared<BinaryFormula>(
                left, BinaryOperator::AND, right);
            break;
        }

        case TemporalOperator::AW: {
            // A(φ W ψ) ≡ ¬E[(¬ψ) U (¬φ ∧ ¬ψ)]
            auto not_psi = neg(make_shared_clone(f.second_operand));
            auto not_phi = neg(make_shared_clone(f.operand));
            auto and_inner = std::make_shared<BinaryFormula>(
                not_phi, BinaryOperator::AND, not_psi);

            auto e_until = std::make_shared<TemporalFormula>(
                TemporalOperator::EU,
                not_psi,
                and_inner);

            result_ = neg(e_until);
            break;
        }

        default:
            throw std::runtime_error("ENFConverterVisitor: unknown temporal operator");
    }
}






 void BinaryToAtomVisitor::visit(const AtomicFormula& formula) {
    result_ = std::make_shared<AtomicFormula>(formula);
 }

 void BinaryToAtomVisitor::visit(const ComparisonFormula& f) {
    // Comparison formulas should always be treated as atomic propositions
    result_ = std::make_shared<AtomicFormula>(f.toString());
}

void BinaryToAtomVisitor::visit(const BooleanLiteral& formula) {
    result_ = std::make_shared<BooleanLiteral>(formula);
}
void BinaryToAtomVisitor::visit(const NegationFormula& formula){
    if(formula_utils::isPurelyPropositional(*formula.operand)){
        result_ = std::make_shared<AtomicFormula>(formula.toString());
    }
    else{
        BinaryToAtomVisitor operand_v;
        formula.operand->accept(operand_v);
        auto operand = operand_v.getResult();
        result_ = std::make_shared<NegationFormula>(operand);
    }
}
void BinaryToAtomVisitor::visit(const BinaryFormula& formula){
    //BinaryToAtomVisitor left_v, right_v;
    //formula.left->accept(left_v);
    //auto left = left_v.getResult();
    //formula.right->accept(right_v);
    //auto right = right_v.getResult();
//
    //result_ = std::make_shared<BinaryFormula>(left, formula.operator_, right);
    //auto l = 
    BinaryToAtomVisitor left_v, right_v;
    CTLFormulaPtr left, right;
    bool is_right, is_left;
    is_left = formula_utils::isPurelyPropositional(*formula.left);
    is_right = formula_utils::isPurelyPropositional(*formula.right);
    if (!is_left) {
        formula.left->accept(left_v);
        left = left_v.getResult();
    }else{
        if (formula.left->getType() == FormulaType::BOOLEAN_LITERAL) {
            auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(formula.left);
            left = std::make_shared<BooleanLiteral>(bool_lit->value);
        } else {
            left = std::make_shared<AtomicFormula>(""+formula.left->toString()+"");
        }
        //left = std::make_shared<AtomicFormula>(""+formula.left->toString()+"");
    }


    if (!is_right) {
        formula.right->accept(right_v);
        right = right_v.getResult();
    }else{
        if (formula.right->getType() == FormulaType::BOOLEAN_LITERAL) {
            auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(formula.right);
            right = std::make_shared<BooleanLiteral>(bool_lit->value);
        } else {
            right = formula.right->clone();
        }
    }

    if (is_left && is_right) {
        result_ = std::make_shared<AtomicFormula>("(" + formula.toString() + ")");
        return;
    }

    result_ = std::make_shared<BinaryFormula>(left, formula.operator_, right);
}
void BinaryToAtomVisitor::visit(const TemporalFormula& formula) {
    //we visit the operand and append it 
    BinaryToAtomVisitor operand_v, second_operand_v;
    CTLFormulaPtr second_operand, operand;
    bool is_first_pure = formula_utils::isPurelyPropositional(*formula.operand);
    bool is_second_pure = false;
    formula.operand->accept(operand_v);
    operand = operand_v.getResult();

    if (formula.second_operand) {
        formula.second_operand->accept(second_operand_v);
        second_operand = second_operand_v.getResult();
        is_second_pure = formula_utils::isPurelyPropositional(*formula.second_operand);
    }

    // we need to distinguish these case:
    // if we have or not a second operand
    //if  one 1 is pure, 2 isnt , viceverse, both or none^
    CTLFormulaPtr final_operand, final_second_operand;

    if (is_first_pure) {
        if (auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(operand)) {
            final_operand = bool_lit;
        } else {
            final_operand = std::make_shared<AtomicFormula>(formula.operand->toString());
        }
    } else {
        final_operand = operand->clone();
    }

    if (formula.second_operand) {
        if ( is_second_pure) {
            if (auto bool_lit = std::dynamic_pointer_cast<BooleanLiteral>(second_operand)) {
                result_ = std::make_shared<TemporalFormula>(formula.operator_, final_operand, bool_lit);
            } else {
                result_ = std::make_shared<TemporalFormula>(formula.operator_, final_operand, std::make_shared<AtomicFormula>(formula.second_operand->toString()));
            }
        } else {
            result_ = std::make_shared<TemporalFormula>(formula.operator_, final_operand, formula.second_operand->clone());
        }
    }   
    else {
        result_ = std::make_shared<TemporalFormula>(formula.operator_, final_operand);
    }


    //

    
}


// --- static entry point ---
CTLFormulaPtr ENFConverterVisitor::convert(const CTLFormula& formula) {
    ENFConverterVisitor visitor;
    formula.accept(visitor);
    return visitor.getResult();
}



// NNF Converter implementation
CTLFormulaPtr NNFConverterVisitor::convert(const CTLFormula& formula, bool negate) {
    NNFConverterVisitor visitor(negate);
    formula.accept(visitor);
    return visitor.getResult();
}

CTLFormulaPtr BinaryToAtomVisitor::convert(const CTLFormula& formula) {
    BinaryToAtomVisitor visitor;
    formula.accept(visitor);
    return visitor.getResult();
}
















WrapPropositionalVisitor::WrapPropositionalVisitor(bool inside_temporal)
    : inside_temporal_(inside_temporal) {}

CTLFormulaPtr WrapPropositionalVisitor::convert(const CTLFormula& formula) {
    WrapPropositionalVisitor v(false);
    formula.accept(v);
    return v.getResult();
}






// ---------- BASE CASES ----------

void WrapPropositionalVisitor::visit(const AtomicFormula& f) {

    if(formula_utils::isPurelyPropositional(f)){
        auto atom = std::make_shared<AtomicFormula>(f.toString());
        result_ = std::make_shared<TemporalFormula>(
                TemporalOperator::EU, std::make_shared<BooleanLiteral>(false), atom);
    }else{
        result_ = std::make_shared<AtomicFormula>(f);
    }
}

void WrapPropositionalVisitor::visit(const ComparisonFormula& f) {
    if(formula_utils::isPurelyPropositional(f)){
        auto atom = std::make_shared<AtomicFormula>(f.toString());
        result_ = std::make_shared<TemporalFormula>(
                TemporalOperator::EU, std::make_shared<BooleanLiteral>(false), atom);
    }else{
        result_ = std::make_shared<ComparisonFormula>(f);
    }
}

void WrapPropositionalVisitor::visit(const BooleanLiteral& f) {
    if(formula_utils::isPurelyPropositional(f)){
        auto atom = std::make_shared<AtomicFormula>(f.toString());
        result_ = std::make_shared<TemporalFormula>(
                TemporalOperator::EU, std::make_shared<BooleanLiteral>(false), atom);
    }else{
        result_ = std::make_shared<BooleanLiteral>(f);
    }
}

// ---------- COMPOSITE FORMULAS ----------

void WrapPropositionalVisitor::visit(const NegationFormula& f) {
    result_= f.clone();
}

void WrapPropositionalVisitor::visit(const BinaryFormula& f) {
    WrapPropositionalVisitor left_v(inside_temporal_);
    WrapPropositionalVisitor right_v(inside_temporal_);
    f.left->accept(left_v);
    f.right->accept(right_v);
    result_ = std::make_shared<BinaryFormula>(
        left_v.getResult(),
        f.operator_,
        right_v.getResult());
}

void WrapPropositionalVisitor::visit(const TemporalFormula& f) {
    // Enter temporal context (disable wrapping for subformulas)
    //WrapPropositionalVisitor op_v(true);
    //f.operand->accept(op_v);
    //auto op = op_v.getResult();
//
    //if (f.second_operand) {
    //    WrapPropositionalVisitor sec_v(true);
    //    f.second_operand->accept(sec_v);
    //    auto sec = sec_v.getResult();
    //    result_ = std::make_shared<TemporalFormula>(
    //        f.operator_, op, sec);
    //} else {
    //    result_ = std::make_shared<TemporalFormula>(
    //        f.operator_, op);
    //}
    result_ = f.clone();
}






}

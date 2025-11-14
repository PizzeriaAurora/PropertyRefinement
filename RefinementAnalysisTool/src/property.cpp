#include "property.h"
#include "parser.h"
#include <algorithm>
#include <unordered_set>

namespace ctl {

// Static cache initialization
std::unordered_map<std::string, std::shared_ptr<CTLProperty>> CTLProperty::property_cache_;

// Constructor implementations
CTLProperty::CTLProperty(const std::string& formula_str) {
    try {
        formula_ = Parser::parseFormula(formula_str);
    } catch (const ParseException& e) {
        throw std::invalid_argument("Failed to parse formula '" + formula_str + "': " + e.what());
    }
}

CTLProperty::CTLProperty(CTLFormulaPtr formula) : formula_(std::move(formula)) {
    if (!formula_) {
        throw std::invalid_argument("Formula cannot be null");
    }
}

// Factory methods with caching
std::shared_ptr<CTLProperty> CTLProperty::create(const std::string& formula_str) {
    auto it = property_cache_.find(formula_str);
    if (it != property_cache_.end()) {
        return it->second;
    }
    
    auto property = std::shared_ptr<CTLProperty>(new CTLProperty(formula_str));
    property_cache_[formula_str] = property;
    return property;
}

std::shared_ptr<CTLProperty> CTLProperty::create(CTLFormulaPtr formula) {
    std::string formula_str = formula->toString();
    return create(formula_str);
}

void CTLProperty::clearStaticCaches() {
    // Clear the static property cache
    property_cache_.clear();
    
    // Force memory deallocation by swapping with empty map
    std::unordered_map<std::string, std::shared_ptr<CTLProperty>> empty_cache;
    property_cache_.swap(empty_cache);
}

void CTLProperty::clearInstanceCaches() {
    // Clear refinement cache to break potential circular references
    refinement_cache_.clear();
    
    // Reset automaton shared_ptr to break any circular references
    automaton_.reset();
    
    // Clear atomic propositions cache
    atomic_props_.clear();
    atomic_props_computed_ = false;
}

// Atomic propositions (cached)
const std::unordered_set<std::string>& CTLProperty::getAtomicPropositions() const {
    if (!atomic_props_computed_) {
        auto atoms = formula_utils::collectAtomicPropositions(*formula_);
        atomic_props_ = std::unordered_set<std::string>(atoms.begin(), atoms.end());
        atomic_props_computed_ = true;
    }
    return atomic_props_;
}

// ABTA (lazy initialization)
const CTLAutomaton& CTLProperty::automaton() const {

    if (!automaton_) {

        automaton_ = std::make_shared<CTLAutomaton>(*formula_);
    }
    return *automaton_;
}

bool CTLProperty::isEmpty() const {
    automaton(); // Ensure ABTA is initialized
    return automaton_->isEmpty();
}

void CTLProperty::simplify() const {
    automaton(); // Ensure ABTA is initialized
    //abta_->simplify();
}

// Refinement checking
bool CTLProperty::refines(const CTLProperty& other, bool use_syntactic, bool use_full_inclusion) const {
    // Check cache first
    //auto shared_other = std::shared_ptr<CTLProperty>(const_cast<CTLProperty*>(&other), [](CTLProperty*){});
    //auto cache_it = refinement_cache_.find(shared_other);
    //if (cache_it != refinement_cache_.end()) {
    //    return cache_it->second;
    //}
    
    bool result = false;
    
    if (use_syntactic) {
        result = refinesSyntactic(other);
        if (result) {
            // Cache and return early if syntactic check succeeds
            //refinement_cache_[shared_other] = result;
            return true;
        }
    }
    
    // Always do semantic check if syntactic doesn't succeed or isn't used
    result = refinesSemantic(other, use_full_inclusion);
    
    // Cache the result
    //refinement_cache_[shared_other] = result;
    return result;
}

bool CTLProperty::refinesSyntactic(const CTLProperty& other) const {
    return refinementCheck(*formula_, *other.formula_);
}

bool CTLProperty::refinesSemantic(const CTLProperty& other, bool use_full_inclusion) const {
    // Use ABTA language inclusion check
    // self.refines(other) iff L(self) ⊆ L(other)
   
    if (use_full_inclusion)
    {
        //std::cout << "Using full language inclusion for semantic refinement check.\n";
        //Use product and emptiness: L(self) ⊆ L(other) 
        //std::cout << "Checking language inclusion L(this) ⊆ L(other).\n";
        //std::cout << "This property formula: " << this->toString() << "\n";
        //std::cout << "Other property formula: " << other.toString() << "\n";
        return other.automaton().languageIncludes(automaton());
        
    }
    else
    {
        const CTLAutomaton& this_abta = automaton();
        const CTLAutomaton& other_abta = other.automaton();
        return  other_abta.simulates(this_abta);
    }
}

// Equality and hashing
bool CTLProperty::equals(const CTLProperty& other) const {
    return formula_->equals(*other.formula_);
}

size_t CTLProperty::hash() const {
    return formula_->hash();
}

// Private syntactic refinement implementation
bool CTLProperty::refinementCheck(const CTLFormula& f1, const CTLFormula& f2) const {
    // Structural equality check first
    if (f1.equals(f2)) {
        return true;
    }
    
    // Dispatch based on formula types
    if (f1.isAtomic() && f2.isAtomic()) {
        return refinementCheckAtomic(f1, f2);
    }
    
    // Handle negation
    if (auto neg1 = dynamic_cast<const NegationFormula*>(&f1)) {
        return refinementCheckNegation(*neg1, f2);
    }
    
    // Handle binary operators
    if (auto bin1 = dynamic_cast<const BinaryFormula*>(&f1)) {
        return refinementCheckBinary(*bin1, f2);
    }
    
    // Handle temporal operators
    if (auto temp1 = dynamic_cast<const TemporalFormula*>(&f1)) {
        return refinementCheckTemporal(*temp1, f2);
    }
    
    // Handle cases where f2 is a binary operator
    if (auto bin2 = dynamic_cast<const BinaryFormula*>(&f2)) {
        switch (bin2->operator_) {
            case BinaryOperator::AND:
                // f1 ⊑ (f2_left ∧ f2_right) iff f1 ⊑ f2_left and f1 ⊑ f2_right
                return refinementCheck(f1, *bin2->left) && refinementCheck(f1, *bin2->right);
                
            case BinaryOperator::OR:
                // f1 ⊑ (f2_left ∨ f2_right) iff f1 ⊑ f2_left or f1 ⊑ f2_right
                return refinementCheck(f1, *bin2->left) || refinementCheck(f1, *bin2->right);
                
            case BinaryOperator::IMPLIES:
                // f1 ⊑ (f2_left → f2_right) is more complex, handle conservatively
                return false;
        }
    }
    
    return false;
}

bool CTLProperty::refinementCheckAtomic(const CTLFormula& f1, const CTLFormula& f2) const {
    // Atomic formulas refine each other only if they are identical
    return f1.equals(f2);
}

bool CTLProperty::refinementCheckNegation(const NegationFormula& f1, const CTLFormula& f2) const {
    // ¬φ ⊑ ψ is handled by contrapositive in some cases
    if (auto neg2 = dynamic_cast<const NegationFormula*>(&f2)) {
        // ¬φ ⊑ ¬ψ iff ψ ⊑ φ (contrapositive)
        return refinementCheck(*neg2->operand, *f1.operand);
    }
    
    return false; // Conservative approach
}

bool CTLProperty::refinementCheckBinary(const BinaryFormula& f1, const CTLFormula& f2) const {
    switch (f1.operator_) {
        case BinaryOperator::AND:
            // (φ ∧ ψ) ⊑ χ iff φ ⊑ χ or ψ ⊑ χ
            return refinementCheck(*f1.left, f2) || refinementCheck(*f1.right, f2);
            
        case BinaryOperator::OR:
            // (φ ∨ ψ) ⊑ χ iff φ ⊑ χ and ψ ⊑ χ
            return refinementCheck(*f1.left, f2) && refinementCheck(*f1.right, f2);
            
        case BinaryOperator::IMPLIES:
            // Handle implication specially
            if (auto bin2 = dynamic_cast<const BinaryFormula*>(&f2)) {
                if (bin2->operator_ == BinaryOperator::IMPLIES) {
                    // (φ → ψ) ⊑ (χ → δ) if φ = χ and ψ ⊑ δ
                    if (f1.left->equals(*bin2->left)) {
                        return refinementCheck(*f1.right, *bin2->right);
                    }
                }
            }
            return false;
    }
    
    return false;
}

bool CTLProperty::refinementCheckTemporal(const TemporalFormula& f1, const CTLFormula& f2) const {
    auto temp2 = dynamic_cast<const TemporalFormula*>(&f2);
    if (!temp2) {
        return false;
    }
    
    // Check if the temporal operators are in refinement order
    if (!temporalOperatorRefines(f1.operator_, temp2->operator_)) {
        return false;
    }
    
    // Check time intervals
    if (!intervalSubsumes(f1.interval, temp2->interval)) {
        return false;
    }
    
    // Check operands based on operator type
    if (f1.second_operand && temp2->second_operand) {
        // Binary temporal operators (EU, AU, etc.)
        if (f1.operator_ == temp2->operator_) {
            switch (f1.operator_) {
                case TemporalOperator::EU:
                case TemporalOperator::AU:
                    // E[φ U ψ] ⊑ E[χ U δ] iff φ ⊑ χ and ψ ⊑ δ
                    return refinementCheck(*f1.operand, *temp2->operand) && 
                           refinementCheck(*f1.second_operand, *temp2->second_operand);
                default:
                    break;
            }
        }
    } else if (!f1.second_operand && !temp2->second_operand) {
        // Unary temporal operators
        return refinementCheck(*f1.operand, *temp2->operand);
    }
    
    return false;
}

// Helper methods
bool CTLProperty::intervalSubsumes(const TimeInterval& inner, const TimeInterval& outer) {
    return outer.subsumes(inner);
}

bool CTLProperty::temporalOperatorRefines(TemporalOperator op1, TemporalOperator op2) {
    // Define refinement relationships between temporal operators
    // Based on the lattice: AG ⊑ AF ⊑ EF and AG ⊑ EG ⊑ EF
    
    if (op1 == op2) {
        return true;
    }
    
    switch (op1) {
        case TemporalOperator::AG:
            return op2 == TemporalOperator::AF || op2 == TemporalOperator::EG || 
                   op2 == TemporalOperator::EF;
            
        case TemporalOperator::AF:
            return op2 == TemporalOperator::EF;
            
        case TemporalOperator::EG:
            return op2 == TemporalOperator::EF;
            
        case TemporalOperator::EF:
            return false; // EF is the top of the lattice
            
        default:
            return false; // Conservative for other operators
    }
}

} // namespace ctl
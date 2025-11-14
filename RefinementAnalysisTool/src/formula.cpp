#include "formula.h"
#include "visitors.h"
#include <sstream>
#include <limits>

namespace ctl {

// AtomicFormula implementation
bool AtomicFormula::equals(const CTLFormula& other) const {
    if (auto atomic = dynamic_cast<const AtomicFormula*>(&other)) {
        return proposition == atomic->proposition;
    }
    return false;
}

size_t AtomicFormula::hash() const {
    return std::hash<std::string>{}("atomic:" + proposition);
}

void AtomicFormula::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

// ComparisonFormula implementation
bool ComparisonFormula::equals(const CTLFormula& other) const {
    if (auto comparison = dynamic_cast<const ComparisonFormula*>(&other)) {
        return variable == comparison->variable && 
               operator_ == comparison->operator_ && 
               value == comparison->value;
    }
    return false;
}

size_t ComparisonFormula::hash() const {
    return std::hash<std::string>{}("comparison:" + variable + operator_ + value);
}

void ComparisonFormula::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

// BooleanLiteral implementation
bool BooleanLiteral::equals(const CTLFormula& other) const {
    if (auto boolean = dynamic_cast<const BooleanLiteral*>(&other)) {
        return value == boolean->value;
    }
    return false;
}

size_t BooleanLiteral::hash() const {
    return std::hash<std::string>{}("boolean:" + std::to_string(value));
}

void BooleanLiteral::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

// NegationFormula implementation
std::string NegationFormula::toString() const {
    if (operand->isAtomic()) {
        return "!(" + operand->toString() + ")";
    }
    return "!("  + operand->toString() + ")";
}

std::string NegationFormula::toNuSMVString() const {
    return "!" + (operand->isAtomic() ? operand->toNuSMVString() : "(" + operand->toNuSMVString() + ")");
}

CTLFormulaPtr NegationFormula::clone() const {
    return std::make_shared<NegationFormula>(operand->clone());
}

bool NegationFormula::equals(const CTLFormula& other) const {
    if (auto negation = dynamic_cast<const NegationFormula*>(&other)) {
        return operand->equals(*negation->operand);
    }
    return false;
}

size_t NegationFormula::hash() const {
    return std::hash<std::string>{}("negation:") ^ (operand->hash() << 1);
}

void NegationFormula::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

// BinaryFormula implementation
std::string BinaryFormula::operatorToString() const {
    switch (operator_) {
        case BinaryOperator::AND: return "&";
        case BinaryOperator::OR: return "|";
        case BinaryOperator::IMPLIES: return "->";
        default: return "?";
    }
}

std::string BinaryFormula::operatorToNuSMVString() const {
    switch (operator_) {
        case BinaryOperator::AND: return "&";
        case BinaryOperator::OR: return "|";
        case BinaryOperator::IMPLIES: return "->";
        default: return "?";
    }
}

std::string BinaryFormula::toString() const {
    std::string leftStr = left->isAtomic() || left->isBinary() ? left->toString() : "(" + left->toString() + ")";
    std::string rightStr = right->isAtomic() ? right->toString() : "(" + right->toString() + ")";
    return leftStr + " " + operatorToString() + " " + rightStr;
}

std::string BinaryFormula::toNuSMVString() const {
    std::string leftStr = left->isAtomic() || left->isBinary() ? left->toNuSMVString() : "(" + left->toNuSMVString() + ")";
    std::string rightStr = right->isAtomic() ? right->toNuSMVString() : "(" + right->toNuSMVString() + ")";
    return leftStr + " " + operatorToNuSMVString() + " " + rightStr;
}

CTLFormulaPtr BinaryFormula::clone() const {
    return std::make_shared<BinaryFormula>(left->clone(), operator_, right->clone());
}

bool BinaryFormula::equals(const CTLFormula& other) const {
    if (auto binary = dynamic_cast<const BinaryFormula*>(&other)) {
        return operator_ == binary->operator_ && 
               left->equals(*binary->left) && 
               right->equals(*binary->right);
    }
    return false;
}

size_t BinaryFormula::hash() const {
    size_t h1 = std::hash<int>{}(static_cast<int>(operator_));
    size_t h2 = left->hash();
    size_t h3 = right->hash();
    return h1 ^ (h2 << 1) ^ (h3 << 2);
}

void BinaryFormula::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

// TemporalFormula implementation
std::string TemporalFormula::operatorToString() const {
    switch (operator_) {
        case TemporalOperator::EF: return "EF";
        case TemporalOperator::AF: return "AF";
        case TemporalOperator::EG: return "EG";
        case TemporalOperator::AG: return "AG";
        case TemporalOperator::EU: return "EU";
        case TemporalOperator::AU: return "AU";
        case TemporalOperator::EW: return "EW";
        case TemporalOperator::AW: return "AW";
        case TemporalOperator::EX: return "EX";
        case TemporalOperator::AX: return "AX";
        case TemporalOperator::EU_TILDE: return "ER";
        case TemporalOperator::AU_TILDE: return "AR";
        default: return "?";
    }
}

std::string TemporalFormula::operatorToNuSMVString() const {
    switch (operator_) {
        case TemporalOperator::EF: return "EF";
        case TemporalOperator::AF: return "AF";
        case TemporalOperator::EG: return "EG";
        case TemporalOperator::AG: return "AG";
        case TemporalOperator::EU: return "E";
        case TemporalOperator::AU: return "A";
        case TemporalOperator::EW: return "E";
        case TemporalOperator::AW: return "A";
        case TemporalOperator::EX: return "EX";
        case TemporalOperator::AX: return "AX";
        default: return "?";
    }
}

std::string TemporalFormula::toString() const {
    std::string result = operatorToString();
    
    // Add time interval if not default
    if (interval.lower != 0 || interval.upper != std::numeric_limits<int>::max()) {
        result += interval.toString();
    }
    
    if (second_operand) {
        // Binary temporal operator
        std::string firstStr = operand->isAtomic() ? operand->toString() : "(" + operand->toString() + ")";
        std::string secondStr = second_operand->isAtomic() ? second_operand->toString() : "(" + second_operand->toString() + ")";
        
        if (operator_ == TemporalOperator::EU || operator_ == TemporalOperator::AU) {
            result = result.substr(0, 1) + "(" + firstStr + " U " + secondStr + ")";
        } else if (operator_ == TemporalOperator::EW || operator_ == TemporalOperator::AW) {
            result = result.substr(0, 1) + "(" + firstStr + " W " + secondStr + ")";
        }else if (operator_ == TemporalOperator::EU_TILDE) {
            result = result.substr(0, 1) + "(" + firstStr + " R " + secondStr + ")";
        }else if (operator_ == TemporalOperator::AU_TILDE) {
            result = result.substr(0, 1) + "(" + firstStr + " R " + secondStr + ")";
        }
    } else {
        // Unary temporal operator
        std::string operandStr = operand->isAtomic() ? operand->toString() : "(" + operand->toString() + ")";
        result += " " + operandStr;
    }
    
    return result;
}

std::string TemporalFormula::toNuSMVString() const {
    std::string result = operatorToNuSMVString();
    
    if (second_operand) {
        // Binary temporal operator
        std::string firstStr = operand->isAtomic() ? operand->toNuSMVString() : "(" + operand->toNuSMVString() + ")";
        std::string secondStr = second_operand->isAtomic() ? second_operand->toNuSMVString() : "(" + second_operand->toNuSMVString() + ")";
        
        if (operator_ == TemporalOperator::EU || operator_ == TemporalOperator::AU) {
            result = result + "[" + firstStr + " U " + secondStr + "]";
        } else if (operator_ == TemporalOperator::EW || operator_ == TemporalOperator::AW) {
            result = result + "[" + firstStr + " W " + secondStr + "]";
        }
    } else {
        // Unary temporal operator
        std::string operandStr = operand->isAtomic() ? operand->toNuSMVString() : "(" + operand->toNuSMVString() + ")";
        result += " " + operandStr;
    }
    
    return result;
}

CTLFormulaPtr TemporalFormula::clone() const {
    if (second_operand) {
        return std::make_shared<TemporalFormula>(operator_, operand->clone(), second_operand->clone());
    } else {
        return std::make_shared<TemporalFormula>(operator_, interval, operand->clone());
    }
}

bool TemporalFormula::equals(const CTLFormula& other) const {
    if (auto temporal = dynamic_cast<const TemporalFormula*>(&other)) {
        if (operator_ != temporal->operator_ || interval != temporal->interval) {
            return false;
        }
        
        if (!operand->equals(*temporal->operand)) {
            return false;
        }
        
        if (second_operand && temporal->second_operand) {
            return second_operand->equals(*temporal->second_operand);
        } else if (!second_operand && !temporal->second_operand) {
            return true;
        }
        
        return false; // One has second operand, other doesn't
    }
    return false;
}

size_t TemporalFormula::hash() const {
    size_t h1 = std::hash<int>{}(static_cast<int>(operator_));
    size_t h2 = std::hash<int>{}(interval.lower) ^ (std::hash<int>{}(interval.upper) << 1);
    size_t h3 = operand->hash();
    size_t h4 = second_operand ? second_operand->hash() : 0;
    return h1 ^ (h2 << 1) ^ (h3 << 2) ^ (h4 << 3);
}

void TemporalFormula::accept(CTLFormulaVisitor& visitor) const {
    visitor.visit(*this);
}

CTLFormulaPtr Conjunction(const CTLFormulaPtr& lhs, const CTLFormulaPtr& rhs) {
    //return  a formula representing the conjunction of this and other
    return std::make_shared<BinaryFormula>(lhs->clone(), BinaryOperator::AND, rhs->clone());
}

bool isPurelyPropositional(const CTLFormula& formula) {
    if (dynamic_cast<const AtomicFormula*>(&formula) ||
        dynamic_cast<const ComparisonFormula*>(&formula) ||
        dynamic_cast<const BooleanLiteral*>(&formula)) {
        return true;
    }
    
    if (auto negation = dynamic_cast<const NegationFormula*>(&formula)) {
        return isPurelyPropositional(*negation->operand);
    }
    
    if (auto binary = dynamic_cast<const BinaryFormula*>(&formula)) {
        return isPurelyPropositional(*binary->left) && isPurelyPropositional(*binary->right);
    }
    
    if (dynamic_cast<const TemporalFormula*>(&formula)) {
        return false;
    }
    
    return false;
}

} // namespace ctl
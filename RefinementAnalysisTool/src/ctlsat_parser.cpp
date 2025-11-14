#include "ctlsat_parser.h"
#include "parser.h"
#include <sstream>

namespace ctl {

// Initialize static members
std::unordered_map<std::string, std::string> CTLSATParser::comparison_map_;
std::unordered_map<std::string, std::string> CTLSATParser::atom_map_;
int CTLSATParser::next_atom_id_ = 1;

std::string CTLSATParser::toCtlSatFormat(const CTLFormula& formula) {
    return convertFormula(formula);
}

std::string CTLSATParser::convertString(const std::string& formula_str) {
    // Parse the formula string first using the static convenience method
    auto formula = Parser::parseFormula(formula_str);
    
    // Convert to CTLSAT format
    return convertFormula(*formula);
}

const std::unordered_map<std::string, std::string>& CTLSATParser::getComparisonMapping() {
    return comparison_map_;
}

void CTLSATParser::clearComparisonMapping() {
    comparison_map_.clear();
    atom_map_.clear();
    next_atom_id_ = 1;
}

std::string CTLSATParser::getComparisonAtom(const std::string& comparison) {
    // Check if we already have a mapping for this comparison
    auto it = comparison_map_.find(comparison);
    if (it != comparison_map_.end()) {
        return it->second;
    }
    
    // Create a new atom for this comparison using single letters
    // Format: a, b, c, ..., z (26 possible atoms)
    if (next_atom_id_ > 26) {
        throw std::runtime_error("Too many unique atoms (max 26)");
    }
    
    char letter = 'a' + (next_atom_id_ - 1);
    std::string atom(1, letter);
    next_atom_id_++;
    comparison_map_[comparison] = atom;
    return atom;
}

std::string CTLSATParser::getAtomLetter(const std::string& atom) {
    // Check if we already have a mapping for this atom
    auto it = atom_map_.find(atom);
    if (it != atom_map_.end()) {
        return it->second;
    }
    
    // Create a new letter for this atom using single letters
    // Format: a, b, c, ..., z (26 possible atoms total across both maps)
    if (next_atom_id_ > 26) {
        throw std::runtime_error("Too many unique atoms (max 26)");
    }
    
    char letter = 'a' + (next_atom_id_ - 1);
    std::string letter_str(1, letter);
    next_atom_id_++;
    atom_map_[atom] = letter_str;
    return letter_str;
}

std::string CTLSATParser::convertFormula(const CTLFormula& formula) {
    // Handle comparison formulas - map to unique atoms (p1, p2, p3, etc.)
    if (auto comp = dynamic_cast<const ComparisonFormula*>(&formula)) {
        std::string comparison_str = comp->toString();
        return getComparisonAtom(comparison_str);
    }
    
    // Handle boolean literals (true/false)
    if (auto boolean = dynamic_cast<const BooleanLiteral*>(&formula)) {
        return boolean->value ? "T" : "~T";
    }
    
    // Handle atomic formulas
    if (auto atomic = dynamic_cast<const AtomicFormula*>(&formula)) {
        if (atomic->proposition == "false") {
            return "~T";
        }
        if (atomic->proposition == "true") {
            return "T";
        }
        // Map atomic proposition to a single letter
        return getAtomLetter(atomic->proposition);
    }
    
    // Handle negation
    if (auto neg = dynamic_cast<const NegationFormula*>(&formula)) {
        return "~(" + convertFormula(*neg->operand) + ")";
    }
    
    // Handle binary formulas (AND, OR, IMPLIES)
    if (auto binary = dynamic_cast<const BinaryFormula*>(&formula)) {
        std::string left_str = convertFormula(*binary->left);
        std::string right_str = convertFormula(*binary->right);
        
        switch (binary->operator_) {
            case BinaryOperator::AND:
                return "(" + left_str + " ^ " + right_str + ")";
            case BinaryOperator::OR:
                return "(" + left_str + " v " + right_str + ")";
            case BinaryOperator::IMPLIES:
                return "(" + left_str + " -> " + right_str + ")";
        }
    }
    
    // Handle temporal formulas
    if (auto temporal = dynamic_cast<const TemporalFormula*>(&formula)) {
        switch (temporal->operator_) {
            case TemporalOperator::EX:
                return "EX(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::AX:
                return "AX(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::EF:
                return "EF(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::AF:
                return "AF(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::EG:
                return "EG(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::AG:
                return "AG(" + convertFormula(*temporal->operand) + ")";
            case TemporalOperator::EU:
                return "E(" + convertFormula(*temporal->operand) + " U " + 
                       convertFormula(*temporal->second_operand) + ")";
            case TemporalOperator::AU:
                return "A(" + convertFormula(*temporal->operand) + " U " + 
                       convertFormula(*temporal->second_operand) + ")";
            case TemporalOperator::EW:
                // E[φ W ψ] is rewritten as E[φ U ψ] | EG φ
                return "(E(" + convertFormula(*temporal->operand) + " U " + 
                       convertFormula(*temporal->second_operand) + ") v EG(" + 
                       convertFormula(*temporal->operand) + "))";
            case TemporalOperator::AW:
                // A[φ W ψ] is rewritten as A[φ U ψ] | AG φ
                return "(A(" + convertFormula(*temporal->operand) + " U " + 
                       convertFormula(*temporal->second_operand) + ") v AG(" + 
                       convertFormula(*temporal->operand) + "))";
        }
    }
    
    // Default case: return formula string representation
    return formula.toString();
}

} // namespace ctl

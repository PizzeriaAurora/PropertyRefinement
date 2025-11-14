
#pragma once
#include "formula.h"
#include "types.h"

#include <string>
#include <unordered_map>
#include <unordered_set>

// Conditional includes based on SMT solver
#ifdef USE_Z3
#include <z3++.h>
#endif

#ifdef USE_CVC5
#include <cvc5/cvc5.h>
#endif



namespace ctl {





// Utility functions for formula manipulation
namespace formula_utils {
    

    struct FormulaKey {
    std::string s;
    explicit FormulaKey(const CTLFormula& f) : s(f.toString()) {}
    bool operator==(const FormulaKey& o) const { return s == o.s; }
    };
    
    struct FormulaKeyHash {
        std::size_t operator()(const FormulaKey& k) const noexcept {
            return std::hash<std::string>{}(k.s);
        }
    };

    // Collect all atomic propositions from a formula
    std::unordered_set<std::string> collectAtomicPropositions(const CTLFormula& formula);
    
    // Collect atomic propositions with their full representation for complexity analysis
    // This includes comparisons like "60<=Weight" as single atoms, and boolean combinations
    std::unordered_set<std::string> getAtomicForAnalysis(const CTLFormula& formula);
    
    // Convert formula to Negation Normal Form (NNF)
    CTLFormulaPtr toNNF(const CTLFormula& formula);
    
    // Check structural equality
    bool structurallyEqual(const CTLFormula& f1, const CTLFormula& f2);
    
    // Compute hash for formulas
    size_t computeHash(const CTLFormula& formula);

    std::unique_ptr<CTLFormula> normalizeToCore(const CTLFormula& f);
    

    /**
     * @brief Checks if a formula contains no temporal operators.
     * @param formula The formula to check
     * @return true if formula is purely propositional (atoms, booleans, and boolean operators only)
     */
    bool isPurelyPropositional(const CTLFormula& formula);

    CTLFormulaPtr Conjunction(const CTLFormulaPtr& lhs, const CTLFormulaPtr& rhs);

    void collectClosureDFS(
    const CTLFormula& f,
    std::unordered_map<FormulaKey, const CTLFormula*, FormulaKeyHash>& seen,
    std::vector<const CTLFormula*>& outTopo); 

#ifdef USE_Z3
     z3::expr parseStringToZ3(const std::string& str, z3::context& ctx, bool as_bool=true);
     z3::expr parseStringToZ3(const std::string_view& str, z3::context& ctx, bool as_bool=true);
#endif

#ifdef USE_CVC5
     cvc5::Term parseStringToCVC5(const std::string& str, cvc5::Solver& solver, bool as_bool=true);
     cvc5::Term parseStringToCVC5(const std::string_view& str, cvc5::Solver& solver, bool as_bool=true);
#endif
    
   // // Simplify formula (remove double negations, etc.)
   // CTLFormulaPtr simplify(const CTLFormula& formula);
   // 
   // // Check if formula is in NNF
   // bool isInNNF(const CTLFormula& formula);
   // 
   // // Get the size (number of nodes) of a formula
   // size_t getFormulaSize(const CTLFormula& formula);
   // 
   // // Get the depth of a formula
   // size_t getFormulaDepth(const CTLFormula& formula);


// conversion from FormulaType to string
static std::string formulaTypeToString(FormulaType type) {
    switch (type) {
        case FormulaType::ATOMIC:
            return "ATOMIC";
        case FormulaType::COMPARISON:
            return "COMPARISON";
        case FormulaType::BOOLEAN_LITERAL:
            return "BOOLEAN_LITERAL";
        case FormulaType::NEGATION:
            return "NEGATION";
        case FormulaType::BINARY:
            return "BINARY";
        case FormulaType::TEMPORAL: 
            return "TEMPORAL";
        default:
            return "UNKNOWN";
    }
}




static std::string blockTypeToString(SCCBlockType type) {
    switch (type) {
        case SCCBlockType::UNIVERSAL:
            return "UNIVERSAL";
        case SCCBlockType::EXISTENTIAL:
            return "EXISTENTIAL";
        case SCCBlockType::SIMPLE:
            return "SIMPLE";
        default:
            return "UNDEFINED";
    }
}

static std::ostream& operator<<(std::ostream& os, SCCBlockType type) {
    os << blockTypeToString(type);
    return os;
}

static std::ostream& operator<<(std::ostream& os, FormulaType type) {
    os << formulaTypeToString(type);
    return os;
}


bool isGreatestFixpointBlock(const CTLFormulaPtr& formula);
bool isLeastFixpointBlock(const CTLFormulaPtr& formula);
SCCAcceptanceType getBlockAcceptanceTypeFromFormula(const CTLFormulaPtr& formula);
bool isExistentialBlock(const CTLFormulaPtr& formula);
bool isUniversalBlock(const CTLFormulaPtr& formula);
SCCBlockType getSCCBlockTypeFromFormula(const CTLFormulaPtr& formula);

#ifdef USE_Z3
z3::expr conjToZ3Expr(const Conj& conj, z3::context& ctx);
z3::expr disjToZ3Expr(const std::vector<Conj>& disj, z3::context& ctx);
#endif

CTLFormulaPtr preprocessFormula(const CTLFormula& formula);
CTLFormulaPtr negateFormula(const CTLFormula& formula);


} // namespace formula_utils

} // namespace ctl
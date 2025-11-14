#include "SMTInterfaces/CVC5SMTInterface.h"
#include "formula_utils.h"
#include <stdexcept>

namespace ctl {

#ifdef USE_CVC5

CVC5SMTInterface::CVC5SMTInterface() 
    : solver_(std::make_unique<cvc5::Solver>()) {
    // Set logic if needed (optional, CVC5 can auto-detect)
    // solver_->setLogic("QF_LIA"); // Quantifier-free linear integer arithmetic
}

bool CVC5SMTInterface::isSatisfiable(const std::string& formula) const {
    // Handle special cases
    if (formula == "true") return true;
    if (formula.empty() || formula == "false") return false;
    
    // Delegate to the set-based version
    return isSatisfiable(std::unordered_set<std::string>{formula});
}

bool CVC5SMTInterface::isSatisfiable(const std::unordered_set<std::string>& formulas) const {
    // Handle empty set
    if (formulas.empty()) return true;
    
    try {
        // Push a new scope to ensure we can clean up
        solver_->push();
        
        // Add all formulas to the solver
        for (const auto& formula : formulas) {
            // Skip special cases
            if (formula == "true" || formula.empty()) continue;
            if (formula == "false") {
                solver_->pop();
                return false;
            }
            
            // Parse and add the formula
            cvc5::Term term = parseToCVC5Term(formula);
            solver_->assertFormula(term);
        }
        
        // Check satisfiability
        cvc5::Result result = solver_->checkSat();
        bool is_sat = result.isSat();
        
        // Pop the scope to clean up
        solver_->pop();
        
        return is_sat;
        
    } catch (const std::exception& e) {
        // Make sure to pop even on exception
        try {
            solver_->pop();
        } catch (...) {
            // Ignore errors during cleanup
        }
        throw std::runtime_error(std::string("CVC5 satisfiability check failed: ") + e.what());
    }
}

cvc5::Term CVC5SMTInterface::parseToCVC5Term(const std::string& str) const {
    // Use the formula_utils parser
    return formula_utils::parseStringToCVC5(str, *solver_);
}

std::unique_ptr<SMTInterface> CVC5SMTInterface::clone() const {
    // Create a new instance with its own CVC5 solver
    return std::make_unique<CVC5SMTInterface>();
}

// Factory function implementation when using CVC5
std::unique_ptr<SMTInterface> createDefaultSMTInterface() {
    return std::make_unique<CVC5SMTInterface>();
}

#endif // USE_CVC5

} // namespace ctl

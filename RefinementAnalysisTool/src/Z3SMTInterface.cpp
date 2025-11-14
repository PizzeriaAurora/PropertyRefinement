#include "SMTInterfaces/Z3SMTInterface.h"
#include "formula_utils.h"
#include <stdexcept>

namespace ctl {

#ifdef USE_Z3

Z3SMTInterface::Z3SMTInterface() 
    : ctx_(std::make_unique<z3::context>()),
      solver_(std::make_unique<z3::solver>(*ctx_)) {
}

// Destructor is defaulted in header, but for clarity:
// Z3 resources (solver and context) are automatically cleaned up
// by unique_ptr destructors. The solver must be destroyed before
// the context it references, which is guaranteed by member
// destruction order (reverse of declaration order).

bool Z3SMTInterface::isSatisfiable(const std::string& formula) const {
    // Handle special cases
    if (formula == "true") return true;
    if (formula.empty() || formula == "false") return false;
    
    // Delegate to the set-based version
    return isSatisfiable(std::unordered_set<std::string>{formula});
}

bool Z3SMTInterface::isSatisfiable(const std::unordered_set<std::string>& formulas) const {
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
            z3::expr expr = parseToZ3Expression(formula);
            solver_->add(expr);

        }

        //std::cout << "Z3SMTInterface: " << *solver_ << "\n";
        // Check satisfiability
        bool result = (solver_->check() == z3::sat);

        // Pop the scope to clean up
        solver_->pop();
        
        return result;
        
    } catch (const std::exception& e) {
        // Make sure to pop even on exception
        try {
            solver_->pop();
        } catch (...) {
            // Ignore errors during cleanup
        }
        throw std::runtime_error(std::string("Z3 satisfiability check failed: ") + e.what());
    }
}

z3::expr Z3SMTInterface::parseToZ3Expression(const std::string& str) const {
    // Use the existing formula_utils parser
    return formula_utils::parseStringToZ3(str, *ctx_);
}

std::unique_ptr<SMTInterface> Z3SMTInterface::clone() const {
    // Create a new instance with its own Z3 context
    return std::make_unique<Z3SMTInterface>();
}

// Factory function implementation when using Z3
std::unique_ptr<SMTInterface> createDefaultSMTInterface() {
    return std::make_unique<Z3SMTInterface>();
}

#endif // USE_Z3

} // namespace ctl

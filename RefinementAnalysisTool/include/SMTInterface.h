#ifndef SMTINTERFACE_H
#define SMTINTERFACE_H

#include <string>
#include <unordered_set>
#include <memory>

namespace ctl {

/**
 * @brief Abstract interface for SMT solver operations
 * 
 * This interface abstracts away the specific SMT solver implementation (Z3, CVC5, etc.)
 * to allow for easy switching between different solvers. The primary use case is
 * checking satisfiability of boolean formulas represented as strings.
 */
class SMTInterface {
public:
    virtual ~SMTInterface() = default;

    /**
     * @brief Check if a single formula is satisfiable
     * @param formula The formula string to check
     * @return true if the formula is satisfiable, false otherwise
     */
    virtual bool isSatisfiable(const std::string& formula) const = 0;

    /**
     * @brief Check if a conjunction of formulas is satisfiable
     * @param formulas A set of formula strings to check (implicitly AND-ed together)
     * @return true if the conjunction is satisfiable, false otherwise
     */
    virtual bool isSatisfiable(const std::unordered_set<std::string>& formulas) const = 0;

    /**
     * @brief Create a clone of this SMT interface
     * @return A unique pointer to a new SMT interface instance
     */
    virtual std::unique_ptr<SMTInterface> clone() const = 0;
};

/**
 * @brief Factory function to create the default SMT interface implementation
 * @return A unique pointer to a new SMT interface instance
 */
std::unique_ptr<SMTInterface> createDefaultSMTInterface();

} // namespace ctl

#endif // SMTINTERFACE_H

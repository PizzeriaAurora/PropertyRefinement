#ifndef Z3SMTINTERFACE_H
#define Z3SMTINTERFACE_H

#include "../SMTInterface.h"
#include <z3++.h>
#include <memory>
#include <unordered_map>

namespace ctl {

/**
 * @brief Z3-based implementation of the SMT interface
 * 
 * This class uses the Z3 SMT solver to check formula satisfiability.
 * Each instance has its own Z3 context and solver, making it thread-safe
 * when each thread uses its own instance.
 */
class Z3SMTInterface : public SMTInterface {
public:
    Z3SMTInterface();
    ~Z3SMTInterface() override = default;

    // Non-copyable to avoid issues with Z3 context sharing
    Z3SMTInterface(const Z3SMTInterface&) = delete;
    Z3SMTInterface& operator=(const Z3SMTInterface&) = delete;

    // Movable
    Z3SMTInterface(Z3SMTInterface&&) noexcept = default;
    Z3SMTInterface& operator=(Z3SMTInterface&&) noexcept = default;

    bool isSatisfiable(const std::string& formula) const override;
    bool isSatisfiable(const std::unordered_set<std::string>& formulas) const override;
    
    std::unique_ptr<SMTInterface> clone() const override;

private:
    /**
     * @brief Parse a string formula into a Z3 expression
     * @param str The formula string
     * @return A Z3 expression
     */
    z3::expr parseToZ3Expression(const std::string& str) const;

    // Each instance has its own Z3 context and solver
    // This ensures thread safety when each thread uses its own Z3SMTInterface instance
    std::unique_ptr<z3::context> ctx_;
    mutable std::unique_ptr<z3::solver> solver_;
    
    // Optional: cache for parsed expressions (per instance)
    // Commented out for now to avoid potential issues, can be enabled if needed
    // mutable std::unordered_map<std::string, std::shared_ptr<z3::expr>> expr_cache_;
};

} // namespace ctl

#endif // Z3SMTINTERFACE_H

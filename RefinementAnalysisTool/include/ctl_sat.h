#pragma once

#include <string>
#include <vector>
#include <memory>


namespace ctl {

class CTLSATInterface {
private:
    std::string ctl_sat_path_;
    bool verbose_ = false;
    
public:
    explicit CTLSATInterface(const std::string& ctl_sat_path = "./extern/ctl-sat");
    
    // Check if formula is satisfiable
    bool isSatisfiable(const std::string& formula, bool with_clearing=false) const;

    // Check if formula1 refines formula2 (formula1 -> formula2)
    bool refines(const std::string& formula1, const std::string& formula2) const;
    bool implies(const std::string& formula1, const std::string& formula2) const;
    // Check if formula1 is equivalent to formula2
    bool equivalent(const std::string& formula1, const std::string& formula2) const;
    
    // Convert CTL formula to CTL-SAT syntax
    static std::string toCTLSATSyntax(const std::string& ctl_formula);
    
    // Run CTL-SAT with given formula and return output
    std::string runCTLSAT(const std::string& formula) const;

    void setVerbose(bool verbose) { verbose_ = verbose; }
};

} // namespace ctl
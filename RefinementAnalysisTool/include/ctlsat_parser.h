#ifndef CTLSAT_PARSER_H
#define CTLSAT_PARSER_H

#include <string>
#include <memory>
#include <unordered_map>
#include "formula.h"

namespace ctl {

/**
 * @brief Converts CTL formulas to CTLSAT solver format
 * 
 * This class provides functionality to convert CTL formulas from the internal
 * representation to the format expected by the CTLSAT solver:
 * https://github.com/nicolaprezza/CTLSAT
 * 
 * The CTLSAT format uses:
 * - 'v' for disjunction (OR)
 * - '^' for conjunction (AND)
 * - '~' for negation (NOT)
 * - '->' for implication
 * - Standard CTL operators: EF, AF, EG, AG, EU, AU, EW, AW
 * 
 * Comparisons are mapped to unique atomic propositions (p1, p2, p3, etc.)
 */
class CTLSATParser {
public:
    /**
     * @brief Convert a CTL formula to CTLSAT format string
     * @param formula The CTL formula to convert
     * @return String in CTLSAT format
     */
    static std::string toCtlSatFormat(const CTLFormula& formula);
    
    /**
     * @brief Convert a CTL formula string to CTLSAT format
     * 
     * This method parses a CTL formula string in standard notation and
     * converts it to CTLSAT format.
     * 
     * @param formula_str The CTL formula string (e.g., "AG(p & q)")
     * @return String in CTLSAT format (e.g., "AG(p^q)")
     */
    static std::string convertString(const std::string& formula_str);
    
    /**
     * @brief Get the mapping from comparison strings to atomic propositions
     * @return Map of comparison expressions to their assigned atoms (p1, p2, etc.)
     */
    static const std::unordered_map<std::string, std::string>& getComparisonMapping();
    
    /**
     * @brief Clear the comparison mapping (useful for starting fresh conversions)
     */
    static void clearComparisonMapping();

private:
    /**
     * @brief Internal recursive conversion function
     * @param formula The formula to convert
     * @return String representation in CTLSAT format
     */
    static std::string convertFormula(const CTLFormula& formula);
    
    /**
     * @brief Get or create an atom for a comparison expression
     * @param comparison The comparison expression as a string
     * @return The atomic proposition assigned to this comparison (e.g., "a")
     */
    static std::string getComparisonAtom(const std::string& comparison);
    
    /**
     * @brief Get or create a letter for an atomic proposition
     * @param atom The atomic proposition as a string
     * @return The single letter assigned to this atom (e.g., "a", "b", "c")
     */
    static std::string getAtomLetter(const std::string& atom);
    
    // Static members to track mappings
    static std::unordered_map<std::string, std::string> comparison_map_;
    static std::unordered_map<std::string, std::string> atom_map_;
    static int next_atom_id_;
};

} // namespace ctl

#endif // CTLSAT_PARSER_H

#pragma once

#include "formula.h"
#include "CTLautomaton.h"
#include <unordered_set>
#include <functional>

namespace ctl {

// Hash and equality for CTLFormulaPtr
struct CTLFormulaHash {
    size_t operator()(const CTLFormulaPtr& formula) const {
        return formula ? formula->hash() : 0;
    }
};

struct CTLFormulaEqual {
    bool operator()(const CTLFormulaPtr& a, const CTLFormulaPtr& b) const {
        if (!a && !b) return true;
        if (!a || !b) return false;
        return a->equals(*b);
    }
};

// Property class that wraps a CTL formula with caching and refinement checking
class CTLProperty {
private:
    CTLFormulaPtr formula_;
    mutable std::shared_ptr<CTLAutomaton> automaton_; // Lazy initialization
    mutable std::unordered_set<std::string> atomic_props_; // Cache
    mutable bool atomic_props_computed_ = false;
    
    // Static cache for parsed properties
    static std::unordered_map<std::string, std::shared_ptr<CTLProperty>> property_cache_;
    
    // Cache for refinement checks
    mutable std::unordered_map<std::shared_ptr<CTLProperty>, bool> refinement_cache_;
    
public:
    explicit CTLProperty(const std::string& formula_str);
    explicit CTLProperty(CTLFormulaPtr formula);
    ~CTLProperty() = default; // Let shared_ptr handle cleanup automatically
    
    // Factory method with caching
    static std::shared_ptr<CTLProperty> create(const std::string& formula_str);
    static std::shared_ptr<CTLProperty> create(CTLFormulaPtr formula);
    
    // Memory management
    static void clearStaticCaches();
    void clearInstanceCaches();
    
    // Getters
    const CTLFormula& getFormula() const { return *formula_; }
    const CTLFormulaPtr& getFormulaPtr() const { return formula_; }
    std::string toString() const { return formula_->toString(); }
    std::string toNuSMVString() const { return formula_->toNuSMVString(); }
    size_t size() const { 
        std::unordered_map<formula_utils::FormulaKey, const CTLFormula*, formula_utils::FormulaKeyHash> seen;
        std::vector<const CTLFormula*> topo;
        formula_utils::collectClosureDFS(*formula_, seen, topo);
        return topo.size(); 
    }
    
    // Atomic propositions (cached)
    const std::unordered_set<std::string>& getAtomicPropositions() const;
    
    // ABTA (lazy initialization)
    const CTLAutomaton& automaton() const;

    void simplify() const;
    bool isEmpty() const;
    
    
    // Refinement checking
    bool refines(const CTLProperty& other, bool use_syntactic = true, bool use_full_inclusion = false) const;
    bool refinesSyntactic(const CTLProperty& other) const;
    bool refinesSemantic(const CTLProperty& other, bool use_full_inclusion = false) const;
    
    // Equality and hashing
    bool equals(const CTLProperty& other) const;
    size_t hash() const;
    
    // Operators
    bool operator==(const CTLProperty& other) const { return equals(other); }
    bool operator!=(const CTLProperty& other) const { return !equals(other); }
    
private:
    // Syntactic refinement checking
    bool refinementCheck(const CTLFormula& f1, const CTLFormula& f2) const;
    bool refinementCheckAtomic(const CTLFormula& f1, const CTLFormula& f2) const;
    bool refinementCheckNegation(const NegationFormula& f1, const CTLFormula& f2) const;
    bool refinementCheckBinary(const BinaryFormula& f1, const CTLFormula& f2) const;
    bool refinementCheckTemporal(const TemporalFormula& f1, const CTLFormula& f2) const;
    
    // Helper for interval subsumption
    static bool intervalSubsumes(const TimeInterval& inner, const TimeInterval& outer);
    
    // Helper for temporal operator ordering
    static bool temporalOperatorRefines(TemporalOperator op1, TemporalOperator op2);
};

// Hash specialization for unordered containers
} // namespace ctl

// Custom hash and equality for CTLProperty shared_ptr
namespace std {
template<>
struct hash<ctl::CTLProperty> {
    size_t operator()(const ctl::CTLProperty& prop) const {
        return prop.hash();
    }
};
}
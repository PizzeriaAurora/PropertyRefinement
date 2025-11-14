#pragma once

#include <string>
#include <vector>
#include <memory>
#include <unordered_map>
#include <variant>
#include <iostream>
#include <limits>
#include "types.h"
namespace ctl {



// Abstract base class for CTL formulas
class CTLFormula {
public:
    virtual ~CTLFormula() = default;
    virtual std::string toString() const = 0;
    virtual std::string toNuSMVString() const = 0;
    virtual CTLFormulaPtr clone() const = 0;
    virtual bool equals(const CTLFormula& other) const = 0;
    virtual size_t hash() const = 0;
    
    // Visitor pattern for tree traversal
    virtual void accept(class CTLFormulaVisitor& visitor) const = 0;
    
    // Type checking
    virtual bool isAtomic() const { return false; }
    virtual bool isTemporal() const { return false; }
    virtual bool isBinary() const { return false; }
    virtual bool isUnary() const { return false; }

    virtual std::vector<CTLFormulaPtr> children() const = 0;
    virtual FormulaType getType() const = 0;

    
    
};

// Atomic proposition
class AtomicFormula : public CTLFormula {
public:
    std::string proposition;
    
    explicit AtomicFormula(const std::string& prop) : proposition(prop) {}

    std::string toString() const override { return "(" + proposition + ")"; }
    std::string toNuSMVString() const override { return "(" + proposition + ")"; }
    CTLFormulaPtr clone() const override { 
        return std::make_shared<AtomicFormula>(proposition); 
    }
    
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isAtomic() const override { return true; }
    FormulaType getType() const override { return FormulaType::ATOMIC; }
    std::vector<CTLFormulaPtr> children() const override { return {}; }
};

// Comparison formula (for arithmetic)
class ComparisonFormula : public CTLFormula {
public:
    std::string variable;
    std::string operator_;
    std::string value;
    
    ComparisonFormula(const std::string& var, const std::string& op, const std::string& val)
        : variable(var), operator_(op), value(val) {
        }
    
    std::string toString() const override { 
        return variable + " " + operator_ + " " + value; 
    }
    
    std::string toNuSMVString() const override { 
        return variable + " " + operator_ + " " + value; 
    }
    
    CTLFormulaPtr clone() const override {
        return std::make_shared<ComparisonFormula>(variable, operator_, value);
    }
    
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isAtomic() const override { return true; }
    FormulaType getType() const override { return FormulaType::COMPARISON; }
    std::vector<CTLFormulaPtr> children() const override { return {}; }
};

// Boolean literals
class BooleanLiteral : public CTLFormula {
public:
    bool value;
    
    explicit BooleanLiteral(bool val) : value(val) {}
    
    std::string toString() const override { return value ? "true" : "false"; }
    std::string toNuSMVString() const override { return value ? "TRUE" : "FALSE"; }
    CTLFormulaPtr clone() const override { 
        return std::make_shared<BooleanLiteral>(value); 
    }
    
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isAtomic() const override { return true; }
    FormulaType getType() const override { return FormulaType::BOOLEAN_LITERAL; }
    std::vector<CTLFormulaPtr> children() const override { return {}; }
};

// Negation
class NegationFormula : public CTLFormula {
public:
    CTLFormulaPtr operand;
    
    explicit NegationFormula(CTLFormulaPtr op) : operand(std::move(op)) {}
    
    std::string toString() const override;
    std::string toNuSMVString() const override;
    CTLFormulaPtr clone() const override;
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isUnary() const override { return true; }
    FormulaType getType() const override { return FormulaType::NEGATION; }
    std::vector<CTLFormulaPtr> children() const override { return { operand }; }
    
    

private:
};



class BinaryFormula : public CTLFormula {
public:
    CTLFormulaPtr left;
    CTLFormulaPtr right;
    BinaryOperator operator_;
    
    BinaryFormula(CTLFormulaPtr l, BinaryOperator op, CTLFormulaPtr r)
        : left(std::move(l)), operator_(op), right(std::move(r)) {}
    
    std::string toString() const override;
    std::string toNuSMVString() const override;
    CTLFormulaPtr clone() const override;
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isBinary() const override { return true; }
    FormulaType getType() const override { return FormulaType::BINARY; }
    std::vector<CTLFormulaPtr> children() const override { return { left, right }; }
    
private:
    std::string operatorToString() const;
    std::string operatorToNuSMVString() const;
};



class TemporalFormula : public CTLFormula {
public:
    TemporalOperator operator_;
    TimeInterval interval;
    CTLFormulaPtr operand;
    CTLFormulaPtr second_operand; // for binary temporal operators (U, W)
    
    // Unary temporal constructor
    TemporalFormula(TemporalOperator op, CTLFormulaPtr operand_)
        : operator_(op), operand(std::move(operand_)) {}
    
    // Unary temporal with time interval constructor
    TemporalFormula(TemporalOperator op, const TimeInterval& interval_, CTLFormulaPtr operand_)
        : operator_(op), interval(interval_), operand(std::move(operand_)) {}
    
    // Binary temporal constructor
    TemporalFormula(TemporalOperator op, CTLFormulaPtr first, CTLFormulaPtr second)
        : operator_(op), operand(std::move(first)), second_operand(std::move(second)) {}
    
    std::string toString() const override;
    std::string toNuSMVString() const override;
    CTLFormulaPtr clone() const override;
    bool equals(const CTLFormula& other) const override;
    size_t hash() const override;
    void accept(class CTLFormulaVisitor& visitor) const override;
    bool isTemporal() const override { return true; }
    bool isBinary() const override { return second_operand != nullptr; }
    bool isUnary() const override { return second_operand == nullptr; }
    
    bool givesUniversalTransition() const {
        return operator_ ==  TemporalOperator::AU_TILDE || operator_ == TemporalOperator::AX ||  operator_ == TemporalOperator::AU ;
        
                //operator_ == TemporalOperator::AF || operator_ == TemporalOperator::AG ||
               //operator_ == TemporalOperator::AU || operator_ == TemporalOperator::AW ||
               //operator_ == TemporalOperator::AX || operator_ == TemporalOperator::AU_TILDE;
    }
    
    bool givesExistensialTransition() const {
        return operator_ == TemporalOperator::EU || operator_ == TemporalOperator::EX || operator_ == TemporalOperator::EU_TILDE ;
        
                //operator_ == TemporalOperator::EF || operator_ == TemporalOperator::EG ||
               //operator_ == TemporalOperator::EU || operator_ == TemporalOperator::EW ||
               //operator_ == TemporalOperator::EX || operator_ == TemporalOperator::EU_TILDE;
    }

    FormulaType getType() const override { return FormulaType::TEMPORAL; }
    std::vector<CTLFormulaPtr> children() const override {
        if (isBinary()) {
            return { operand, second_operand };
        } else {
            return { operand };
        }
    }
    
private:
    std::string operatorToString() const;
    std::string operatorToNuSMVString() const;
};













} // namespace ctl


/*

nohup ./check_refinements ./assets/benchmark/Dataset/Properties/2019/ -o results_simulation_RCTLC_s/2024 --verbose > logs/log_2024_simulation_s_luca_manual.log 2>&1 &

 ./run_benchmarks.sh ./assets/benchmark/Dataset/Properties language_inclusion serial no_transitive_optimization  

*/
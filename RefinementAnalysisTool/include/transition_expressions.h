#pragma once

#include <string>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace ctl {
    
// Transition expression types for ABTA
class TransitionExpr {
public:
    virtual ~TransitionExpr() = default;
    virtual std::string toString() const = 0;
    
    virtual std::shared_ptr<TransitionExpr> clone() const = 0;
    virtual bool equals(const TransitionExpr& other) const = 0;
    virtual size_t hash() const = 0;
    virtual std::vector<std::shared_ptr<TransitionExpr>> children() const = 0;

};
using TransitionExprPtr = std::shared_ptr<TransitionExpr>;


// True expression
class TrueExpr : public TransitionExpr {
public:
    std::string toString() const override { return "true"; }
    TransitionExprPtr clone() const override { return std::make_shared<TrueExpr>(); }
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override { return std::hash<std::string>{}("true"); }
    std::vector<TransitionExprPtr> children() const override { return {}; }
};

// False expression
class FalseExpr : public TransitionExpr {
public:
    std::string toString() const override { return "false"; }
    TransitionExprPtr clone() const override { return std::make_shared<FalseExpr>(); }
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override { return std::hash<std::string>{}("false"); }
    std::vector<TransitionExprPtr> children() const override { return {}; }
};

// Atomic expression
class AtomicTransitionExpr : public TransitionExpr {
public:
    std::string symbol;
    
    explicit AtomicTransitionExpr(const std::string& sym) : symbol(sym) {}
    
    std::string toString() const override { return symbol; }
    TransitionExprPtr clone() const override { 
        return std::make_shared<AtomicTransitionExpr>(symbol); 
    }
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override { return std::hash<std::string>{}(symbol); }
    std::vector<TransitionExprPtr> children() const override { return {}; }
};

// And expression
class AndTransitionExpr : public TransitionExpr {
public:
    TransitionExprPtr left;
    TransitionExprPtr right;
    
    AndTransitionExpr(TransitionExprPtr l, TransitionExprPtr r) 
        : left(std::move(l)), right(std::move(r)) {}
    
    std::string toString() const override;
    TransitionExprPtr clone() const override;
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override;
    std::vector<TransitionExprPtr> children() const override { return {left, right}; }
};

// Or expression
class OrTransitionExpr : public TransitionExpr {
public:
    TransitionExprPtr left;
    TransitionExprPtr right;
    
    OrTransitionExpr(TransitionExprPtr l, TransitionExprPtr r) 
        : left(std::move(l)), right(std::move(r)) {}
    
    std::string toString() const override;
    TransitionExprPtr clone() const override;
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override;
    std::vector<TransitionExprPtr> children() const override { return {left, right}; }
};

// Not expression
class NotTransitionExpr : public TransitionExpr {
public:
    TransitionExprPtr expr;
    
    explicit NotTransitionExpr(TransitionExprPtr e) : expr(std::move(e)) {}
    
    std::string toString() const override;
    TransitionExprPtr clone() const override;
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override;
    std::vector<TransitionExprPtr> children() const override { return {expr}; }
};

// Next expression (for tree automata)
class NextTransitionExpr : public TransitionExpr {
public:
    std::string direction;
    std::string state;
    
    NextTransitionExpr(const std::string& dir, const std::string& st) 
        : direction(dir), state(st) {}
    
    std::string toString() const override;
    TransitionExprPtr clone() const override;
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override;
    std::vector<TransitionExprPtr> children() const override { return {}; }
};

// State expression (reference to another state)
// State expression (reference to another state's transition logic)
class StateExpr : public TransitionExpr {
public:
    std::string state;
    
    explicit StateExpr(const std::string& st) : state(st) {}
    
    std::string toString() const override { return state; }
    TransitionExprPtr clone() const override { 
        return std::make_shared<StateExpr>(state); 
    }
    bool equals(const TransitionExpr& other) const override;
    size_t hash() const override { return std::hash<std::string>{}(state); }
    std::vector<TransitionExprPtr> children() const override { return {}; }
};
}
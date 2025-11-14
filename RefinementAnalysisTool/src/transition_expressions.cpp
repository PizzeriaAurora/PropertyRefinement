
#include "transition_expressions.h"

using namespace ctl;
// TransitionExpr implementations
bool TrueExpr::equals(const TransitionExpr& other) const {
    return dynamic_cast<const TrueExpr*>(&other) != nullptr;
}

bool FalseExpr::equals(const TransitionExpr& other) const {
    return dynamic_cast<const FalseExpr*>(&other) != nullptr;
}

bool AtomicTransitionExpr::equals(const TransitionExpr& other) const {
    if (auto atomic = dynamic_cast<const AtomicTransitionExpr*>(&other)) {
        return symbol == atomic->symbol;
    }
    return false;
}

std::string AndTransitionExpr::toString() const {
    return "(" + left->toString() + " & " + right->toString() + ")";
}

TransitionExprPtr AndTransitionExpr::clone() const {
    return std::make_shared<AndTransitionExpr>(left->clone(), right->clone());
}

bool AndTransitionExpr::equals(const TransitionExpr& other) const {
    if (auto and_expr = dynamic_cast<const AndTransitionExpr*>(&other)) {
        return left->equals(*and_expr->left) && right->equals(*and_expr->right);
    }
    return false;
}

size_t AndTransitionExpr::hash() const {
    return std::hash<std::string>{}("and") ^ (left->hash() << 1) ^ (right->hash() << 2);
}

std::string OrTransitionExpr::toString() const {
    return "(" + left->toString() + " | " + right->toString() + ")";
}

TransitionExprPtr OrTransitionExpr::clone() const {
    return std::make_shared<OrTransitionExpr>(left->clone(), right->clone());
}

bool OrTransitionExpr::equals(const TransitionExpr& other) const {
    if (auto or_expr = dynamic_cast<const OrTransitionExpr*>(&other)) {
        return left->equals(*or_expr->left) && right->equals(*or_expr->right);
    }
    return false;
}

size_t OrTransitionExpr::hash() const {
    return std::hash<std::string>{}("or") ^ (left->hash() << 1) ^ (right->hash() << 2);
}

std::string NotTransitionExpr::toString() const {
    return "!" + expr->toString();
}

TransitionExprPtr NotTransitionExpr::clone() const {
    return std::make_shared<NotTransitionExpr>(expr->clone());
}

bool NotTransitionExpr::equals(const TransitionExpr& other) const {
    if (auto not_expr = dynamic_cast<const NotTransitionExpr*>(&other)) {
        return expr->equals(*not_expr->expr);
    }
    return false;
}

size_t NotTransitionExpr::hash() const {
    return std::hash<std::string>{}("not") ^ (expr->hash() << 1);
}

std::string NextTransitionExpr::toString() const {
    return "next(" + direction + ", " + state + ")";
}

TransitionExprPtr NextTransitionExpr::clone() const {
    return std::make_shared<NextTransitionExpr>(direction, state);
}

bool NextTransitionExpr::equals(const TransitionExpr& other) const {
    if (auto next_expr = dynamic_cast<const NextTransitionExpr*>(&other)) {
        return direction == next_expr->direction && state == next_expr->state;
    }
    return false;
}

size_t NextTransitionExpr::hash() const {
    return std::hash<std::string>{}("next") ^ 
           std::hash<std::string>{}(direction) ^ 
           std::hash<std::string>{}(state);
}

bool StateExpr::equals(const TransitionExpr& other) const {
    if (auto state_expr = dynamic_cast<const StateExpr*>(&other)) {
        return state == state_expr->state;
    }
    return false;
}
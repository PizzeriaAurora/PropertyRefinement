
#include "formula_utils.h"
#include "visitors.h"
// Utility functions implementation
namespace ctl::formula_utils {

CTLFormulaPtr toNNF(const CTLFormula& formula) {
    return NNFConverterVisitor::convert(formula);
}

bool structurallyEqual(const CTLFormula& f1, const CTLFormula& f2) {
    return f1.equals(f2);
}

size_t computeHash(const CTLFormula& formula) {
    return formula.hash();
}



std::unordered_set<std::string> collectAtomicPropositions(const CTLFormula& formula) {
    AtomCollectorVisitor visitor;
    formula.accept(visitor);
    return visitor.getAtoms();
}

std::unordered_set<std::string> getAtomicForAnalysis(const CTLFormula& formula) {
    std::unordered_set<std::string> atoms;
    
    // Recursive function to collect atomic propositions with full representation
    std::function<void(const CTLFormula&)> collect = [&](const CTLFormula& f) {
        // Atomic proposition (simple variable)
        if (auto atom = dynamic_cast<const AtomicFormula*>(&f)) {
            atoms.insert(atom->proposition);
            return;
        }
        
        // Comparison formula - this is what we want to capture!
        // Returns the full comparison like "60<=Weight_Right_Wheel"
        if (auto comp = dynamic_cast<const ComparisonFormula*>(&f)) {
            atoms.insert(comp->toString());
            return;
        }
        
        // Boolean literal
        if (dynamic_cast<const BooleanLiteral*>(&f)) {
            return; // Don't count true/false as atoms
        }
        
        // Negation - only recurse if it's negating an atom or comparison
        if (auto neg = dynamic_cast<const NegationFormula*>(&f)) {
            // Check if we're negating an atomic or comparison
            if (dynamic_cast<const AtomicFormula*>(neg->operand.get()) ||
                dynamic_cast<const ComparisonFormula*>(neg->operand.get())) {
                // Include the negation as part of the atom representation
                atoms.insert("!" + neg->operand->toString());
            } else {
                collect(*neg->operand);
            }
            return;
        }
        
        // Binary formula (AND, OR, IMPLIES, etc.)
        if (auto binary = dynamic_cast<const BinaryFormula*>(&f)) {
            // Check if this is a boolean combination at the atomic level
            // If both sides are atomic/comparison and connected by boolean ops,
            // this might be a complex atomic proposition
            bool left_is_atomic = (dynamic_cast<const AtomicFormula*>(binary->left.get()) != nullptr ||
                                  dynamic_cast<const ComparisonFormula*>(binary->left.get()) != nullptr);
            bool right_is_atomic = (dynamic_cast<const AtomicFormula*>(binary->right.get()) != nullptr ||
                                   dynamic_cast<const ComparisonFormula*>(binary->right.get()) != nullptr);
            
            // If it's a boolean combination of atomic propositions, treat as complex atom
            if (left_is_atomic && right_is_atomic && 
                (binary->operator_ == BinaryOperator::AND || 
                 binary->operator_ == BinaryOperator::OR)) {
                atoms.insert(f.toString());
            } else {
                // Otherwise recurse into both sides
                collect(*binary->left);
                collect(*binary->right);
            }
            return;
        }
        
        // Temporal formula - recurse into operands but don't include temporal ops
        if (auto temp = dynamic_cast<const TemporalFormula*>(&f)) {
            if (temp->operand) {
                collect(*temp->operand);
            }
            if (temp->second_operand) {
                collect(*temp->second_operand);
            }
            return;
        }
    };
    
    collect(formula);
    return atoms;
}


CTLFormulaPtr Conjunction(const CTLFormulaPtr& lhs, const CTLFormulaPtr& rhs) {
    //return  a formula representing the conjunction of this and other
    return std::make_shared<BinaryFormula>(lhs->clone(), BinaryOperator::AND, rhs->clone());
}

bool isPurelyPropositional(const CTLFormula& formula) {
    if (dynamic_cast<const AtomicFormula*>(&formula) ||
        dynamic_cast<const ComparisonFormula*>(&formula) ||
        dynamic_cast<const BooleanLiteral*>(&formula)) {
        return true;
    }
    
    if (auto negation = dynamic_cast<const NegationFormula*>(&formula)) {
        return isPurelyPropositional(*negation->operand);
    }
    
    if (auto binary = dynamic_cast<const BinaryFormula*>(&formula)) {
        bool left = isPurelyPropositional(*binary->left);
        bool right = isPurelyPropositional(*binary->right);
        return left && right;
    }
    
    if (dynamic_cast<const TemporalFormula*>(&formula)) {
        return false;
    }
    
    return false;
}



  // ---------- core-operator normalisation ----------
std::unique_ptr<CTLFormula> normalizeToCore(const CTLFormula& f) {
    // We assume NNF has already been applied outside (no ¬ over non-atom).
    if (auto b = dynamic_cast<const BooleanLiteral*>(&f)) {
        return std::make_unique<BooleanLiteral>(b->value);
    }
    if (auto a = dynamic_cast<const AtomicFormula*>(&f)) {
        return std::make_unique<AtomicFormula>(a->proposition);
    }
    if (auto n = dynamic_cast<const NegationFormula*>(&f)) {
        // Only ¬p allowed in NNF.
        return std::make_unique<NegationFormula>(n->operand->clone());
    }
    if (auto c = dynamic_cast<const ComparisonFormula*>(&f))
    {
        return std::make_unique<AtomicFormula>(c->toString());
    }
    
    if (auto bin = dynamic_cast<const BinaryFormula*>(&f)) {
        auto L = normalizeToCore(*bin->left);
        auto R = normalizeToCore(*bin->right);
        return std::make_unique<BinaryFormula>(std::move(L), bin->operator_,std::move(R));
    }
    if (auto t = dynamic_cast<const TemporalFormula*>(&f)) {
        using Op = TemporalOperator;
        switch (t->operator_) {
            case Op::AX:
            case Op::EX: {
                auto sub = normalizeToCore(*t->operand);
                return std::make_unique<TemporalFormula>(t->operator_, std::move(sub));
            }

            // EF φ  ≡  E(true U φ)
            case Op::EF: {
                auto phi  = normalizeToCore(*t->operand);
                auto tru  = std::make_unique<BooleanLiteral>(true);
                return std::make_unique<TemporalFormula>(Op::EU, std::move(tru), std::move(phi));
            }
            // AF φ  ≡  A(true U φ)
            case Op::AF: {
                auto phi  = normalizeToCore(*t->operand);
                auto tru  = std::make_unique<BooleanLiteral>(true);
                return std::make_unique<TemporalFormula>(Op::AU, std::move(tru), std::move(phi));
            }
            // EG φ  ≡  E(false Ũ φ)
            case Op::EG: {
                auto phi  = normalizeToCore(*t->operand);
                auto fls  = std::make_unique<BooleanLiteral>(false);
                return std::make_unique<TemporalFormula>(Op::EU_TILDE, std::move(fls), std::move(phi));
            }
            // AG φ  ≡  A(false Ũ φ)
            case Op::AG: {
                auto phi  = normalizeToCore(*t->operand);
                auto fls  = std::make_unique<BooleanLiteral>(false);
                return std::make_unique<TemporalFormula>(Op::AU_TILDE, std::move(fls), std::move(phi));
            }
            // EW(φ,ψ) ≡ EU(φ,ψ) ∨ EG φ  ≡ EU(φ,ψ) ∨ EŨ(false,φ)
            case Op::EW: {
                auto L_eu = std::make_unique<TemporalFormula>(Op::EU,
                              normalizeToCore(*t->operand),
                              normalizeToCore(*t->second_operand));
                //auto eg   = std::make_unique<TemporalFormula>(Op::EG,
                //              normalizeToCore(*t->operand));
                auto normalized_eg = std::make_unique<TemporalFormula>(Op::EU_TILDE,
                                      std::make_unique<BooleanLiteral>(false),
                                      normalizeToCore(*t->operand));
                return std::make_unique<BinaryFormula>(std::move(L_eu), BinaryOperator::OR, std::move(normalized_eg));
            }
            // AW(φ,ψ) ≡ AU(φ,ψ) ∨ AG φ  ≡ AU(φ,ψ) ∨ AŨ(false,φ)
            case Op::AW: {
                auto L_au = std::make_unique<TemporalFormula>(Op::AU,
                              normalizeToCore(*t->operand),
                              normalizeToCore(*t->second_operand));
                //auto ag   = std::make_unique<TemporalFormula>(Op::AG,
                //              normalizeToCore(*t->operand));
                auto normalized_ag = std::make_unique<TemporalFormula>(Op::AU_TILDE,
                                      std::make_unique<BooleanLiteral>(false),
                                      normalizeToCore(*t->operand));
                return std::make_unique<BinaryFormula>(std::move(L_au), BinaryOperator::OR, std::move(normalized_ag));
            }

            // Already core 2-ary temporal operators:
            case Op::EU:
            case Op::AU:
            case Op::EU_TILDE:
            case Op::AU_TILDE: {
                auto L = normalizeToCore(*t->operand);
                auto R = normalizeToCore(*t->second_operand);
                return std::make_unique<TemporalFormula>(t->operator_, std::move(L), std::move(R));
            }
            default:
                throw std::runtime_error("Unsupported temporal operator in normalizeToCore: " + f.toString());
        }
    }
    throw std::runtime_error("Unknown formula node in normalizeToCore: " + f.toString());
}

// ---------- collect closure cl(φ) (state subformulas) ----------
void collectClosureDFS(
    const CTLFormula& f,
    std::unordered_map<FormulaKey, const CTLFormula*, FormulaKeyHash>& seen,
    std::vector<const CTLFormula*>& outTopo
) {
    FormulaKey k{f};
    if (seen.count(k)) return;
    // Recurse first to maintain a topological (constituents-first) order

    if(f.getType() == FormulaType::BOOLEAN_LITERAL) 
    {
        seen.emplace(k, &f);
        return;
    }

    if (auto bin = dynamic_cast<const BinaryFormula*>(&f)) {
        collectClosureDFS(*bin->left,  seen, outTopo);
        collectClosureDFS(*bin->right, seen, outTopo);
    } else if (auto t = dynamic_cast<const TemporalFormula*>(&f)) {
        collectClosureDFS(*t->operand, seen, outTopo);
        if (t->second_operand) collectClosureDFS(*t->second_operand, seen, outTopo);
    } else if (auto n = dynamic_cast<const NegationFormula*>(&f)) {
        if(n->operand->getType() == FormulaType::BOOLEAN_LITERAL){
            seen.emplace(k, &f);
            return;
        }
        collectClosureDFS(*n->operand, seen, outTopo);
        
    }
    // Now add this formula itself (state subformula)
    seen.emplace(k, &f);
    outTopo.push_back(&f);
}


#ifdef USE_Z3

z3::expr parseStringToZ3(const std::string_view& str, z3::context& ctx, bool as_bool)
{
    return parseStringToZ3(std::string(str), ctx, as_bool);
}


z3::expr parseStringToZ3(const std::string& str, z3::context& ctx, bool as_bool) {
    // Parse a string into a Z3 boolean/int expression.
    // Handles: literals, negation, conjunction, disjunction, implication, equivalence, and comparisons.

    auto trim = [](const std::string& s) -> std::string {
        std::string result;
        for (char c : s) {
            if (!std::isspace(static_cast<unsigned char>(c))) result += c;
        }
        return result;
    };

    std::string trimmed = trim(str);
    if (trimmed.empty()) throw std::runtime_error("Empty formula");

    // Boolean literals
    

    // Remove outer parentheses if they enclose the whole expression
    while (trimmed.front() == '(' && trimmed.back() == ')') {
        int depth = 0;
        bool encloses_all = true;
        for (size_t i = 0; i < trimmed.size(); ++i) {
            if (trimmed[i] == '(') depth++;
            else if (trimmed[i] == ')') depth--;
            if (depth == 0 && i < trimmed.size() - 1) { encloses_all = false; break; }
        }
        if (!encloses_all) break;
        trimmed = trim(trimmed.substr(1, trimmed.size() - 2));
    }
    if (as_bool) {
        if (trimmed == "true" || trimmed == "1")  return ctx.bool_val(true);
        if (trimmed == "false" || trimmed == "0") return ctx.bool_val(false);
    }
    

    // Operator detection
    int paren_depth = 0;
    int imp_pos = -1, eqv_pos = -1, or_pos = -1, and_pos = -1, cmp_pos = -1;
    std::string cmp_op;

    for (size_t i = 0; i < trimmed.size(); ++i) {
        char c = trimmed[i];
        if (c == '(') paren_depth++;
        else if (c == ')') paren_depth--;
        else if (paren_depth == 0) {
            // Skip comparison sequences while scanning for logical operators
            if (i + 1 < trimmed.size()) {
                std::string sub = trimmed.substr(i, 2);
                if (sub == "<=" || sub == ">=" || sub == "==" || sub == "!=") { i++; continue; }
            }
            if (c == '<' || c == '>') continue; // skip single comparison ops

            // Implication / Equivalence
            if (i + 1 < trimmed.size() && (trimmed.substr(i, 2) == "=>" || trimmed.substr(i, 2) == "->")) imp_pos = i;
            else if (i + 2 < trimmed.size() && trimmed.substr(i, 3) == "<=>") eqv_pos = i;
            else if (c == '|') or_pos = i;
            else if (c == '&') and_pos = i;
        }
    }

    // Precedence: implication lowest
    if (imp_pos != -1) {
        std::string left = trim(trimmed.substr(0, imp_pos));
        std::string right = trim(trimmed.substr(imp_pos + 2));
        return z3::implies(parseStringToZ3(left, ctx, true), parseStringToZ3(right, ctx, true));
    }

    // Equivalence
    if (eqv_pos != -1) {
        std::string left = trim(trimmed.substr(0, eqv_pos));
        std::string right = trim(trimmed.substr(eqv_pos + 3));
        return parseStringToZ3(left, ctx, true) == parseStringToZ3(right, ctx, true);
    }

    // OR
    if (or_pos != -1) {
        std::string left = trim(trimmed.substr(0, or_pos));
        std::string right = trim(trimmed.substr(or_pos + 1));
        return parseStringToZ3(left, ctx, true) || parseStringToZ3(right, ctx, true);
    }

    // AND
    if (and_pos != -1) {
        std::string left = trim(trimmed.substr(0, and_pos));
        std::string right = trim(trimmed.substr(and_pos + 1));
        auto expr= parseStringToZ3(left, ctx, true) && parseStringToZ3(right, ctx, true);
        return expr;
    }

    // Negation
    if (trimmed.front() == '!') {
        return !parseStringToZ3(trim(trimmed.substr(1)), ctx, true);
    }

    // --- Comparison detection ---
    paren_depth = 0;
    for (size_t i = 0; i < trimmed.size(); ++i) {
        char c = trimmed[i];
        if (c == '(') paren_depth++;
        else if (c == ')') paren_depth--;
        else if (paren_depth == 0) {
            if (i + 1 < trimmed.size()) {
                std::string sub = trimmed.substr(i, 2);
                if (sub == "<=" || sub == ">=" || sub == "==" || sub == "!=") {
                    cmp_pos = i; cmp_op = sub; break;
                }
            }
            if (c == '<' || c == '>') { cmp_pos = i; cmp_op = std::string(1, c); break; }
        }
    }

    if (cmp_pos != -1) {
        std::string left = trim(trimmed.substr(0, cmp_pos));
        std::string right = trim(trimmed.substr(cmp_pos + cmp_op.size()));

        // Parse operands numerically
        z3::expr lhs = parseStringToZ3(left, ctx, false);
        z3::expr rhs = parseStringToZ3(right, ctx, false);


        if (cmp_op == "==") return lhs == rhs;
        if (cmp_op == "!=") return lhs != rhs;
        if (cmp_op == "<")  return lhs < rhs;
        if (cmp_op == "<=") return lhs <= rhs;
        if (cmp_op == ">")  return lhs > rhs;
        if (cmp_op == ">=") return lhs >= rhs;
    }

    // --- Atomic term (variable or numeric literal) ---
    for (char ch : trimmed) {
        if (!std::isalnum(static_cast<unsigned char>(ch)) && ch != '_' && ch != '-' && ch != '.') {
            throw std::runtime_error("Invalid character in atomic formula: " + trimmed);
        }
    }

    // Numeric constant?
    if (!as_bool && (std::isdigit(trimmed[0]) ||
        ((trimmed[0] == '-' || trimmed[0] == '+') && trimmed.size() > 1 && std::isdigit(trimmed[1])))) {
        return ctx.int_val(std::stoi(trimmed));
    }

    // Variable or Boolean atom
    if (as_bool) return ctx.bool_const(trimmed.c_str());
    else         return ctx.int_const(trimmed.c_str());
}

#endif // USE_Z3


SCCAcceptanceType getBlockAcceptanceTypeFromFormula(const CTLFormulaPtr& formula){
    if(!formula){
        return SCCAcceptanceType::UNDEFINED;
    }
    if (formula->isTemporal()) {
        auto temp = std::dynamic_pointer_cast<TemporalFormula>(formula);
        if (temp) {
            return isGreatestFixpointBlock(formula) ? SCCAcceptanceType::GREATEST : SCCAcceptanceType::LEAST;
        }
    }
    return SCCAcceptanceType::SIMPLE;
}


bool isGreatestFixpointBlock(const CTLFormulaPtr& formula){
    if (formula->isTemporal()) {
        auto temp = std::dynamic_pointer_cast<TemporalFormula>(formula);
        if (temp) {
            switch (temp->operator_) {
                case TemporalOperator::EU_TILDE:
                case TemporalOperator::AU_TILDE:
                    return true;
                default:
                    return false;
            }
        }
    }
    return false;
}


bool isLeastFixpointBlock(const CTLFormulaPtr& formula){
    if (formula->isTemporal()) {
        auto temp = std::dynamic_pointer_cast<TemporalFormula>(formula);
        if (temp) {
            switch (temp->operator_) {
                case TemporalOperator::EU:
                case TemporalOperator::AU:
                    return true;
                default:
                    return false;
            }
        }
    }
    return false;
}



bool isExistentialBlock(const CTLFormulaPtr& formula){
    if (formula->isTemporal()) {
        auto temp = std::dynamic_pointer_cast<TemporalFormula>(formula);
        return temp->givesExistensialTransition();
    }
    //if (formula->isBinary()) {
    //    auto bin = std::dynamic_pointer_cast<BinaryFormula>(formula);
    //    if(bin->operator_ == BinaryOperator::OR)
    //        return true;
    //}
    return false;
}


bool isUniversalBlock(const CTLFormulaPtr& formula){
    if (formula->isTemporal()) {
        auto temp = std::dynamic_pointer_cast<TemporalFormula>(formula);
        if (temp) {
            return temp->givesUniversalTransition();
        }
    }
    //if (formula->isBinary()) {
    //    auto bin = std::dynamic_pointer_cast<BinaryFormula>(formula);
    //    if(bin->operator_ == BinaryOperator::AND)
    //        return true;
    //}
    return false;
}

SCCBlockType getSCCBlockTypeFromFormula(const CTLFormulaPtr& formula){
    if(isExistentialBlock(formula)){
        return SCCBlockType::EXISTENTIAL;
    }
    if(isUniversalBlock(formula)){
        return SCCBlockType::UNIVERSAL;
    }
    return SCCBlockType::SIMPLE;
}


#ifdef USE_Z3

z3::expr conjToZ3Expr(const Conj& conj, z3::context& ctx) {
    z3::expr result = ctx.bool_val(true);
    for (const auto& atom : conj.atoms) {
        z3::expr atom_expr = ctx.bool_const(atom.qnext.data());
        result = result && atom_expr;
    }
    return result;
}
z3::expr disjToZ3Expr(const std::vector<Conj>& disj, z3::context& ctx) {
    z3::expr result = ctx.bool_val(false);
    for (const auto& conj : disj) {
        z3::expr conj_expr = conjToZ3Expr(conj, ctx);
        result = result || conj_expr;
    }
    return result;
}

#endif // USE_Z3



CTLFormulaPtr preprocessFormula(const CTLFormula& formula)
{
    auto bin  = BinaryToAtomVisitor::convert(formula);
    auto nnf  = formula_utils::toNNF(*bin);
    auto core = formula_utils::normalizeToCore(*nnf);
    return core;
}



CTLFormulaPtr negateFormula(const CTLFormula& formula)
{
    // Negate the formula and convert to NNF and core normal form.
    NegationFormula neg(formula.clone());
    auto bin  = BinaryToAtomVisitor::convert(neg);
    auto nnf  = formula_utils::toNNF(*bin);
    auto core = formula_utils::normalizeToCore(*nnf);
    return core;
}


#ifdef USE_CVC5

cvc5::Term parseStringToCVC5(const std::string_view& str, cvc5::Solver& solver, bool as_bool)
{
    return parseStringToCVC5(std::string(str), solver, as_bool);
}



cvc5::Term parseStringToCVC5(const std::string& str, cvc5::Solver& solver, bool as_bool)
{
    auto trim = [](const std::string& s) -> std::string {
        std::string result;
        result.reserve(s.size());
        for (char c : s)
            if (!std::isspace(static_cast<unsigned char>(c)))
                result += c;
        return result;
    };

    std::string trimmed = trim(str);
    if (trimmed.empty())
        throw std::runtime_error("Empty formula");

    // --- Strip outer parentheses if they enclose the whole expression ---
    while (trimmed.size() >= 2 && trimmed.front() == '(' && trimmed.back() == ')') {
        int depth = 0;
        bool encloses_all = true;
        for (size_t i = 0; i < trimmed.size(); ++i) {
            if (trimmed[i] == '(') ++depth;
            else if (trimmed[i] == ')') --depth;
            if (depth == 0 && i < trimmed.size() - 1) { encloses_all = false; break; }
        }
        if (!encloses_all) break;
        trimmed = trim(trimmed.substr(1, trimmed.size() - 2));
    }

    // --- Boolean constants ---
    if (as_bool) {
        if (trimmed == "true" || trimmed == "1")  return solver.mkTrue();
        if (trimmed == "false" || trimmed == "0") return solver.mkFalse();
    }

    // --- Operator detection (lowest precedence first) ---
    int paren_depth = 0;
    int imp_pos = -1, eqv_pos = -1, or_pos = -1, and_pos = -1, cmp_pos = -1;
    std::string cmp_op;

    for (size_t i = 0; i < trimmed.size(); ++i) {
        char c = trimmed[i];
        if (c == '(') { ++paren_depth; continue; }
        if (c == ')') { --paren_depth; continue; }
        if (paren_depth != 0) continue;

        // Implication / equivalence / and / or operators
        if (i + 2 <= trimmed.size() && trimmed.substr(i, 3) == "<=>") eqv_pos = i;
        else if (i + 1 < trimmed.size() && trimmed.substr(i, 2) == "=>") imp_pos = i;
        else if (c == '|') or_pos = i;
        else if (c == '&') and_pos = i;
    }

    // --- Logical connectives (in increasing precedence) ---
    if (imp_pos != -1) {
        std::string left = trimmed.substr(0, imp_pos);
        std::string right = trimmed.substr(imp_pos + 2);
        auto lhs = parseStringToCVC5(left, solver, true);
        auto rhs = parseStringToCVC5(right, solver, true);
        return solver.mkTerm(cvc5::Kind::IMPLIES, {lhs, rhs});
    }

    if (eqv_pos != -1) {
        std::string left = trimmed.substr(0, eqv_pos);
        std::string right = trimmed.substr(eqv_pos + 3);
        auto lhs = parseStringToCVC5(left, solver, true);
        auto rhs = parseStringToCVC5(right, solver, true);
        return solver.mkTerm(cvc5::Kind::EQUAL, {lhs, rhs});
    }

    if (or_pos != -1) {
        std::string left = trimmed.substr(0, or_pos);
        std::string right = trimmed.substr(or_pos + 1);
        auto lhs = parseStringToCVC5(left, solver, true);
        auto rhs = parseStringToCVC5(right, solver, true);
        return solver.mkTerm(cvc5::Kind::OR, {lhs, rhs});
    }

    if (and_pos != -1) {
        std::string left = trimmed.substr(0, and_pos);
        std::string right = trimmed.substr(and_pos + 1);
        auto lhs = parseStringToCVC5(left, solver, true);
        auto rhs = parseStringToCVC5(right, solver, true);
        return solver.mkTerm(cvc5::Kind::AND, {lhs, rhs});
    }

    // --- Negation ---
    if (trimmed.front() == '!') {
        auto inner = parseStringToCVC5(trimmed.substr(1), solver, true);
        return solver.mkTerm(cvc5::Kind::NOT, {inner});
    }

    // --- Comparison detection ---
    paren_depth = 0;
    for (size_t i = 0; i < trimmed.size(); ++i) {
        char c = trimmed[i];
        if (c == '(') { ++paren_depth; continue; }
        if (c == ')') { --paren_depth; continue; }
        if (paren_depth != 0) continue;

        if (i + 1 < trimmed.size()) {
            std::string sub2 = trimmed.substr(i, 2);
            if (sub2 == "<=" || sub2 == ">=" || sub2 == "==" || sub2 == "!=") {
                cmp_pos = i; cmp_op = sub2; break;
            }
        }
        if (c == '<' || c == '>') {
            cmp_pos = i; cmp_op = std::string(1, c); break;
        }
    }

    if (cmp_pos != -1) {
        std::string left = trimmed.substr(0, cmp_pos);
        std::string right = trimmed.substr(cmp_pos + cmp_op.size());
        auto lhs = parseStringToCVC5(left, solver, false);
        auto rhs = parseStringToCVC5(right, solver, false);

        if (cmp_op == "==") return solver.mkTerm(cvc5::Kind::EQUAL, {lhs, rhs});
        if (cmp_op == "!=") return solver.mkTerm(cvc5::Kind::DISTINCT, {lhs, rhs});
        if (cmp_op == "<")  return solver.mkTerm(cvc5::Kind::LT, {lhs, rhs});
        if (cmp_op == "<=") return solver.mkTerm(cvc5::Kind::LEQ, {lhs, rhs});
        if (cmp_op == ">")  return solver.mkTerm(cvc5::Kind::GT, {lhs, rhs});
        if (cmp_op == ">=") return solver.mkTerm(cvc5::Kind::GEQ, {lhs, rhs});
    }

    // --- Atomic term (variable or literal) ---
    for (char ch : trimmed)
        if (!std::isalnum(static_cast<unsigned char>(ch)) && ch != '_' && ch != '-' && ch != '.')
            throw std::runtime_error("Invalid character in atomic formula: " + trimmed);

    // Numeric constant
    if (!as_bool &&
        (std::isdigit(trimmed[0]) ||
         ((trimmed[0] == '-' || trimmed[0] == '+') && trimmed.size() > 1 && std::isdigit(trimmed[1]))))
    {
        try {
            return solver.mkInteger(std::stoll(trimmed));
        } catch (...) {
            throw std::runtime_error("Invalid numeric literal: " + trimmed);
        }
    }

    // Variable / Boolean atom
    if (as_bool)
        return solver.mkConst(solver.getBooleanSort(), trimmed);
    else
        return solver.mkConst(solver.getIntegerSort(), trimmed);
}


#endif // USE_CVC5


} // namespace formula_utils

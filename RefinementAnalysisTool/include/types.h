



#pragma once
#include <string>
#include <vector>
#include <unordered_map>
#include <set>
#include <iostream>
#include <memory>
#include <limits>
#include <unordered_set>

namespace ctl
{
    

// Forward declarations
class CTLFormula;
using CTLFormulaPtr = std::shared_ptr<CTLFormula>;
class CTLAutomaton;
using CTLAutomatonPtr = std::shared_ptr<CTLAutomaton>;

// Time interval for timed CTL operators
struct TimeInterval {
    int lower;
    int upper;
    
    TimeInterval() : lower(0), upper(std::numeric_limits<int>::max()) {}
    TimeInterval(int l, int u) : lower(l), upper(u) {}
    
    bool operator==(const TimeInterval& other) const {
        return lower == other.lower && upper == other.upper;
    }

    bool operator!=(const TimeInterval& other) const {
        return !(*this == other);
    }
    
    bool subsumes(const TimeInterval& inner) const {
        return lower <= inner.lower && upper >= inner.upper;
    }
    
    std::string toString() const {
        if (upper == std::numeric_limits<int>::max()) {
            return "[" + std::to_string(lower) + ",∞]";
        }
        return "[" + std::to_string(lower) + "," + std::to_string(upper) + "]";
    }
};

// Token types for the lexer
enum class TokenType {
    ATOM,           // atomic proposition
    COMPARISON,     // arithmetic comparison
    NUMBER,         // numeric literal
    LPAREN,         // (
    RPAREN,         // )
    LBRACKET,       // [
    RBRACKET,       // ]
    COMMA,          // ,
    EXCLAMATION,    // !
    AMPERSAND,      // &
    PIPE,           // |
    ARROW,          // ->
    EF,             // EF
    AF,             // AF
    EG,             // EG
    AG,             // AG
    EU,             // E(...U...)
    AU,             // A(...U...)
    EW,             // E(...W...)
    AW,             // A(...W...)
    EX,             // EX
    AX,             // AX
    AR,             // AR
    ER,             // ER
    EQUALS,         // ==
    NOT_EQUALS,     // !=
    LESS_EQUAL,     // <=
    GREATER_EQUAL,  // >=
    LESS,           // <
    GREATER,        // >
    TRUE_LIT,       // true
    FALSE_LIT,      // false
    END_OF_INPUT,
    INVALID
};

// Token structure
struct Token {
    TokenType type;
    std::string value;
    size_t position;
    
    Token(TokenType t, const std::string& v, size_t pos) 
        : type(t), value(v), position(pos) {}
};


enum class FormulaType {
    ATOMIC,
    COMPARISON,
    BOOLEAN_LITERAL,
    NEGATION,
    BINARY,
    TEMPORAL

   //overload string operator for FormulaType
    

};



// Binary operators (AND, OR, IMPLIES)
enum class BinaryOperator {
    AND,
    OR,
    IMPLIES,
    NONE
};


// Temporal operators
enum class TemporalOperator {
    EF, AF, EG, AG, EU, AU, EW, AW, EX, AX, EU_TILDE, AU_TILDE
};


static std::string temporalOperatorToString(TemporalOperator op) {
    switch (op) {
        case TemporalOperator::EF: return "EF";
        case TemporalOperator::AF: return "AF";
        case TemporalOperator::EG: return "EG";
        case TemporalOperator::AG: return "AG";
        case TemporalOperator::EU: return "EU";
        case TemporalOperator::AU: return "AU";
        case TemporalOperator::EW: return "EW";
        case TemporalOperator::AW: return "AW";
        case TemporalOperator::EX: return "EX";
        case TemporalOperator::AX: return "AX";
        case TemporalOperator::EU_TILDE: return "ER";
        case TemporalOperator::AU_TILDE: return "AR";
        default: return "UNKNOWN_TEMPORAL_OP";
    }
}


struct CTLState {
        std::string name;
        CTLFormulaPtr formula;
    };
struct Atom { int dir; std::string_view qnext; };    // (dir, q')
struct Conj {  std::vector<Atom> atoms; };       // ∧ of atoms
using FromToPair = std::pair<std::string_view, std::string_view>;

struct CTLTransition { 
        std::string guard; 
        std::vector<Conj> disjuncts; // guard ∧ (∨ Conj)
        std::string_view from;

        CTLTransition() = default;
        CTLTransition(const std::string& g, const std::vector<Conj>& d,
                      std::string_view f)
            : guard(g), disjuncts(d), from(f) {}
    }; 

using CTLStatePtr = std::shared_ptr<CTLState>;
using CTLTransitionPtr = std::shared_ptr<CTLTransition>;



enum class SCCAcceptanceType {
    LEAST, 
    MU = LEAST,
    GREATEST,
    NU = GREATEST,
    SIMPLE,
    UNDEFINED
};


enum class SCCBlockType {
    EXISTENTIAL,
    UNIVERSAL,
    SIMPLE,
    UNDEFINED
};



    // Helper struct to represent a simulation pair (state from φ, state from φ')
    struct SimPair {
        std::string_view q_phi;      // state from A_φ (the one being simulated)
        std::string_view q_phi_prime; // state from A_φ' (the simulator)
        
        bool operator==(const SimPair& o) const {
            return q_phi == o.q_phi && q_phi_prime == o.q_phi_prime;
        }
    };
    
    // Hash function for SimPair
    struct SimPairHash {
        std::size_t operator()(const SimPair& p) const {
            auto a = std::hash<std::string>{}(
                std::string(p.q_phi) + ""
            );
            auto b = std::hash<std::string>{}(
                std::string(p.q_phi_prime) + ""
            );
            return a ^ (b << 1);
        }
    };

    // Represent a move in Python-style: (atoms, next_states)
    // atoms: set of atomic propositions that must hold
    // next_states: set of (direction, state) pairs for temporal requirements
    struct DirectionStatePair {
        int dir;
        std::string_view state;
        
        bool operator==(const DirectionStatePair& other) const {
            return dir == other.dir && state == other.state;
        }
    };
    
    struct DirectionStatePairHash {
        std::size_t operator()(const DirectionStatePair& p) const {
            return std::hash<int>{}(p.dir) ^ (std::hash<std::string_view>{}(p.state) << 1);
        }
    };

    struct Move {
        std::unordered_set<std::string> atoms;
        std::unordered_set<DirectionStatePair, DirectionStatePairHash> next_states;
        
        // Default constructor
        Move() = default;
        
        // Move constructor and assignment
        Move(Move&&) = default;
        Move& operator=(Move&&) = default;
        
        // Copy constructor and assignment
        Move(const Move&) = default;
        Move& operator=(const Move&) = default;

        bool operator==(const Move& o) const noexcept {
            return atoms == o.atoms && next_states == o.next_states;
        }

        std::string toString() const {
            std::string result = "Atoms: { ";
            for (const auto& atom : atoms) {
                result += atom + " ";
            }
            result += "} | Next States: { ";
            for (const auto& pair : next_states) {
                result += "(" + std::to_string(pair.dir) + ", " + std::string(pair.state) + ") ";
            }
            result += "}";
            return result;
        }
    };

   


} // namespace ctl


namespace std {
    template<>
    struct hash<ctl::Move> {
        size_t operator()(ctl::Move const& m) const noexcept {
            size_t h = 1469598103934665603u;
            for (auto &a : m.atoms) h ^= std::hash<std::string>{}(a) + 0x9e3779b97f4a7c15 + (h<<6) + (h>>2);
            for (auto &p : m.next_states) h ^= std::hash<long long>{}(((long long)p.dir<<32) ^ std::hash<std::string>{}(std::string(p.state)));
            return h;
        }
    };
}
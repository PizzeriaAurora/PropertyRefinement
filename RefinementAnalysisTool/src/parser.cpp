#include "parser.h"
#include <algorithm>
#include <cctype>
#include <stdexcept>
#include <sstream>
#include "visitors.h"
namespace ctl {


// Parser implementation
Parser::Parser(const std::vector<Token>& tokens) : tokens_(tokens), current_token_(0) {}

const Token& Parser::current() const {
    if (current_token_ < tokens_.size()) {
        return tokens_[current_token_];
    }
    static Token end_token(TokenType::END_OF_INPUT, "", 0);
    return end_token;
}

const Token& Parser::peek(size_t offset) const {
    size_t pos = current_token_ + offset;
    if (pos < tokens_.size()) {
        return tokens_[pos];
    }
    static Token end_token(TokenType::END_OF_INPUT, "", 0);
    return end_token;
}

void Parser::advance() {
    if (current_token_ < tokens_.size()) {
        current_token_++;
    }
}

bool Parser::match(TokenType type) {
    if (check(type)) {
        advance();
        return true;
    }
    return false;
}

bool Parser::check(TokenType type) const {
    return current().type == type;
}

void Parser::consume(TokenType type, const std::string& error_message) {
    if (!match(type)) {
        throw ParseException(error_message + ", got: " + current().value, current().position);
    }
}

CTLFormulaPtr Parser::parse() {
    auto result = parse_expression();
    if (!check(TokenType::END_OF_INPUT)) {
        throw ParseException("Expected end of input", current().position);
    }
    return result;
}

CTLFormulaPtr Parser::parse_expression() {
    return parse_implication();
}

CTLFormulaPtr Parser::parse_implication() {
    auto left = parse_or();
    while (match(TokenType::ARROW)) {
        auto right = parse_or();

        left = std::make_shared<BinaryFormula>(left, BinaryOperator::IMPLIES, right);
    }
    
    return left;
}

CTLFormulaPtr Parser::parse_or() {
    auto left = parse_and();
    
    while (match(TokenType::PIPE)) {
        auto right = parse_and();
        left = std::make_shared<BinaryFormula>(left, BinaryOperator::OR, right);
    }
    
    return left;
}

CTLFormulaPtr Parser::parse_and() {
    auto left = parse_unary();
    
    while (match(TokenType::AMPERSAND)) {
        auto right = parse_unary();
        left = std::make_shared<BinaryFormula>(left, BinaryOperator::AND, right);
    }
    
    return left;
}

CTLFormulaPtr Parser::parse_unary() {
    if (match(TokenType::EXCLAMATION)) {
        auto operand = parse_unary();
        return std::make_shared<NegationFormula>(operand);
    }
    
    return parse_temporal();
}

CTLFormulaPtr Parser::parse_temporal() {
    // Check for temporal operators
    if (check(TokenType::EF) || check(TokenType::AF) || check(TokenType::EG) || 
        check(TokenType::AG) || check(TokenType::EX) || check(TokenType::AX)) {
        
        auto op_token = current();
        advance();
        
        TimeInterval interval;
        // Check for time interval
        if (check(TokenType::LBRACKET)) {
            //interval = parse_time_interval();
            throw ParseException("Time intervals not supported in this version", current().position);
        }
        
        auto operand = parse_unary();
        return std::make_shared<TemporalFormula>(token_to_temporal_operator(op_token.type), interval, operand);
    }
    
    // Handle binary temporal operators E(...) and A(...)
    if ((check(TokenType::EU) || check(TokenType::AU)) && peek().type == TokenType::LPAREN) {
        auto op_token = current();
        advance();
        consume(TokenType::LPAREN, "Expected '(' after " + op_token.value);
        
        auto first = parse_expression();
        
        // Look for 'U' or 'W' token
        if (check(TokenType::ATOM)) {
            std::string token_val = current().value;
            if (token_val == "U" || token_val == "W" || token_val == "R") {
                advance(); // consume 'U' or 'W' or 'R'

                auto second = parse_expression();
                consume(TokenType::RPAREN, "Expected ')' after temporal expression");
                
                TemporalOperator op;
                if (op_token.value == "E") {
                    op = (token_val == "U") ? TemporalOperator::EU : 
                        (token_val == "W") ? TemporalOperator::EW : TemporalOperator::EU_TILDE;
                } else {
                    op = (token_val == "U") ? TemporalOperator::AU : 
                        (token_val == "W") ? TemporalOperator::AW : TemporalOperator::AU_TILDE;
                }
                
                return std::make_shared<TemporalFormula>(op, first, second);
            }
        }
        
        throw ParseException("Expected 'U' or 'W' or 'R' in temporal expression", current().position);
    }
    
    return parse_primary();
}

CTLFormulaPtr Parser::parse_primary() {
    if (match(TokenType::TRUE_LIT)) {
        return std::make_shared<BooleanLiteral>(true);
    }
    
    if (match(TokenType::FALSE_LIT)) {
        return std::make_shared<BooleanLiteral>(false);
    }
    
    if (match(TokenType::LPAREN)) {
        auto expr = parse_expression();
        consume(TokenType::RPAREN, "Expected ')' after expression");
        return expr;
    }
    
    // Handle numbers that might be part of a comparison (e.g., "2 <= WeightPossibleVal")
    if (check(TokenType::NUMBER)) {
        auto num_token = current();
        advance();
        
        // Check if this is a comparison
        if (check(TokenType::EQUALS) || check(TokenType::NOT_EQUALS) ||
            check(TokenType::LESS) || check(TokenType::GREATER) ||
            check(TokenType::LESS_EQUAL) || check(TokenType::GREATER_EQUAL)) {
            
            auto op_token = current();
            advance();
            
            std::string value;
            if (check(TokenType::NUMBER)) {
                value = current().value;
                advance();
            } else if (check(TokenType::ATOM)) {
                value = current().value;
                advance();
            } else {
                throw ParseException("Expected value after comparison operator", current().position);
            }
            
            return std::make_shared<ComparisonFormula>(num_token.value, 
                                                     comparison_token_to_string(op_token.type), 
                                                     value);
        }
        
        // If not a comparison, treat as a standalone number (could be an atomic proposition)
        return std::make_shared<AtomicFormula>(num_token.value);
    }
    
    if (check(TokenType::ATOM)) {
        auto atom_token = current();
        advance();
        
        // Check if this is a comparison
        if (check(TokenType::EQUALS) || check(TokenType::NOT_EQUALS) ||
            check(TokenType::LESS) || check(TokenType::GREATER) ||
            check(TokenType::LESS_EQUAL) || check(TokenType::GREATER_EQUAL)) {
            
            auto op_token = current();
            advance();
            
            std::string value;
            if (check(TokenType::NUMBER)) {
                value = current().value;
                advance();
            } else if (check(TokenType::ATOM)) {
                value = current().value;
                advance();
            } else {
                throw ParseException("Expected value after comparison operator", current().position);
            }
            
            return std::make_shared<ComparisonFormula>(atom_token.value, 
                                                     comparison_token_to_string(op_token.type), 
                                                     value);
        }
        
        return std::make_shared<AtomicFormula>(atom_token.value);
    }
    
    throw ParseException("Expected expression", current().position);
}

TimeInterval Parser::parse_time_interval() {
    consume(TokenType::LBRACKET, "Expected '['");
    
    if (!check(TokenType::NUMBER)) {
        throw ParseException("Expected number for time interval lower bound", current().position);
    }
    int lower = std::stoi(current().value);
    advance();
    
    consume(TokenType::COMMA, "Expected ',' in time interval");
    
    if (!check(TokenType::NUMBER)) {
        throw ParseException("Expected number for time interval upper bound", current().position);
    }
    int upper = std::stoi(current().value);
    advance();
    
    consume(TokenType::RBRACKET, "Expected ']'");
    
    return TimeInterval(lower, upper);
}

BinaryOperator Parser::token_to_binary_operator(TokenType type) {
    switch (type) {
        case TokenType::AMPERSAND: return BinaryOperator::AND;
        case TokenType::PIPE: return BinaryOperator::OR;
        case TokenType::ARROW: return BinaryOperator::IMPLIES;
        default: throw ParseException("Invalid binary operator");
    }
}

TemporalOperator Parser::token_to_temporal_operator(TokenType type) {
    switch (type) {
        case TokenType::EF: return TemporalOperator::EF;
        case TokenType::AF: return TemporalOperator::AF;
        case TokenType::EG: return TemporalOperator::EG;
        case TokenType::AG: return TemporalOperator::AG;
        case TokenType::EU: return TemporalOperator::EU;
        case TokenType::AU: return TemporalOperator::AU;
        case TokenType::EW: return TemporalOperator::EW;
        case TokenType::AW: return TemporalOperator::AW;
        case TokenType::EX: return TemporalOperator::EX;
        case TokenType::AX: return TemporalOperator::AX;
        case TokenType::ER: return TemporalOperator::EU_TILDE;
        case TokenType::AR: return TemporalOperator::AU_TILDE;
        default: throw ParseException("Invalid temporal operator");
    }
}

std::string Parser::comparison_token_to_string(TokenType type) {
    switch (type) {
        case TokenType::EQUALS: return "==";
        case TokenType::NOT_EQUALS: return "!=";
        case TokenType::LESS: return "<";
        case TokenType::GREATER: return ">";
        case TokenType::LESS_EQUAL: return "<=";
        case TokenType::GREATER_EQUAL: return ">=";
        default: throw ParseException("Invalid comparison operator");
    }
}

CTLFormulaPtr Parser::parseFormula(const std::string& input) {
    Lexer lexer(input);
    Parser parser(lexer.getTokens());
    return parser.parse();
}

} // namespace ctl



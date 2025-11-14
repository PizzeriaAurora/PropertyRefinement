#pragma once

#include "formula.h"
#include <exception>
#include <sstream>

namespace ctl {

// Parser exceptions
class ParseException : public std::exception {
private:
    std::string message_;
    size_t position_;
    
public:
    ParseException(const std::string& msg, size_t pos = 0) 
        : message_(msg), position_(pos) {}
    
    const char* what() const noexcept override {
        return message_.c_str();
    }
    
    size_t position() const { return position_; }
};

// Lexer class for tokenizing CTL formulas
class Lexer {
private:
    std::string input_;
    size_t position_;
    std::vector<Token> tokens_;
    
    char current_char() const;
    char peek_char(size_t offset = 1) const;
    void advance();
    void skip_whitespace();
    Token read_identifier();
    Token read_number();
    Token read_comparison_operator();
    void tokenize();
    
public:
    explicit Lexer(const std::string& input);
    const std::vector<Token>& getTokens() const { return tokens_; }
    std::string getErrorContext(size_t pos, size_t context_size = 10) const;
};

// Recursive descent parser for CTL formulas with proper precedence handling
class Parser {
private:
    std::vector<Token> tokens_;
    size_t current_token_;
    
    const Token& current() const;
    const Token& peek(size_t offset = 1) const;
    void advance();
    bool match(TokenType type);
    bool check(TokenType type) const;
    void consume(TokenType type, const std::string& error_message);
    
    // Recursive descent parsing methods (in order of precedence)
    CTLFormulaPtr parse_expression();
    CTLFormulaPtr parse_implication();
    CTLFormulaPtr parse_or();
    CTLFormulaPtr parse_and();
    CTLFormulaPtr parse_unary();
    CTLFormulaPtr parse_temporal();
    CTLFormulaPtr parse_primary();
    // Helper methods
    TimeInterval parse_time_interval();
    BinaryOperator token_to_binary_operator(TokenType type);
    TemporalOperator token_to_temporal_operator(TokenType type);
    std::string comparison_token_to_string(TokenType type);
    
public:
    explicit Parser(const std::vector<Token>& tokens);
    CTLFormulaPtr parse();
    
    // Static convenience method
    static CTLFormulaPtr parseFormula(const std::string& input);
};




} // namespace ctl
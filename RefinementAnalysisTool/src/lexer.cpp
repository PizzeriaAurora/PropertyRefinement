
#include "parser.h"
#include <algorithm>
#include <cctype>
#include <stdexcept>
#include <sstream>

namespace ctl {
// Lexer implementation
Lexer::Lexer(const std::string& input) : input_(input), position_(0) {
    tokenize();
}

char Lexer::current_char() const {
    if (position_ >= input_.length()) {
        return '\0';
    }
    return input_[position_];
}

char Lexer::peek_char(size_t offset) const {
    size_t pos = position_ + offset;
    if (pos >= input_.length()) {
        return '\0';
    }
    return input_[pos];
}

void Lexer::advance() {
    if (position_ < input_.length()) {
        position_++;
    }
}

void Lexer::skip_whitespace() {
    while (position_ < input_.length() && std::isspace(current_char())) {
        advance();
    }
}

Token Lexer::read_identifier() {
    size_t start = position_;
    std::string value;
    
    while (position_ < input_.length() && 
           (std::isalnum(current_char()) || current_char() == '_' || current_char() == '.' || current_char() == '-')) {
        value += current_char();
        advance();
    }    
    // Check for keywords
    if (value == "true") return Token(TokenType::TRUE_LIT, value, start);
    if (value == "false") return Token(TokenType::FALSE_LIT, value, start);
    if (value == "EF") return Token(TokenType::EF, value, start);
    if (value == "AF") return Token(TokenType::AF, value, start);
    if (value == "EG") return Token(TokenType::EG, value, start);
    if (value == "AG") return Token(TokenType::AG, value, start);
    if (value == "EU") return Token(TokenType::EU, value, start);
    if (value == "AU") return Token(TokenType::AU, value, start);
    if (value == "EW") return Token(TokenType::EW, value, start);
    if (value == "AW") return Token(TokenType::AW, value, start);
    if (value == "EX") return Token(TokenType::EX, value, start);
    if (value == "AX") return Token(TokenType::AX, value, start);
    if (value == "E") return Token(TokenType::EU, value, start); // Will be handled in parser context
    if (value == "A") return Token(TokenType::AU, value, start); // Will be handled in parser context
    
    return Token(TokenType::ATOM, value, start);
}

Token Lexer::read_number() {
    size_t start = position_;
    std::string value;
    
    while (position_ < input_.length() && 
           (std::isdigit(current_char()) || current_char() == '.')) {
        value += current_char();
        advance();
    }
    
    return Token(TokenType::NUMBER, value, start);
}

Token Lexer::read_comparison_operator() {
    size_t start = position_;
    char first = current_char();
    char second = peek_char();
    
    if (first == '=' && second == '=') {
        advance();
        advance();
        return Token(TokenType::EQUALS, "==", start);
    } else if (first == '!' && second == '=') {
        advance();
        advance();
        return Token(TokenType::NOT_EQUALS, "!=", start);
    } else if (first == '<' && second == '=') {
        advance();
        advance();
        return Token(TokenType::LESS_EQUAL, "<=", start);
    } else if (first == '>' && second == '=') {
        advance();
        advance();
        return Token(TokenType::GREATER_EQUAL, ">=", start);
    } else if (first == '<') {
        advance();
        return Token(TokenType::LESS, "<", start);
    } else if (first == '>') {
        advance();
        return Token(TokenType::GREATER, ">", start);
    } else if (first == '=') {
        advance();
        return Token(TokenType::EQUALS, "=", start);
    } else if (first == '!') {
        // This is a standalone '!' (negation), not part of '!='
        advance();
        return Token(TokenType::EXCLAMATION, "!", start);
    }
    
    return Token(TokenType::INVALID, std::string(1, first), start);
}

void Lexer::tokenize() {
    while (position_ < input_.length()) {
        skip_whitespace();
        
        if (position_ >= input_.length()) {
            break;
        }
        
        char ch = current_char();
        size_t start = position_;
        
        if (std::isalpha(ch) || ch == '_' || ch == '.' || (ch == '-' && peek_char() != '>')) {
            tokens_.push_back(read_identifier());
        } else if (std::isdigit(ch)) {
            tokens_.push_back(read_number());
        } else if (ch == '(' || ch == ')') {
            tokens_.push_back(Token(ch == '(' ? TokenType::LPAREN : TokenType::RPAREN, 
                                  std::string(1, ch), start));
            advance();
        } else if (ch == '[' || ch == ']') {
            tokens_.push_back(Token(ch == '[' ? TokenType::LBRACKET : TokenType::RBRACKET, 
                                  std::string(1, ch), start));
            advance();
        } else if (ch == ',') {
            tokens_.push_back(Token(TokenType::COMMA, ",", start));
            advance();
        } else if (ch == '-' ) {
            if (peek_char() != '>') {
                throw ParseException("Unexpected character: " + std::string(1, ch), start);
            }
            tokens_.push_back(Token(TokenType::ARROW, "->", start));
            advance();
            advance();
            advance();
        } else if (ch == '=' || ch == '!' || ch == '<' || ch == '>') {
            // Check for comparison operators first (multi-character)
            tokens_.push_back(read_comparison_operator());
        } else if (ch == '&') {
            tokens_.push_back(Token(TokenType::AMPERSAND, "&", start));
            advance();
        } else if (ch == '|') {
            tokens_.push_back(Token(TokenType::PIPE, "|", start));
            advance();
        } else {
            throw ParseException("Unexpected character: " + std::string(1, ch), start);
        }
    }
    
    tokens_.push_back(Token(TokenType::END_OF_INPUT, "", position_));
}

std::string Lexer::getErrorContext(size_t pos, size_t context_size) const {
    size_t start = pos >= context_size ? pos - context_size : 0;
    size_t end = std::min(pos + context_size, input_.length());
    
    std::string context = input_.substr(start, end - start);
    std::string marker(pos - start, ' ');
    marker += "^";
    
    return context + "\n" + marker;
}
}
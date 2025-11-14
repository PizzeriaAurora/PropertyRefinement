#include <gtest/gtest.h>
#include "ctlsat_parser.h"
#include "parser.h"

using namespace ctl;

// Test atomic formula
TEST(CTLSATParserTest, AtomicFormula) {
    auto formula = Parser::parseFormula("p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "p");
}

// Test comparison collapses to unique atoms
TEST(CTLSATParserTest, ComparisonToAtom) {
    CTLSATParser::clearComparisonMapping();  // Start fresh
    
    auto formula1 = Parser::parseFormula("x <= 5");
    std::string result1 = CTLSATParser::toCtlSatFormat(*formula1);
    EXPECT_EQ(result1, "a");  // First comparison gets a
    
    auto formula2 = Parser::parseFormula("y > 3");
    std::string result2 = CTLSATParser::toCtlSatFormat(*formula2);
    EXPECT_EQ(result2, "b");  // Second comparison gets b
    
    // Same comparison should reuse the same atom
    auto formula3 = Parser::parseFormula("x <= 5");
    std::string result3 = CTLSATParser::toCtlSatFormat(*formula3);
    EXPECT_EQ(result3, "a");  // Same as first
    
    // Check the mapping
    auto mapping = CTLSATParser::getComparisonMapping();
    EXPECT_EQ(mapping.size(), 2);
    EXPECT_EQ(mapping.at("x <= 5"), "a");
    EXPECT_EQ(mapping.at("y > 3"), "b");
}

// Test boolean literals
TEST(CTLSATParserTest, BooleanTrue) {
    auto formula = Parser::parseFormula("true");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "T");
}

TEST(CTLSATParserTest, BooleanFalse) {
    auto formula = Parser::parseFormula("false");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "~T");
}

// Test negation
TEST(CTLSATParserTest, Negation) {
    auto formula = Parser::parseFormula("!p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "~(p)");
}

// Test conjunction (AND)
TEST(CTLSATParserTest, Conjunction) {
    auto formula = Parser::parseFormula("p & q");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "(p ^ q)");
}

// Test disjunction (OR)
TEST(CTLSATParserTest, Disjunction) {
    auto formula = Parser::parseFormula("p | q");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "(p v q)");
}

// Test implication
TEST(CTLSATParserTest, Implication) {
    auto formula = Parser::parseFormula("p -> q");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "(p -> q)");
}

// Test EF (exists finally)
TEST(CTLSATParserTest, EF) {
    auto formula = Parser::parseFormula("EF p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "EF(p)");
}

// Test AF (always finally)
TEST(CTLSATParserTest, AF) {
    auto formula = Parser::parseFormula("AF p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "AF(p)");
}

// Test EG (exists globally)
TEST(CTLSATParserTest, EG) {
    auto formula = Parser::parseFormula("EG p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "EG(p)");
}

// Test AG (always globally)
TEST(CTLSATParserTest, AG) {
    auto formula = Parser::parseFormula("AG p");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "AG(p)");
}

// Test EU (exists until)
TEST(CTLSATParserTest, EU) {
    auto formula = Parser::parseFormula("E(p U q)");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "E(p U q)");
}

// Test AU (always until)
TEST(CTLSATParserTest, AU) {
    auto formula = Parser::parseFormula("A(p U q)");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "A(p U q)");
}

// Test EW (exists weak until) - should rewrite as E[φ U ψ] | EG φ
TEST(CTLSATParserTest, EW) {
    auto formula = Parser::parseFormula("E(p W q)");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "(E(p U q) v EG(p))");
}

// Test AW (always weak until) - should rewrite as A[φ U ψ] | AG φ
TEST(CTLSATParserTest, AW) {
    auto formula = Parser::parseFormula("A(p W q)");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "(A(p U q) v AG(p))");
}

// Test complex nested formula
TEST(CTLSATParserTest, ComplexFormula) {
    auto formula = Parser::parseFormula("AG (p -> EF q)");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    EXPECT_EQ(result, "AG((p -> EF(q)))");
}

// Test using convertString
TEST(CTLSATParserTest, ConvertString) {
    std::string result = CTLSATParser::convertString("AG (p -> EF q)");
    // Expected: AG((p->EF(q)))
    EXPECT_TRUE(result.find("AG") != std::string::npos);
    EXPECT_TRUE(result.find("->") != std::string::npos);
    EXPECT_TRUE(result.find("EF") != std::string::npos);
}

// Test the problematic case: A(false W (EG (!(P1 <= P3))))
TEST(CTLSATParserTest, FalseWeakUntil) {
    auto formula = Parser::parseFormula("A(false W EG(!P1))");
    std::string result = CTLSATParser::toCtlSatFormat(*formula);
    // Should rewrite as: (A(false U EG(!P1)) v AG(false))
    // With false -> ~T: (A(~T U EG(~(P1))) v AG(~T))
    EXPECT_TRUE(result.find("~T") != std::string::npos);
    EXPECT_TRUE(result.find("AG") != std::string::npos);
    EXPECT_TRUE(result.find("EG") != std::string::npos);
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

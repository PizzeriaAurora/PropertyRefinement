#include <gtest/gtest.h>
#include "../include/formula.h"
#include "../include/CTLautomaton.h"
#include "../include/property.h"
#include <memory>
#include <string>
#include <fstream>
#include <iostream>

using namespace ctl;

// ---------------------------------------------------------------------
// Helper: create property and simplify
// ---------------------------------------------------------------------
std::shared_ptr<CTLProperty> makeProperty(const std::string& formula_str) {
    auto p = std::make_shared<CTLProperty>(formula_str);
    //p->simplifyABTA();
    //if (p->isEmpty()) {
    //    std::cerr << "Warning: '" << formula_str << "' yields empty ABTA.\n";
    //}
    return p;
}

// ---------------------------------------------------------------------
// SECTION 1: BASIC EMPTINESS TESTS
// ---------------------------------------------------------------------

TEST(EmptinessTest, Test01_FalseIsEmpty) {
    auto prop = makeProperty("p & !p");
    EXPECT_TRUE(prop->isEmpty());
}

TEST(EmptinessTest, Test02_TrueIsNotEmpty) {
    auto prop = makeProperty("true");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test03_AtomicFormulaIsNotEmpty) {
    auto prop = makeProperty("p");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test04_ConjunctionEmptyWhenFalse) {
    auto prop = makeProperty("(p & false)");
    EXPECT_TRUE(prop->isEmpty());
}

TEST(EmptinessTest, Test05_DisjunctionNonEmptyWhenOneTrue) {
    auto prop = makeProperty("(p | true)");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test06_AGTrueNonEmpty) {
    auto prop = makeProperty("AG(true)");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test07_EGFalseEmpty) {
    auto prop = makeProperty("EG(false)");
    EXPECT_TRUE(prop->isEmpty());
}

TEST(EmptinessTest, Test08_AFTrueNonEmpty) {
    auto prop = makeProperty("AF(true)");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test09_EFTrueNonEmpty) {
    auto prop = makeProperty("EF(true)");
    EXPECT_FALSE(prop->isEmpty());
}

TEST(EmptinessTest, Test10_ComplexEmpty) {
    auto prop = makeProperty("AG(false & p)");
    EXPECT_TRUE(prop->isEmpty());
    
}





// ---------------------------------------------------------------------
// SECTION 2: PRODUCT TESTS
// ---------------------------------------------------------------------

TEST(ProductTest, Test11_ProductOfTrueAndTrueNonEmpty) {
    auto prop1 = makeProperty("true & true");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test12_ProductOfTrueAndFalseEmpty) {
    auto prop1 = makeProperty("true & false");
    EXPECT_TRUE(prop1->isEmpty());
}

TEST(ProductTest, Test13_ProductOfFalseAndFalseEmpty) {
    auto prop1 = makeProperty("false & false");
    EXPECT_TRUE(prop1->isEmpty());
}



TEST(ProductTest, Test14_ProductOfAGpAndEGpNonEmpty) {
    auto prop1 = makeProperty("AG(p) & EG(p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test15_ProductOfAGpAndAGqNonEmpty) {
    auto prop1 = makeProperty("AG(p) & AG(q)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test16_ProductPreservesAcceptingStates) {
    auto prop1 = makeProperty("p&p");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test17_ProductDetectsReachability) {
    auto prop1 = makeProperty("EF(p) & AF(p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test18_ProductOfEFpAndEGqNonEmpty) {
    auto prop1 = makeProperty("EF(p)&EG(q)");
    EXPECT_FALSE(prop1->isEmpty());
}


TEST(ProductTest, Test19_ProductNestedTemporal) {
    auto prop1 = makeProperty("AG(EF(p)) & AF(p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(ProductTest, Test20_ProductAFpAndAFpNonEmpty) {
    auto prop1 = makeProperty("AF(p) & AF(p)");
    EXPECT_FALSE(prop1->isEmpty());
}



// ---------------------------------------------------------------------
// SECTION 3: LANGUAGE INCLUSION TESTS
// ---------------------------------------------------------------------

TEST(LanguageInclusionTest, Test21_TrueIncludesEverything) {
    auto prop_true = makeProperty("true");
    auto prop_p = makeProperty("p");
    EXPECT_TRUE(prop_true->automaton().languageIncludes(prop_p->automaton()));
}

TEST(LanguageInclusionTest, Test22_FalseIncludedInEverything) {
    auto prop_false = makeProperty("false");
    auto prop_p = makeProperty("p");
    EXPECT_TRUE(prop_p->automaton().languageIncludes(prop_false->automaton()));
}

TEST(LanguageInclusionTest, Test23_SameFormulaIncludesItself) {
    auto prop1 = makeProperty("AG(p)");
    auto prop2 = makeProperty("AG(p)");
    
    EXPECT_TRUE(makeProperty("AG(p) & !AG(p)")->isEmpty());
}

TEST(LanguageInclusionTest, Test24_StrongerImpliesWeaker) {
    auto prop_af = makeProperty("AF(p)");
    auto prop_ef = makeProperty("EF(p)");
    EXPECT_FALSE(prop_af->automaton().languageIncludes(prop_ef->automaton()));
}

TEST(LanguageInclusionTest, Test25_WeakerIncludeStronger) {
    auto prop_ef = makeProperty("EF(p)");
    auto prop_af = makeProperty("AF(p)");
    EXPECT_TRUE(prop_ef->automaton().languageIncludes(prop_af->automaton()));
    EXPECT_TRUE(makeProperty("!EF(p) & AF(p)")->isEmpty());
}

TEST(LanguageInclusionTest, Test26_AGRefinesEG) {
    auto prop_eg = makeProperty("EG(p)");
    auto prop_ag = makeProperty("AG(p)");
    EXPECT_FALSE(prop_ag->automaton().languageIncludes(prop_eg->automaton()));
}
TEST(LanguageInclusionTest, Test26b_AGRefinesEG) {
    auto prop_eg = makeProperty("EG(p)");
    auto prop_ag = makeProperty("AG(p)");
    EXPECT_TRUE(prop_eg->automaton().languageIncludes(prop_ag->automaton()));
}

TEST(LanguageInclusionTest, Test27) {
    auto prop_eg = makeProperty("AG(p) & !EG(p)");
    EXPECT_TRUE(prop_eg->isEmpty());
}

TEST(LanguageInclusionTest, Test28_AURefinesEU) {
    auto prop_au = makeProperty("A(p U q) & !E(p U q)");
    EXPECT_TRUE(prop_au->isEmpty());
}


TEST(LanguageInclusionTest, EUimplesNotAU) {
    auto prop_au = makeProperty("A(p U q) & !E(p U q)");

    // A(p U q) and !E(p U q) are contradictory → product should be empty
    EXPECT_TRUE(prop_au->isEmpty());
}



TEST(LanguageInclusionTest, Test30_ComplexMixed) {
    auto prop1 = makeProperty("AG(p) | EF(q) & !AG(p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(LanguageInclusionTest, Test31){
    auto prop1 = makeProperty("EF (p) & !AF (p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(LanguageInclusionTest, Test32){
    auto prop1 = makeProperty("!EF (p) & AF (p)");
    EXPECT_TRUE(prop1->isEmpty());
}

TEST(LanguageInclusionTest, Test33){
    auto prop1 = makeProperty("AG(p) & !EG(p)");
    EXPECT_TRUE(prop1->isEmpty());
}

TEST(LanguageInclusionTest, Test34){
    auto prop1 = makeProperty("!AG(p) & EG(p)");
    EXPECT_FALSE(prop1->isEmpty());
}

TEST(LanguageInclusionTest, Test344){
    auto prop1 = makeProperty("A(false R (E(true U (A(true U (2 <= p84)))) | ((26 <= p53) | (E(false R (A(false R (p63 <= p56)))))) & ((!(15 <= p13)) | (A((!(p2 <= 50)) U ((!(p11 <= p13)) & (!(p2 <= 50)))) | (A(false R (!(p2 <= 50))))) | (A(false R (E((p53 <= p43) U (p55 <= 1)))))) | (A((!(p76 <= p13 | 16 <= p74)) U ((!(7 <= p62 | p71 <= 34)) & (!(p76 <= p13 | 16 <= p74)))) | (A(false R (!(p76 <= p13 | 16 <= p74)))) | (E(false U (1 <= p47)) | (E(false R false))) | ((!(p37 <= p66)) & (E(true U (!(p29 <= 16)))) | (A((!(p53 <= 21 & p45 <= p11)) U ((!(!(8 <= p27))) & (!(p53 <= 21 & p45 <= p11)))) | (A(false R (!(p53 <= 21 & p45 <= p11))))))))) & (A(false R (E(true U (A((!(p17 <= p53)) U (A(false R (!(p10 <= 18))) & (!(p17 <= p53)))) | (A(false R (!(p17 <= p53)))))) | (!(!(21 <= p30))) | (E(true U (!(p58 <= p43 & p84 <= p33))) & (E(true U (!(22 <= p8))) & ((!(p52 <= p12 & p33 <= 40)) & (A(false R (!(5 <= p12)))))) | (A(true U (!(p36 <= p20 | 25 <= p26)))) | (A(true U (!(23 <= p49))))))))");
    EXPECT_FALSE(prop1->isEmpty());
}






// ---------------------------------------------------------------------
// MAIN
// ---------------------------------------------------------------------
int main(int argc, char **argv) {
    testing::InitGoogleTest(&argc, argv);
    int result = RUN_ALL_TESTS();
    return result;
}

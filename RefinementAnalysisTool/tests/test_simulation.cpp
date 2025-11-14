#include <gtest/gtest.h>
#include "../include/formula.h"
#include "../include/CTLautomaton.h"
#include "../include/property.h"
#include <memory>

using namespace ctl;

// Helper function to create properties
std::shared_ptr<CTLProperty> makeProperty(const std::string& formula_str) {
    auto a = std::make_shared<CTLProperty>(formula_str);
    //a->simplifyABTA();
    //if (a->isEmpty()) { 
    //    std::cerr << "Warning: Property '" << formula_str << "' simplifies to an empty ABTA and will be treated as 'false'.\n";
    //}
    return a;
}

// ==================== BASIC ATOMIC FORMULAS ====================

TEST(SimulationTest, Test01_SameAtomicFormula) {
    // p should refine p (reflexivity)
    auto prop1 = makeProperty("p");
    auto prop2 = makeProperty("p");
    EXPECT_TRUE(prop1->automaton().simulates(prop2->automaton()));
    
}


TEST(SimulationTest, Test01_SameAtomicFormulaOpposite) {
    // p should refine p (reflexivity)
    auto prop1 = makeProperty("p");
    auto prop2 = makeProperty("p");
    EXPECT_TRUE(prop2->automaton().simulates(prop1->automaton()));
    //EXPECT_TRUE(prop1->refines(*prop2, fase, false));
    //EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

TEST(SimulationTest, Test02_DifferentAtomicFormulas) {
    // p should NOT refine q
    auto prop1 = makeProperty("p");
    auto prop2 = makeProperty("q");
    
    EXPECT_FALSE(prop1->automaton().simulates(prop2->automaton()));
}

TEST(SimulationTest, Test02_DifferentAtomicFormulasOpposite) {
    // p should NOT refine q
    auto prop1 = makeProperty("p");
    auto prop2 = makeProperty("q");

    EXPECT_FALSE(prop2->automaton().simulates(prop1->automaton()));
}



TEST(SimulationTest, Test03_TrueSimulatesEverything) {
    // true should refine any formula (true is the weakest)
    auto prop_true = makeProperty("true");
    auto prop_p = makeProperty("p");

    EXPECT_TRUE(prop_true->automaton().simulates(prop_p->automaton()));
}

TEST(SimulationTest, Test03_TrueIsSimulatedByNothing) {
    // true should refine any formula (true is the weakest)
    auto prop_true = makeProperty("true");
    auto prop_p = makeProperty("p");

    EXPECT_FALSE(prop_p->automaton().simulates(prop_true->automaton()));
}


TEST(SimulationTest, Test04_FalseisSimulatedByEverything) {
    // false should be refined by everything (false is the strongest)
    auto prop_false = makeProperty("false");
    auto prop_p = makeProperty("p");
    EXPECT_TRUE(prop_p->automaton().simulates(prop_false->automaton()));
    //EXPECT_TRUE(prop_false->refines(*prop_p, false, false));  // false is stronger
    //EXPECT_FALSE(prop_p->refines(*prop_false, false, false)); // p is weaker
}

TEST(SimulationTest, Test04_FalseSimulatesNothing) {
    auto prop_false = makeProperty("false");
    auto prop_p = makeProperty("p");
    EXPECT_FALSE(prop_false->automaton().simulates(prop_p->automaton()));
    //EXPECT_TRUE(prop_false->refines(*prop_p, false, false));  // false is stronger
    //EXPECT_FALSE(prop_p->refines(*prop_false, false, false)); // p is weaker
}





// ==================== BOOLEAN OPERATORS ====================

TEST(SimulationTest, Test05_ConjunctionIsSimulatedByOperands) {
    // (p & q) should refine p
    auto prop_and = makeProperty("(p & q)");
    auto prop_p = makeProperty("p");
    EXPECT_TRUE(prop_p->automaton().simulates(prop_and->automaton()));
}

TEST(SimulationTest, Test05_ConjunctionDOESNTSimulateOperands) {
    // (p & q) should refine p
    auto prop_and = makeProperty("(p & q)");
    auto prop_p = makeProperty("p");
    EXPECT_FALSE(prop_and->automaton().simulates(prop_p->automaton()));
}


TEST(SimulationTest, Test06_OperandRefinesDisjunction) {
    // p should refine (p | q)
    auto prop_p = makeProperty("p");
    auto prop_or = makeProperty("p | q");
    
    EXPECT_TRUE(prop_p->refines(*prop_or, false, false));
    EXPECT_FALSE(prop_or->refines(*prop_p, false, false));
}


TEST(SimulationTest, Test06_OperandCanBeSimulatedByDisjunction) {
    // p should refine (p | q)
    auto prop_p = makeProperty("p");
    auto prop_or = makeProperty("p | q");
    
    EXPECT_TRUE(prop_or->automaton().simulates(prop_p->automaton()));
}


TEST(SimulationTest, Test06_DisjunctionCanNotBeSimulatedOperand) {
    // p should refine (p | q)
    auto prop_p = makeProperty("p");
    auto prop_or = makeProperty("p | q");
    
    EXPECT_FALSE(prop_p->automaton().simulates(prop_or->automaton()));
}


TEST(SimulationTest, Test07_ConjunctionAssociativity) {
    // (p & q) should refine (p & q) regardless of parenthesization
    auto prop1 = makeProperty("((p & q) & r)");
    auto prop2 = makeProperty("(p & (q & r))");
    
    // Both should refine each other (equivalent)
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

TEST(SimulationTest, Test08_DisjunctionAssociativity) {
    // (p | q) should refine (p | q) regardless of parenthesization
    auto prop1 = makeProperty("((p | q) | r)");
    auto prop2 = makeProperty("(p | (q | r))");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

// ==================== NEGATION ====================

TEST(SimulationTest, Test09_DoubleNegation) {
    // !!p should be equivalent to p
    auto prop_p = makeProperty("p");
    auto prop_not_not_p = makeProperty("!(!p)");
    
    EXPECT_TRUE(prop_p->refines(*prop_not_not_p, false, false));
    EXPECT_TRUE(prop_not_not_p->refines(*prop_p, false, false));
}

TEST(SimulationTest, Test10_DeMorgan1) {
    // !(p & q) should be equivalent to (!p | !q)
    auto prop1 = makeProperty("!(p & q)");
    auto prop2 = makeProperty("(!p | !q)");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

// ==================== TEMPORAL OPERATORS - EG vs AG ====================

TEST(SimulationTest, Test11_AG_DOESNT_Simulate_EG) {
    // AG(p) should simulate EG(p) (universal is stronger than existential)
    auto prop_ag = makeProperty("AG p");
    auto prop_eg = makeProperty("EG p");
    
    //EXPECT_FALSE(prop_ag->automaton().simulates(prop_eg->automaton()));
    EXPECT_TRUE(prop_eg->automaton().simulates(prop_ag->automaton()));
    
}

TEST(SimulationTest, Test12_EG_SameFormula) {
    // EG(p) should simulate EG(p)
    auto prop1 = makeProperty("EG(p)");
    auto prop2 = makeProperty("EG(p)");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

TEST(SimulationTest, Test13_AG_SameFormula) {
    // AG(p) should simulate AG(p)
    auto prop1 = makeProperty("AG(p)");
    auto prop2 = makeProperty("AG(p)");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}




// ==================== TEMPORAL OPERATORS - EF vs AF ====================

TEST(SimulationTest, Test14_AF_Simulates_EF) {
    // AF(p) should refine EF(p)
    auto prop_af = makeProperty("AF(p)");
    auto prop_ef = makeProperty("EF(p)");
   
    

    EXPECT_TRUE(prop_af->refines(*prop_ef, false, false));
}


TEST(SimulationTest, Test14_AF_Simulates_EF2) {
    // AF(p) should refine EF(p)
    auto prop_af = makeProperty("AF(p)");
    auto prop_ef = makeProperty("EF(p)");


    EXPECT_FALSE(prop_af->automaton().simulates(prop_ef->automaton()));
}

TEST(SimulationTest, Test15_EF_SameFormula) {
    // EF(p) should Simulate EF(p)
    auto prop1 = makeProperty("EF(p)");
    auto prop2 = makeProperty("EF(p)");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

TEST(SimulationTest, Test16_AF_SameFormula) {
    // AF(p) should Simulate AF(p)
    auto prop1 = makeProperty("AF(p)");
    auto prop2 = makeProperty("AF(p)");
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}



// ==================== NESTED TEMPORAL OPERATORS ====================

TEST(SimulationTest, Test17_NestedAG) {
    // AG(AG(p)) should refine AG(p)
    auto prop_nested = makeProperty("AG(AG(p))");
    auto prop_single = makeProperty("AG(p)");
    
    EXPECT_TRUE(prop_nested->refines(*prop_single, false, false));
    EXPECT_TRUE(prop_single->refines(*prop_nested, false, false)); // These are equivalent
}



TEST(SimulationTest, Test18_NestedEG) {
    //  EG(p) should refine EG(EG(p))
    auto prop_nested = makeProperty("EG(EG(p))");
    auto prop_single = makeProperty("EG(p)");
    
    EXPECT_TRUE(prop_nested->refines(*prop_single, false, false));
    EXPECT_TRUE(prop_single->refines(*prop_nested, false, false)); 
}

TEST(SimulationTest, Test19_AG_of_Conjunction) {
    // AG(p & q) should refine AG(p)
    auto prop_conj = makeProperty("AG(p & q)");
    auto prop_p = makeProperty("AG(p)");
    
    EXPECT_TRUE(prop_conj->refines(*prop_p, false, false));
    EXPECT_FALSE(prop_p->refines(*prop_conj, false, false));
}

TEST(SimulationTest, Test20_EG_of_Disjunction) {
    // EG(p) should refine EG(p | q)
    auto prop_p = makeProperty("EG(p)");
    auto prop_disj = makeProperty("EG(p | q)");
    
    EXPECT_TRUE(prop_p->refines(*prop_disj, false, false));
    EXPECT_FALSE(prop_disj->refines(*prop_p, false, false));
}

// ==================== UNTIL OPERATORS ====================

TEST(SimulationTest, Test21_AU_Refines_EU) {
    // A(p U q) should refine E(p U q)
    auto prop_au = makeProperty("A(p U q)");
    auto prop_eu = makeProperty("E(p U q)");
    
    EXPECT_TRUE(prop_au->refines(*prop_eu, false, false));
    EXPECT_FALSE(prop_eu->refines(*prop_au, false, false));
}
/*
TEST(SimulationTest, Test22_Until_Destination) {
    // A(p U q) should refine AF(q)
    auto prop_au = makeProperty("A(p U q)");
    auto prop_af = makeProperty("AF(q)");
    
    EXPECT_TRUE(prop_au->refines(*prop_af, false, false));
    EXPECT_FALSE(prop_af->refines(*prop_au, false, false));
}

TEST(SimulationTest, Test23_Until_ImpliesEventually) {
    // E(p U q) should refine EF(q)
    auto prop_eu = makeProperty("E(p U q)");
    auto prop_ef = makeProperty("EF(q)");
    
    EXPECT_TRUE(prop_eu->refines(*prop_ef, false, false));
    EXPECT_FALSE(prop_ef->refines(*prop_eu, false, false));
}

// ==================== WEAK UNTIL OPERATORS ====================

TEST(SimulationTest, Test24_AW_vs_AU) {
    // A(p U q) should refine A(p W q) (strong until is stronger)
    auto prop_au = makeProperty("A(p U q)");
    auto prop_aw = makeProperty("A(p W q)");
    
    EXPECT_TRUE(prop_au->refines(*prop_aw, false, false));
    EXPECT_FALSE(prop_aw->refines(*prop_au, false, false));
}

TEST(SimulationTest, Test25_EW_vs_EU) {
    // E(p U q) should refine E(p W q)
    auto prop_eu = makeProperty("E(p U q)");
    auto prop_ew = makeProperty("E(p W q)");
    
    EXPECT_TRUE(prop_eu->refines(*prop_ew, false, false));
    EXPECT_FALSE(prop_ew->refines(*prop_eu, false, false));
}

TEST(SimulationTest, Test26_AW_Refines_EW) {
    // A(p W q) should refine E(p W q)
    auto prop_aw = makeProperty("A(p W q)");
    auto prop_ew = makeProperty("E(p W q)");
    
    EXPECT_TRUE(prop_aw->refines(*prop_ew, false, false));
    EXPECT_FALSE(prop_ew->refines(*prop_aw, false, false));
}

// ==================== COMPARISON FORMULAS ====================

TEST(SimulationTest, Test27_SameComparison) {
    // (p1 <= p2) should refine (p1 <= p2)
    std::string formula1 = "(p1 <= p2)";
    std::string formula2 = "(p1 <= p2)";
    auto prop1 = makeProperty(formula1);
    auto prop2 = makeProperty(formula2);
    
    EXPECT_TRUE(prop1->refines(*prop2, false, false));
    EXPECT_TRUE(prop2->refines(*prop1, false, false));
}

TEST(SimulationTest, Test28_DifferentComparisons) {
    // (p1 <= p2) should NOT automatically refine (p1 < p2)
    std::string formula1 = "(p1 <= p2)";
    std::string formula2 = "(p1 < p2)";
    auto prop1 = makeProperty(formula1);
    auto prop2 = makeProperty(formula2);
    
    // Without semantic reasoning, these are different
    EXPECT_FALSE(prop1->refines(*prop2, false, false));
    EXPECT_FALSE(prop2->refines(*prop1, false, false));
}

// ==================== COMPLEX NESTED FORMULAS ====================

/*
TEST(SimulationTest, Test29_ComplexNesting) {
    // AG(p & EF(q)) should refine AG(p)
    auto prop_a = makeProperty("AG((p & EF(q)))");
    auto prop_b = makeProperty("AG(p)");
    
    EXPECT_TRUE(prop_a->refines(*prop_b, false, false));
    EXPECT_FALSE(prop_b->refines(*prop_a, false, false));
}

TEST(SimulationTest, Test30_RealWorldExample) {
    // From AutoFlight: EG should refine more complex formula with same atoms
    // A(false W p) is equivalent to AG(p) or p holds forever
    auto prop_eg = makeProperty("EG(p)");
    auto prop_aweak = makeProperty("A(false W p)");
    
    // A(false W p) = AG(p) which should refine EG(p)
    EXPECT_TRUE(prop_aweak->refines(*prop_eg, false, false));
    EXPECT_FALSE(prop_eg->refines(*prop_aweak, false, false));
}
*/

// ==================== MAIN ====================

int main(int argc, char **argv) {
    testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}

#include <iostream>
#include <fstream>
#include "property.h"
#include "parser.h"

using namespace ctl;

std::shared_ptr<CTLProperty> makeProperty(const std::string& formula_str) {
    auto p = std::make_shared<CTLProperty>(formula_str);
    return p;
}

int main() {
    // Test the ABTAs for the failing language inclusion tests   
    std::vector<std::string> test_formulas = {
        //"!EF(p)", // should be non-empty
       // "!(AG (!(((AltitudePossibleVal <= stp3) & (Speed_Right_Wheel <= P5)))))"
       " AG (( (usr5_ai1_re6 &(usr4_ai1_ce1 &(usr4_ai1_re1 &usr3_ai1_ce3))) ->  (usr5_ai1_re6 &usr4_ai1_ce1)) &  (usr4_ai1_re1 &(usr3_ai1_ce3 &(usr3_ni1_ne1 &none)))) ", // should be non-empty

    };
    
    //save all log in a txt file
    std::ofstream log_file("test_abta_debug.log", std::ios::out);
    std::streambuf* coutbuf = std::cout.rdbuf(); //save old buffer
    
    for (const auto& formula : test_formulas) {
        auto prop = makeProperty(formula);
        
        //clean file
        log_file << "=========================\n";
        
        //std::cout.rdbuf(log_file.rdbuf()); //redirect std::cout to log file

        std::cout << "Formula: " << formula << "\n";
        std::cout << "ABTA:\n" << prop->automaton().toString() << "\n";
        std::cout << "Negated formula ABTA:\n" << prop->automaton().getNegatedFormula()->toString() << "\n";
        std::cout << "Checking emptiness...\n";
        bool empty = prop->automaton().isEmpty();
        std::cout << "Formula EMPTY: " << (empty ? "YES" : "NO") << " = formula: "<< formula << "\n";
        std::cout << "Expected: ";
        
       
    }
    
    std::cout << "Tests completed. Check 'test_abta_debug.log' for details.\n";

    

    std::cout.rdbuf(coutbuf); //reset to standard output again
    return 0;
}


/*"p & !p",
        "AG p & !AG p",
        "true | !p",
        "AG(EF(p)) & AF(p)",
        "p & EG p",
        " false | AG p",
        "AG(AG(p) | EG(p)) & AF(p)",
        
        "EG(p) & !AG(p)",
        "AG(p) & !AG(p)",
        "!A(p U q) & E(p U q)",
        "AF(p) & !EF(p)",
        "EG(p) & !AG(p)",
        "AG(p) & !EG(p)",
        "!A(p U q) & E(p U q)",
        "A(p U q) & !E(p U q)",
        "AG(p) & !EG(p)",
       "p & EG p",
       " false | AG p",
       "AG p",
       "AG !p & EG p",
       "A (false U q) ",
       "AG p",
       "AF p",
       "EF p",
       "AG p & EF p",
       "AG p & !EF p",
        "EG p -> !AF p",
        "AG p & !AG p"
        "p & !p",
        "p & q",
        "p  | !p",
        "AF true",
        "EF false",
        "AF false",
        "AG  true",
        "EG  true",
        "AG  false",
        "EG  false",
        "E(true U true)",
        "A(true U true)",
        "E(false U false)",
        "A(false U false)",
        "E(true U false)",
        "A(true U false)",
        "E(false U true)",
        "A(false U true)",
        "E( EF false U EF false)",
        "A( EF false U AF false)",
        "AG true & !AG true",
        "AG (p) & !AG (p)",
        "EF (p) & AF (p)",
        "AG (p) | EG (p)",
        "AF (p) & EG (!p)", 
        */
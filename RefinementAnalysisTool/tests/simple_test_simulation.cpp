#include "../include/formula.h"
#include "../include/CTLautomaton.h"
#include "../include/property.h"
#include <memory>
#include <iostream>

using namespace ctl;

int main() {
    // Test case: p vs true
    auto prop_p = std::make_shared<CTLProperty>("EG EG p");
    auto prop_true = std::make_shared<CTLProperty>("EG p");
    
    std::cout << "===== Automaton for 'p' =====\n";
    std::cout << prop_p->automaton().toString() << "\n\n";
    
    std::cout << "===== Automaton for 'true' =====\n";
    std::cout << prop_true->automaton().toString() << "\n\n";
    
    std::cout << "===== Testing p.simulates(true) =====\n";
    bool result = prop_p->automaton().simulates(prop_true->automaton());
    std::cout << "Result: " << (result ? "TRUE" : "FALSE") << "\n\n";
    
    std::cout << "===== Testing true.simulates(p) =====\n";
    result = prop_true->automaton().simulates(prop_p->automaton());
    std::cout << "Result: " << (result ? "TRUE" : "FALSE") << "\n";
    
    return 0;
}

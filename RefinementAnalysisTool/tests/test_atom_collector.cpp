#include "../include/formula.h"
#include "../include/visitors.h"
#include <iostream>
#include <vector>

using namespace ctl;

int main() {
    // Test 1: Simple atomic formula with complex expression
    auto formula1 = std::make_shared<AtomicFormula>("p % q");
    AtomCollectorVisitor visitor1;
    formula1->accept(visitor1);
    
    std::cout << "Test 1 - AtomicFormula('p % q'):" << std::endl;
    auto atoms1 = visitor1.getAtoms();
    for (const auto& atom : atoms1) {
        std::cout << "  Collected atom: " << atom << std::endl;
    }
    std::cout << std::endl;
    
    // Test 2: Comparison formula with complex expression  
    auto formula2 = std::make_shared<ComparisonFormula>("p % q", "<", "5");
    AtomCollectorVisitor visitor2;
    formula2->accept(visitor2);
    
    std::cout << "Test 2 - ComparisonFormula('p % q', '<', '5'):" << std::endl;
    auto atoms2 = visitor2.getAtoms();
    for (const auto& atom : atoms2) {
        std::cout << "  Collected atom: " << atom << std::endl;
    }
    std::cout << std::endl;
    
    // Test 3: More complex expression
    auto formula3 = std::make_shared<AtomicFormula>("1 < p + q * r > 5");
    AtomCollectorVisitor visitor3;
    formula3->accept(visitor3);
    
    std::cout << "Test 3 - AtomicFormula('1 < p + q * r > 5'):" << std::endl;
    auto atoms3 = visitor3.getAtoms();
    for (const auto& atom : atoms3) {
        std::cout << "  Collected atom: " << atom << std::endl;
    }
    std::cout << std::endl;
    
    // Test 4: Comparison with variables on both sides
    auto formula4 = std::make_shared<ComparisonFormula>("p + q", "<=", "r - s");
    AtomCollectorVisitor visitor4;
    formula4->accept(visitor4);
    
    std::cout << "Test 4 - ComparisonFormula('p + q', '<=', 'r - s'):" << std::endl;
    auto atoms4 = visitor4.getAtoms();
    for (const auto& atom : atoms4) {
        std::cout << "  Collected atom: " << atom << std::endl;
    }



    auto formula5 = std::make_shared<AtomicFormula>("p32 <=4 & p32 >=1");
    AtomCollectorVisitor visitor5;
    formula5->accept(visitor5);
    std::cout << "Test 5 - AtomicFormula('p32 <=4 & p32 >=1'):" << std::endl;
    auto atoms5 = visitor5.getAtoms();
    for (const auto& atom : atoms5) {
        std::cout << "  Collected atom: " << atom << std::endl;
    }
    
    return 0;
}
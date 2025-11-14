#include <iostream>
#ifdef USE_Z3
#include <z3++.h>
#endif
#include "../include/formula_utils.h"

int main() {
    #ifdef USE_Z3
        try {
            z3::context ctx;
            
            // Test the specific failing case
            std::cout << "Testing just: 5<=p32" << std::endl;
            z3::expr test1 = ctl::formula_utils::parseStringToZ3(std::string("1<=p32"), ctx, true);
            std::cout << "Result: " << test1 << std::endl;


            std::cout << "Checking if the previous implies 3<=p32" << std::endl;

            z3::expr test2 = ctl::formula_utils::parseStringToZ3(std::string("3<=p32"), ctx, true);
            std::cout << "Result: " << test2 << std::endl;

            z3::expr implication = z3::implies(test1, test2);
            std::cout << "Implication result: " << implication << std::endl;

            z3::expr test3 = ctl::formula_utils::parseStringToZ3(std::string("3<=p32"), ctx, true);

            
        } catch (const std::exception& e) {
            std::cout << "Exception: " << e.what() << std::endl;
            return 1;
        }
    #else
    std::cout << "Z3 support is not enabled." << std::endl;
    #endif
    
    return 0;
}
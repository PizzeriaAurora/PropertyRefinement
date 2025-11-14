#include "CTLautomaton.h"

#include <queue>

namespace ctl {

    #ifndef USE_ON_THE_FLY_PRODUCT
        
        bool CTLAutomaton::languageIncludes(const CTLAutomaton& other) const {
            //// Implementation
            //// the implementation is checking whether L(this) ⊇ L(other) = L(other & !this) 
            if (this->getFormula()->hash() == TRUE_HASH) return true;
            if (other.getFormula()->hash() == FALSE_HASH) return true;
            //std::cout << "Checking language inclusion L(this) ⊇ L(other) by checking emptiness of L(other & !this).\n";
            //std::cout << "This automaton formula: " << this->getFormula()->toString() << "\n";
            //std::cout << "Other automaton formula: " << other.getFormula()->toString() << "\n";
            auto this_neg = this->getNegatedFormula();
            auto other_prop = other.getFormula();
            auto combined = std::make_shared<BinaryFormula>(
                other_prop, BinaryOperator::AND, this_neg);
            CTLAutomaton combined_automaton(*combined);

            return combined_automaton.isEmpty();
        }
    #endif // USE_ON_THE_FLY_PRODUCT


}
#include "SCCBlocks.h"
#include <algorithm>
namespace ctl {

    void SCCBlocks::setIds() {
        block_ids.resize(blocks.size());
        for (size_t i = 0; i < blocks.size(); ++i) {
            block_ids[i] = i;
        }
    }


    void SCCBlocks::setInfoAt(size_t block_id, const BlockInfo& info) {
        block_info[block_id] = info;
    }
    
    void SCCBlocks::setInfoAt(size_t block_id, SCCAcceptanceType acceptance_type, SCCBlockType block_type) {
        block_info[block_id] = BlockInfo{acceptance_type, block_type};
    }

    


    BlockInfo SCCBlocks::getBlockInfo(size_t block_id) const {
        auto it = block_info.find(block_id);
        if (it != block_info.end()) {
            return it->second;
        }
        throw std::runtime_error("BlockInfo not found for block id: " + std::to_string(block_id));
    }





    SCCAcceptanceType SCCBlocks::getBlockAcceptanceType(size_t block_id) const {
        return getBlockInfo(block_id).type;
    }

    SCCBlockType SCCBlocks::getBlockType(size_t block_id) const {
        return getBlockInfo(block_id).block_type;
    }


    
    bool SCCBlocks::isGreatestFixedPoint(size_t block_id) const {
        auto it = block_info.find(block_id);
        if (it != block_info.end()) {
            return it->second.isGreatestFixedPoint();
        }
        throw std::runtime_error("BlockInfo not found for block id: " + std::to_string(block_id));
    }



    bool SCCBlocks::isSimple(size_t block_id) const {
        auto it = block_info.find(block_id);
        if (it != block_info.end()) {
            return it->second.type == SCCAcceptanceType::SIMPLE;
        }
        throw std::runtime_error("BlockInfo not found for block id: " + std::to_string(block_id));
    }

    



    std::string SCCBlocks::toString() const {
        std::string repr;
        for (auto i : block_ids) {
            repr += "Block " + std::to_string(block_ids[i]) + " ( Is Greatest Fixed Point:";
            repr += isGreatestFixedPoint(block_ids[i]) ? "Yes " : "No ";
            repr += ", Block acceptance Type: ";
            switch (getBlockType(block_ids[i])) {
                case SCCBlockType::EXISTENTIAL:
                    repr += "E";
                    break;
                case SCCBlockType::UNIVERSAL:
                    repr += "A";
                    break;
                case SCCBlockType::SIMPLE:
                    repr += "Simple";
                    break;
                default:
                    repr += "Undefined";
                    break;
            }
            repr += "): ";
            //repr += isExistential(block_ids[i]) ? "∃): " : "∀): ";
            for (const auto& state : blocks[i]) {
                repr += std::string(state) + " ";
            }
            repr += "\n";
        }
        return repr;
    }



    int SCCBlocks::getBlockId(const std::string_view state_name) const {
        for (size_t i = 0; i < blocks.size(); ++i) {
            const auto& block = blocks[i];
            if (std::find(block.begin(), block.end(), state_name) != block.end()) {
                return static_cast<int>(block_ids[i]);
            }
        }
        throw std::runtime_error("State " + std::string(state_name) + " not found in any block.");
    }



    const std::vector<std::string_view>& SCCBlocks::getStatesInBlock(size_t block_id) const {
        if (block_id >= blocks.size()) {
            throw std::runtime_error("Block ID " + std::to_string(block_id) + " is out of range.");
        }
        return blocks[block_id];
    }

} // namespace ctl

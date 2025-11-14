#pragma once

#include "types.h"




namespace ctl {
struct BlockInfo {
    SCCAcceptanceType type;       // ν-block (accepting) or μ-block (rejecting)
    SCCBlockType block_type; // UNIVERSAL or EXISTENTIAL

    bool isGreatestFixedPoint() const {
        return type == SCCAcceptanceType::GREATEST ;
    }
    bool isLeastFixedPoint() const {
        return type == SCCAcceptanceType::LEAST ;
    }
    bool isExistential() const {
        return block_type == SCCBlockType::EXISTENTIAL;
    }
    bool isUniversal() const {
        return block_type == SCCBlockType::UNIVERSAL;
    }
    bool isSimple() const {
        return block_type == SCCBlockType::SIMPLE;
    }
};




class SCCBlocks {
public:
    std::vector<size_t> block_ids;
    std::vector<std::vector<std::string_view>> blocks;
    std::unordered_map<size_t, BlockInfo> block_info;
    SCCBlocks() = default;
    SCCBlocks(const std::vector<std::vector<std::string_view>>& blocks)
        : blocks(blocks) {
        setIds();
    }

    bool is_empty() const { return blocks.empty(); }
    void print() const {std::cout << toString();}
    BlockInfo getBlockInfo(size_t block_id) const;
    SCCAcceptanceType getBlockAcceptanceType(size_t block_id) const;
    SCCBlockType getBlockType(size_t block_id) const;
    bool isGreatestFixedPoint(size_t block_id) const;
    bool isSimple(size_t block_id) const;
    std::string toString() const;
    void setInfoAt(size_t block_id, const BlockInfo& info);
    void setInfoAt(size_t block_id, SCCAcceptanceType acceptance_type, SCCBlockType block_type);
    size_t size() const { return blocks.size(); }
    int getBlockId(const std::string_view state_name) const;

    const std::vector<std::string_view>& getStatesInBlock(size_t block_id) const;
private:
    void setIds();
    
};

} // namespace ctl

// Copyright (c) 2023 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <node/mini_miner.h>

#include <boost/multi_index/detail/hash_index_iterator.hpp>
#include <boost/operators.hpp>
#include <consensus/amount.h>
#include <policy/feerate.h>
#include <primitives/transaction.h>
#include <sync.h>
#include <txgraph.h>
#include <txmempool.h>
#include <uint256.h>
#include <util/check.h>
#include <util/feefrac.h>

#include <algorithm>
#include <numeric>
#include <utility>

static constexpr unsigned MAX_CLUSTER_COUNT{64}; // Must be <= MAX_CLUSTER_COUNT_LIMIT

namespace node {

MiniMiner::MiniMiner(const CTxMemPool& mempool, const std::vector<COutPoint>& outpoints)
{
    LOCK(mempool.cs);
    // Find which outpoints to calculate bump fees for.
    // Anything that's spent by the mempool is to-be-replaced
    // Anything otherwise unavailable just has a bump fee of 0
    for (const auto& outpoint : outpoints) {
        if (!mempool.exists(GenTxid::Txid(outpoint.hash))) {
            // This UTXO is either confirmed or not yet submitted to mempool.
            // If it's confirmed, no bump fee is required.
            // If it's not yet submitted, we have no information, so return 0.
            m_bump_fees.emplace(outpoint, 0);
            continue;
        }

        // UXTO is created by transaction in mempool, add to map.
        // Note: This will either create a missing entry or add the outpoint to an existing entry
        m_requested_outpoints_by_txid[outpoint.hash].push_back(outpoint);

        if (const auto ptx{mempool.GetConflictTx(outpoint)}) {
            // This outpoint is already being spent by another transaction in the mempool. We
            // assume that the caller wants to replace this transaction and its descendants. It
            // would be unusual for the transaction to have descendants as the wallet won’t normally
            // attempt to replace transactions with descendants. If the outpoint is from a mempool
            // transaction, we still need to calculate its ancestors bump fees (added to
            // m_requested_outpoints_by_txid below), but after removing the to-be-replaced entries.
            //
            // Note that the descendants of a transaction include the transaction itself. Also note,
            // that this is only calculating bump fees. RBF fee rules should be handled separately.
            CTxMemPool::setEntries descendants;
            mempool.CalculateDescendants(mempool.GetIter(ptx->GetHash()).value(), descendants);
            for (const auto& desc_txiter : descendants) {
                m_to_be_replaced.insert(desc_txiter->GetTx().GetHash());
            }
        }
    }

    // No unconfirmed UTXOs, so nothing mempool-related needs to be calculated.
    if (m_requested_outpoints_by_txid.empty()) return;

    // Calculate the cluster and construct the entry map.
    std::vector<uint256> txids_needed;
    txids_needed.reserve(m_requested_outpoints_by_txid.size());
    for (const auto& [txid, _]: m_requested_outpoints_by_txid) {
        txids_needed.push_back(txid);
    }
    const auto cluster = mempool.GatherClusters(txids_needed);
    if (cluster.empty()) {
        // An empty cluster means that at least one of the transactions is missing from the mempool
        // (should not be possible given processing above) or DoS limit was hit.
        m_ready_to_calculate = false;
        return;
    }

    // Create TxGraph and process all transactions in single pass
    m_txgraph = MakeTxGraph(MAX_CLUSTER_COUNT);

    for (const auto& txiter : cluster) {
        if (m_to_be_replaced.count(txiter->GetTx().GetHash())) {
            // Handle to-be-replaced transaction outpoints - set bump fee to 0
            auto outpoints_it = m_requested_outpoints_by_txid.find(txiter->GetTx().GetHash());
            if (outpoints_it != m_requested_outpoints_by_txid.end()) {
                // This UTXO is the output of a to-be-replaced transaction. Bump fee is 0; spending
                // this UTXO is impossible as it will no longer exist after the replacement.
                for (const auto& outpoint : outpoints_it->second) {
                    m_bump_fees.emplace(outpoint, 0);
                }
                m_requested_outpoints_by_txid.erase(outpoints_it);
            }
        } else {
            // Add transaction to TxGraph
            FeePerWeight feerate{txiter->GetModifiedFee(), static_cast<int32_t>(txiter->GetTxSize())};
            auto ref = m_txgraph->AddTransaction(feerate);
            m_txid_to_ref.emplace(txiter->GetTx().GetHash(), std::move(ref));
        }
    }
    
    // add dependencies, all transactions should exist before being added as dependency
    for (const auto& txiter : cluster) {
        if (!m_to_be_replaced.count(txiter->GetTx().GetHash())) {
            auto child_it = m_txid_to_ref.find(txiter->GetTx().GetHash());
            Assume(child_it != m_txid_to_ref.end());
            
            for (const auto& input : txiter->GetTx().vin) {
                auto parent_it = m_txid_to_ref.find(input.prevout.hash);
                if (parent_it != m_txid_to_ref.end()) {
                    m_txgraph->AddDependency(parent_it->second, child_it->second);
                }
            }
        }
    }


    // Release the mempool lock; we now have all the information we need for a subset of the entries
    // we care about. We will solely operate on the MiniMinerMempoolEntry map from now on. todo: not the entry map now
    Assume(m_in_block.empty());
    Assume(m_requested_outpoints_by_txid.size() <= outpoints.size());

    m_txgraph->SanityCheck();
}

MiniMiner::MiniMiner(const std::vector<MiniMinerMempoolEntry>& manual_entries,
                     const std::map<Txid, std::set<Txid>>& descendant_caches)
{
    // Create TxGraph for manual entries
    m_txgraph = MakeTxGraph(MAX_CLUSTER_COUNT);

    // First pass: Add all transactions to TxGraph
    for (const auto& entry : manual_entries) {
        const auto& txid = entry.GetTx().GetHash();
        // We need to know the descendant set of every transaction.
        if (!Assume(descendant_caches.count(txid) > 0)) {
            m_ready_to_calculate = false;
            return;
        }
        
        // Add transaction to TxGraph
        FeePerWeight feerate{entry.GetModifiedFee(), static_cast<int32_t>(entry.GetTxSize())};
        auto ref = m_txgraph->AddTransaction(feerate);
        auto [txid_ref_iter, txid_ref_success] = m_txid_to_ref.emplace(txid, std::move(ref));
        
        // Txids must be unique
        if (!Assume(txid_ref_success)) {
            m_ready_to_calculate = false;
            return;
        }
    }
    
    // Second pass: Add dependencies based on transaction inputs
    for (const auto& entry : manual_entries) {
        const auto& txid = entry.GetTx().GetHash();
        auto child_it = m_txid_to_ref.find(txid);
        Assume(child_it != m_txid_to_ref.end());
        
        // Add dependencies for each input
        for (const auto& input : entry.GetTx().vin) {
            auto parent_it = m_txid_to_ref.find(input.prevout.hash);
            if (parent_it != m_txid_to_ref.end()) {
                m_txgraph->AddDependency(parent_it->second, child_it->second);
            }
        }
    }
    
    // Validate descendant relationships are consistent with our TxGraph
    for (const auto& [txid, desc_txids] : descendant_caches) {
        // Descendant cache should include at least the tx itself
        if (!Assume(!desc_txids.empty())) {
            m_ready_to_calculate = false;
            return;
        }
        
        // Verify that all descendant txids correspond to transactions we added
        for (const auto& desc_txid : desc_txids) {
            if (!Assume(m_txid_to_ref.find(desc_txid) != m_txid_to_ref.end())) {
                m_ready_to_calculate = false;
                return;
            }
        }
    }
    
    Assume(m_to_be_replaced.empty());
    Assume(m_requested_outpoints_by_txid.empty());
    Assume(m_bump_fees.empty());
    Assume(m_inclusion_order.empty());
    
    m_txgraph->SanityCheck();
    
}

void MiniMiner::BuildMockTemplate(std::optional<CFeeRate> target_feerate)
{
    if (!m_txgraph) {
        m_ready_to_calculate = false;
        return;
    }

    const auto num_txns = m_txid_to_ref.size();
    uint32_t sequence_num = 0;

    // Handle empty case
    if (m_txid_to_ref.empty()) {
        if (!target_feerate.has_value()) {
            Assume(m_in_block.size() == num_txns);
        }
        Assume(m_in_block.empty());
        Assume(m_in_block.size() == m_inclusion_order.size());
        m_ready_to_calculate = false;
        return;
    }

    auto block_builder = m_txgraph->GetBlockBuilder();

    while (auto chunk_opt = block_builder->GetCurrentChunk()) {
        auto [transactions, chunk_feerate] = *chunk_opt;
        
        // Stop here if target feerate provided and this chunk doesn't meet it
        // Convert target_feerate to FeePerWeight for comparison
        if (target_feerate.has_value()) {
            FeePerWeight target_fee_per_weight{target_feerate->GetFee(1), 1};
            if (chunk_feerate < target_fee_per_weight) {
                break;
            }
        }

        // Track the order in which transactions were selected
        for (auto* ref : transactions) {
            // Find txid for this ref by searching m_txid_to_ref
            for (const auto& [txid, graph_ref] : m_txid_to_ref) {
                if (&graph_ref == ref) {
                    m_inclusion_order.emplace(Txid::FromUint256(txid), sequence_num);
                    m_in_block.insert(txid);
                    
                     // Update totals using individual feerate
                     auto individual_feerate = m_txgraph->GetIndividualFeerate(graph_ref);
                     if (!individual_feerate.IsEmpty()) {
                         // Extract fee and size directly from FeePerWeight
                         m_total_fees += individual_feerate.fee;
                         m_total_vsize += individual_feerate.size;
                     }
                    break;
                }
            }
        }

        block_builder->Include();
        ++sequence_num;
    }

    // Final validation
    if (!target_feerate.has_value()) {
        Assume(m_in_block.size() == num_txns);
    } else {
        Assume(m_in_block.empty() || m_total_fees >= target_feerate->GetFee(m_total_vsize));
    }
    Assume(m_in_block.empty() || sequence_num > 0);
    Assume(m_in_block.size() == m_inclusion_order.size());
    
    // Do not try to continue building the block template with a different feerate
    m_ready_to_calculate = false;
}


std::map<Txid, uint32_t> MiniMiner::Linearize()
{
    BuildMockTemplate(std::nullopt);
    return m_inclusion_order;
}

std::map<COutPoint, CAmount> MiniMiner::CalculateBumpFees(const CFeeRate& target_feerate)
{
    if (!m_ready_to_calculate) return {};
    // Build a block template until the target feerate is hit.
    BuildMockTemplate(target_feerate);

    // Each transaction that "made it into the block" has a bumpfee of 0, i.e. they are part of an
    // ancestor package with at least the target feerate and don't need to be bumped.
    for (const auto& txid : m_in_block) {
        // Not all of the block transactions were necessarily requested.
        auto it = m_requested_outpoints_by_txid.find(txid);
        if (it != m_requested_outpoints_by_txid.end()) {
            for (const auto& outpoint : it->second) {
                m_bump_fees.emplace(outpoint, 0);
            }
            m_requested_outpoints_by_txid.erase(it);
        }
    }

    // A transactions and its ancestors will only be picked into a block when
    // both the ancestor set feerate and the individual feerate meet the target
    // feerate.
    //
    // We had to convince ourselves that after running the mini miner and
    // picking all eligible transactions into our MockBlockTemplate, there
    // could still be transactions remaining that have a lower individual
    // feerate than their ancestor feerate. So here is an example:
    //
    //               ┌─────────────────┐
    //               │                 │
    //               │   Grandparent   │
    //               │    1700 vB      │
    //               │    1700 sats    │                    Target feerate: 10    s/vB
    //               │       1 s/vB    │    GP Ancestor Set Feerate (ASFR):  1    s/vB
    //               │                 │                           P1_ASFR:  9.84 s/vB
    //               │                 │                           P2_ASFR:  2.47 s/vB
    //               │                 │                           C_ASFR: 10.27 s/vB
    // ┌───────────────┐    │   │    ┌──────────────┐
    // │               ├────┘   └────┤              │             ⇒ C_FR < TFR < C_ASFR
    // │   Parent 1    │             │   Parent 2   │
    // │    200 vB     │             │    200 vB    │
    // │  17000 sats   │             │   3000 sats  │
    // │     85 s/vB   │             │     15 s/vB  │
    // │               │             │              │
    // └───────────▲───┘             └───▲──────────┘
    //             │                     │
    //             │    ┌───────────┐    │
    //             └────┤           ├────┘
    //                  │   Child   │
    //                  │  100 vB   │
    //                  │  900 sats │
    //                  │    9 s/vB │
    //                  │           │
    //                  └───────────┘
    //
    // We therefore calculate both the bump fee that is necessary to elevate
    // the individual transaction to the target feerate:
    //         target_feerate × tx_size - tx_fees
    // and the bump fee that is necessary to bump the entire ancestor set to
    // the target feerate:
    //         target_feerate × ancestor_set_size - ancestor_set_fees
    // By picking the maximum from the two, we ensure that a transaction meets
    // both criteria.
    for (const auto& [txid, outpoints] : m_requested_outpoints_by_txid) {
        auto ref_it = m_txid_to_ref.find(txid);
        if (ref_it == m_txid_to_ref.end()) continue;
        
        const auto& tx_ref = ref_it->second;
        
        // Get individual transaction feerate
        auto individual_feerate = m_txgraph->GetIndividualFeerate(tx_ref);
        if (individual_feerate.IsEmpty()) continue;
        
        int64_t individual_size = individual_feerate.size;
        CAmount individual_fee = individual_feerate.fee;
        
        // Get ancestor set using TxGraph
        auto ancestors = m_txgraph->GetAncestors(tx_ref);
        
        // Calculate ancestor set totals (including the transaction itself)
        int64_t ancestor_set_size = individual_size;
        CAmount ancestor_set_fee = individual_fee;
        
        for (auto* ancestor_ref : ancestors) {
            auto ancestor_feerate = m_txgraph->GetIndividualFeerate(*ancestor_ref);
            if (!ancestor_feerate.IsEmpty()) {
                ancestor_set_size += ancestor_feerate.size;
                ancestor_set_fee += ancestor_feerate.fee;
            }
        }
        
        Assume(target_feerate.GetFee(ancestor_set_size) > std::min(individual_fee, ancestor_set_fee));
        CAmount bump_fee_with_ancestors = target_feerate.GetFee(ancestor_set_size) - ancestor_set_fee;
        CAmount bump_fee_individual = target_feerate.GetFee(individual_size) - individual_fee;
        const CAmount bump_fee{std::max(bump_fee_with_ancestors, bump_fee_individual)};
        Assume(bump_fee >= 0);
        for (const auto& outpoint : outpoints) {
            m_bump_fees.emplace(outpoint, bump_fee);
        }
    }
    return m_bump_fees;
}

std::optional<CAmount> MiniMiner::CalculateTotalBumpFees(const CFeeRate& target_feerate)
{
    if (!m_ready_to_calculate) return std::nullopt;
    // Build a block template until the target feerate is hit.
    BuildMockTemplate(target_feerate);

    // All remaining ancestors that are not part of m_in_block must be bumped, but no other relatives
    std::set<uint256> all_ancestor_txids;
    
    for (const auto& [txid, outpoints] : m_requested_outpoints_by_txid) {
        // Skip any ancestors that already have a miner score higher than the target feerate
        // (already "made it" into the block)
        if (m_in_block.count(txid)) continue;
        
        auto ref_it = m_txid_to_ref.find(txid);
        if (ref_it == m_txid_to_ref.end()) continue;
        
        // Get all ancestors using TxGraph
        auto ancestors = m_txgraph->GetAncestors(ref_it->second);
        
        // Add all ancestor txids to the set
        for (auto* ancestor_ref : ancestors) {
            // Find txid for this ancestor ref
            for (const auto& [ancestor_txid, graph_ref] : m_txid_to_ref) {
                if (&graph_ref == ancestor_ref) {
                    all_ancestor_txids.insert(ancestor_txid);
                    break;
                }
            }
        }
    }
    
    // Calculate total size and fee for all unique ancestors
    int64_t ancestor_package_size = 0;
    CAmount ancestor_package_fee = 0;
    
    for (const auto& ancestor_txid : all_ancestor_txids) {
        auto ref_it = m_txid_to_ref.find(ancestor_txid);
        if (ref_it != m_txid_to_ref.end()) {
            auto feerate = m_txgraph->GetIndividualFeerate(ref_it->second);
            if (!feerate.IsEmpty()) {
                ancestor_package_size += feerate.size;
                ancestor_package_fee += feerate.fee;
            }
        }
    }
    
    return target_feerate.GetFee(ancestor_package_size) - ancestor_package_fee;
}
} // namespace node

/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

std::unordered_set<unsigned> specialNodeIDs = {3}; // DummyObjVar's ID is 3

// Helper methods to get successors and predecessors with specific labels
std::unordered_set<unsigned> CFLRGraph::getSuccessors(unsigned src, EdgeLabel label) {
    if (succMap.find(src) != succMap.end() && succMap[src].find(label) != succMap[src].end()) {
        return succMap[src][label];
    }
    return std::unordered_set<unsigned>();
}

std::unordered_set<unsigned> CFLRGraph::getPredecessors(unsigned dst, EdgeLabel label) {
    if (predMap.find(dst) != predMap.end() && predMap[dst].find(label) != predMap[dst].end()) {
        return predMap[dst][label];
    }
    return std::unordered_set<unsigned>();
}

// Check if a node is an object node
bool CFLRGraph::isObjectNode(unsigned node) {
    if (succMap.find(node) != succMap.end()) {
        auto& succLabels = succMap[node];
        if (succLabels.find(Addr) != succLabels.end() && !succLabels[Addr].empty()) {
            return true;
        }
    }
    return false;
}

// Check if a node is a special node
bool CFLRGraph::isSpecialNode(unsigned node) {
    return specialNodeIDs.find(node) != specialNodeIDs.end();
}

// Helper method to add edge and push to worklist if new
void CFLR::addEdgeToWorklist(unsigned src, unsigned dst, EdgeLabel label)
{
    if (!graph->hasEdge(src, dst, label))
    {
        graph->addEdge(src, dst, label);
        workList.push(CFLREdge(src, dst, label));
    }
}

// Apply grammar production rules
void CFLR::applyProductionRules(const CFLREdge& edge)
{
    unsigned src = edge.src;
    unsigned dst = edge.dst;
    EdgeLabel label = edge.label;

    // Rule: p = &a
    // In PAG: a --Addr--> p  =>  p --PT--> a
    if (label == Addr)
    {
        addEdgeToWorklist(dst, src, PT);
    }

    // Rule: p = q (pointer copy propagation)
    // In PAG: p --Copy--> q, creates p --VF--> q
    // If q --PT--> o and p --VF--> q, then p --PT--> o
    
    if (label == PT) // src --PT--> dst (src points-to dst)
    {
        // Find all q where q --VF--> src (src's value copied to q)
        for (unsigned q : graph->getPredecessors(src, VF))
        {
            addEdgeToWorklist(q, dst, PT);
        }
    }

    if (label == VF) // src --VF--> dst (dst's value copied to src)
    {
        // Find all o where dst --PT--> o
        for (unsigned o : graph->getSuccessors(dst, PT))
        {
            addEdgeToWorklist(src, o, PT);
        }
    }
    
    // Rule: (PT)^- ::= Addr VF  =>  (VF)^- (Addr)^- -> (PT)^-
    if (label == AddrBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, VFBar))
        {
            addEdgeToWorklist(mid, src, PTBar);
        }
    }
    
    if (label == VFBar)
    {
        for (unsigned mid : graph->getSuccessors(src, AddrBar))
        {
            addEdgeToWorklist(dst, mid, PTBar);
        }
    }
    
    // Rule: VF ::= VF VF (transitivity)
    if (label == VF)
    {
        // Forward: src --VF--> dst --VF--> next  =>  src --VF--> next
        for (unsigned next : graph->getSuccessors(dst, VF))
        {
            addEdgeToWorklist(src, next, VF);
        }
        // Backward: prev --VF--> src --VF--> dst  =>  prev --VF--> dst
        for (unsigned prev : graph->getPredecessors(src, VF))
        {
            addEdgeToWorklist(prev, dst, VF);
        }
    }
    
    // Rule: (VF)^- ::= (VF)^- (VF)^- (transitivity)
    if (label == VFBar)
    {
        for (unsigned next : graph->getPredecessors(dst, VFBar))
        {
            addEdgeToWorklist(next, src, VFBar);
        }
        for (unsigned prev : graph->getSuccessors(src, VFBar))
        {
            addEdgeToWorklist(dst, prev, VFBar);
        }
    }
    
    // Rule: VF ::= Copy
    if (label == Copy)
    {
        addEdgeToWorklist(src, dst, VF);
    }
    
    // Rule: (VF)^- ::= (Copy)^-
    if (label == CopyBar)
    {
        addEdgeToWorklist(dst, src, VFBar);
    }
    
    // Rule: SV ::= Store VA
    if (label == Store)
    {
        for (unsigned mid : graph->getSuccessors(dst, VA))
        {
            addEdgeToWorklist(src, mid, SV);
        }
    }
    
    if (label == VA)
    {
        for (unsigned mid : graph->getPredecessors(src, Store))
        {
            addEdgeToWorklist(mid, dst, SV);
        }
    }
    
    // Rule: (SV)^- ::= (VA)^- (Store)^-
    if (label == StoreBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, VA))
        {
            addEdgeToWorklist(mid, src, SVBar);
        }
    }
    
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(src, StoreBar))
        {
            addEdgeToWorklist(dst, mid, SVBar);
        }
    }
    
    // Rule: VF ::= SV Load
    if (label == SV)
    {
        for (unsigned mid : graph->getSuccessors(dst, Load))
        {
            addEdgeToWorklist(src, mid, VF);
        }
    }
    
    if (label == Load)
    {
        for (unsigned mid : graph->getPredecessors(src, SV))
        {
            addEdgeToWorklist(mid, dst, VF);
        }
    }
    
    // Rule: (VF)^- ::= (Load)^- (SV)^-
    if (label == LoadBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, SVBar))
        {
            addEdgeToWorklist(mid, src, VFBar);
        }
    }
    
    if (label == SVBar)
    {
        for (unsigned mid : graph->getSuccessors(src, LoadBar))
        {
            addEdgeToWorklist(dst, mid, VFBar);
        }
    }
    
    // Rule: LV ::= (Load)^- VA
    if (label == LoadBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, VA))
        {
            addEdgeToWorklist(mid, src, LV);
        }
    }
    
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(src, LoadBar))
        {
            addEdgeToWorklist(dst, mid, LV);
        }
    }
    
    // Rule: VA ::= LV Load
    if (label == LV)
    {
        for (unsigned mid : graph->getSuccessors(dst, Load))
        {
            addEdgeToWorklist(src, mid, VA);
        }
    }
    
    if (label == Load)
    {
        for (unsigned mid : graph->getPredecessors(src, LV))
        {
            addEdgeToWorklist(mid, dst, VA);
        }
    }
    
    // Rule: PV ::= (PT)^- VA
    if (label == PTBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, VA))
        {
            addEdgeToWorklist(mid, src, PV);
        }
    }
    
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(src, PTBar))
        {
            addEdgeToWorklist(dst, mid, PV);
        }
    }
    
    // Rule: VF ::= PV Load
    if (label == PV)
    {
        for (unsigned mid : graph->getSuccessors(dst, Load))
        {
            addEdgeToWorklist(src, mid, VF);
        }
    }
    
    if (label == Load)
    {
        for (unsigned mid : graph->getPredecessors(src, PV))
        {
            addEdgeToWorklist(mid, dst, VF);
        }
    }
    
    // Rule: (VF)^- ::= (Load)^- (PV)^-
    if (label == LoadBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, PVBar))
        {
            addEdgeToWorklist(mid, src, VFBar);
        }
    }
    
    if (label == PVBar)
    {
        for (unsigned mid : graph->getSuccessors(src, LoadBar))
        {
            addEdgeToWorklist(dst, mid, VFBar);
        }
    }
    
    // Rule: VP ::= VA PT
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(dst, PT))
        {
            addEdgeToWorklist(src, mid, VP);
        }
    }
    
    if (label == PT)
    {
        for (unsigned mid : graph->getPredecessors(src, VA))
        {
            addEdgeToWorklist(mid, dst, VP);
        }
    }
    
    // Rule: VF ::= Store VP
    if (label == Store)
    {
        for (unsigned mid : graph->getSuccessors(dst, VP))
        {
            addEdgeToWorklist(src, mid, VF);
        }
    }
    
    if (label == VP)
    {
        for (unsigned mid : graph->getPredecessors(src, Store))
        {
            addEdgeToWorklist(mid, dst, VF);
        }
    }
    
    // Rule: (VF)^- ::= (VP)^- (Store)^-
    if (label == VPBar)
    {
        for (unsigned mid : graph->getSuccessors(src, StoreBar))
        {
            addEdgeToWorklist(dst, mid, VFBar);
        }
    }
    
    if (label == StoreBar)
    {
        for (unsigned mid : graph->getPredecessors(src, VPBar))
        {
            addEdgeToWorklist(mid, dst, VFBar);
        }
    }
    
    // Rule: VA ::= (VF)^- VA
    if (label == VFBar)
    {
        for (unsigned mid : graph->getPredecessors(dst, VA))
        {
            addEdgeToWorklist(mid, src, VA);
        }
    }
    
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(src, VFBar))
        {
            addEdgeToWorklist(dst, mid, VA);
        }
    }
    
    // Rule: VA ::= VA VF
    if (label == VA)
    {
        for (unsigned mid : graph->getSuccessors(dst, VF))
        {
            addEdgeToWorklist(src, mid, VA);
        }
    }
    
    if (label == VF)
    {
        for (unsigned mid : graph->getPredecessors(src, VA))
        {
            addEdgeToWorklist(mid, dst, VA);
        }
    }
}


int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump("PAG");

    CFLR solver;
    solver.buildGraph(pag);
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // Initialize worklist with existing edges
    for (auto& nodeItr : graph->getSuccessorMap())
    {
        unsigned src = nodeItr.first;
        for (auto& lblItr : nodeItr.second)
        {
            EdgeLabel label = lblItr.first;
            for (unsigned dst : lblItr.second)
            {
                workList.push(CFLREdge(src, dst, label));
            }
        }
    }
    
    // Add epsilon edges for VA (VA ::= epsilon means every node has VA self-loop)
    for (auto& nodeItr : graph->getSuccessorMap())
    {
        unsigned node = nodeItr.first;
        addEdgeToWorklist(node, node, VA);
    }
    
    // Dynamic programming algorithm
    while (!workList.empty())
    {
        CFLREdge edge = workList.pop();
        applyProductionRules(edge);
    }
}
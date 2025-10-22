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
    // An object node is the source of an Addr edge.
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

// Context structure for context-sensitive analysis
struct CallContext {
    unsigned callSite;  // call site ID
    unsigned depth;     // call depth
    
    CallContext(unsigned cs = 0, unsigned d = 0) : callSite(cs), depth(d) {}
    
    bool operator==(const CallContext& other) const {
        return callSite == other.callSite && depth == other.depth;
    }
};

// Hash function for CallContext
namespace std {
    template<>
    struct hash<CallContext> {
        size_t operator()(const CallContext& ctx) const {
            return hash<unsigned>()(ctx.callSite) ^ hash<unsigned>()(ctx.depth);
        }
    };
}

// Context-sensitive edge structure
struct ContextEdge {
    unsigned src;
    unsigned dst;
    EdgeLabel label;
    CallContext context;
    
    ContextEdge(unsigned s, unsigned d, EdgeLabel l, CallContext ctx = CallContext())
        : src(s), dst(d), label(l), context(ctx) {}
    
    bool operator==(const ContextEdge& other) const {
        return src == other.src && dst == other.dst && 
               label == other.label && context == other.context;
    }
};

// Hash function for ContextEdge
namespace std {
    template<>
    struct hash<ContextEdge> {
        size_t operator()(const ContextEdge& edge) const {
            return hash<unsigned>()(edge.src) ^ 
                   hash<unsigned>()(edge.dst) ^ 
                   hash<int>()(edge.label) ^
                   hash<CallContext>()(edge.context);
        }
    };
}
 
 // Apply grammar production rules
 void CFLR::applyProductionRules(const CFLREdge& edge)
 {
     unsigned src = edge.src;
     unsigned dst = edge.dst;
     EdgeLabel label = edge.label;

    // Rule for p = &a. This is represented as a --Addr--> p.
    // This directly implies p --PT--> a.
    if (label == Addr)
    {
        // IMPORTANT: This rule must filter out internal PAG edges like ObjVar(a) --Addr--> ValVar(a),
        // which do NOT represent an address-of operation. A simple and effective way is to ensure
        // the source and destination nodes are not the same.
        if (src != dst && !graph->isSpecialNode(src) && !graph->isSpecialNode(dst)) {
            addEdgeToWorklist(dst, src, PT);
        }
    }

    // Rule for pointer copy propagation (q = p).
    // If p --PT--> a (src --PT--> mid) and p --VF--> q (src --VF--> dst),
    // then q --PT--> a (dst --PT--> mid).
    // This is triggered by new PT or VF edges.

    if (label == PT) // Edge is: src --PT--> dst
    {
        // Find all q where p --VF--> q (src --VF--> next)
        for (unsigned next : graph->getSuccessors(src, VF))
        {

            if (!graph->isSpecialNode(next) && !graph->isSpecialNode(dst))
                addEdgeToWorklist(next, dst, PT);
        }
    }

    if (label == VF) // Edge is: src --VF--> dst
    {
        // Find all a where p --PT--> a (src --PT--> mid)
        for (unsigned mid : graph->getSuccessors(src, PT))
        {

            if (!graph->isSpecialNode(mid) && !graph->isSpecialNode(dst))
                addEdgeToWorklist(dst, mid, PT);
        }
    }
     
     // Rule: (PT)^- ::= Addr VF
     // Which means: (VF)^- (Addr)^- -> (PT)^-
     if (label == AddrBar)
     {
         for (unsigned mid : graph->getPredecessors(dst, VFBar))
         {
             addEdgeToWorklist(mid, src, PTBar);
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
     
     // Rule: (VF)^- ::= (VF)^- (VF)^- (transitivity for bar)
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
     
     // Rule: (SV)^- ::= VA (Store)^-
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
     
     // Rule: (VF)^- ::= (Load)^- VP
     if (label == LoadBar)
     {
         for (unsigned mid : graph->getSuccessors(dst, VP))
         {
             addEdgeToWorklist(src, mid, VFBar);
         }
     }
     
     if (label == VP)
     {
         for (unsigned mid : graph->getPredecessors(src, LoadBar))
         {
             addEdgeToWorklist(mid, dst, VFBar);
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
     
     // Rule: (VF)^- ::= PV (Store)^-
     if (label == PV)
     {
         for (unsigned mid : graph->getSuccessors(dst, StoreBar))
         {
             addEdgeToWorklist(src, mid, VFBar);
         }
     }
     
     if (label == StoreBar)
     {
         for (unsigned mid : graph->getPredecessors(src, PV))
         {
             addEdgeToWorklist(mid, dst, VFBar);
         }
     }
     
     // Rule: VA ::= (VF)^- VA
     if (label == VFBar)
     {
         for (unsigned mid : graph->getPredecessors(dst, VA))
         {
             if (!graph->isSpecialNode(mid) && !graph->isSpecialNode(src))
                 addEdgeToWorklist(mid, src, VA);
         }
     }
     
     if (label == VA)
     {
         for (unsigned mid : graph->getSuccessors(src, VFBar))
         {
             if (!graph->isSpecialNode(mid) && !graph->isSpecialNode(dst))
                 addEdgeToWorklist(dst, mid, VA);
         }
     }
     
     // Rule: VA ::= VA VF
     if (label == VA)
     {
         for (unsigned mid : graph->getSuccessors(dst, VF))
         {
             if (!graph->isSpecialNode(mid) && !graph->isSpecialNode(src))
                 addEdgeToWorklist(src, mid, VA);
         }
     }
     
     if (label == VF)
     {
         for (unsigned mid : graph->getPredecessors(src, VA))
         {
             if (!graph->isSpecialNode(mid) && !graph->isSpecialNode(dst))
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
         if (!graph->isSpecialNode(node))
         {
             addEdgeToWorklist(node, node, VA);
         }
     }
     
     // Dynamic programming algorithm
     while (!workList.empty())
     {
         CFLREdge edge = workList.pop();
         applyProductionRules(edge);
     }
 }

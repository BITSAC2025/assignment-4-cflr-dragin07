/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // Dynamic programming CFL-reachability algorithm
    while (!workList.empty()) {
        CFLREdge edge = workList.pop();
        unsigned src = edge.src;
        unsigned dst = edge.dst;
        EdgeLabel label = edge.label;
        
        auto &succMap = graph->getSuccessorMap();
        auto &predMap = graph->getPredecessorMap();
        
        // Rule 1: Addr ⊆ PT and Addr ⊆ PV
        // p = &o generates both points-to and value relations
        if (label == Addr) {
            if (!graph->hasEdge(src, dst, PT)) {
                graph->addEdge(src, dst, PT);
                workList.push(CFLREdge(src, dst, PT));
            }
            if (!graph->hasEdge(src, dst, PV)) {
                graph->addEdge(src, dst, PV);
                workList.push(CFLREdge(src, dst, PV));
            }
        }
        
        // Rule 2: Copy · PT ⊆ PT
        // p = q, q points-to o => p points-to o
        if (label == Copy) {
            if (succMap.count(dst) && succMap[dst].count(PT)) {
                for (unsigned o : succMap[dst][PT]) {
                    if (!graph->hasEdge(src, o, PT)) {
                        graph->addEdge(src, o, PT);
                        workList.push(CFLREdge(src, o, PT));
                    }
                }
            }
        }
        if (label == PT) {
            if (predMap.count(src) && predMap[src].count(Copy)) {
                for (unsigned x : predMap[src][Copy]) {
                    if (!graph->hasEdge(x, dst, PT)) {
                        graph->addEdge(x, dst, PT);
                        workList.push(CFLREdge(x, dst, PT));
                    }
                }
            }
        }
        
        // Rule 3: PT · Load ⊆ VP
        // x points-to m, load from m to p => value flows from x to p
        if (label == PT) {
            if (succMap.count(dst) && succMap[dst].count(Load)) {
                for (unsigned p : succMap[dst][Load]) {
                    if (!graph->hasEdge(src, p, VP)) {
                        graph->addEdge(src, p, VP);
                        workList.push(CFLREdge(src, p, VP));
                    }
                }
            }
        }
        if (label == Load) {
            if (predMap.count(src) && predMap[src].count(PT)) {
                for (unsigned x : predMap[src][PT]) {
                    if (!graph->hasEdge(x, dst, VP)) {
                        graph->addEdge(x, dst, VP);
                        workList.push(CFLREdge(x, dst, VP));
                    }
                }
            }
        }
        
        // Rule 4: Store · PT ⊆ SV
        // p stores q, q points-to o => intermediate store-value relation
        if (label == Store) {
            if (succMap.count(dst) && succMap[dst].count(PT)) {
                for (unsigned o : succMap[dst][PT]) {
                    if (!graph->hasEdge(src, o, SV)) {
                        graph->addEdge(src, o, SV);
                        workList.push(CFLREdge(src, o, SV));
                    }
                }
            }
        }
        if (label == PT) {
            if (predMap.count(src) && predMap[src].count(Store)) {
                for (unsigned x : predMap[src][Store]) {
                    if (!graph->hasEdge(x, dst, SV)) {
                        graph->addEdge(x, dst, SV);
                        workList.push(CFLREdge(x, dst, SV));
                    }
                }
            }
        }
        
        // Rule 5: PT · SV ⊆ PV
        // p points-to m, p has store-value o => m has pointer-value o
        if (label == PT) {
            if (succMap.count(src) && succMap[src].count(SV)) {
                for (unsigned o : succMap[src][SV]) {
                    if (!graph->hasEdge(dst, o, PV)) {
                        graph->addEdge(dst, o, PV);
                        workList.push(CFLREdge(dst, o, PV));
                    }
                }
            }
        }
        if (label == SV) {
            if (succMap.count(src) && succMap[src].count(PT)) {
                for (unsigned m : succMap[src][PT]) {
                    if (!graph->hasEdge(m, dst, PV)) {
                        graph->addEdge(m, dst, PV);
                        workList.push(CFLREdge(m, dst, PV));
                    }
                }
            }
        }
        
        // Rule 6: VP · PV ⊆ PT
        // value flows to p through x, x has pointer-value o => p points-to o
        if (label == VP) {
            if (succMap.count(dst) && succMap[dst].count(PV)) {
                for (unsigned o : succMap[dst][PV]) {
                    if (!graph->hasEdge(src, o, PT)) {
                        graph->addEdge(src, o, PT);
                        workList.push(CFLREdge(src, o, PT));
                    }
                }
            }
        }
        if (label == PV) {
            if (predMap.count(src) && predMap[src].count(VP)) {
                for (unsigned x : predMap[src][VP]) {
                    if (!graph->hasEdge(x, dst, PT)) {
                        graph->addEdge(x, dst, PT);
                        workList.push(CFLREdge(x, dst, PT));
                    }
                }
            }
        }
    }
}
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
    // 收集所有节点并初始化工作表
    std::unordered_set<unsigned> allNodes;
    
    // 将图中所有已存在的边加入工作表
    for (auto &nodeItr : graph->getSuccessorMap())
    {
        unsigned src = nodeItr.first;
        allNodes.insert(src);
        
        for (auto &lblItr : nodeItr.second)
        {
            EdgeLabel label = lblItr.first;
            for (auto dst : lblItr.second)
            {
                allNodes.insert(dst);
                workList.push(CFLREdge(src, dst, label));
            }
        }
    }
    
    // 辅助 lambda 函数：添加边（如果不存在则加入图和工作表）
    auto addEdge = [this](unsigned src, unsigned dst, EdgeLabel label) {
        if (!graph->hasEdge(src, dst, label))
        {
            graph->addEdge(src, dst, label);
            workList.push(CFLREdge(src, dst, label));
        }
    };
    
    // 为每个节点添加 epsilon 边（VF, VFBar, VA）
    for (auto node : allNodes)
    {
        addEdge(node, node, VF);
        addEdge(node, node, VFBar);
        addEdge(node, node, VA);
    }
    
    // 主循环：动态规划 CFL 可达性算法
    while (!workList.empty())
    {
        CFLREdge edge = workList.pop();
        unsigned x = edge.src;
        unsigned z = edge.dst;
        EdgeLabel label = edge.label;
        
        auto &succMap = graph->getSuccessorMap();
        auto &predMap = graph->getPredecessorMap();
        
        // 应用语法规则 A ::= B C
        // 情况1: 新边是 B (x -B-> z)，找所有 z -C-> w，添加 x -A-> w
        // 情况2: 新边是 C (x -C-> z)，找所有 y -B-> x，添加 y -A-> z
        
        // PT ::= VFBar AddrBar
        if (label == VFBar && succMap.count(z) && succMap[z].count(AddrBar))
        {
            for (auto w : succMap[z][AddrBar])
                addEdge(x, w, PT);
        }
        if (label == AddrBar && predMap.count(x) && predMap[x].count(VFBar))
        {
            for (auto y : predMap[x][VFBar])
                addEdge(y, z, PT);
        }
        
        // PTBar ::= Addr VF
        if (label == Addr && succMap.count(z) && succMap[z].count(VF))
        {
            for (auto w : succMap[z][VF])
                addEdge(x, w, PTBar);
        }
        if (label == VF && predMap.count(x) && predMap[x].count(Addr))
        {
            for (auto y : predMap[x][Addr])
                addEdge(y, z, PTBar);
        }
        
        // VF ::= VF VF
        if (label == VF)
        {
            if (succMap.count(z) && succMap[z].count(VF))
            {
                for (auto w : succMap[z][VF])
                    addEdge(x, w, VF);
            }
            if (predMap.count(x) && predMap[x].count(VF))
            {
                for (auto y : predMap[x][VF])
                    addEdge(y, z, VF);
            }
        }
        
        // VF ::= Copy
        if (label == Copy)
        {
            addEdge(x, z, VF);
        }
        
        // VF ::= SV Load
        if (label == SV && succMap.count(z) && succMap[z].count(Load))
        {
            for (auto w : succMap[z][Load])
                addEdge(x, w, VF);
        }
        if (label == Load && predMap.count(x) && predMap[x].count(SV))
        {
            for (auto y : predMap[x][SV])
                addEdge(y, z, VF);
        }
        
        // VF ::= PV Load
        if (label == PV && succMap.count(z) && succMap[z].count(Load))
        {
            for (auto w : succMap[z][Load])
                addEdge(x, w, VF);
        }
        if (label == Load && predMap.count(x) && predMap[x].count(PV))
        {
            for (auto y : predMap[x][PV])
                addEdge(y, z, VF);
        }
        
        // VF ::= Store VP
        if (label == Store && succMap.count(z) && succMap[z].count(VP))
        {
            for (auto w : succMap[z][VP])
                addEdge(x, w, VF);
        }
        if (label == VP && predMap.count(x) && predMap[x].count(Store))
        {
            for (auto y : predMap[x][Store])
                addEdge(y, z, VF);
        }
        
        // VFBar ::= VFBar VFBar
        if (label == VFBar)
        {
            if (succMap.count(z) && succMap[z].count(VFBar))
            {
                for (auto w : succMap[z][VFBar])
                    addEdge(x, w, VFBar);
            }
            if (predMap.count(x) && predMap[x].count(VFBar))
            {
                for (auto y : predMap[x][VFBar])
                    addEdge(y, z, VFBar);
            }
        }
        
        // VFBar ::= CopyBar
        if (label == CopyBar)
        {
            addEdge(x, z, VFBar);
        }
        
        // VFBar ::= LoadBar SVBar
        if (label == LoadBar && succMap.count(z) && succMap[z].count(SVBar))
        {
            for (auto w : succMap[z][SVBar])
                addEdge(x, w, VFBar);
        }
        if (label == SVBar && predMap.count(x) && predMap[x].count(LoadBar))
        {
            for (auto y : predMap[x][LoadBar])
                addEdge(y, z, VFBar);
        }
        
        // VFBar ::= LoadBar VP
        if (label == LoadBar && succMap.count(z) && succMap[z].count(VP))
        {
            for (auto w : succMap[z][VP])
                addEdge(x, w, VFBar);
        }
        if (label == VP && predMap.count(x) && predMap[x].count(LoadBar))
        {
            for (auto y : predMap[x][LoadBar])
                addEdge(y, z, VFBar);
        }
        
        // VFBar ::= PV StoreBar
        if (label == PV && succMap.count(z) && succMap[z].count(StoreBar))
        {
            for (auto w : succMap[z][StoreBar])
                addEdge(x, w, VFBar);
        }
        if (label == StoreBar && predMap.count(x) && predMap[x].count(PV))
        {
            for (auto y : predMap[x][PV])
                addEdge(y, z, VFBar);
        }
        
        // VA ::= LV Load
        if (label == LV && succMap.count(z) && succMap[z].count(Load))
        {
            for (auto w : succMap[z][Load])
                addEdge(x, w, VA);
        }
        if (label == Load && predMap.count(x) && predMap[x].count(LV))
        {
            for (auto y : predMap[x][LV])
                addEdge(y, z, VA);
        }
        
        // VA ::= VFBar VA
        if (label == VFBar && succMap.count(z) && succMap[z].count(VA))
        {
            for (auto w : succMap[z][VA])
                addEdge(x, w, VA);
        }
        if (label == VA && predMap.count(x) && predMap[x].count(VFBar))
        {
            for (auto y : predMap[x][VFBar])
                addEdge(y, z, VA);
        }
        
        // VA ::= VA VF
        if (label == VA && succMap.count(z) && succMap[z].count(VF))
        {
            for (auto w : succMap[z][VF])
                addEdge(x, w, VA);
        }
        if (label == VF && predMap.count(x) && predMap[x].count(VA))
        {
            for (auto y : predMap[x][VA])
                addEdge(y, z, VA);
        }
        
        // SV ::= Store VA
        if (label == Store && succMap.count(z) && succMap[z].count(VA))
        {
            for (auto w : succMap[z][VA])
                addEdge(x, w, SV);
        }
        if (label == VA && predMap.count(x) && predMap[x].count(Store))
        {
            for (auto y : predMap[x][Store])
                addEdge(y, z, SV);
        }
        
        // SVBar ::= VA StoreBar
        if (label == VA && succMap.count(z) && succMap[z].count(StoreBar))
        {
            for (auto w : succMap[z][StoreBar])
                addEdge(x, w, SVBar);
        }
        if (label == StoreBar && predMap.count(x) && predMap[x].count(VA))
        {
            for (auto y : predMap[x][VA])
                addEdge(y, z, SVBar);
        }
        
        // PV ::= PTBar VA
        if (label == PTBar && succMap.count(z) && succMap[z].count(VA))
        {
            for (auto w : succMap[z][VA])
                addEdge(x, w, PV);
        }
        if (label == VA && predMap.count(x) && predMap[x].count(PTBar))
        {
            for (auto y : predMap[x][PTBar])
                addEdge(y, z, PV);
        }
        
        // VP ::= VA PT
        if (label == VA && succMap.count(z) && succMap[z].count(PT))
        {
            for (auto w : succMap[z][PT])
                addEdge(x, w, VP);
        }
        if (label == PT && predMap.count(x) && predMap[x].count(VA))
        {
            for (auto y : predMap[x][VA])
                addEdge(y, z, VP);
        }
        
        // LV ::= LoadBar VA
        if (label == LoadBar && succMap.count(z) && succMap[z].count(VA))
        {
            for (auto w : succMap[z][VA])
                addEdge(x, w, LV);
        }
        if (label == VA && predMap.count(x) && predMap[x].count(LoadBar))
        {
            for (auto y : predMap[x][LoadBar])
                addEdge(y, z, LV);
        }
    }
}

/**
 * A4Header.h
 * @author kisslune 
 */

#ifndef ANSWERS_A4HEADER_H
#define ANSWERS_A4HEADER_H

#include <utility>

#include "SVF-LLVM/SVFIRBuilder.h"

using EdgeLabel = unsigned;

enum EdgeLabelType
{
    Addr, AddrBar,
    Copy, CopyBar,
    Store, StoreBar,
    Load, LoadBar,
    PT, PTBar,
    SV, SVBar,
    PV, PVBar,
    VP, VPBar,
    VF, VFBar,
    VA, VABar,
    LV, LVBar,
};


/**
 * The edge type of CFL-reachability
 */
struct CFLREdge
{
    unsigned src;   // source
    unsigned dst;   // target
    EdgeLabel label;

    CFLREdge(unsigned src, unsigned dst, EdgeLabel lbl) :
            src(src), dst(dst), label(lbl)
    {}

    inline bool operator<(const CFLREdge &rhs) const
    {
        if (src != rhs.src) return src < rhs.src;
        if (dst != rhs.dst) return dst < rhs.dst;
        return label < rhs.label;
    }

    inline bool operator==(const CFLREdge &rhs) const
    {
        return (src == rhs.src) && (dst == rhs.dst) && (label == rhs.label);
    }
};


template<>
struct std::hash<CFLREdge>
{
    size_t operator()(const CFLREdge &edge) const
    { return ((uint64_t) edge.src << 32) | (uint64_t) edge.dst; }
};


/**
 * The graph for CFL-reachability-based pointer analysis
 */
class CFLRGraph
{
public:
    /// We use a source -> label -> target map to represent the adjacency list of the predecessors/successors of nodes.
    using DataMap = std::unordered_map<unsigned, std::unordered_map<EdgeLabel, std::unordered_set<unsigned>>>;

    /// Construct a graph from a PAG
    explicit CFLRGraph(SVF::SVFIR *pag);

    /**
     * Check whether an edge is already in the graph
     * @param src the source node of the edge
     * @param dst the target node of the edge
     * @param label the label of the edge
     * @return true of the edge already exists, false otherwise
     */
    bool hasEdge(unsigned src, unsigned dst, EdgeLabel label);

    /**
     * Add an edge to the graph
     * @param src the source node of the edge
     * @param dst the target node of the edge
     * @param label the label of the edge
     */
    void addEdge(unsigned src, unsigned dst, EdgeLabel label);

    DataMap &getSuccessorMap()
    { return succMap; }

    DataMap &getPredecessorMap()
    { return predMap; }
    
    /**
     * Get all successor nodes with a specific edge label
     * @param src the source node
     * @param label the edge label
     * @return a set of successor nodes
     */
    std::unordered_set<unsigned> getSuccessors(unsigned src, EdgeLabel label);

    /**
     * Get all predecessor nodes with a specific edge label
     * @param dst the destination node
     * @param label the edge label
     * @return a set of predecessor nodes
     */
    std::unordered_set<unsigned> getPredecessors(unsigned dst, EdgeLabel label);
    
    /**
     * Check if a node is an object node
     * @param node the node to check
     * @return true if the node is an object node, false otherwise
     */
    bool isObjectNode(unsigned node);
    
    /**
     * Check if a node is a special node (like DummyObjVar)
     * @param node the node to check
     * @return true if the node is a special node, false otherwise
     */
    bool isSpecialNode(unsigned node);

protected:
    DataMap predMap;   // holding predecessors
    DataMap succMap;   // holding successors
};


/**
 * FIFO worklist
 */
template<class T>
class WorkList
{
public:
    /// Check whether the worklist is empty.
    inline bool empty() const
    { return data_list.empty(); }

    /// Clear the worklist
    inline void clear()
    {
        data_list.clear();
        data_set.clear();
    }

    /// Push a data into the END work list.
    inline bool push(const T &data)
    {
        if (data_set.find(data) == data_set.end())
        {
            this->data_list.push_back(data);
            this->data_set.insert(data);
            return true;
        }
        else
            return false;
    }

    /// Pop a data from the FRONT of work list.
    inline T pop()
    {
        assert(!this->empty() && "work list is empty");
        T data = this->data_list.front();
        this->data_list.pop_front();
        this->data_set.erase(data);
        return data;
    }

protected:
    std::unordered_set<T> data_set;       ///< to avoid duplicate elements
    std::deque<T> data_list;     ///< to access the elements at both the beginning and the end
};


/**
 * CFL-reachability implementation
 */
class CFLR
{
    WorkList<CFLREdge> workList;
    CFLRGraph *graph;

public:
    CFLR() : graph(nullptr)
    {}

    ~CFLR()
    { delete graph; }

    /// Build a graph from PAG
    void buildGraph(SVF::PAG *pag);

    void addEdgeToWorklist(unsigned src, unsigned dst, EdgeLabel label);
    void applyProductionRules(const CFLREdge& edge);
    
    /// The dynamic-programming CFL-reachability algorithm.
    void solve();
    /// Dump results into a file
    void dumpResult();
};

#endif //ANSWERS_A4HEADER_H

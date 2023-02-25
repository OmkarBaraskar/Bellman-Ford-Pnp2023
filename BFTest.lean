import BellmanFord
import SPFA
import Graph


namespace Graph

----------Construction of Graph----------

def g_array : Array Nat := #[1,2,3,4,5]

def g : Graph Nat Int := makeGraphFromArray g_array

/-It takes a graph g and a array of edges (of form ((u,v),weight of edge u to v)) as input and outputs a graph with these array of edges-/
private def adding_edges_by_arrays {α : Type} (g : Graph α Int) (as : Array (Array Nat × Int)) : Graph α Int := Id.run do
    let mut ret : Graph α Int := g
    for i in as do
        ret := addEdgeByID ret (i.fst[0]!-1) (i.fst[1]!-1) i.snd 
    ret
def g_final := adding_edges_by_arrays g (#[(#[1,2],5),(#[2,1],-2),(#[3,2],7),(#[4,3],9),(#[1,4],8),(#[1,3],-4),(#[5,1],6),(#[5,4],7),(#[3,5],2),(#[4,2],-3)])

#eval g_final ---For better visualisaton of the graph refer to Fig 24.4 of Introduction to Algorithms (CLRS)


<<<<<<< HEAD
----------End of Construction of Graph----------

----------Testing----------
=======
def w1 := BellmanFord g_final 4
>>>>>>> b6002c20edee006ebefd83467e6c77fa4ff83897


def BF_weight_array := BellmanFord g_final 4

def BF_shortest_path := BFShortestPath g_final 1 2

def SPFA_weight_array := SPFA g_final 4


#eval BF_weight_array ---weight array
#eval BF_shortest_path --- shortest path from to source to target
#eval SPFA_weight_array --- weight array from a slightly optimised BF algorithm

---Dynamic Allocation testing---

/-Removing the edge (0,1) with weight 5-/
def g_final_mod := removeAllEdgesFromTo g_final 0 1

def BF_weight_array_mod := BellmanFord g_final_mod 4

/-Dynamically adding edge back-/
def BF_weight_array_dyn := (BF_dynamic_edgeAdd g_final_mod BF_weight_array_mod ⟨ 0, 1, 5 ⟩).2

#eval BF_weight_array_dyn

---End of Dynamic Allocation testing---


----------End of Testing----------

end Graph
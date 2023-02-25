import BellmanFord
import SPFA
import Graph


namespace Graph
def g_array : Array Nat := #[1,2,3,4,5]

def g : Graph Nat Int := makeGraphFromArray g_array

def adding_edges_by_arrays (g : Graph Nat Int) (as : Array (Array Nat × Int)) : Graph Nat Int := Id.run do
    let mut ret : Graph Nat Int := g
    for i in as do
        ret := addEdgeByID ret (i.fst[0]!-1) (i.fst[1]!-1) i.snd 
    ret
def g_final := adding_edges_by_arrays g (#[(#[1,2],5),(#[2,1],-2),(#[3,2],7),(#[4,3],9),(#[1,4],8),(#[1,3],-4),(#[5,1],6),(#[5,4],7),(#[3,5],2),(#[4,2],-3)])

#eval g_final 

#eval g_final.edgeCount

#eval Bellman_Ford_Aux g_final 4 (mkArray g.vertexCount default) 4

def w1 := BellmanFord! g_final 4

def dynamic_edge_addition (g : Graph Nat Int) (w: Array BFVertex) (source : Nat) (edge : Nat × Nat × Int) : Graph Nat Int × Array BFVertex :=
    let g_updated := addEdgeByID g edge.1 edge.2.1 edge.2.2
    ⟨ g_updated, (Bellman_Ford_Aux g_updated source w) 1⟩ 

def g_final_1 := adding_edges_by_arrays g (#[(#[1,2],5),(#[2,1],-2),(#[3,2],7),(#[4,3],9),(#[1,4],8),(#[1,3],-4),(#[5,1],6),(#[5,4],7),(#[3,5],2)])

def w2 :=  dynamic_edge_addition g_final_1 w1 4 (4,2,-3)

#eval w2

def dynamic_vertex_addition (g : Graph Nat Int) (w: Array BFVertex) (source : Nat) (vertex : Vertex Nat Nat) : Graph Nat Int × Array BFVertex := 
    let g_updated := (addVertex g vertex.payload).fst  
    ⟨ g_updated, (Bellman_Ford_Aux g_updated source w) 1⟩

#eval BellmanFord g_final 4
#eval BFShortestPath g_final 4 3
#eval SPFA g_final 4
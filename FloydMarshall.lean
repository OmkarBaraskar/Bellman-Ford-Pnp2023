import Mathlib

import Graph.Graph

namespace Graph

variable {α : Type} [Inhabited α]

structure FMArray (β : Type) (g : Graph α β) where
  distance : Array (Array (Option β)) 
  predecessor : Array (Array (Option Nat)) 

def nan_matrix (β : Type) (rank : Nat) : Array (Array (Option β)) := mkArray rank (mkArray rank none)  

----------Getting the Adjacency Matrix-----------

def ToAdjancencyMatrix (g : Graph α Int) : Array (Array (Option Int)) := Id.run do
    let mut ret : Array (Array (Option Int)) := nan_matrix Int g.vertexCount
    for i in [0:g.vertexCount] do
        for edge in (g.vertices[i]!).adjacencyList do
            ret := ret.set! i ((ret[i]!).set! edge.target edge.weight)
        ret := ret.set! i ((ret[i]!).set! i (some 0))
    ret

----------End Of Getting the Adjacency Matrix----------

----------Floyd Marshall Algorithm----------

private def UpdateFMArray (g : Graph α Int) (FMTree : FMArray Int g) (k : Nat) : FMArray Int g := Id.run do
    let mut ret := FMTree
    for i in [0:g.vertexCount] do
        for j in [0:g.vertexCount] do
            ret := ⟨ ret.distance.set! i (ret.distance[i]!.set! j (
              match (FMTree.distance[i]!)[j]!, (FMTree.distance[i]!)[k]!, (FMTree.distance[k]!)[j]! with
              | some x, some y, some z => some (min x (y+z))
              | some x, _, _ => some x
              | _, some y, some z => some (y + z)
              | _, _, _ => none
           )),  
             ret.predecessor.set! i ((ret.predecessor[i]!).set! j (
              match (ret.distance[i]!)[j]!, (ret.distance[i]!)[k]!, (ret.distance[k]!)[j]! with
              | some x, some y, some z => if x > y + z then (FMTree.predecessor[k]!)[j]! else (FMTree.predecessor[i]!)[j]! 
              | none, some _, some _ => (FMTree.predecessor[k]!)[j]! 
              | some _, _, _ => (FMTree.predecessor[i]!)[j]!
              | _, _, _ => none
            ))⟩ 
    ret

private def FMArrayAux (g : Graph α Int) (FMTree : FMArray Int g) : Nat → FMArray Int g
    | 0 => FMTree
    | k + 1 => UpdateFMArray g (FMArrayAux g FMTree k) k

def FloydMarshall (g : Graph α Int) : FMArray Int g := Id.run do
    let mut ret_pred : Array (Array (Option Nat)) := nan_matrix Nat g.vertexCount ---Predecessor Matrix
    let ret_dis := ToAdjancencyMatrix g ---Distance Matrix
    for i in [0:g.vertexCount] do
        for j in [0:g.vertexCount] do
            ret_pred := 
            match (ret_dis[i]!)[j]! with 
            | none => ret_pred 
            | some 0 => ret_pred 
            | _ => ret_pred.set! i  ((ret_pred[i]!).set! j i)        
    FMArrayAux g ⟨ ret_dis, ret_pred ⟩ g.vertexCount   

----------End Of Floyd Marshall Algorithm----------

----------Testing----------

/-Graph Construction-/
def g_array : Array Nat := #[1,2,3,4,5]

def g : Graph Nat Int := makeGraphFromArray g_array

/-It takes a graph g and a array of edges (of form ((u,v),weight of edge u to v)) as input and outputs a graph with these array of edges-/
private def adding_edges_by_arrays {α : Type} (g : Graph α Int) (as : Array (Array Nat × Int)) : Graph α Int := Id.run do
    let mut ret : Graph α Int := g
    for i in as do
        ret := addEdgeByID ret (i.fst[0]!-1) (i.fst[1]!-1) i.snd 
    ret
def g_final := adding_edges_by_arrays g (#[(#[1,2],3),(#[1,5],-4),(#[1,3],8),(#[2,4],1),(#[2,5],7),(#[3,2],4),(#[4,1],2),(#[4,3],-5),(#[5,4],6)])

#eval g_final ---For better visualisaton of the graph refer to Fig 25.1 of Introduction to Algorithms (CLRS)

/-Testing Floyd Marshall Algorithm-/

def FMObject := FloydMarshall g_final

#eval ToAdjancencyMatrix g_final 
#eval FMObject.distance ---To check this check Fig. 25.4 of Introduction to Algorithms (CLRS)
#eval FMObject.predecessor

----------End Of Testing----------
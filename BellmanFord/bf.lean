import BellmanFord.Graph_theorems
import Mathlib

namespace Graph

structure BFVertex where --BFVertices so we just make one array of BFVertex for output rather than two arrays (Distance and PRedecessor)
  predecessor : Nat
  distance : Option Int := none

instance : ToString BFVertex where toString dv := "Predecessor: " ++ (toString dv.predecessor) ++ ", current distance: " ++ (toString dv.distance) ++ "\n"
instance : Inhabited BFVertex := ⟨ { predecessor := default } ⟩

def relax_edge (BFList : List BFVertex) (edge : Edge Int) (hyp : edge.source < BFList.length ∧ edge.target < BFList.length) : List BFVertex :=
  match (BFList[edge.source]'(hyp.1)).distance with
  | none => BFList
  | some u => match (BFList[edge.target]'(hyp.2)).distance with
              | none => BFList.set edge.target {predecessor := edge.source, distance := u + edge.weight}
              | some v => if v > u + edge.weight then
                            BFList.set edge.target {predecessor := edge.source, distance := u + edge.weight}
                          else BFList

def relax (g : Graph α Int) (BFn : List BFVertex) (counter : Nat) : List BFVertex := 
  let edges : List (Edge Int) := g.getAllEdges
  match counter with
  | 0 => BFn
  | n + 1 => let BFnplus1 : List BFVertex := edges.foldl (λ bflist edge => 
                                                                           have hyp1: edge.source < bflist.length := by sorry
                                                                           have hyp2: edge.target < bflist.length := by sorry
                                                                           have hyp: edge.source < bflist.length ∧ edge.target < bflist.length := by 
                                                                            apply And.intro
                                                                            · assumption
                                                                            · assumption
                                                                           relax_edge bflist edge hyp) BFn
             relax g BFnplus1 n

def BellmanFord (g : Graph α Int) (source : Nat) : List BFVertex :=
  let init : List BFVertex := g.vertices.foldl (λ bfver _ => bfver ++ [{predecessor := source}]) []
  let BF0 : List BFVertex := init.set source {predecessor := source, distance := some 0}
  let BFdone : List BFVertex := relax g BF0 (g.vertexCount - 1)
  BFdone
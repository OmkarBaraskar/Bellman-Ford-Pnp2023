import BellmanFord.BellmanFord
import Graph
namespace Graph

/- Approach for SPFA

We want to take a (Graph α Int) i.e. a graph with payloads of type α and weights of type Int and a source
vertex (type is ℕ because vertices are identified by their indices in Graph.vertices) and output an array
of Nat (the ith entry is the predecessor of vertex i) and an array of Int (the ith entry is the shortest
distance between i and source).

------Algorithm--------
Initialize the output Distance and Predecessor arrays to infinity and null respectively (Distance from the
source itself is, of course, zero). Also, have a queue Q. Add source to Q and now, while Q is not empty,
pop the first element out of the queue and then relax each edge in the adjacency list of this element (which
is a vertex). Also, add the other vertex along each edge to Q if its not already in it. As mentioned before
repeat this until Q is empty.

If this algorithm terminates, the Distance and Predecessor arrays will represent the shortest path distances 
from source and the predecessor along this path for each vertex respectively.

The algorithm, however, does not terminate if there are negative cycles in the graph.
-------End of Algorithm--------

-/
variable {α : Type} [Inhabited α]

private def SPFAAux (g : Graph α Int) (current : Nat) (queue : List Nat) (BFVerticesTemp : Array (BFVertex)) : Array (BFVertex) :=

  if not queue.isEmpty then Id.run do
    let mut queueUpdate : List Nat := queue.erase current
    let mut BFVertices : Array BFVertex := BFVerticesTemp
    for edge in g.vertices[current]!.adjacencyList do
      let tentativeDistance : Int := match BFVertices[current]!.distance with
        | some x => x + edge.weight
        | none => panic! "Not possible!"
      let newBFVertex : BFVertex := {predecessor := current, distance := tentativeDistance, edgeWeightToPredecessor := edge.weight} -- new BFVertex to represent edge.target
      queueUpdate := match BFVertices[edge.target]!.distance with
        | some x => if tentativeDistance < x then if not (queueUpdate.contains edge.target) then (queueUpdate.concat edge.target) else queueUpdate else queueUpdate
        | none => queueUpdate.concat edge.target
      BFVertices := match BFVertices[edge.target]!.distance with
        | some x => if tentativeDistance < x then BFVertices.set! edge.target newBFVertex else BFVertices
        | none => BFVertices.set! edge.target newBFVertex
      
    let BFVerticesUpdated : Array BFVertex := match queueUpdate with
      | [] => BFVertices
      | head::tail => SPFAAux g queueUpdate[0]! queueUpdate BFVertices
    BFVerticesUpdated
  else
    BFVerticesTemp
decreasing_by sorry

private def SPFAAuxBase (g : Graph α Int) (source : Nat) : Array (BFVertex) :=
  let BFVerticesInitial : Array (BFVertex) := mkArray g.vertexCount {predecessor := source} 
  if h : source < BFVerticesInitial.size then
    let BFVertices := BFVerticesInitial.set ⟨source, h⟩ {predecessor := source, distance := some 0}
    let queue : List Nat := Id.run do
      let mut temp : List Nat := []
      temp := temp.concat source
      temp
    let BFVerticesUpdated := SPFAAux g source queue BFVertices
    BFVerticesUpdated
  else
      panic! "source out of bounds"

def SPFA (g : Graph α Int) (source : Nat) : BFShortestPathTree := ⟨ (SPFAAuxBase g source) ⟩
--------------------------------------------
----------------------------------------------

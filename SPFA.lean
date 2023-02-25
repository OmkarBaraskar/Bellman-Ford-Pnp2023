import BellmanFord
import Graph
namespace Graph

/- Approach for SPFA

We want to take a (Graph α Int) i.e. a graph with payloads of type α and weights of type Int and a source
vertex (type is ℕ because vertices are identified by their indices in Graph.vertices) and output an array
of Nat (the ith entry is the predecessor of vertex i) and an array of Int (the ith entry is the shortest
distance between i and source).

------Algorithm--------
Initialize the output Distance and Predecessor arrays to infinity and null respectively (Distance from the
source itself is, of course, zero). Then, for each edge (u, v) with weight w, we check if 
distance[v] > distance[u] + w. If so, set distance[v] to (distance[u] + w) and set predecessor[v] to u.
Repeat this |V| - 1 times, where |V| is the number of vertices in the graph.

Note that if the graph is disconnected, every vertex 'i' in a connected component not containing the source 
will have Distance[i] = ∞.

Now, on to negative cycle detection. For this, we go through every edge (u, v) with weight w in the graph
and check if distance[u] + w < distance[v]. If so, let us have an array called NegativeEdges := [v, u].

Now, check if for any edge (NegativeEdge[0], v) with weight w from the first element of NegativeEdges,
we have distance[NegativeEdge[0]] + w < distance[v]. If so, add this vertex v to the beginning of
NegativeEdges. Repeat this |V| - 1 times.

Now that NegativeEdges is populated with the vertices forming a negative weight cycle, we run a cycle
detection algorithm on NegativeEdges and report it.

If there are no negative cycles detected, we return Distance and Predecessor.
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
  let BFVerticesInitial : Array (BFVertex) := mkArray g.vertexCount {predecessor := source} -- predecessor is only a placeholder here, it has no significance and will be replaced or not used
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

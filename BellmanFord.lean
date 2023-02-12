import Graph.Dijkstra

namespace Graph

def hello := "world"

-- Trying random stuff from Graph.Graph -----------------

def emptyGraph : Graph Nat Nat := empty

def array1 : Array Nat := #[0, 0, 0, 0]

def graph_with_4_vertices : Graph Nat Nat := makeGraphFromArray array1

def num : Int := 0

#eval graph_with_4_vertices
#eval graph_with_4_vertices.hasNoEdges
#eval graph_with_4_vertices.hasNoVertices

#eval addEdgeByID graph_with_4_vertices 0 3 3

def n : Option Nat:= some 2
#check n

----------------------------------------------------------

/- Approach for Bellman-Ford

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


Have a look at Graph.Dijkstra.

```lean
def BellmanFord (g : Graph α Int) : Array Nat × Array Int :=
  sorry
```
This will probably not be what the actual implementation of Bellman-Ford looks like, but its here for
now.
-/

/-!
## Bellman-Ford Algorithm

We'll be using copies of ShortestPathTree and DijkstraVertex structures defined in Graph.Dijkstra since
they fit the structres needed for Bellman-Ford nicely as well. We define BFVertex based on the 
DijkstraVertex structure due to the fact that it requires Nat edge weights while we are dealing with Int
edge weights. Similarly, BFShortestPathTree since it needs Array DijktraVertex rather than Array 
BFVertex.
!-/

variable {α : Type} [Inhabited α] -- generic Type for the payloads of the vertices. never comes up


----------BFVertex---------------------
structure BFVertex where --BFVertices so we just make one array of BFVertex for output rather than two arrays (Distance and PRedecessor)
  predecessor : Nat
  distance : Option Int := none
  edgeWeightToPredecessor : Int := 0

instance : ToString BFVertex where toString dv := "Predecessor: " ++ (toString dv.predecessor) ++ ", current distance: " ++ (toString dv.distance) ++ "\n"
instance : Inhabited BFVertex := ⟨ { predecessor := default } ⟩
----------End of BFVertex---------------

----------BFShortestPathTree------------
structure BFShortestPathTree where
  BFVertices : Array BFVertex

namespace BFShortestPathTree

instance : ToString BFShortestPathTree where toString t := toString t.BFVertices

/-- Returns the distance from the root of the tree to a specific node. -/
def distanceToVertex (t : BFShortestPathTree) (id : Nat) : Option Int := t.BFVertices[id]!.distance

end BFShortestPathTree
----------End of BFShortestPathTree-----

----------BFAlgo------------------------
-- private def BFAuxBase (g : Graph α Int) (source : Nat) (target : Option Nat) : Array (DijkstraVertex) :=
--   let dijkstraVerticesInitial : Array (DijkstraVertex) := mkArray g.vertexCount {predecessor := source} -- predecessor is only a placeholder here, it has no significance and will be replaced or not used
--   if h : source < dijkstraVerticesInitial.size then
--     let dijkstraVertices := dijkstraVerticesInitial.set ⟨source, h⟩ {predecessor := source, distance := some 0}
--     let isTargetFound : Bool := match target with
--       | some t => t == source
--       | none => false
--     if isTargetFound then dijkstraVertices
--     else
--       let unvisitedSet : Lean.HashSet Nat := Id.run do
--         let mut temp : Lean.HashSet Nat := Lean.HashSet.empty
--         for i in g.getAllVertexIDs do temp := temp.insert i
--         temp
--       dijkstraAux g source target (unvisitedSet.erase source) dijkstraVertices (unvisitedSet.size-1)
--   else
--       panic! "source out of bounds"

-- def BellmanFord (g : Graph α Int) (source : Nat) : ShortestPathTree := (BFAuxBase g source none)
-------------End of BFAlgo---------------
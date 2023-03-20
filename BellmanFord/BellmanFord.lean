import Graph.Dijkstra

namespace Graph

/- Approach for Bellman-Ford

We want to take a (Graph α Int) i.e. a graph with payloads of type α and weights of type Int and a source
vertex (type is ℕ because vertices are identified by their indices in Graph.vertices) and output an array of
structure BFVertex where BFVertex for each vertex v stores 
  · predecessor : Nat : The element just before v in the shortest path from source to v
  · distance : Option Int : The distance of v from source
  · edgeWeightToPredecessor : Int

----------Algorithm----------

The Bellman-Ford algorithm consists of the following four steps:-

1) Initialisation: Initialize the Distance and Predecessor arrays to infinity and null respectively except the source vertex
   whose distance from itself is zero. 

2) Relaxation: Then, for each edge (u, v) with weight w, we check if 
   distance[v] > distance[u] + w. If so, set distance[v] to (distance[u] + w) and set predecessor[v] to u.
   We repeat this for |V| - 1 where |V| is the number of vertices in the graph.

Note that if the graph is disconnected, every vertex 'i' in a connected component not containing the source 
will have Distance[i] = ∞.

3) Negative cycle detection : We loop over all edges and check the existence of a edge (u,v) 
   s.t v.distance > u.distance + (edge weight of (u,v)). 

If there are no negative cycles detected, we return Distance and Predecessor array.

----------End of Algorithm----------

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


----------BFVertex----------

structure BFVertex where --BFVertices so we just make one array of BFVertex for output rather than two arrays (Distance and PRedecessor)
  predecessor : Nat
  distance : Option Int := none
  edgeWeightToPredecessor : Int := 0
deriving Repr, Inhabited
instance : ToString BFVertex where toString dv := "Predecessor: " ++ (toString dv.predecessor) ++ ", current distance: " ++ (toString dv.distance) ++ "\n"
instance : Inhabited BFVertex := ⟨ { predecessor := default } ⟩

----------End of BFVertex----------

----------BFShortestPathTree----------

structure BFShortestPathTree where
  BFVertices : Array BFVertex

namespace BFShortestPathTree

instance : ToString BFShortestPathTree where toString t := toString t.BFVertices

/--Returns the distance from the root of the tree to a specific node--/
def distanceToVertex (t : BFShortestPathTree) (id : Nat) : Option Int := t.BFVertices[id]!.distance

private def pathToVertexAux (t : BFShortestPathTree) (id : Nat) (pathSoFar : Path Int false) : Nat -> Path Int true
  | 0 => panic! "This should not be possible" -- This case is impossible since the longest shortest path possible can contain atmost n-1 vertices
  | n + 1 =>
    let currentVertex := t.BFVertices[id]!
    match currentVertex.distance with
      | none => panic! "Current vertex in shortest path tree is not reachable, this should not be possible"
      | some _ =>
        let pathWithCurrentVertexAdded : Path Int true := Path.vertex id pathSoFar
        if currentVertex.predecessor == id then pathWithCurrentVertexAdded else
        let pathWithCurrentEdgeAdded : Path Int false := Path.edge currentVertex.edgeWeightToPredecessor pathWithCurrentVertexAdded
        pathToVertexAux t currentVertex.predecessor pathWithCurrentEdgeAdded n

/--Returns the shortest path from the tree root to the specified vertex--/
def pathToVertex (t : BFShortestPathTree) (id : Nat) : Option (Path Int true) := match t.BFVertices[id]!.distance with
  | none => none
  | some _ => some (pathToVertexAux t id Path.empty t.BFVertices.size)

end BFShortestPathTree

----------End of BFShortestPathTree----------

----------BFAlgo----------

/--BFAux2 takes the graph, a vertex and the BFVertices array and iterates over the edges from the vertex, updating
distances and predecessors in BFVertices as described in the algorithm above--/
private def BFAux2 (g : Graph α Int) (vertex : Nat) (BFVerticesTemp : Array BFVertex) : Array BFVertex := Id.run do
  let mut BFVertices : Array BFVertex := BFVerticesTemp
  for edge in g.vertices[vertex]!.adjacencyList do -- for each edge in adj list of vertex
    let tentativeDistance : Option Int := match BFVertices[vertex]!.distance with -- creating new distance for edge.target. treat "none" as infinity.
      | some x => x + edge.weight
      | none => none
    let newBFVertex : BFVertex := {predecessor := vertex, distance := tentativeDistance, edgeWeightToPredecessor := edge.weight} -- new BFVertex to represent edge.target
    BFVertices := match BFVertices[edge.target]!.distance with
      | some x => match newBFVertex.distance with -- again, treat none as infinity here, and the logic should be clear. if previous distance is larger than new distance, replace the BFVertex. Otherwise let it be.
                  | some y => if y < x then BFVertices.set! edge.target newBFVertex else BFVertices
                  | none => BFVertices
      | none => BFVertices.set! edge.target newBFVertex
  return BFVertices

/--BFAux recurses over itself n times, where n = g.vertexCount - 1. Every iteration, it goes over every edge in the graph and updates distance and predecessors as described in the algorithm--/
private def BFAux (g : Graph α Int) (BFVerticesTemp : Array BFVertex) : Nat -> Array BFVertex
  | 0 => BFVerticesTemp
  | n + 1 => Id.run do --for recursion
    let mut BFVertices : Array BFVertex := BFVerticesTemp
    for vertex in g.getAllVertexIDs do -- for each vertex in g, we update distances and predecessors for each edge in g.vertices[vertex].adjacencyList.
      BFVertices := BFAux2 g vertex BFVertices
    BFAux g BFVertices n --for recursion.

---The negative cycle detection---

private def negative_cycle_detection_edge (i : Nat) (edge : Edge Int) (w : Array BFVertex) : Bool :=
    match w[i]!.distance with
    | none => true
    | some u => 
        match w[edge.target]!.distance with
        | none =>  true
        | some v => 
            if v  > u + edge.weight  then 
              false
            else
              true

private def negative_cycle_detection (g : Graph α Int) (w : Array BFVertex) (nncycle : Bool) : Nat → Bool 
    | 0 => nncycle
    | n + 1 => Id.run do
        let mut no_neg_cycle : Bool := true
        for edge in g.vertices[n]!.adjacencyList do
            no_neg_cycle :=
              match (negative_cycle_detection_edge (n) edge w) with
              | true => no_neg_cycle
              | false => false
        negative_cycle_detection g w (nncycle ∧ no_neg_cycle) n

---End of negative cycle detection algorithm---

private def BFAuxBase (g : Graph α Int) (source : Nat) : Array (BFVertex) :=
  let BFVerticesInitial : Array (BFVertex) := mkArray g.vertexCount {predecessor := source} -- predecessor is only a placeholder here, it has no significance and will be replaced or not used
  if h : source < BFVerticesInitial.size then
    let BFVertices := BFVerticesInitial.set ⟨source, h⟩ {predecessor := source, distance := some 0}
    let BFVerticesUpdated : Array (BFVertex) := BFAux g BFVertices (g.vertexCount - 1)
    match (negative_cycle_detection g BFVerticesUpdated true g.vertexCount) with
    | true => BFVerticesUpdated
    | false => panic! "The Graph has negative cycle"
  else
      panic! "source out of bounds"

def BellmanFord (g : Graph α Int) (source : Nat) : Array BFVertex := BFAuxBase g source -- call this function to turn BF Algorithm on a given graph g at vertex source.

def BFShortestPath (g : Graph α Int) (source : Nat) (target : Nat) : Option (Path Int true) :=
  let BFshortestPathTree : BFShortestPathTree := ⟨ (BFAuxBase g source ) ⟩
  BFshortestPathTree.pathToVertex target

----------End of BFAlgo----------

----------Dynamic allocation----------

/-Let's say we have graph g and a weight array w which we obtained by performing Bellman-Ford algorithm
  on g. Now say we want add a edge or vertex to the graph and get the updated weight array, to do that using
  the above functions require you to perform the whole BellmanFord procedure again but using the given weight array
  we only need one iteration-/

/-It takes a graph, weight array and a edge as input and outputs the updated graph and updated weight array-/
def BF_dynamic_edgeAdd (g : Graph α Int) (w: Array BFVertex) (edge : Nat × Nat × Int) : Graph α Int × Array BFVertex :=
    let g_updated := addEdgeByID g edge.1 edge.2.1 edge.2.2
    ⟨ g_updated, (BFAux g_updated w) 1 ⟩

/-It takes a a graph, weight array and a vertex as input and outputs the updated graph and updated weight array-/
def BF_dynamic_vertex_addition (g : Graph Nat Int) (w: Array BFVertex) (vertex : Vertex Nat Nat) : Graph Nat Int × Array BFVertex := 
    let g_updated := (addVertex g vertex.payload).fst  
    ⟨ g_updated, (BFAux g_updated w) 1⟩


----------End of Dynamic allocation----------

end Graph
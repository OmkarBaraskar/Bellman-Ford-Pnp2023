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

def Initialise_graph (g : Graph α Int) (source : Nat): Array (BFVertex) := 
    let ver : BFVertex :=   {predecessor:= 0, distance := some 0}  
    Array.setD (mkArray g.vertexCount default) source ver

def relax (edge : Edge Int) (w: Array (BFVertex)) (i : Nat) : Array (BFVertex) :=
    match w[i]!.distance with
    | none => w
    | some u => 
        match w[edge.target]!.distance with
        | none =>  Array.setD w edge.target {predecessor := i,  distance := u + edge.weight}
        | some v => 
            if v  > u + edge.weight  then 
              Array.setD w edge.target {predecessor := i, distance := u + edge.weight}
            else
              w


def relax_all_edges (g : Graph α Int) (w : Array BFVertex) : Nat → Array (BFVertex)
    | 0 => w
    | n + 1 => Id.run do
        let mut ret : Array BFVertex := w
        for edge in g.vertices[n]!.adjacencyList do
            ret := relax edge ret n
        relax_all_edges g ret n

def Bellman_Ford_Aux (g : Graph α Int) (source : Nat) (w : Array BFVertex) : Nat → Array (BFVertex) 
    | 0 => Initialise_graph g source
    | n + 1 => relax_all_edges g (Bellman_Ford_Aux g source w n) g.vertexCount  


def negative_cycle_detection_edge (i : Nat) (edge : Edge Int) (w : Array BFVertex) : Bool :=
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

def negative_cycle_detection (g : Graph α Int) (w : Array BFVertex) (nncycle : Bool) : Nat → Bool 
    | 0 => nncycle
    | n + 1 => Id.run do
        let mut no_neg_cycle : Bool := true
        for edge in g.vertices[n]!.adjacencyList do
            no_neg_cycle :=
              match (negative_cycle_detection_edge (n) edge w) with
              | true => no_neg_cycle
              | false => false
        negative_cycle_detection g w (nncycle ∧ no_neg_cycle) n

def BellmanFord! (g : Graph α Int) (source : Nat) : Array BFVertex :=
    let BFGraph : Array BFVertex := Bellman_Ford_Aux g source (mkArray g.vertexCount default) g.vertexCount
    match (negative_cycle_detection g BFGraph true g.vertexCount) with
    | true => BFGraph
    | false => panic! "The Graph has negative cycle"      
                

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

#eval BellmanFord! g_final 4



             


     

    
    










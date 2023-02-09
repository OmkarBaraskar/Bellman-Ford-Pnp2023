import Graph

def hello := "world"

-- Trying random stuff from Graph.Graph -----------------

def emptyGraph : Graph Nat Nat := Graph.empty

def array1 : Array Nat := #[0, 0, 0, 0]

def graph_with_4_vertices : Graph Nat Nat := Graph.makeGraphFromArray array1

def num : Int := 0

#eval graph_with_4_vertices
#eval graph_with_4_vertices.hasNoEdges
#eval graph_with_4_vertices.hasNoVertices

#eval Graph.addEdgeByID graph_with_4_vertices 0 3 3

----------------------------------------------------------

/- Approach for Bellman-Ford

We want to take a (Graph α Int ) i.e. a graph with payloads of type α and weights of type Int and a source
vertex (type is ℕ because vertices are identified by their indices in Graph.vertices) and output an array
of Nat (the ith entry is the predecessor of vertex i) and an array of Int (the ith entry is the shortest
distance between i and source).

Have a look at Graph.Djikstra.

```lean
def BellmanFord (g : Graph α Int) : Array Nat × Array Int :=
  sorry
```
This will probably not be what the actual implementation of Bellman-Ford looks like, but its here for
now.
-/


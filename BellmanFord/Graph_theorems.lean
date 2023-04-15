import Mathlib

namespace Graph

structure Edge (β : Type) where
  source : Nat
  target : Nat
  weight : β

structure Vertex (α : Type) (β : Type) where
  payload : α
  adjacencyList : List (Edge β) := []

instance [Inhabited α] : Inhabited (Vertex α β) := ⟨ { payload := default } ⟩

end Graph

structure Graph (α : Type) (β : Type) where
  vertices : List (Graph.Vertex α β) := []

namespace Graph

variable {α : Type} [Inhabited α] {β : Type}

/-- Empty graph, α is the vertex payload type, β is edge weight type --/
def empty : Graph α β := ⟨[]⟩

/-- Total edge count in the graph. -/
def edgeCount (g : Graph α β) : Nat := g.vertices.foldr (λ vertex count => vertex.adjacencyList.length + count) 0

def vertexCount (g : Graph α β) : Nat := g.vertices.length

def getAllVertexIDs (g : Graph α β) : List Nat := Id.run do
  let mut arr := mkArray g.vertexCount 0
  for i in [0:g.vertexCount] do arr := arr.set! i i
  arr.toList

def makeGraphFromArray (a : List α) : Graph α β := ⟨
  a.map (λ element => { payload := element } )
⟩

def addVertex (g : Graph α β) (payload : α) : (Graph α β) × Nat :=
  let res := { g with vertices := g.vertices.append [{ payload := payload }] }
  let id : Nat := res.vertexCount - 1
  (res, id)

def addEdgeByID (g : Graph α β) (source : Nat) (target : Nat) (weight : β) : Graph α β := {
  g with vertices := (g.vertices.toArray.modify source (λ vertex => { vertex with adjacencyList := (vertex.adjacencyList.toArray.push {source := source, target := target, weight := weight}).toList })).toList
}

def getAllEdges (g: Graph α β) : List (Edge β) := 
  g.vertices.foldl (λ edgeListSoFar vertex => edgeListSoFar ++ vertex.adjacencyList) []

instance [ToString β] : ToString (List (Edge β)) where toString :=
  (λ list => "list" ++ list.foldr foldEdges "")
  where foldEdges (e : Edge β) (s : String) : String :=
    s ++ "   target: " ++ (ToString.toString e.target) ++ ", weight: " ++ (ToString.toString e.weight) ++ "\n"

namespace Vertex

private def toString [ToString α] [ToString β] (v : Vertex α β) : String := "\nVertex payload: " ++ ToString.toString v.payload ++ ", edges:\n" ++ v.adjacencyList.foldr foldEdges "" ++ "\n"
  where foldEdges (e : Edge β) (s : String) : String :=
    s ++ "   target: " ++ (ToString.toString e.target) ++ ", weight: " ++ (ToString.toString e.weight) ++ "\n"

instance [ToString α] [ToString β] : ToString (Vertex α β) where toString := toString

end Vertex

instance [ToString α] [ToString β] : ToString (Graph α β) where toString :=
  (λ g => toString (g.getAllVertexIDs.zip g.vertices))

end Graph

namespace Graph

structure Path (α :Type) where
  edgeList : List (Edge α) 
  hyp : ∃ n : Nat, edgeList.length = n

@[ext] theorem Path.ext {α : Type} (p q : Path α) (h : p.edgeList = q.edgeList) : p = q := by
  cases p
  cases q
  simp only [Path, edgeList] at h
  subst h
  rfl

end Graph

namespace Graph

def null_path : Path Int := ⟨ [] , by simp[];  ⟩  

def Pathsource (p: Path Int) : Nat :=
  match p.edgeList with
    |[] => p.edgeList.length
    |head::_ => head.source

def Pathtarget (p: Path Int) : Nat :=
  match c:p.edgeList with
    |[] => p.edgeList.length
    |head::tail => (p.edgeList[p.edgeList.length-1]'(by 
                                                      have hyp: p.edgeList.length > 0 := by
                                                        rw[c]
                                                        simp[Nat.succ_pos]
                                                      simp[Nat.sub_lt, hyp])).target

def w (p : Path Int) : Int :=
  match c: p.edgeList with
  | [] => 0
  | head::tail => have hyp2 : Eq (head::tail) p.edgeList  := by rw[c]
                  have hyp11 : tail.length = (head::tail).length - 1:= by
                      simp[]
                  have hyp1 : ∃ m : Nat, tail.length = m := by
                    let ⟨ n, h ⟩ := p.hyp
                    rw[hyp2,h] at hyp11
                    exists n-1
                  (head.weight + w ⟨ tail, hyp1 ⟩ )
termination_by w p => p.edgeList.length
decreasing_by 
    simp_wf
    rw [c,hyp2,hyp11]
    rw[c]
    simp[List.length_cons]


theorem List_add {α : Type} (l1 : List α ) (l2 : List α) : (l1 ++ l2).length = l1.length + l2.length := 
  match l1 with
  | [] => by 
          rw[List.nil_append]
          simp[]
  | head::tail => by 
                  have h : ((head :: tail) ++ l2) = head::(tail ++ l2) := by simp[List.cons_append]
                  rw[List.length_cons]
                  simp[h]
                  simp[Nat.succ_eq_add_one]
                  simp[Nat.add_right_comm,Nat.add_right_cancel]


def conc (p1 : Path Int) (p2 : Path Int) : Path Int :=
    let edge_list := p1.edgeList ++ p2.edgeList
    have h : ∃ n : Nat, edge_list.length = n := 
            match  p1.hyp, p2.hyp   with
            | ⟨ w1, hw1 ⟩ , ⟨ w2, hw2 ⟩  => ⟨ w1 + w2, by simp[List_add,hw1,hw2] ⟩
    ⟨ edge_list , h ⟩

theorem conc_nil (p1 : Path Int) : (conc p1 null_path) = p1 := by
  simp[conc]
  simp[null_path]

theorem nil_conc (p1 : Path Int) : (conc null_path p1) = p1 := by
  simp[conc]
  simp[null_path]

theorem w_null_path : w null_path = 0 := by
  rw[w]
  simp[null_path]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm


theorem conc_w (p1 p2 : Path Int) : w (conc p1 p2) = (w p1) + (w p2) := 
  match c: p1.edgeList with
  | [] => by  
          have h : p1 = null_path := by
           have h1 : p1.edgeList = null_path.edgeList := by 
            rw[c,null_path]
           apply Path.ext p1 null_path h1
          rw[h,w_null_path]
          simp[nil_conc]
  | head :: tail => by
    rw[w]   
    simp[]
    let tail_path : Path Int := ⟨ tail, by simp[] ⟩
    have h : w p1 = head.weight + w tail_path := by sorry
    have h1 : w tail_path + w p2 = w (conc tail_path p2) := by 
      apply Eq.symm (conc_w tail_path p2)
    have h2 : w p1 + w p2 = head.weight + w (conc tail_path p2) := by
      rw[h]
      /-
      have h3 : (head.weight + w tail_path) + w p2 = head.weight + w (conc tail_path p2) := by
        apply h1 ▸ (Nat.add_assoc head.weight (w tail_path) (w p2)) 
      -/
      sorry
    sorry
decreasing_by sorry

structure shortestPath (start : Nat) (finish : Nat) where
  path : Path Int
  hyp : ∀ p' : Path Int, w path <= w p'

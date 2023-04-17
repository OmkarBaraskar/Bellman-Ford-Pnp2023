import Mathlib

namespace Graph

structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  weight : Int

structure Graph (n : Nat) where
  edges : List (Edge n)

inductive EdgePath (g : Graph n) : Fin n → Fin n → Type   where
| point (v : Fin n) : EdgePath g v v
| cons  (e : Edge n) (w : Fin n) (hyp : e ∈ g.edges) (p : EdgePath g w e.source) : EdgePath g w e.target

def weight (p : EdgePath g a b) : Int := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons e _ _ p' => e.weight + weight p'

def length (p : EdgePath g a b) : Nat := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons _ _ _ p' => 1 + length p'

-- structure BFVertex (n : Nat) where
--   distance : Option Int
--   predecessor : Fin n
--   edgeweightofpred : Int := 0

-- structure BFVertexNew (n : Nat) (source : Fin n) where
--   index : Fin n
--   path : Option (EdgePath n source index)

-- structure BFListLengthHypNew (n : Nat) (source: Fin n) where
--   BFList : List (BFVertexNew n source)
--   hyp : BFList.length = n

-- structure BFListLengthHyp (n : Nat) where
--   BFList : List (BFVertex n)
--   hyp : BFList.length = n

-- def initializedNew (source : Fin n): BFListLengthHypNew n source:=
--   let init : List (BFVertexNew n source) := List.map (fun index ↦ {index := index, path := none} ) (List.finRange n)
--   let BF0 : List (BFVertexNew n source) := init.set source {index := source, path := EdgePath.point source}
--   have BF_len_eq_n : BF0.length = n := by simp[]
--   ⟨ BF0, BF_len_eq_n⟩ 

-- def initialized (source : Fin n): BFListLengthHyp n:=
--   let init : List (BFVertex n) := List.map (fun _ ↦ {distance := none, predecessor := source} ) (List.finRange n)
--   let BF0 : List (BFVertex n) := init.set source {predecessor := source, distance := some 0}
--   have BF_len_eq_n : BF0.length = n := by simp[]
--   ⟨ BF0, BF_len_eq_n⟩ 

def initPaths (source : Fin n) : (index: Fin n) → Option (EdgePath g source index) :=
  let temp : (index: Fin n) → Option (EdgePath g source index) := fun index ↦ if h:index = source then (some (by rw[h]; exact EdgePath.point source)) else none
  temp

/- BF starts-/

def relax_edge (paths : (index : Fin n) → Option (EdgePath g source index)) (edge : Edge n) (hyp : edge ∈ g.edges): (index : Fin n) → Option (EdgePath g source index):=
  match (paths edge.source) with
  | none => paths
  | some u => match (paths edge.target)  with
              | none => fun index ↦ if h:index = edge.target then (some (by rw[h]; exact EdgePath.cons edge source hyp u)) else (paths index)
                        
              | some v => if weight v > weight u + edge.weight then
                            fun index ↦ if h:index = edge.target then (some (by rw[h]; exact EdgePath.cons edge source hyp u)) else (paths index)
                          else paths

def recurse_over_all_edges (remaining : List (Edge n)) (hyp : remaining ⊆ g.edges) (paths :(index : Fin n) → Option (EdgePath g source index)) : (index : Fin n) → Option (EdgePath g source index) :=
  match h: remaining with
  | [] => paths
  | head::tail => have tail_is_sub : tail ⊆ g.edges := by 
                    exact List.subset_of_cons_subset (hyp)
                  
                  let pathsnext : (index : Fin n) → Option (EdgePath g source index) := relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1)
                  recurse_over_all_edges tail tail_is_sub pathsnext

def relax (g : Graph n) (BFn : (index : Fin n) → Option (EdgePath g source index)) (counter : Nat) : (index : Fin n) → Option (EdgePath g source index):= 
  match counter with
  | 0 => BFn
  | m + 1 => let BFnplus1 : (index : Fin n) → Option (EdgePath g source index) := 
              have hyp : g.edges ⊆ g.edges := by simp[]
              recurse_over_all_edges g.edges hyp BFn

             relax g BFnplus1 m


def BellmanFord (g : Graph n) (source : Fin n) : (index : Fin n) → Option (EdgePath g source index) :=
  relax g (initPaths source) (n - 1)
  

/- BF Ends-/

/- Proof -/

#check Option.get

theorem relax_edge_some (edge : Edge n) (hyp : edge ∈ g.edges) (paths : (index : Fin n) → Option (EdgePath g source index))
  (h1 : (paths edge.source).isSome)
  : ((relax_edge paths edge hyp) edge.target).isSome:= by
    match h :(paths edge.source) with
      | none => rw[h] at h1
                contradiction
      | some u => match j : (paths edge.target) with
                  | none => rw[relax_edge]
                            simp[h, j]
                  | some v => rw[relax_edge]
                              simp[h, j]
                              split
                              · simp[]
                              · simp[j]


theorem relax_edge_leq (edge : Edge n) (hyp : edge ∈ g.edges) (paths : (index : Fin n) → Option (EdgePath g source index))
  (h1 : (paths edge.source).isSome) (h2 : (paths edge.target).isSome)
  : (weight (((relax_edge paths edge hyp) edge.target).get (by exact relax_edge_some edge hyp paths h1)) ≤ (weight ((paths edge.target).get h2)) ) := by 
      match h :(paths edge.source) with
      | none => rw[h] at h1
                contradiction
      | some u => match j : (paths edge.target) with
                  | none => sorry
                  | some v => sorry


-- theorem relax_gives_dist_eq_path (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n) (counter : Nat)
--   (BFList_is_after_counter_relaxes : BFListhyp = relax g (initialized source) counter):
--     (((BFListhyp.BFList[i]'(by simp[BFListhyp.hyp])).distance ≠ none) →
--     (∃ p : (EdgePath n source i), (BFListhyp.BFList[i]'(by simp[BFListhyp.hyp])).distance = weight p)) := by
--       sorry
    

-- -- theorem relax_dist_atmost_shortest (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n) (counter : Nat)
-- --   (BFList_is_from_BellmanFord : BFListhyp = relax g (initialized source) counter):

-- theorem BellmanFord_gives_shortest_path (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n)
--   (BFList_is_from_BellmanFord : BFListhyp = BellmanFord g source):
--     ∀ p : EdgePath n source i, weight p ≥ weight (pathViaBellmanFord g source i) := by
--       sorry
import Mathlib

namespace Graph

structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  weight : Int

#check List.toString

instance : ToString (Edge n) where toString edge := "edge (" ++ (toString edge.source) ++ ", " ++ (toString edge.target) ++ ") weight: " ++ (toString edge.weight) ++ "\n"

structure Graph (n : Nat) where
  edges : List (Edge n)

instance : ToString (Graph n) where toString graph := toString graph.edges

inductive EdgePath (g : Graph n) : Fin n → Fin n → Type   where
| point (v : Fin n) : EdgePath g v v
| cons  (e : Edge n) (w : Fin n) (hyp : e ∈ g.edges) (p : EdgePath g w e.source) : EdgePath g w e.target

def get_path_edges (n : Nat) (g : Graph n) (a : Fin n) (b : Fin n) (path : EdgePath g a b) : List (Edge n) :=
  match path with
  | EdgePath.point c => [{source := c, target := c, weight := 0}]
  | EdgePath.cons edge _ _ p => [⟨ edge.source, edge.target, edge.weight⟩ ] ++ get_path_edges n g a edge.source p

instance : ToString (EdgePath g a b) where toString path := toString (get_path_edges _ g a b path)

def graph1 : Graph 4 :=
  {edges := [⟨ 0, 2, 3⟩ , ⟨1, 3, 5⟩ , ⟨ 2, 3, 4⟩ , ⟨ 3, 1, -2⟩  ]}

#eval graph1

def path1 : EdgePath graph1 0 3 :=
  EdgePath.cons ⟨ 2, 3, 4⟩ 0 (by rw[graph1]; simp[]) (EdgePath.cons ⟨ 0, 2, 3⟩ 0 (by rw[graph1]; simp[]) (EdgePath.point 0))

#eval path1

def weight (p : EdgePath g a b) : Int := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons e _ _ p' => e.weight + weight p'

def length (p : EdgePath g a b) : Nat := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons _ _ _ p' => 1 + length p'

theorem len_zero_imp_weight_zero (p : EdgePath g a b) : length p = 0 → weight p = 0 := by
  intro hyp
  match p with
  | EdgePath.point c => simp[weight]
  | EdgePath.cons e _ _ p' => simp[length] at hyp
  
theorem length_geq_zero (p : EdgePath g a b) : length p ≥ 0 := by
  induction p
  case point => simp[]
  case cons e _ _ p' _ => simp[]
 

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

def initPaths (g : Graph n) (source : Fin n) : (index: Fin n) → Option (EdgePath g source index) :=
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
  relax g (initPaths g source) (n - 1)
  

/- BF Ends-/

#eval (BellmanFord graph1 2 3)

/- Proof -/

#check Option.get

theorem init_path_some_source (g : Graph n) (source : Fin n) (i : Fin n) : ((initPaths g source) i).isSome → i = source := by
  have lm : ¬ i = source → ¬ (initPaths g source i).isSome := by
    intro hyp
    simp[initPaths, hyp]
  rw[not_imp_not] at lm
  assumption


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
      | some u => let v := (paths edge.target).get h2
                  if cond : weight v > weight u + edge.weight then
                    have lm : (relax_edge paths edge hyp edge.target) = some (EdgePath.cons edge source hyp u) := by
                      rw[relax_edge]
                      simp[h]
                      match j: paths edge.target with
                        | none => rw[j] at h2; contradiction
                        | some v1 => have lm2 : v1 = v := by simp[j]
                                     simp[]
                                     rw[lm2]
                                     simp[cond]
                    have lm2 : ((relax_edge paths edge hyp) edge.target).get (by exact relax_edge_some edge hyp paths h1) = EdgePath.cons edge source hyp u := by simp[lm]
                    simp[lm2]
                    simp[weight]
                    have lm3: weight v ≥ edge.weight + weight u := by
                      apply Int.le_of_lt
                      have obvious : weight u + edge.weight = edge.weight + weight u := by
                        apply Int.add_comm
                      rw[<- obvious]
                      exact cond
                    simp[] at lm3
                    exact lm3

                  else
                    have lm : (relax_edge paths edge hyp edge.target) = paths edge.target := by
                      rw[relax_edge]
                      simp[h]
                      match j: paths edge.target with
                        | none => rw[j] at h2; contradiction
                        | some v1 => have lm2 : v1 = v := by simp[j]
                                     simp[]
                                     rw[lm2]
                                     simp[cond]
                    have lm2 : ((relax_edge paths edge hyp) edge.target).get (by exact relax_edge_some edge hyp paths h1) = ((paths edge.target).get h2) := by simp[lm]
                    simp[lm2]
                        


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

theorem BellmanFordAux (source : Fin n) (counter : Nat) (source i: Fin n):
    (h: ((relax g (initPaths g source) (counter)) i).isSome) → 
  (p : (EdgePath g source i)) →  (h1 : (length p ≤ counter)) → (weight p ≥ weight (((relax g (initPaths g source) (counter)) i).get h)) := by
  --let BF_paths_curr := (relax g (initPaths source) (counter))
  induction counter
  case zero =>
    intro h p h1
    simp[relax]
    simp[length_geq_zero] at h1
    simp[h1,len_zero_imp_weight_zero]
    have h2 : i = source := (init_path_some_source g source i) h
    sorry

    
  

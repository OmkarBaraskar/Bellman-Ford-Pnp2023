import Mathlib

namespace Graph

structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  weight : Int

structure Graph (n : Nat) where
  edges : List (Edge n)

inductive EdgePath (n : ℕ) : Fin n → Fin n → Type   where
| point (v : Fin n) : EdgePath n v v
| cons  (e : Edge n) (w : Fin n) (p : EdgePath n w e.source) : EdgePath n w e.target

def weight (p : EdgePath n a b) : Int := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons e _ p' => e.weight + weight p'

def length (p : EdgePath n a b) : Nat := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons _ _ p' => 1 + length p'

structure BFVertex (n : Nat) where
  distance : Option Int
  predecessor : Fin n
  edgeweightofpred : Int := 0

structure BFVertexNew (n : Nat) (source : Fin n) where
  index : Fin n
  path : Option (EdgePath n source index)

structure BFListLengthHypNew (n : Nat) (source: Fin n) where
  BFList : List (BFVertexNew n source)
  hyp : BFList.length = n

structure BFListLengthHyp (n : Nat) where
  BFList : List (BFVertex n)
  hyp : BFList.length = n

def initializedNew (source : Fin n): BFListLengthHypNew n source:=
  let init : List (BFVertexNew n source) := List.map (fun index ↦ {index := index, path := none} ) (List.finRange n)
  let BF0 : List (BFVertexNew n source) := init.set source {index := source, path := EdgePath.point source}
  have BF_len_eq_n : BF0.length = n := by simp[]
  ⟨ BF0, BF_len_eq_n⟩ 

def initialized (source : Fin n): BFListLengthHyp n:=
  let init : List (BFVertex n) := List.map (fun _ ↦ {distance := none, predecessor := source} ) (List.finRange n)
  let BF0 : List (BFVertex n) := init.set source {predecessor := source, distance := some 0}
  have BF_len_eq_n : BF0.length = n := by simp[]
  ⟨ BF0, BF_len_eq_n⟩ 


/- BF starts-/

def relax_edge (BFList_and_hyp : BFListLengthHypNew n source) (edge : Edge n) : BFListLengthHypNew n source:=
  let ⟨BFList, hyp⟩ := BFList_and_hyp
  match (BFList[edge.source]'(by simp[hyp])).path with
  | none => BFList_and_hyp
  | some u => match (BFList[edge.target]'(by simp[hyp])).path  with
              | none => 
                        have indices_eq : (BFList[edge.source]'(by simp[hyp])).index = edge.source := by sorry
                        -- let p : EdgePath n source edge.source := by sorry
                        --   rw[<- indices_eq]
                        --   exact u
                        let newBFList : List (BFVertexNew n source) := BFList.set edge.target {index := edge.target, path:= EdgePath.cons edge source _}
                        have hyp2 : newBFList.length = n := by simp[hyp]
                        ⟨ newBFList, hyp2 ⟩ 
                        
              | some v => if weight v > weight u + edge.weight then
                            have indices_eq : (BFList[edge.source]'(by simp[hyp])).index = edge.source := by sorry
                            let p : EdgePath n source edge.source := by
                              rw[<- indices_eq]
                              exact u
                            let newBFList : List (BFVertexNew n source) := BFList.set edge.target {index := edge.target, path:= EdgePath.cons edge source p}
                            have hyp2 : newBFList.length = n := by simp[hyp]
                            ⟨ newBFList, hyp2 ⟩ 
                          else BFList_and_hyp

def relax (g : Graph n) (BFn : BFListLengthHypNew n source) (counter : Nat) : BFListLengthHypNew n source:= 
  match counter with
  | 0 => BFn
  | m + 1 => let BFnplus1 : BFListLengthHypNew n source := g.edges.foldl (fun bflist edge ↦ relax_edge bflist edge) BFn
             relax g BFnplus1 m
             

def BellmanFord (g : Graph n) (source : Fin n) : BFListLengthHypNew n source :=
  relax g (initializedNew source) (n - 1)
  

/- BF Ends-/

/- Proof -/

#check Option

theorem relax_gives_dist_eq_path (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n) (counter : Nat)
  (BFList_is_after_counter_relaxes : BFListhyp = relax g (initialized source) counter):
    (((BFListhyp.BFList[i]'(by simp[BFListhyp.hyp])).distance ≠ none) →
    (∃ p : (EdgePath n source i), (BFListhyp.BFList[i]'(by simp[BFListhyp.hyp])).distance = weight p)) := by
      sorry
    

-- theorem relax_dist_atmost_shortest (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n) (counter : Nat)
--   (BFList_is_from_BellmanFord : BFListhyp = relax g (initialized source) counter):

theorem BellmanFord_gives_shortest_path (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFListLengthHyp n)
  (BFList_is_from_BellmanFord : BFListhyp = BellmanFord g source):
    ∀ p : EdgePath n source i, weight p ≥ weight (pathViaBellmanFord g source i) := by
      sorry
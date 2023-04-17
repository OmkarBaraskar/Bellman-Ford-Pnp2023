import Mathlib

namespace Graph

structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  weight : Int

structure Graph (n : Nat) where
  edges : List (Edge n)

structure BFVertex (n : Nat) where
  distance : Option Int
  predecessor : Fin n
  edgeweightofpred : Int := 0

structure BFPath (n : Nat) where
  BFList : List (BFVertex n)
  hyp : BFList.length = n

def initialized (source : Fin n): BFPath n:=
  let init : List (BFVertex n) := List.map (fun _ ↦ {distance := none, predecessor := source} ) (List.finRange n)
  let BF0 : List (BFVertex n) := init.set source {predecessor := source, distance := some 0}
  have BF_len_eq_n : BF0.length = n := by simp[]
  ⟨ BF0, BF_len_eq_n⟩

theorem initialized_non_source_dist_none (i : Fin n) : i ≠ source → ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone := by
  intro h
  let base : BFVertex n := {distance := none, predecessor := source}
  have trueing (b : BFVertex n) (b_eq : b = base) : b.distance.isNone := by rw[b_eq]; simp[]
  apply trueing
  let init : List (BFVertex n) := List.map (fun _ ↦ base ) (List.finRange n)
  let BF0 : List (BFVertex n) := init.set source {predecessor := source, distance := some 0}
  have BF_len_eq_n : BF0.length = n := by simp[]
  let inited : BFPath n := ⟨ BF0, BF_len_eq_n⟩ 
  have h1 : (initialized source) = inited := by
    rw[initialized]
  rw[h1]
  have h2: inited.BFList = BF0 := by simp[]
  have h3: inited.BFList[i] = BF0[i] := by simp[h2]
  rw[h3]
  have h6 : BF0[i] = init[i] := by
    apply List.get_set_of_ne
    have k : i.val ≠ source.val := by 
      rw[<- Fin.ne_iff_vne]
      exact h
    rw[ne_comm]
    assumption
  rw[h6]
  simp[] 

theorem initialized_dist_none_non_source (i : Fin n) : ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone → i ≠ source := by
  -- intro h
  let base : BFVertex n := {distance := none, predecessor := source}
  let init : List (BFVertex n) := List.map (fun _ ↦ base ) (List.finRange n)
  let BF0 : List (BFVertex n) := init.set source {predecessor := source, distance := some 0}
  have BF_len_eq_n : BF0.length = n := by simp[]
  let inited : BFPath n := ⟨ BF0, BF_len_eq_n⟩ 
  have h1 : (initialized source) = inited := by
    rw[initialized]
  -- rw[h1] at h
  have h2: inited.BFList = BF0 := by simp[]
  have h3: inited.BFList[i] = BF0[i] := by simp[h2]
  -- rw[h3] at h
  have contrapos (k : Not (i ≠ source)) : Not ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone := by
    simp[] at k
    rw[h1, h3]
    have k1 : BF0[i] = {predecessor := source, distance := some 0} := by
      simp[k]
    have k2 : BF0[i].distance = some 0:= by rw[k1]
    rw[k2]
    simp[]
  rw[not_imp_not] at contrapos
  assumption


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

/- BF starts-/

def relax_edge (BFList_and_hyp : BFPath n) (edge : Edge n) : BFPath n :=
  let ⟨BFList, hyp⟩ := BFList_and_hyp
  match (BFList[edge.source]'(by simp[hyp])).distance with
  | none => BFList_and_hyp
  | some u => match (BFList[edge.target]'(by simp[hyp])).distance with
              | none => let newBFList : List (BFVertex n) := BFList.set edge.target {predecessor := edge.source, distance := u + edge.weight}
                        have hyp2 : newBFList.length = n := by simp[hyp]
                        ⟨ newBFList, hyp2 ⟩ 
                        
              | some v => if v > u + edge.weight then
                            let newBFList : List (BFVertex n) := BFList.set edge.target {predecessor := edge.source, distance := u + edge.weight}
                            have hyp2 : newBFList.length = n := by simp[hyp]
                            ⟨ newBFList, hyp2 ⟩ 
                          else BFList_and_hyp

def relax (g : Graph n) (BFn : BFPath n) (counter : Nat) : BFPath n := 
  match counter with
  | 0 => BFn
  | m + 1 => relax g (g.edges.foldl (fun bflist edge ↦ relax_edge bflist edge) BFn) m

theorem relax_recur (g : Graph n) (BFn : BFPath n) (counter : Nat) : 
  relax g BFn (counter + 1) = relax g (g.edges.foldl (fun bflist edge ↦ relax_edge bflist edge) BFn) counter :=
      by simp[relax]
             

def BellmanFord (g : Graph n) (source : Fin n) : BFPath n :=
  relax g (initialized source)  (n - 1)


def BFPathmaker (source target : Fin n)(BFListhyp : BFPath n) : EdgePath n source target :=
  let ⟨ dist, pred, weight ⟩:= BFListhyp.BFList[target]'(by simp[BFListhyp.hyp])
  if c: source = target then by 
    rw[<- c]
    exact EdgePath.point source
  else
    EdgePath.cons ⟨ pred, target, weight⟩ source (BFPathmaker source pred BFListhyp)
decreasing_by sorry



def pathViaBellmanFord (g : Graph n) (source : Fin n) (target : Fin n) : EdgePath n source target :=
  let BFListhyp : BFPath n := BellmanFord g source
  BFPathmaker source target BFListhyp
  

/- BF Ends-/

/- Proof -/

#check Option

theorem init_BFList_2 (source : Fin n) : Ne ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance  none → i = source  := by
  intro j
  have h : i ≠ source → ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone := by
    exact initialized_non_source_dist_none i
  have k : Ne ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance  none → ¬ ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone := by
    rw[ne_eq]
    rw[not_imp_not]
    apply Option.eq_none_of_isNone
  have k1 : ¬ (((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance.isNone) → i = source := by
    have aux : (i = source) = ¬ (i ≠ source ) := by simp[]
    rw[aux]
    rw[not_imp_not]
    apply h
  rw[k1]
  apply k
  apply j


theorem relax_gives_dist_eq_path (source : Fin n) (g : Graph n) (BFList_curr : BFPath n) (counter : Nat)
  (BFList_after_relaxation : BFList_curr = relax g (initialized source) counter):
    (i : Fin n) → (((BFList_curr.BFList[i]'(by simp[BFList_curr.hyp])).distance ≠ none) →
    (∃ p : (EdgePath n source i), (BFList_curr.BFList[i]'(by simp[BFList_curr.hyp])).distance = weight p)) := by
      induction counter
      case zero => 
        rw[BFList_after_relaxation,relax]
        exact fun (i :Fin n) => fun h : Ne ((initialized source).BFList[i]'(by simp[(initialized source).hyp])).distance none
          => by
          simp[init_BFList_2]
          have h1 : i = source := (init_BFList_2 source) h
          rw[h1]
          simp[initialized]
          exact Exists.intro (EdgePath.point source) (by rw[weight])
      case succ counter ih => 
        exact fun (i : Fin n) => fun h : Ne (BFList_curr.BFList[i]'(by simp[BFList_curr.hyp])).distance none
          => by
            rw[relax_recur] at BFList_after_relaxation 
            rw[BFList_after_relaxation]
            sorry





-- theorem relax_dist_atmost_shortest (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFPath n) (counter : Nat)
--   (BFList_is_from_BellmanFord : BFListhyp = relax g (initialized source) counter):

theorem BellmanFord_gives_shortest_path (source : Fin n) (i : Fin n) (g : Graph n) (BFListhyp : BFPath n)
  (BFList_is_from_BellmanFord : BFListhyp = BellmanFord g source):
    ∀ p : EdgePath n source i, weight p ≥ weight (pathViaBellmanFord g source i) := by
      sorry
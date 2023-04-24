import Mathlib

namespace Graph

structure Edge (n : Nat) where
  source : Fin n
  target : Fin n
  weight : Int


instance : ToString (Edge n) where toString edge := "edge (" ++ (toString edge.source) ++ ", " ++ (toString edge.target) ++ ") weight: " ++ (toString edge.weight) ++ "\n"

structure Graph (n : Nat) where
  edges : List (Edge n)

instance : ToString (Graph n) where toString graph := toString graph.edges


theorem nat_basic : (n > 0) → (n-1 < n) := by
    intro hyp
    have h_1 : 0 < 1 := by simp[]
    apply Nat.sub_lt hyp h_1

/-- EdgePath definition, done inductively. When adding an edge to the path, requires a hypothesis that that edge is
an edge of graph g.-/
inductive EdgePath (g : Graph n) : Fin n → Fin n → Type where
| point (v : Fin n) : EdgePath g v v
| cons  (e : Edge n) (w : Fin n) (hyp : e ∈ g.edges) (p : EdgePath g w e.source) : EdgePath g w e.target

/-- Auxilliary function for representing EdgePath. Returns a list of edges in an EdgePath-/
def get_path_edges (n : Nat) (g : Graph n) (a : Fin n) (b : Fin n) (path : EdgePath g a b) : List (Edge n) :=
  match path with
  | EdgePath.point c => [{source := c, target := c, weight := 0}]
  | EdgePath.cons edge _ _ p => [⟨ edge.source, edge.target, edge.weight⟩ ] ++ get_path_edges n g a edge.source p

/-Vertex array and its theorems-/

def get_path_ver (g : Graph n) (p : EdgePath g source sink) : List (Fin n) :=
  match p with
  | EdgePath.point source => [source]
  | EdgePath.cons e source _ p' => (get_path_ver g p') ++ [e.target]

theorem get_path_ver_len (g : Graph n) (p : EdgePath g source sink) : 
  List.length (get_path_ver g p) > 0 := by
  induction p
  case point => simp[get_path_ver]
  case cons e source hyp p' ih => simp[get_path_ver]

theorem get_path_ver_point (g : Graph n) (v : Fin n) : get_path_ver g (EdgePath.point v) = [v] := by
  simp[get_path_ver]



#check Nat.lt_by_cases

theorem source_sink_in_ver (g : Graph n) (source sink : Fin n) (p : EdgePath g source sink) :
  (source ∈ get_path_ver g p) ∧ (sink ∈ get_path_ver g p) := by
    have hl : source ∈ get_path_ver g p := by
      induction p
      case point => simp[get_path_ver]
      case cons e source hyp p' ih => simp[get_path_ver,ih]
    have hr : sink ∈ get_path_ver g p := by 
      induction p
      case point => simp[get_path_ver]
      case cons e source hyp p' ih => simp[get_path_ver,ih]
    exact ⟨ hl, hr ⟩ 
  

theorem path_ver_cons_lin (g : Graph n)(e : Edge n) (hyp : e ∈ g.edges) (source : Fin n)
  (p : EdgePath g source e.source):
  (get_path_ver g (EdgePath.cons e source hyp p)) = (get_path_ver g p) ++ [e.target] := by
  simp[get_path_ver] 

theorem path_ver_cons (g : Graph n) (e : Edge n) (hyp : e ∈ g.edges) (source : Fin n)
  (p : EdgePath g source e.source) (i : Nat) (hi: i < List.length (get_path_ver g p)) :
  (get_path_ver g p)[i]'(hi) =
  (get_path_ver g (EdgePath.cons e source hyp p))[i]'(by 
    simp[get_path_ver]
    apply Nat.lt_add_right i (List.length (get_path_ver g p)) 1 hi
  )
  := by
    simp[path_ver_cons_lin]
    have h : (get_path_ver g p)[i]'(hi) = ((get_path_ver g p) ++ [e.target])[i]'(by 
      simp[List.length]
      apply Nat.lt_add_right i (List.length (get_path_ver g p)) 1 hi
    )   := by
       apply Eq.symm (List.get_append i hi) 
    apply h

theorem get_path_ver_source_sink (g : Graph n) (p : EdgePath g source sink) :
  ((get_path_ver g p)[0]'(get_path_ver_len g p) = source) ∧ 
  ((get_path_ver g p)[(List.length (get_path_ver g p) -1)]'(nat_basic (get_path_ver_len g p)) = sink) := by
  induction p
  case point v => 
    apply And.intro
    · simp[get_path_ver]
    · simp[get_path_ver]
  case cons e source hyp p' ih =>
    apply And.intro
    · calc
      (get_path_ver g (EdgePath.cons e source hyp p'))[0]'(get_path_ver_len g (EdgePath.cons e source hyp p')) = 
        (get_path_ver g p')[0]'(get_path_ver_len g p') := Eq.symm (path_ver_cons g e hyp source p' 0 (get_path_ver_len g p'))
      _ = source := ih.left
    · have h : List.length (get_path_ver g (EdgePath.cons e source hyp p')) = List.length (get_path_ver g p') +1 :=
        by simp[get_path_ver]
      simp[h,get_path_ver]
      have h1 : ¬ (List.length (get_path_ver g p') < List.length (get_path_ver g p')) := Nat.lt_irrefl (List.length (get_path_ver g p'))
      have h2 : (List.length (get_path_ver g p') - List.length (get_path_ver g p')) < List.length [e.target] := by
        simp[get_path_ver] 
      have h3 : List.length (get_path_ver g p') < List.length ((get_path_ver g p') ++ [e.target]) := by 
        simp[]

      have hf : ((get_path_ver g p') ++ [e.target])[(List.length (get_path_ver g p'))]'(h3) = 
        ([e.target])[(List.length (get_path_ver g p') - List.length (get_path_ver g p'))]'(h2) :=
          List.get_append_right (get_path_ver g p') ([e.target]) h1 
      simp[] at hf
      rw[hf]
     
     

#check List.get_append_right
#check Nat.sub_lt
#check Nat.lt_irrefl

instance : ToString (EdgePath g a b) where toString path := toString (get_path_edges _ g a b path)

/-- Weight of path. This is the sum of edge weights of the path.-/
def weight (p : EdgePath g a b) : Int := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons e _ _ p' => e.weight + weight p'

/-- Length of path. Number of edges in the path-/
def length (p : EdgePath g a b) : Nat := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons _ _ _ p' => 1 + length p'

theorem length_path_to_list (g : Graph n) (p : EdgePath g source sink) : 
  List.length (get_path_ver g p) = (length p) + 1 := by
  induction p
  case point => 
    simp[length,get_path_ver]
  case cons e source hyp p' ih =>
    simp[length,get_path_ver,ih,Nat.add_comm]

theorem length_cons (g : Graph n) (e : Edge n) (hyp : e ∈ g.edges) (source : Fin n)
  (p : EdgePath g source e.source) : 
  List.length (get_path_ver g (EdgePath.cons e source hyp p)) =
  List.length (get_path_ver g p) + 1 := by
  simp[get_path_ver]

/-Concatenation of paths-/

def conc (p : EdgePath g source i) (p' : EdgePath g i sink) : EdgePath g source sink :=
  match p' with
  | EdgePath.point i => p
  | EdgePath.cons e i hyp p1 => EdgePath.cons e source hyp (conc p p1) 

theorem con_w (p : EdgePath g source i) (p' : EdgePath g i sink) :
  weight (conc p p') = (weight p) + (weight p') := by  
      induction p'  
      case point => 
        rw[weight]
        simp[conc]
      case cons e i hyp p1 ih =>
        simp[conc,weight,ih]
        rw[Int.add_comm,Int.add_right_comm]
        simp[Int.add_assoc]

theorem conc_len (p : EdgePath g source i) (p' : EdgePath g i sink) :
  length (conc p p') = length p + length p' := by
  induction p'
  case point => 
    simp[conc,length]
  case cons e source hyp p'' ih =>
    simp[length,Nat.add_comm]
    simp[ih]
    rw[Nat.add_assoc]

theorem conc_cons (g: Graph n) (e : Edge n) (source i : Fin n) (hyp : e ∈ g.edges) 
  (p1 : EdgePath g source i) (p2 : EdgePath g i e.source)  
 : conc p1 (EdgePath.cons e i hyp p2) = EdgePath.cons e source hyp (conc p1 p2) := by
     simp[conc]

theorem conc_point (g : Graph n) (i : Fin n) (p : EdgePath g i i): 
  (h : p = EdgePath.point i) → (p = conc p p) :=
  by
    intro h 
    simp[h]
    rw[conc]

theorem conc_point_exists (g : Graph n) (i : Fin n) (p : EdgePath g i i): 
  (h : p = EdgePath.point i) → 
  ((∃ (p1 : EdgePath g i i) (p2 : EdgePath g i i), p = (conc p1 p2))) :=
  by
    intro h 
    exact ⟨ p, p, conc_point g i p h ⟩ 

theorem conc_indices (g : Graph n) (p : EdgePath g source sink) (p1 : EdgePath g source w) 
  (p2 : EdgePath g w sink) (i : Nat) (hi: i < List.length (get_path_ver g p1)) (hp: p = conc p1 p2): 
  (i < List.length (get_path_ver g p)) := by 
     simp[length_path_to_list] at *
     simp[hp,conc_len]
     rw[Nat.add_right_comm]
     apply Nat.lt_add_right 
     simp[hi] 

theorem conc_get_path_ver (g : Graph n) (p : EdgePath g source sink) (p1 : EdgePath g source w) 
  (p2 : EdgePath g w sink) (i : Nat) (hi: i < List.length (get_path_ver g p1)) (hp: p = conc p1 p2):
  ((get_path_ver g p)[i]'(conc_indices g p p1 p2 i hi hp) = (get_path_ver g p1)[i]'(hi)) := by
   induction p2
   case point v => 
    simp[conc] at hp
    simp[hp]
   case cons e w hyp p' ih =>
     rw[conc_cons] at hp
     calc
     (get_path_ver g p)[i]'(by
        simp[length_path_to_list] at *
        simp[hp,conc_len]
        simp[length,conc_len]
        rw[Nat.add_left_comm,<-Nat.add_assoc]
        apply Nat.lt_add_right 
        apply Nat.lt_add_right 
        simp[hi]
     ) = 
      (get_path_ver g (conc p1 p'))[i]'(conc_indices g (conc p1 p') p1 p' i hi (by rfl)) := 
        (by
           simp[hp]
           apply Eq.symm (path_ver_cons g e hyp source (conc p1 p') i (conc_indices g (conc p1 p') p1 p' i hi (by rfl)))
        )
     _ = (get_path_ver g p1)[i]'(hi) := (ih (conc p1 p') p1 hi (by rfl)) 

      

theorem conc_sub_paths_exists (g : Graph n) (p : EdgePath g source sink) :
  (j : Nat) → (hyp: j < (List.length (get_path_ver g p))) →  
  (∃ w : Fin n,  
  (∃ (p1 : EdgePath g source w) 
     (p2 : EdgePath g w sink), 
      (p = conc p1 p2) ∧ (length p1 = j) ∧ (w = (get_path_ver g p)[(⟨ j, hyp ⟩: Fin (List.length (get_path_ver g p)))]))) := by
    intro j hyp
    induction p
    case point v => 
      use v
      use EdgePath.point v
      use EdgePath.point v
      have h: List.length (get_path_ver g (EdgePath.point v)) = 1 := by
        simp[length_path_to_list]
        simp[length]
      have h1: j = 0 := by
        rw[h] at hyp
        simp[Nat.lt_add_one_iff] at hyp
        rw[hyp]
      apply And.intro 
      · simp[conc]
      · apply And.intro
        · simp[length,h1]
        · subst h1
          simp[get_path_ver]
    case cons e source hyp' p' ih =>
      by_cases h : j < List.length (get_path_ver g p') 
      case pos => 
        match (ih h) with
        | ⟨ w, p1',p2',hp'⟩ =>
          let hp'_conc := hp'.left
          let hp'_len := hp'.right.left
          let hp'_w := hp'.right.right
          let p2 : EdgePath g w e.target := 
            (EdgePath.cons e w hyp' p2')
          have hf : EdgePath.cons e source hyp' (conc p1' p2') = conc p1' p2 := by
            simp[conc]
          use w
          use p1'
          use p2
          apply And.intro
          · rw[<-hp'_conc] at hf
            rw[hf]
          · apply And.intro
            · apply hp'_len
            · calc 
              w = (get_path_ver g p')[j]'(h) := (hp'_w)
              _ = (get_path_ver g (EdgePath.cons e source hyp' p'))[j]'(hyp) := (by apply path_ver_cons g e hyp' source p' j h)
      case neg =>      
        have hf : j = List.length (get_path_ver g (EdgePath.cons e source hyp' p')) - 1 := by 
          have h1 : j ≥ List.length (get_path_ver g (EdgePath.cons e source hyp' p')) - 1 := by 
            rw[length_cons]
            simp[Nat.add_comm]
            let dum := Nat.lt_or_ge j (List.length (get_path_ver g p'))
            simp[h] at dum
            simp[dum]
          have h2 : j ≤ List.length (get_path_ver g (EdgePath.cons e source hyp' p')) - 1 := by
            simp[Nat.lt_iff_add_one_le] at hyp
            rw[length_cons] at hyp
            rw[length_cons]
            simp[Nat.add_comm]
            simp[Nat.succ_le_succ_iff] at hyp
            simp[hyp]
          apply (Nat.le_antisymm h2 h1)
        subst hf
        use e.target
        use (EdgePath.cons e source hyp' p')
        use EdgePath.point e.target
        apply And.intro
        · simp[conc]
        · apply And.intro
          · simp[get_path_ver]
            simp[length]
            rw[Nat.add_comm]
            apply (Eq.symm (length_path_to_list g p'))
          · apply Eq.symm (get_path_ver_source_sink g (EdgePath.cons e source hyp' p')).right



            
#check List.get_append_right
#check Nat.lt_add_right

theorem con_sub_cycle_paths_exists (g : Graph n) (p : EdgePath g source sink) 
  (i j: Nat):
  (i < j) → (hi: i < List.length (get_path_ver g p)) → (hj: j < List.length (get_path_ver g p) ) → 
  (  ∃ w1 w2 : Fin n,
    ( ∃ (p1 : EdgePath g source w1)
     (c : EdgePath g w1 w2)
     (p2 : EdgePath g w2 sink),
     (p = conc (conc p1 c) p2) ∧ (length c = j-i) ∧ (w1 = (get_path_ver g p)[i]'(hi)) ∧ (w2 = (get_path_ver g p)[j]'(hj))
    )
  )
   := by
  intro leij hi hj
  let fir_split := conc_sub_paths_exists g p j hj 
  match fir_split with
  | ⟨ w2, p1', p2, hp ⟩ =>
    have h : i < length p1' := by simp[hp,leij]
    have h1 : 1+ length p1' = List.length (get_path_ver g p1') := by 
      simp[length_path_to_list,Nat.add_comm]
    have h2 : i < List.length (get_path_ver g p1') := by
      have h3 : i < 1+ length p1' := by
       apply (Nat.lt_add_left i (length p1') 1) h
      rw[<-h1]
      simp[h3]
    let second_split := conc_sub_paths_exists g p1' i h2
    match second_split with
    | ⟨ w1, p1, c, hp'⟩ =>
      let hpl' := hp'.left
      let hpr' := hp'.right.left
      let hpl := hp.left
      let hpr := hp.right.left
      let hpy_w2 := hp.right.right
      let hpy_w1 := hp'.right.right 
      have h4 : length c = j-i := by
        have h41 : length (conc p1 c) = length c + length p1:= by
          simp[conc_len]
          rw[Nat.add_comm] 
        have h42 : length p1' = length c + length p1 := by
          rw[<-h41]
          rw[<-hpl']
        have h43 : j = length c + i := by
          rw[hpr] at h42
          rw[hpr'] at h42
          simp[h42]
        simp[h43,<-Nat.sub_eq_iff_eq_add]
      have h5 : p = conc (conc p1 c) p2 := by
        simp[<-hpl']
        simp[<-hpl]
      use w1
      use w2
      use p1
      use c
      use p2
      apply And.intro
      · apply h5
      · apply And.intro
        · apply h4
        · apply And.intro
          · calc 
            w1 = (get_path_ver g p1')[i]'(h2) := (hpy_w1)
            _ = (get_path_ver g p)[i]'(hi) := Eq.symm (conc_get_path_ver g p p1' p2 i h2 hpl)
          · apply hpy_w2
      
        





/--For any path, length of p = 0 implies weight of p = 0--/
theorem len_zero_imp_weight_zero (p : EdgePath g a b) : length p = 0 → weight p = 0 := by
  intro hyp
  match p with
  | EdgePath.point c => simp[weight]
  | EdgePath.cons e _ _ p' => simp[length] at hyp
  
theorem length_geq_zero (p : EdgePath g a b) : length p ≥ 0 := by
  induction p
  case point => simp[]
  case cons e _ _ p' _ => simp[]

/-- Assuming no negative cycles-/
axiom non_negative_cycle (n : Nat) (g : Graph n) (i : Fin n) : ∀ p : EdgePath g i i, weight p ≥ 0 


/-- Initialized version of the "List of paths" which BellmanFord is going to return. The type is a function from
Fin n to Option (EdgePath g source index). Sets the function to none whenever index ≠ source, and an empty
path at the source when index = source.-/
def initPaths (g : Graph n) (source : Fin n) : (index: Fin n) → Option (EdgePath g source index) :=
  let temp : (index: Fin n) → Option (EdgePath g source index) := fun index ↦ if h:index = source then (some (by rw[h]; exact EdgePath.point source)) else none
  temp

theorem weight_initPaths (g : Graph n) (source : Fin n) : weight ((initPaths g source source).get (by simp[initPaths])) = 0 := 
  by simp[initPaths,weight]

theorem path_length_cons (g : Graph n) (e : Edge n) (hyp : e ∈ g.edges) (source: Fin n) (p : EdgePath g source e.source) (len : Nat): 
  (h : length (EdgePath.cons e source hyp p) ≤ len + 1) → 
  (length p ≤ len) := by
    intro h
    rw[length] at h
    simp[Nat.add_comm,Nat.succ_le_succ_iff.mp] at h
    simp[h]
    
    


/- BF starts-/

/-- relax_edge relaxes an edge. In the "List of Paths", whenever there is some path at edge.source, it checks if
the (weight of path at edge.source) + (edge.weight) < (weight of path at edge.target). If so, it updates the "List of Paths"
by replacing the path at edge.target with a new EdgePath, which is just the path at edge.source followed by edge.-/
def relax_edge (paths : (index : Fin n) → Option (EdgePath g source index)) (edge : Edge n) (hyp : edge ∈ g.edges): (index : Fin n) → Option (EdgePath g source index):=
  match (paths edge.source) with
  | none => paths
  | some u => match (paths edge.target)  with
              | none => fun index ↦ if h:index = edge.target then (some (by rw[h]; exact EdgePath.cons edge source hyp u)) else (paths index)
                        
              | some v => if weight v > weight u + edge.weight then
                            fun index ↦ if h:index = edge.target then (some (by rw[h]; exact EdgePath.cons edge source hyp u)) else (paths index)
                          else paths

-- /-- This is the auxiliiary recursive function which recurses over all edges of g.edges in relax. It propogates the hypothesis
-- that the current remaining list of edges is a subset of g.edges in order to continue providing the hypothesis that edge
-- ∈ g.edges which relax_edge requires.-/
-- def recurse_over_all_edges (remaining : List (Edge n)) (hyp : remaining ⊆ g.edges) (paths :(index : Fin n) → Option (EdgePath g source index)) : (index : Fin n) → Option (EdgePath g source index) :=
--   match h: remaining with
--   | [] => paths
--   | head::tail => have tail_is_sub : tail ⊆ g.edges := by 
--                     exact List.subset_of_cons_subset (hyp)
                  
--                   let pathsnext : (index : Fin n) → Option (EdgePath g source index) := relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1)
--                   recurse_over_all_edges tail tail_is_sub pathsnext

/-- Each execution of relax calls relax_edge on the "List of Paths" and each edge in g.edges. Since EdgePath requires
a hypothesis that the edge is in g.edges, we write an extra recursive function rather than using List.foldl.-/
def relax (g : Graph n) (BFn : (index : Fin n) → Option (EdgePath g source index)) (counter : Nat) : (index : Fin n) → Option (EdgePath g source index):= 
  match counter with
  | 0 => BFn
  | m + 1 => let BFnplus1 : (index : Fin n) → Option (EdgePath g source index) := 
              have hyp : g.edges ⊆ g.edges := by simp[]
              let rec over_all_edges : (remaining : List (Edge n)) -> (hyp : remaining ⊆ g.edges) -> (paths :(index : Fin n) → Option (EdgePath g source index)) -> ((index : Fin n) → Option (EdgePath g source index))
                | [], _, paths => paths
                | head::tail, hyp, paths => have tail_is_sub : tail ⊆ g.edges := by 
                                              exact List.subset_of_cons_subset (hyp)
                                            
                                            let pathsnext : (index : Fin n) → Option (EdgePath g source index) := relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1)
                                            over_all_edges tail tail_is_sub pathsnext
              over_all_edges g.edges hyp BFn
             relax g BFnplus1 m

/-- BellmanFord just calls relax with counter = n-1-/
def BellmanFord (g : Graph n) (source : Fin n) : (index : Fin n) → Option (EdgePath g source index) :=
  relax g (initPaths g source) (n - 1)

/- BF Ends-/

/-Examples-/

def graph1 : Graph 4 :=
  {edges := [⟨ 0, 2, 3⟩ , ⟨1, 3, 5⟩ , ⟨ 2, 3, 4⟩ , ⟨ 3, 1, -2⟩  ]}

#eval graph1

def path1 : EdgePath graph1 0 3 :=
  EdgePath.cons ⟨ 2, 3, 4⟩ 0 (by rw[graph1]; simp[]) (EdgePath.cons ⟨ 0, 2, 3⟩ 0 (by rw[graph1]; simp[]) (EdgePath.point 0))

#eval path1

#eval (BellmanFord graph1 0 1)

/- Proof -/
 
/-- In initPaths, if path at index i isSome, then i = source-/
theorem init_path_some_source (g : Graph n) (source : Fin n) (i : Fin n) : ((initPaths g source) i).isSome → i = source := by
  have lm : ¬ i = source → ¬ (initPaths g source i).isSome := by
    intro hyp
    simp[initPaths, hyp]
  rw[not_imp_not] at lm
  assumption

/-- Monotonicity Thm 1. In a "List of Paths", given an edge, if path at edge.source isSome, then after execution of 
relax_edge on this "List of Paths" at this edge, the path at edge.target isSome (i.e. relax_edge doesn't add nones)-/
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

theorem relax_edge_some_given_index (source i : Fin n) (edge : Edge n) (hyp : edge ∈ g.edges)  (paths : (index : Fin n) → Option (EdgePath g source index)) (h : (paths i).isSome)
  : (relax_edge paths edge hyp i).isSome:= by
    match c1 : paths edge.source with
      | none => rw[relax_edge]
                simp[c1]
                exact h
      | some p => match c2 : paths edge.target with
                  | none => if con: i = edge.target then
                              rw[<- con] at c2
                              rw[c2] at h
                              contradiction
                            else 
                              rw[relax_edge]
                              simp[c1, c2, con]
                              exact h

                  | some q => if cond: i = edge.target then 
                                rw[relax_edge]
                                simp[c1, c2, cond]
                                split
                                case inl => simp[]
                                case inr => exact h

                              else 
                                rw[relax_edge]
                                simp[c1, c2, cond]
                                split
                                · exact h
                                · exact h

/-- Monotonicity Thm 2. If path at edge.source isSome and path at edge.target isSome, then the new path at edge.target
(after execution of relax_edge) has weight ≤ weight of original path at edge.target-/
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

theorem relax_edge_leq_given_index (source i : Fin n) (edge : Edge n) (hyp : edge ∈ g.edges)  (paths : (index : Fin n) → Option (EdgePath g source index)) (h : (paths i).isSome)
  : weight ((relax_edge paths edge hyp i).get (by apply relax_edge_some_given_index; exact h)) ≤ weight ((paths i).get h):= by
    match c1 : paths edge.source with
      | none => have lm : relax_edge paths edge hyp i = paths i := by
                  rw[relax_edge]
                  simp[c1]
                simp[lm]
      | some p => match c2 : paths edge.target with
                  | none => if con: i = edge.target then
                              rw[<- con] at c2
                              rw[c2] at h
                              contradiction
                            else 
                              have lm : relax_edge paths edge hyp i = paths i := by
                                rw[relax_edge]
                                simp[c1, c2, con]
                              simp[lm]

                  | some q => if con: i = edge.target then
                                by_cases condition : weight q > weight p + edge.weight
                                case pos => 
                              else 
                                have lm : relax_edge paths edge hyp i = paths i := by
                                  rw[relax_edge]
                                  simp[c1, c2, con]
                                  split
                                  · simp[]
                                  · simp[]
                                simp[lm]


/-If there exists a path of length ≤ counter then after counter many relaxations then it will assigned some distance which is not none-/
theorem path_exists_then_isSome (g : Graph n) (source i : Fin n) (counter : Nat): (p : EdgePath g source i) → (h : length p ≤ counter) →
  ((relax g (initPaths g source) counter) i).isSome := by
    intro p h
    induction counter
    case zero => have h1 : length p ≥ 0 := by apply length_geq_zero
                 simp[] at h
                 have h2 : i = source := by
                  match p with
                  | EdgePath.point c => simp[]
                  | EdgePath.cons e _ _ p' => simp[length] at h
                 have h3 : (relax g (initPaths g source) Nat.zero) = initPaths g source := by simp[relax]
                 rw[h3]
                 rw[h2]
                 simp[initPaths]
    case succ counter ih => 
                            rw[relax]
                            sorry




theorem relax_ind (g : Graph n) (paths : (index : Fin n) → Option (EdgePath g source index)) (counter : Nat)
  : relax g paths (counter+1) = relax g (relax g paths counter) 1 := by
    simp[relax]
    let rec prove : (counter : Nat) → (paths : (index : Fin n) → Option (EdgePath g source index)) → (relax g (relax.over_all_edges g g.edges (by simp[]) paths) counter = relax.over_all_edges g g.edges (by simp[]) (relax g paths counter))
    | 0, paths1 => by simp[relax]
    | m + 1, paths1 => by 
                      simp[relax]
                      exact (prove m (relax.over_all_edges g g.edges (by simp[]) paths1))
    exact prove counter paths

theorem over_edges_isSome (source i : Fin n) (edgelist : List (Edge n)) (hyp : edgelist ⊆ g.edges) (paths :(index : Fin n) → Option (EdgePath g source index)) (h : (paths i).isSome)
  : (relax.over_all_edges g edgelist hyp paths i).isSome := by
    match e : edgelist with
    | [] => simp[relax.over_all_edges]
            exact h
    | head::tail => simp[relax.over_all_edges]
                    have k : (relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1) i).isSome := by apply relax_edge_some_given_index; exact h
                    exact over_edges_isSome source i tail (by exact List.subset_of_cons_subset (hyp)) (relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1)) k

theorem over_edges_leq (source i : Fin n) (edgelist : List (Edge n)) (hyp : edgelist ⊆ g.edges) (paths :(index : Fin n) → Option (EdgePath g source index)) (h : (paths i).isSome)
  : weight ((relax.over_all_edges g edgelist hyp paths i).get (by apply over_edges_isSome; exact h)) ≤  weight ((paths i).get h):= by
    match e : edgelist with
    | [] => simp[relax.over_all_edges]
    | head::tail => simp[relax.over_all_edges]
                    have k : weight ((relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1) i).get (by apply relax_edge_some_given_index; exact h)) ≤ 
                      weight ((paths i).get h):= by
                      apply relax_edge_leq_given_index
                    have l := over_edges_leq source i tail (by exact List.subset_of_cons_subset (hyp)) (relax_edge paths head (by rw[List.cons_subset] at hyp; exact hyp.1)) (by apply relax_edge_some_given_index; exact h)
                    apply Int.le_trans l k



/-- If there is a path at ith index in "List of Paths", then there will be one after one execution of relax-/
theorem relax_isSome (g : Graph n) (source i : Fin n) (h : ((relax g (initPaths g source) counter) i).isSome) :
  ((relax g (initPaths g source) (counter+1)) i).isSome := by
    have h1 : relax g (initPaths g source) (counter + 1) = relax g (relax g (initPaths g source) counter) 1 := by apply relax_ind
    rw[h1]
    simp[relax]
    let v : (index : Fin n) → Option (EdgePath g source index) := (relax g (initPaths g source) counter)
    sorry

      


/-- If there is a path at ith index in "List of Paths", then weight of path after one execution of relax ≤ 
weight of original path-/
theorem relax_leq (g : Graph n) (source i : Fin n) (h : ((relax g (initPaths g source) counter) i).isSome) :
  weight (((relax g (initPaths g source) counter) i).get h) ≥ weight (((relax g (initPaths g source) (counter+1)) i).get (relax_isSome g source i h))
  := by
  have h1 : relax g (initPaths g source) (counter + 1) = relax g (relax g (initPaths g source) counter) 1 := by apply relax_ind
  have h2 : ((relax g (initPaths g source) (counter+1)) i).get (relax_isSome g source i h) = ((relax g (relax g (initPaths g source) counter) 1 i).get (by apply over_edges_isSome; exact h)) := by simp[h1]
  rw[h2]
  simp[relax]
  apply over_edges_leq


/-It states that for given edge e in the graph say both e.source and e.target are assigned distance by BellmanFord algorithm after counter many
relaxations then it states that distance assigned by BellmanFord to e.source + e.weight ≥ distance assigned to BellmanFord to e.target -/
theorem relax_leq_edge (g : Graph n) (e: Edge n) (hyp : e ∈ g.edges) 
  (h1 : ((relax g (initPaths g source) counter) e.source).isSome) (h2 : ((relax g (initPaths g source) counter) e.target).isSome) : 
  weight (((relax g (initPaths g source) counter) e.source).get h1) + e.weight ≥ weight (((relax g (initPaths g source) counter) e.target).get h2) 
  := sorry 


/-The following theorems below state that distance assigned to source is 0 for any (counter : Nat)-/
theorem weight_source_isSome (g : Graph n) (source : Fin n) (counter: Nat): 
  ((relax g (initPaths g source) counter) source).isSome:= by 
  induction counter
  case zero => 
    simp[relax]
    simp[initPaths]
  case succ counter ih =>
    apply (relax_isSome g source source ih) 
     

theorem weight_source_is_zero (g : Graph n) (source : Fin n) (counter: Nat) : 
   weight ( ((relax g (initPaths g source) counter) source).get (weight_source_isSome g source counter) ) = 0 := by
   induction counter
   case zero =>
    simp[relax]
    simp[initPaths]
    simp[weight]
   case succ counter ih =>
    let hyp := (weight_source_isSome g source counter)
    let hyp_next := (weight_source_isSome g source (counter+1)) 
    have h : 
      weight (((relax g (initPaths g source) counter) source).get hyp) 
        ≥ weight (((relax g (initPaths g source) (counter+1)) source).get hyp_next)
        := by simp[relax_leq]
    rw[ih] at h
    have h1 : weight (((relax g (initPaths g source) (counter+1)) source).get hyp_next) ≥ 0 := 
      let p : EdgePath g source source := ((relax g (initPaths g source) (counter+1)) source).get hyp_next 
      non_negative_cycle n g source p
    apply Int.le_antisymm h h1
    
#check Nat.le_antisymm

theorem BellmanFordAux (source : Fin n) (counter : Nat):
  (i: Fin n) → 
  (h: ((relax g (initPaths g source) (counter)) i).isSome) →  
  (p : (EdgePath g source i)) →  
  (h1 : (length p ≤ counter))  →  
  (weight p ≥ weight (((relax g (initPaths g source) (counter)) i).get h)) := by
  --let BF_paths_curr := (relax g (initPaths source) (counter))
  induction counter
  case zero =>
    intro i h p h1
    simp[relax]
    simp[length_geq_zero] at h1
    simp[h1,len_zero_imp_weight_zero]
    have h2 : source = i := Eq.symm ((init_path_some_source g source i) h)
    subst h2
    simp[initPaths,weight]
  case succ counter ih =>
    intro i h p h1
    induction p
    case point source => 
      rw[weight]
      simp[weight_source_is_zero]
    case cons e source hyp p' ih1 =>
        have h2 : length p' ≤ counter := by
          apply path_length_cons g e hyp source p' counter h1
        let path_exists_hyp := (path_exists_then_isSome g source e.source counter p') h2
        let path_exists_hyp_next := (relax_isSome g source e.source path_exists_hyp)
        have h3 : 
          weight p' ≥ weight (((relax g (initPaths g source) (counter)) e.source).get path_exists_hyp) := 
          by apply (ih e.source path_exists_hyp p') h2
        have h4 : 
          weight (((relax g (initPaths g source) (counter)) e.source).get path_exists_hyp) + e.weight ≥ 
          weight (((relax g (initPaths g source) (counter+1)) e.target).get h) :=
          by
            calc
            weight (((relax g (initPaths g source) (counter)) e.source).get path_exists_hyp) + e.weight 
              ≥ weight (((relax g (initPaths g source) (counter + 1)) e.source).get path_exists_hyp_next) + e.weight 
              := (by simp[relax_leq])
            _ ≥ weight (((relax g (initPaths g source) (counter+1)) e.target).get h) 
              := (relax_leq_edge g e hyp path_exists_hyp_next h)
        have h5: weight p' + e.weight ≥ weight (((relax g (initPaths g source) (counter+1)) e.target).get h) :=
          by
            calc
            weight p' + e.weight ≥ weight (((relax g (initPaths g source) (counter)) e.source).get path_exists_hyp) + e.weight
              := (by simp[h3])
            _ ≥ weight (((relax g (initPaths g source) (counter+1)) e.target).get h) := (by simp[h4])
        have h6 : weight (EdgePath.cons e source hyp p') = weight p' + e.weight  := by
          simp[weight]
          apply Int.add_comm e.weight (weight p')
        rw[h6]
        simp[h5]

/-Part 3-/

/-Defining Sub Paths of a Path-/

/-- For any index i and path p from source to i, there exists a path with atmost n-1 edges whose weight ≤ weight p-/

theorem list_repeat (n : Nat) (l : List (Fin n)) : 
  (List.length l > n) → (∃ i j : Fin (List.length l), (i < j) ∧ (l[i] = l[j])) := by sorry



theorem Reduced_Path_theorem (g : Graph n) (source : Fin n) : (i : Fin n) → (p : EdgePath g source i) → 
  (∃ p' : EdgePath g source i, (length p' ≤ n -1) ∧ (weight p ≥ weight p')) 
  := by 
  intro i p
  by_cases h : List.length (get_path_ver g p) > n
  case neg =>
    use p
    simp[length_path_to_list] at h
    simp[h]
    apply Nat.le_sub_of_add_le h
  case pos =>
    have h1 : ∃ j k : Fin (List.length (get_path_ver g p)), (j < k) ∧ ((get_path_ver g p)[j] = (get_path_ver g p)[k]) := by 
      apply (list_repeat n (get_path_ver g p)) h
    match h1 with
    | ⟨ j , k , hind ⟩ => 
      let hind_f := hind.left
      let ther := con_sub_cycle_paths_exists g p j k hind_f j.isLt k.isLt
      match ther with
      | ⟨ w1, w2, p1, c, p2, hsp ⟩ =>
        have hw : w1 = w2 := by
          calc 
          w1 = (get_path_ver g p)[j] := (hsp.right.right.left)
          _ = (get_path_ver g p)[k] := (hind.right)
          _ = w2 := (Eq.symm hsp.right.right.right)
        subst hw
        let hp := (Reduced_Path_theorem g source i (conc p1 p2))
        match hp with
        | ⟨ p', hp'⟩ => 
          have hp1 : weight p ≥ weight (conc p1 p2) := by
            rw[hsp.left]
            simp[con_w]
            apply non_negative_cycle
          use p'
          apply And.intro
          · apply hp'.left
          · calc
            weight p ≥ weight (conc p1 p2) := (hp1)
            _ ≥ weight p' := (hp'.right)
termination_by Reduced_Path_theorem g source i p => length p
decreasing_by
  simp_wf
  rw[hsp.left]
  simp[conc_len]
  rw[hsp.right.left]
  apply Nat.sub_pos_of_lt
  apply hind.left       
 
#check Nat.sub_pos_of_lt  
/-It states that if there exists a path p from source to i then BellamnFord will assign a distance to i-/
theorem path_exists_then_isSome_BellmanFord (g : Graph n) (source : Fin n) : (i : Fin n) →  (p : EdgePath g source i) →  
  ((BellmanFord g source) i).isSome := by
  intro i p
  let ther : (∃ p' : EdgePath g source i, (length p' ≤ n -1) ∧ (weight p ≥ weight p')) := Reduced_Path_theorem g source i p 
  match ther with
  | ⟨ p' , hp' ⟩ => exact (path_exists_then_isSome g source i (n-1) p' hp'.left) 

/-Correctness Of BellmanFord-/
theorem BellamnFordPf (g: Graph n) (source : Fin n) : 
  (i : Fin n) → 
  (p : EdgePath g source i) →  
  (weight p ≥ weight (((BellmanFord g source) i).get (path_exists_then_isSome_BellmanFord g source i p))) := 
  by 
    intro i p
    let ther : (∃ p' : EdgePath g source i, (length p' ≤ n -1) ∧ (weight p ≥ weight p')) := Reduced_Path_theorem g source i p
    match ther with
    | ⟨ p', hp'⟩ => 
      have h : weight p' ≥ weight (((BellmanFord g source) i).get (path_exists_then_isSome_BellmanFord g source i p)) :=
        by
          apply BellmanFordAux source (n-1) i (path_exists_then_isSome_BellmanFord g source i p) p' hp'.left
      calc
      weight p ≥ weight p' := (hp'.right)
      _ ≥ weight (((BellmanFord g source) i).get (path_exists_then_isSome_BellmanFord g source i p)) := (h)        

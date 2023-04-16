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

structure BFListLengthHyp (n : Nat) where
  BFList : List (BFVertex n)
  hyp : BFList.length = n


inductive EdgePath (n : ℕ) : Fin n → Fin n → Type   where
| point (v : Fin n) : EdgePath n v v
| cons  (e : Edge n) (w : Fin n) (p : EdgePath n e.target w) : EdgePath n e.source w

def weight (p : EdgePath n a b) : Int := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons e _ p' => e.weight + weight p'

def length (p : EdgePath n a b) : Nat := 
  match p with
  |EdgePath.point _  => 0
  |EdgePath.cons _ _ p' => 1 + length p'

def conc (p1 : EdgePath n u v) (p2 : EdgePath n v w) : EdgePath n u w :=
  match p1 with 
  | EdgePath.point _ => p2
  | EdgePath.cons head _ tail => EdgePath.cons head _ (conc tail p2)

theorem weight_conc (p1 : EdgePath n u v) (p2 : EdgePath n v w) : weight (conc p1 p2) = weight p1 + weight p2 := by
  induction p1
  case point u => simp [weight,conc]
  case cons head v tail ih =>
    rw[weight,conc,weight,ih]
    simp[add_assoc]


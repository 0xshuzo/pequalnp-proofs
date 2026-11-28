import PEqualNP.Defs
namespace Research10009.Discharge
open Finset
def left (g : Nat) := g%32
def right (g : Nat) := (g/32)%32
def fee (g : Nat) := g/1024
def paid (pick : Nat → Nat) (i : Nat) (G : List Nat) :=
  (G.map (fun z => if pick z=i then fee z else 0)).sum

theorem distribute (P : Finset Nat) (s : Nat→Nat) (G : List Nat) :
    (∑i∈P,paid s i G) = (G.map (fun z => if s z∈P then fee z else 0)).sum := by
  induction G with
  | nil => simp [paid]
  | cons g G ih =>
    simp only [paid,List.map_cons,List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib,ih]
    simp

theorem discharge (P Q : Finset Nat) (G : List Nat)
    (sep : ∀g∈G,left g∈P → right g∉Q) :
    (∑i∈P,paid left i G) + (∑j∈Q,paid right j G) ≤ (G.map fee).sum := by
  rw [distribute,distribute]
  induction G with
  | nil => simp
  | cons g G ih =>
    have one := sep g (by simp)
    have rest := ih (fun z hz => sep z (by simp [hz]))
    simp only [List.map_cons,List.sum_cons]
    by_cases a : left g∈P
    · simp only [if_pos a,if_neg (one a),zero_add]
      omega
    · simp only [if_neg a,zero_add]
      split <;> omega

theorem bounded (P Q : Finset Nat) (G : List Nat) (w v : Nat→Nat)
    (sep : ∀g∈G,left g∈P → right g∉Q)
    (l : ∀i∈P,w i≤paid left i G) (r : ∀j∈Q,v j≤paid right j G)
    (cost : (G.map fee).sum≤72) : (∑i∈P,w i)+(∑j∈Q,v j)≤72 :=
  (Nat.add_le_add (Finset.sum_le_sum l) (Finset.sum_le_sum r)).trans
    ((discharge P Q G sep).trans cost)
end Research10009.Discharge

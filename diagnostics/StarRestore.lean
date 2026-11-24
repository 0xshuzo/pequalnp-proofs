import Mathlib
import PEqualNP.Defs

namespace Restore4885

abbrev H (X : Type) := Bool → Set X

def comb {X : Type} (d : Bool) (a b : H X) (c : Bool) : Set X :=
  if c = d then a c ∪ b c else a c ∩ b c

def gate {X : Type} (P : List (H X)) (y : H X) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ d : Bool, ∀ c, y c ⊆ comb d a b c

def valid {X : Type} (U A : List (H X)) : Prop :=
  ∀ i : Fin A.length, gate (U ++ A.take i.val) (A.get i)

-- The ordered-list extension step is adapted from P_snoc in L_meta_3533.
theorem snoc {X : Type} {U A : List (H X)} {v : H X}
    (ok : valid U A) (h : gate (U ++ A) v) : valid U (A ++ [v]) := by
  rintro ⟨i, hi⟩
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i A.length with lt | ge
  · have old := ok ⟨i,lt⟩
    simpa [List.take_append_of_le_length (Nat.le_of_lt lt), List.getElem_append_left lt] using old
  · have eq : i = A.length := by omega
    subst i
    simpa using h

theorem appendGate {X : Type} {U A : List (H X)} {a b : H X}
    (ok : valid U A) (ha : a ∈ U ++ A) (hb : b ∈ U ++ A) (d : Bool) :
    valid U (A ++ [comb d a b]) :=
  snoc ok ⟨a,ha,b,hb,d,fun _ => Set.Subset.rfl⟩

theorem block {X : Type} {U A : List (H X)} (h : valid U A)
    {q a b l y : H X} (hq : q ∈ U ++ A) (ha : a ∈ U ++ A) (hb : b ∈ U ++ A)
    (hl : l ∈ U ++ A) (hy : y ∈ U ++ A) :
    ∃ G : List (H X), G.length = A.length + 4 ∧ valid U G ∧
      comb true y (comb false l (comb true (comb true q a) b)) ∈ U ++ G := by
  let s := comb true q a
  let t := comb true s b
  let e := comb false l t
  let o := comb true y e
  let A1 := A ++ [s]
  let A2 := A1 ++ [t]
  let A3 := A2 ++ [e]
  have keep {B : List (H X)} {g v : H X} (hv : v ∈ U ++ B) :
      v ∈ U ++ (B ++ [g]) := by
    rw [← List.append_assoc]
    exact List.mem_append_left _ hv
  have h1 : valid U A1 := appendGate h hq ha true
  have hs : s ∈ U ++ A1 := List.mem_append_right _ (by simp [A1])
  have h2 : valid U A2 := appendGate h1 hs (keep hb) true
  have ht : t ∈ U ++ A2 := List.mem_append_right _ (by simp [A2])
  have h3 : valid U A3 := appendGate h2 (keep (keep hl)) ht false
  have he : e ∈ U ++ A3 := List.mem_append_right _ (by simp [A3])
  refine ⟨A3 ++ [o], by simp [A3,A2,A1], appendGate h3 (keep (keep (keep hy))) he true, ?_⟩
  exact List.mem_append_right _ (by simp [o,e,t,s])

theorem exact_child : ∀ (X : Type) (U : List (Bool → Set X)),
      let m := fun (d : Bool) (a b : Bool → Set X) (c : Bool) =>
        if c = d then a c ∪ b c else a c ∩ b c
      let ok := fun (A : List (Bool → Set X)) => ∀ i : Fin A.length, let P := U ++ A.take i.val
          ∃ a ∈ P, ∃ b ∈ P, ∃ d : Bool, ∀ c : Bool,
            A.get i c ⊆ if c = d then a c ∪ b c else a c ∩ b c
      ∀ A, ok A → ∀ q ∈ U ++ A, ∀ a ∈ U ++ A, ∀ b ∈ U ++ A,
        ∀ l ∈ U ++ A, ∀ y ∈ U ++ A, ∃ G : List (Bool → Set X),
        G.length = A.length + 4 ∧ ok G ∧
          m true y (m false l (m true (m true q a) b)) ∈ U ++ G := by
  intro X U
  try dsimp only
  intro A ok q hq a ha b hb l hl y hy
  exact block ok hq ha hb hl hy

end Restore4885

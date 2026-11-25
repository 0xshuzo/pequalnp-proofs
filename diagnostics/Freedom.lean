import Mathlib
import PEqualNP.Defs
namespace Freedom2626
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 8192
abbrev I := Fin 13
abbrev V := Fin (13+13)
def D : Finset I := {0,1,3,9}
def seeds : List (Nat × Nat) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
def mult : List I := [1,3,9]
def row (x : Nat × Nat) (m t : I) (sw : Bool) : V → Bool :=
  let get := fun (a b : Nat) (i : I) => if sw=true then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
  Fin.append (get x.1 x.2) (get x.2 x.1)
def pair (p l : I) (i : V) := decide (i=p.castAdd 13 ∨ i=Fin.natAdd 13 l)
def Positive (C : Circuit) := ∀ p l : I, (∃ v∈D,p=l+v) → circuitFun 26 C (pair p l)=true
def Negative (C : Circuit) := ∀ s∈seeds,∀ m∈mult, ∀ (t : I) (w : Bool), circuitFun 26 C (row s m t w)=false

def existsEdge (x : V → Bool) : Prop := ∃ p l : I, (∃ v∈D,p=l+v) ∧
  x (p.castAdd 13)=true ∧ x (Fin.natAdd 13 l)=true
instance (x : V → Bool) : Decidable (existsEdge x) := by unfold existsEdge; infer_instance
def triple (x : V → Bool) := x 0 && x 1 && x 3
def strict (x : V → Bool) := decide (existsEdge x) || triple x
theorem upwards : Monotone strict := by
  intro x y le
  apply Bool.le_iff_imp.mpr
  intro h
  rcases Bool.or_eq_true_iff.mp h with eh|th
  · obtain ⟨p,l,edge,hp,hl⟩ := of_decide_eq_true eh
    exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ⟨p,l,edge,
      Bool.le_iff_imp.mp (le _) hp,Bool.le_iff_imp.mp (le _) hl⟩))
  · have tri : x 0=true ∧ x 1=true ∧ x 3=true := by simpa [triple,Bool.and_eq_true,and_assoc] using th
    apply Bool.or_eq_true_iff.mpr
    right
    simpa [triple,Bool.and_eq_true,and_assoc] using
      And.intro (Bool.le_iff_imp.mp (le _) tri.1) (And.intro (Bool.le_iff_imp.mp (le _) tri.2.1) (Bool.le_iff_imp.mp (le _) tri.2.2))
theorem positive (p l : I) (h : ∃ v∈D,p=l+v) : strict (pair p l)=true := by
  apply Bool.or_eq_true_iff.mpr
  left
  exact decide_eq_true ⟨p,l,h,by simp [pair],by simp [pair]⟩
def safe (s : Nat × Nat) := ∀ m∈mult, ∀ (t : I) (w : Bool), strict (row s m t w)=false
instance (s : Nat × Nat) : Decidable (safe s) := by unfold safe mult; infer_instance
theorem s0 : safe (7,904) := by decide +kernel
theorem s1 : safe (13,2848) := by decide +kernel
theorem s2 : safe (19,708) := by decide +kernel
theorem s3 : safe (21,2720) := by decide +kernel
theorem s4 : safe (25,2656) := by decide +kernel
theorem s5 : safe (37,2440) := by decide +kernel
theorem s6 : safe (41,2370) := by decide +kernel
theorem s7 : safe (133,808) := by decide +kernel

theorem negative : ∀ s∈seeds,∀ m∈mult,∀ (t : I) (w : Bool),strict (row s m t w)=false := by
  intro s hs
  simp only [seeds,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact s0 | exact s1 | exact s2 | exact s3 | exact s4 | exact s5 | exact s6 | exact s7
theorem fails : ∃ x : V → Bool, ¬existsEdge x ∧ strict x=true := by
  refine ⟨fun i => decide (i=0 ∨ i=1 ∨ i=3),?_⟩
  decide +kernel
end Freedom2626

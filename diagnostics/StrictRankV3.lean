import PEqualNP.Defs
namespace Research9350.StrictRank
open Finset
abbrev V := Fin 21
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (r c : V) : Bool := !((board.getD r.val 0).testBit c.val)
def column (c r : V) : ℚ := if zeroCell r c then 1 else 0
def dual (c r : V) : ℚ := if zeroCell r c then 1 else -3
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem evaluate : ∀ i j : V, (∑ r : V, dual i r * column j r) =
    if i=j then 16 else 0 := by decide +kernel

theorem independent : LinearIndependent ℚ column := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff rel i
  have coord (r : V) : (∑ j : V, coeff j * column j r)=0 := by
    simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun rel r
  have dot : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r))=0 := by
    simp [coord]
  have swap : (∑ r : V, dual i r * (∑ j : V, coeff j * column j r)) =
      ∑ j : V, coeff j * (∑ r : V, dual i r * column j r) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    ring
  rw [swap] at dot
  simp_rw [evaluate] at dot
  have atI : (∑ j : V, coeff j * (if i=j then 16 else 0))=coeff i * 16 := by
    rw [sum_eq_single_of_mem i (mem_univ i)]
    · simp
    · intro j _ ne
      simp [Ne.symm ne]
  rw [atI] at dot
  linarith

abbrev Box := Finset V × Finset V
def rv (b : Box) (r : V) : ℚ := if r ∈ b.1 then 1 else 0
def cv (b : Box) (c : V) : ℚ := if c ∈ b.2 then 1 else 0
def unitRow (s r : V) : ℚ := if s = r then 1 else 0


def pair (c : V) (f : V → ℚ) := ∑ r : V, dual c r * f r
def mix (S : Finset V) (x : V) (g : V → ℚ) (i : ↥(insert x S)) : V → ℚ :=
  if i.val = x then g else column i.val

theorem replaceIndependent (S : Finset V) (x : V) (g : V → ℚ)
    (ng : pair x g ≠ 0) : LinearIndependent ℚ (mix S x g) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff rel i
  let z : ↥(insert x S) := ⟨x,mem_insert_self _ _⟩
  have coord (r : V) : (∑ j, coeff j * mix S x g j r) = 0 := by
    simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun rel r
  have dot : (∑ j, coeff j * pair x (mix S x g j)) = 0 := by
    simp only [pair,mul_sum]
    rw [sum_comm]
    have inner (r : V) : (∑ j, coeff j * (dual x r * mix S x g j r)) = 0 := by
      calc
        _ = dual x r * (∑ j, coeff j * mix S x g j r) := by
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [coord,mul_zero]
    exact (Finset.sum_congr rfl (fun r _ => inner r)).trans (by simp)
  have cz : coeff z = 0 := by
    rw [sum_eq_single_of_mem z (mem_univ z)] at dot
    · have mm : mix S x g z = g := by simp [mix,z]
      rw [mm] at dot
      exact (mul_eq_zero.mp dot).resolve_right ng
    · intro b _ ne
      have bx : b.val ≠ x := fun eq => ne (Subtype.ext eq)
      simp [mix,bx,pair,evaluate,Ne.symm bx]
  have rel' : (∑ j : ↥(insert x S), coeff j • column j.val) = 0 := by
    rw [← rel]
    apply sum_congr rfl
    intro b _
    by_cases hb : b.val = x
    · have same : b = z := Subtype.ext hb
      subst b
      rw [cz]
      simp
    · simp [mix,hb]
  have li := independent.comp (fun j : ↥(insert x S) => j.val) Subtype.val_injective
  exact Fintype.linearIndependent_iff.mp li coeff rel' i

def actual {m : Nat} (B : Fin m → Box) (c : V) : V → ℚ :=
  ∑ i : Fin m, cv (B i) c • rv (B i)

theorem strictBudget {m : Nat} (B : Fin m → Box) (S : Finset V) (x : V) (outside : x ∉ S)
    (agree : ∀ c ∈ S, actual B c = column c)
    (law : ∀ r, zeroCell r x = false → actual B x r = 0)
    (lower : ∀ r, column x r ≤ actual B x r) :
    S.card + 1 ≤ m := by
  classical
  let R (i : Fin m) := rv (B i)
  let W := Submodule.span ℚ (Set.range R)
  have represented (c : V) : actual B c ∈ W := by
    apply Submodule.sum_mem
    intro i _
    exact W.smul_mem _ (show R i ∈ W from Submodule.subset_span ⟨i,rfl⟩)
  have positive : 0 < pair x (actual B x) := by
    have term (r : V) : dual x r * column x r ≤ dual x r * actual B x r := by
      cases z : zeroCell r x with
      | true => simpa [dual,z] using lower r
      | false => simp [dual,column,z,law r z]
    have H := sum_le_sum (s := (univ : Finset V)) (fun r _ => term r)
    rw [evaluate] at H
    simp only [ite_true] at H
    change 0 < ∑ r : V, dual x r * actual B x r
    linarith
  let g := mix S x (actual B x)
  have inside (i : ↥(insert x S)) : g i ∈ W := by
    by_cases h : i.val = x
    · simpa [g,mix,h] using represented x
    · have hs : i.val ∈ S := (mem_insert.mp i.property).resolve_left h
      simpa [g,mix,h,← agree i.val hs] using represented i.val
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (i : ↥(insert x S)) : ↥W := ⟨g i,inside i⟩
  have li : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    exact replaceIndependent S x _ positive.ne'
  have lo : (insert x S).card ≤ Module.finrank ℚ W := by
    rw [← Fintype.card_coe (insert x S)]
    exact li.fintype_card_le_finrank
  have hi : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa using Fintype.card_range_le R
  rw [card_insert_of_notMem outside] at lo
  omega

end Research9350.StrictRank

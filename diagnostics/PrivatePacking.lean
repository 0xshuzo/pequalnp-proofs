import PEqualNP.Outside.L_meta_10006
namespace PEqualNP.Outside.L_meta_10008.PrivatePacking
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators
abbrev T := Fin 8 × Fin 31
abbrev C := V × V
def rbase (z : Fin 8) (i : Fin 3) := ([26, 27, 30, 24, 25, 30, 19, 29, 30, 14, 16, 30, 19, 28, 30, 23, 27, 30, 16, 26, 30, 17, 23, 30] : List Nat).getD (3*z.val+i.val) 0
def cbase (z : Fin 8) (i : Fin 3) := ([3, 25, 2, 29, 19, 0, 5, 25, 18, 5, 3, 20, 3, 25, 23, 3, 29, 22, 25, 5, 15, 29, 6, 12] : List Nat).getD (3*z.val+i.val) 0
def slot (t : T) (i : Fin 3) : C :=
 (⟨(rbase t.1 i + t.2.val)%31, Nat.mod_lt _ (by decide)⟩,
  ⟨(cbase t.1 i + t.2.val)%31, Nat.mod_lt _ (by decide)⟩)
def indexTag : List Nat := [0, 1, 5, 0, 0, 1, 0, 0, 0, 6, 6, 5, 7, 7, 7, 4, 6, 2, 3, 2, 0, 3, 3, 5, 4, 1, 0, 2, 4, 0, 0]
def pointTag : List Nat := [0, 30, 27, 30, 0, 24, 0, 0, 26, 16, 26, 23, 17, 30, 23, 19, 30, 19, 16, 30, 0, 30, 14, 30, 30, 25, 0, 29, 28, 27, 0]
def back (c : C) : T :=
  let d := (c.2.val+31-c.1.val)%31
  (⟨(indexTag.getD d 0)%8, Nat.mod_lt _ (by decide)⟩,
   ⟨(c.1.val+31-pointTag.getD d 0)%31, Nat.mod_lt _ (by decide)⟩)
def rowCheck (z : Fin 8) := ∀ s : Fin 31, ∀ i j : Fin 3,
  back (slot (z,s) i) = (z,s) ∧
    matrix (slot (z,s) i).1 (slot (z,s) j).2 = decide (i ≠ j)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root0 : rowCheck 0 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root1 : rowCheck 1 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root2 : rowCheck 2 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root3 : rowCheck 3 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root4 : rowCheck 4 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root5 : rowCheck 5 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root6 : rowCheck 6 := by unfold rowCheck; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
private theorem root7 : rowCheck 7 := by unfold rowCheck; decide +kernel
theorem packCheck (t : T) (i j : Fin 3) : back (slot t i) = t ∧
    matrix (slot t i).1 (slot t j).2 = decide (i ≠ j) := by
  obtain ⟨z,s⟩ := t
  fin_cases z
  · exact root0 s i j
  · exact root1 s i j
  · exact root2 s i j
  · exact root3 s i j
  · exact root4 s i j
  · exact root5 s i j
  · exact root6 s i j
  · exact root7 s i j

theorem privateTriangle {k : Nat} (R : Fin k → Box) (cap : k ≤ 17)
    (pure : ∀ t, plain (R t))
    (cov : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    ∃ t : T, ∀ i : Fin 3, multiplicity R (slot t i).1 (slot t i).2 = 1 := by
  classical
  have area := total_load R pure cov count_table
  have up := sum_le_sum (s := (univ : Finset (Fin k))) (fun t _ => Area.matrix_area_le_60 (R t) (pure t))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at up
  have excess : ∑ j, load matrix R j ≤ 245 := by omega
  let bad : Finset C := univ.filter (fun c => 0 < extra matrix R c.1 c.2)
  have countBad : bad.card ≤ 245 := by
    have ind (c : C) : (if 0 < extra matrix R c.1 c.2 then 1 else 0) ≤ extra matrix R c.1 c.2 := by split <;> omega
    have b := sum_le_sum (s := (univ : Finset C)) (fun c _ => ind c)
    change (univ.filter (fun c : C => 0 < extra matrix R c.1 c.2)).card ≤ 245
    rw [Finset.card_filter]
    apply b.trans
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact excess
  by_contra missing
  have findBad (t : T) : ∃ i : Fin 3, slot t i ∈ bad := by
    by_contra absent
    apply missing
    refine ⟨t,fun i => ?_⟩
    have e : extra matrix R (slot t i).1 (slot t i).2 = 0 := by
      by_contra h
      apply absent
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩⟩
    have inc := (packCheck t i i).2
    have bl : matrix (slot t i).1 (slot t i).2 = false := by simpa using inc
    simpa [zeroEntry,bl,e] using multiplicity_eq matrix R pure cov (slot t i).1 (slot t i).2
  let f (t : T) := slot t (findBad t).choose
  have inj : Function.Injective f := by
    intro a b eq
    have ha := (packCheck a (findBad a).choose (findBad a).choose).1
    have hb := (packCheck b (findBad b).choose (findBad b).choose).1
    exact ha.symm.trans ((congrArg back eq).trans hb)
  have sub : (univ.image f) ⊆ bad := by
    intro c hc
    obtain ⟨t,_,rfl⟩ := mem_image.mp hc
    exact (findBad t).choose_spec
  have h := card_le_card sub
  rw [card_image_of_injective _ inj] at h
  have n : (univ : Finset T).card = 248 := by decide
  omega
end PEqualNP.Outside.L_meta_10008.PrivatePacking

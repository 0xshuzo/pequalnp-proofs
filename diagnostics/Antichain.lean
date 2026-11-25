import Mathlib
import PEqualNP.Outside.L_meta_697
import PEqualNP.Outside.L_meta_696
namespace Low606
open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.LowMergeProof

def NoRect {P L : Nat} (inc : Fin P → Fin L → Bool) := ∀ p q w v,
    p≠q → w≠v → ¬(inc p w=true ∧ inc p v=true ∧ inc q w=true ∧ inc q v=true)

theorem two {P L : Nat} {inc : Fin P → Fin L → Bool} {C : Circuit} {g : Nat} {w : Fin L}
    (h : IsLowMerge P L inc C g w) : 2≤(aliveSet P L C g w).card := by
  obtain ⟨hg,a,ha,b,hb,gate,_,ab,ba⟩ := h
  obtain ⟨p,pa,pb⟩ := Finset.not_subset.mp ab
  obtain ⟨q,qb,qa⟩ := Finset.not_subset.mp ba
  apply Finset.one_lt_card.mpr
  have atOr (v : Fin P) : wireVal C (pointLineInput P L v w) g =
      (wireVal C (pointLineInput P L v w) a || wireVal C (pointLineInput P L v w) b) := by
    have len : (pointLineInput P L v w).length=P+L := by simp [pointLineInput,restrictInput]
    have eq := PEqualNP.Outside.L_meta_697_aux.or_val C (pointLineInput P L v w) (g-(P+L)) a b gate
      (by rw [len];omega) (by rw [len];omega)
    simpa only [wireVal,len,Nat.add_sub_cancel' hg] using eq
  have zero (v : Fin P) (a : Nat) : v∈aliveSet P L C a w ↔ wireVal C (pointLineInput P L v w) a=true := by
    simp [aliveSet]
  refine ⟨p,?_,q,?_,fun e=>qa (e ▸ pa)⟩
  · rw [zero,atOr,(zero _ _).mp pa,Bool.true_or]
  · rw [zero,atOr,(zero _ _).mp qb,Bool.or_true]

theorem inter {P L : Nat} {inc : Fin P → Fin L → Bool} {C : Circuit} {g : Nat} {w v : Fin L}
    (geometry : NoRect inc) (ne : w≠v) (hw : IsLow P L inc C g w) (hv : IsLow P L inc C g v) :
    ((aliveSet P L C g w) ∩ (aliveSet P L C g v)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra neq
  have aw := alive_sub_line inc C g w hw (Finset.mem_inter.mp ha).1
  have av := alive_sub_line inc C g v hv (Finset.mem_inter.mp ha).2
  have bw := alive_sub_line inc C g w hw (Finset.mem_inter.mp hb).1
  have bv := alive_sub_line inc C g v hv (Finset.mem_inter.mp hb).2
  exact geometry a b w v neq ne ⟨(Finset.mem_filter.mp aw).2,(Finset.mem_filter.mp av).2,
    (Finset.mem_filter.mp bw).2,(Finset.mem_filter.mp bv).2⟩

theorem comparable {P L : Nat} {inc : Fin P → Fin L → Bool} {C : Circuit} {g : Nat} {w v : Fin L}
    (geometry : NoRect inc) (hw : IsLowMerge P L inc C g w) (hv : IsLow P L inc C g v)
    (ordered : aliveSet P L C g w ⊆ aliveSet P L C g v) : w=v := by
  have lw : IsLow P L inc C g w := by obtain ⟨_,_,_,_,_,_,h,_,_⟩ := hw; exact h
  by_contra neq
  have limit := inter geometry neq lw hv
  rw [Finset.inter_eq_left.mpr ordered] at limit
  have lb := two hw
  omega

theorem chainBudget {P L k : Nat} {inc : Fin P → Fin L → Bool} {C : Circuit} (g : Nat)
    (geometry : NoRect inc) (color : Fin L → Fin k)
    (chain : ∀ w v, color w=color v →
       aliveSet P L C g w ⊆ aliveSet P L C g v ∨ aliveSet P L C g v ⊆ aliveSet P L C g w) :
    (Finset.univ.filter fun w=>IsLowMerge P L inc C g w).card ≤ k := by
  classical
  let S := Finset.univ.filter fun w=>IsLowMerge P L inc C g w
  let f (s : S) := color s.val
  have hf : Function.Injective f := by
    intro a b eq
    have ha := (Finset.mem_filter.mp a.property).2
    have hb := (Finset.mem_filter.mp b.property).2
    have low {w : Fin L} (h : IsLowMerge P L inc C g w) : IsLow P L inc C g w := by
      obtain ⟨_,_,_,_,_,_,h,_,_⟩ := h; exact h
    apply Subtype.ext
    rcases chain _ _ eq with ab|ba
    · exact comparable geometry ha (low hb) ab
    · exact (comparable geometry hb (low ha) ba).symm
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
end Low606

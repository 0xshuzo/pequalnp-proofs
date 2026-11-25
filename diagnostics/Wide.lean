import Mathlib
import PEqualNP.Defs

namespace Exchange1593

def Indep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

theorem no3 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c a) (n01 : a ≠ b) (n02 : a ≠ c) (n12 : b ≠ c) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 SimpleGraph.Walk.nil))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n12,n12.symm]
  have h := girth a W valid
  simp [W] at h

theorem no4 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n12 : b ≠ c) (n13 : b ≠ d) (n23 : c ≠ d) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 SimpleGraph.Walk.nil)))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n12,n12.symm,n13,n13.symm,n23,n23.symm]
  have h := girth a W valid
  simp [W] at h

theorem no5 {n : ℕ} (G : SimpleGraph (Fin n)) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (a b c d e : Fin n) (e0 : G.Adj a b) (e1 : G.Adj b c) (e2 : G.Adj c d) (e3 : G.Adj d e) (e4 : G.Adj e a) (n01 : a ≠ b) (n02 : a ≠ c) (n03 : a ≠ d) (n04 : a ≠ e) (n12 : b ≠ c) (n13 : b ≠ d) (n14 : b ≠ e) (n23 : c ≠ d) (n24 : c ≠ e) (n34 : d ≠ e) : False := by
  let W : G.Walk a a := SimpleGraph.Walk.cons e0 (SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e3 (SimpleGraph.Walk.cons e4 SimpleGraph.Walk.nil))))
  have valid : W.IsCycle := by
    change (SimpleGraph.Walk.cons e0 _).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · simp [SimpleGraph.Walk.cons_isPath_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
    · simp [Sym2.eq_iff,n01,n01.symm,n02,n02.symm,n03,n03.symm,n04,n04.symm,n12,n12.symm,n13,n13.symm,n14,n14.symm,n23,n23.symm,n24,n24.symm,n34,n34.symm]
  have h := girth a W valid
  simp [W] at h

open PEqualNP.EdgeOwnership

theorem wide {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Finset (Fin n)) (degree : ∀ u∈D, 2≤G.degree u)
    (girth : ∀ u (w : G.Walk u u), w.IsCycle → 7 ≤ w.length)
    (A B : (Fin n → Bool) → Bool) (ma : Monotone A) (mb : Monotone B)
    (table : ∀ u v, (A (pairInput u v) && B (pairInput u v)) = true ↔ G.Adj u v) :
    (∀ u ∈ D, ∃ x, A (Function.update x u false) ≠ A x) ∨
    (∀ u ∈ D, ∃ x, B (Function.update x u false) ≠ B x) := by
  classical
  by_contra! bad
  obtain ⟨⟨u,hu,blindA⟩,⟨v,hv,blindB⟩⟩ := bad
  have bleach {r s : Fin n} (diff : r≠s) :
      Function.update (pairInput r s) r false = pairInput s s := by
    funext w
    by_cases e:w=r
    · subst w
      simp [pairInput,diff]
    · simp [Function.update_of_ne e,pairInput,e]
  have aHot {a} (e : G.Adj u a) : A (pairInput a a)=true := by
    have on := (Bool.and_eq_true_iff.mp ((table u a).mpr e)).1
    have m := blindA (pairInput u a)
    rw [bleach e.ne] at m
    exact m.trans on
  have bHot {b} (e : G.Adj v b) : B (pairInput b b)=true := by
    have on := (Bool.and_eq_true_iff.mp ((table v b).mpr e)).2
    have m := blindB (pairInput v b)
    rw [bleach e.ne] at m
    exact m.trans on
  have lower (a b : Fin n) : pairInput a a ≤ pairInput a b ∧ pairInput b b ≤ pairInput a b := by
    constructor <;> intro w <;> apply Bool.le_iff_imp.mpr <;> intro h
    · have e : w=a := by simpa [pairInput] using h
      simp [pairInput,e]
    · have e : w=b := by simpa [pairInput] using h
      simp [pairInput,e]
  have cross {a b} (ha : G.Adj u a) (hb : G.Adj v b) : G.Adj a b := by
    apply (table a b).mp
    apply Bool.and_eq_true_iff.mpr
    exact ⟨Bool.le_iff_imp.mp (ma (lower a b).1) (aHot ha),
      Bool.le_iff_imp.mp (mb (lower a b).2) (bHot hb)⟩
  have cu : 1 < (G.neighborFinset u).card := by rw [SimpleGraph.card_neighborFinset_eq_degree];exact degree u hu
  have cv : 1 < (G.neighborFinset v).card := by rw [SimpleGraph.card_neighborFinset_eq_degree];exact degree v hv
  obtain ⟨a,aU,c,cU,ac⟩ := Finset.one_lt_card.mp cu
  obtain ⟨b,bV,d,dV,bd⟩ := Finset.one_lt_card.mp cv
  have ab := cross ((G.mem_neighborFinset u a).mp aU) ((G.mem_neighborFinset v b).mp bV)
  have cb := cross ((G.mem_neighborFinset u c).mp cU) ((G.mem_neighborFinset v b).mp bV)
  have cd := cross ((G.mem_neighborFinset u c).mp cU) ((G.mem_neighborFinset v d).mp dV)
  have ad := cross ((G.mem_neighborFinset u a).mp aU) ((G.mem_neighborFinset v d).mp dV)
  exact no4 G girth a b c d ab cb.symm cd ad.symm ab.ne ac ad.ne cb.ne.symm bd cd.ne

end Exchange1593

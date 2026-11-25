import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3696

namespace Plane2583

lemma pencil_le (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ (x8 : Fin N), Fintype.card { x9 : Fin N // I x9 x8 } = q + 1)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p : Fin N) (Lp : Finset (Fin N)) (hLp : ∀ l ∈ Lp, I p l) : Lp.card ≤ q + 1 := by
  have hT : ∀ l ∈ Lp, ((Finset.univ.filter (fun r => I r l)).erase p).card = q := by
    intro l hl
    have hpl : I p l := hLp l hl
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl⟩)]
    have h1 : (Finset.univ.filter (fun r => I r l)).card = q + 1 := by
      rw [← hL l]
      exact (Fintype.card_of_subtype _ (fun x => by simp)).symm
    omega
  have hdisj : ∀ l ∈ Lp, ∀ l' ∈ Lp, l ≠ l' →
      Disjoint ((Finset.univ.filter (fun r => I r l)).erase p)
        ((Finset.univ.filter (fun r => I r l')).erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_erase, Finset.mem_filter] at hr hr'
    obtain ⟨m, _, hm⟩ := hU p r (fun e => hr.1 e.symm)
    have e1 := hm l ⟨hLp l hl, hr.2.2⟩
    have e2 := hm l' ⟨hLp l' hl', hr'.2.2⟩
    exact hne (e1.trans e2.symm)
  have hcard : (Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)).card
      = Lp.card * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hT]
  have hsub : Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)
      ⊆ Finset.univ.erase p := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨l, _, hr⟩ := hr
    rw [Finset.mem_erase] at hr ⊢
    exact ⟨hr.1, Finset.mem_univ r⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
    Fintype.card_fin] at h1
  have h3 : N - 1 = (q + 1) * q := by
    rw [hN]
    have h4 : q ^ 2 + q + 1 - 1 = q ^ 2 + q := by omega
    rw [h4]; ring
  rw [h3] at h1
  exact Nat.le_of_mul_le_mul_right h1 hq

end Plane2583

namespace Plane2583

theorem pencil_exact {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter (I p)).card = q+1 := by
  classical
  have col (l : Fin N) : Fintype.card {x // I x l} = q+1 := by
    rw [← hL l]
    exact Fintype.card_of_subtype _ (fun _ => by simp)
  have le (x : Fin N) : (Finset.univ.filter (I x)).card ≤ q+1 :=
    pencil_le N q I (by omega) hN col hU x _ (fun _ h => (Finset.mem_filter.mp h).2)
  apply le_antisymm (le p)
  by_contra! small
  have strict := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin N)))
    (fun x _ => le x) ⟨p,Finset.mem_univ p,small⟩
  have same : (∑ x : Fin N, (Finset.univ.filter (I x)).card) = ∑ _x : Fin N, q+1 := by
    calc
      (∑ x : Fin N, (Finset.univ.filter (I x)).card) =
          ∑ l : Fin N, (Finset.univ.filter (fun x => I x l)).card := by
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl (fun l _ => hL l)
  exact (Nat.ne_of_lt strict) same

theorem expansion_arith (a b q : ℕ) (pos : 1 ≤ a) (hi : a ≤ q^2)
    (CS : (a*(q+1))^2 ≤ b*(a*(q+1)+a*(a-1))) : a+q ≤ b := by
  have predEq : a-1+1 = a := by omega
  have hbody : a*(q+1)+a*(a-1) = a*(a+q) := by
    calc
      _ = a*(a-1+1+q) := by ring
      _ = _ := by rw [predEq]
  have hh : a*((q+1)^2*a) ≤ a*(b*(a+q)) := by
    rw [hbody] at CS
    convert CS using 1 <;> ring
  have cc := Nat.le_of_mul_le_mul_left hh (by omega : 0<a)
  have quadratic : (a+q)^2 ≤ (q+1)^2*a := by
    zify at pos hi ⊢
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (a:ℤ)-1 by omega)
      (show (0:ℤ) ≤ (q:ℤ)^2-(a:ℤ) by linarith)]
  have final : (a+q)*(a+q) ≤ b*(a+q) := by simpa only [pow_two] using quadratic.trans cc
  exact Nat.le_of_mul_le_mul_right final (by omega)

/-- Independent sets meeting both shores are at least q smaller than a shore. -/
theorem mixed_independent {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (pne : P.Nonempty) (lne : L.Nonempty)
    (indep : ∀ p ∈ P, ∀ l ∈ L, ¬ I p l) : P.card+L.card+q ≤ N := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have memE (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E]
  have hC4 : ∀ a a' b b' : Fin N, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E) := by
    rintro a a' b b' ha hb ⟨ab,ab',a'b,a'b'⟩
    exact hb ((hU a a' ha).unique ⟨(memE _ _).mp ab,(memE _ _).mp a'b⟩
      ⟨(memE _ _).mp ab',(memE _ _).mp a'b'⟩)
  have hrow (l : Fin N) (hl : l ∈ L) : (Pᶜ.filter (fun p => (p,l) ∈ E)).card = q+1 := by
    rw [← hL l]
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and, memE]
    exact ⟨And.right, fun hi => ⟨fun hp => indep p hp l hl hi,hi⟩⟩
  have imax : L.card ≤ q^2 := by
    obtain ⟨p,hp⟩ := pne
    have hsub : L ⊆ (Finset.univ.filter (I p))ᶜ := by
      intro l hl
      exact Finset.mem_compl.mpr (fun h => indep p hp l hl (Finset.mem_filter.mp h).2)
    have capp := Finset.card_le_card hsub
    have count := pencil_exact I hq hN hL hU p
    rw [Finset.card_compl, Fintype.card_fin, count] at capp
    omega
  have CS := PEqualNP.Outside.L_meta_3696.c4sq _ _ E hC4 Pᶜ L
  have cardE : (((Pᶜ ×ˢ L).filter (fun e => e ∈ E))).card = L.card*(q+1) := by
    rw [PEqualNP.Outside.L_meta_3696.card_filter_product_eq_sum]
    calc (∑ p ∈ Pᶜ, (L.filter (fun l => (p,l) ∈ E)).card)
        = ∑ l ∈ L, (Pᶜ.filter (fun p => (p,l) ∈ E)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
      _ = _ := Finset.sum_const_nat hrow
  rw [cardE] at CS
  have h := expansion_arith L.card Pᶜ.card q (Finset.card_pos.mpr lne) imax CS
  have tot : Pᶜ.card+P.card=N := by simp
  omega

end Plane2583

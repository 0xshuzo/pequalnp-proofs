import PEqualNP.Defs

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

theorem cover_size {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (P L : Finset (Fin N)) (hcov : ∀ p l, I p l → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card := by
  have hL' (l : Fin N) : Fintype.card {p : Fin N // I p l} = q + 1 := by
    rw [← hL l]
    exact Fintype.card_of_subtype _ (fun x => by simp)
  have hbound (p : Fin N) : (Finset.bipartiteAbove I Lᶜ p).card ≤ q + 1 := by
    apply pencil_le N q I (by omega) hN hL' hU p
    exact fun l hl => (Finset.mem_filter.mp hl).2
  have hfull (l : Fin N) (hl : l ∈ Lᶜ) : (Finset.bipartiteBelow I P l).card = q + 1 := by
    rw [← hL l]
    congr 1
    ext p
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hi => ⟨(hcov p l hi).resolve_right (Finset.mem_compl.mp hl), hi⟩⟩
  have hcompare : Lᶜ.card * (q + 1) ≤ P.card * (q + 1) := by
    calc Lᶜ.card * (q + 1)
        = ∑ l ∈ Lᶜ, (Finset.bipartiteBelow I P l).card := (Finset.sum_const_nat hfull).symm
      _ = ∑ p ∈ P, (Finset.bipartiteAbove I Lᶜ p).card :=
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I).symm
      _ ≤ ∑ _p ∈ P, (q + 1) := Finset.sum_le_sum (fun p _ => hbound p)
      _ = P.card * (q + 1) := by simp
  have hle : Lᶜ.card ≤ P.card := Nat.le_of_mul_le_mul_right hcompare (by omega)
  have htotal : Lᶜ.card + L.card = N := by simp
  omega

end Plane2583

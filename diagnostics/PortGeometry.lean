import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3310
theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem port_geometry (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (T : Finset (Finset (Fin N))) (covers : ∀ p l, I p l →
      ∃ S∈T, p∈S ∧ ∀ r∈S, I r l) : N ≤ T.card := by
  classical
  let P := fun l : Fin N => Finset.univ.filter (fun p => I p l)
  let lines := fun S : Finset (Fin N) => Finset.univ.filter (fun l => S ⊆ P l)
  have hc (l : Fin N) : (P l).card=q+1 := by simpa [P,Fintype.card_subtype] using degree l
  have row := lines_through q N I hq order hc unique
  have val (S : Finset (Fin N)) : S.card*(lines S).card ≤ q+1 := by
    by_cases zero : S=∅
    · simp [zero]
    obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    by_cases one : S={p}
    · simpa [one,lines,P] using (row p).le
    have existsOther : ∃ r∈S, r≠p := by
      by_contra! no
      apply one
      ext a
      constructor
      · intro ha; simpa using no a ha
      · intro ha; have eq : a=p := by simpa using ha
        simpa [eq] using hp
    obtain ⟨r,hr,ne⟩ := existsOther
    have sub : ∀ l∈lines S, S⊆P l := fun l hl => (Finset.mem_filter.mp hl).2
    have oneLine : (lines S).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro l hl m hm
      apply (unique p r ne.symm).unique
      · exact ⟨(Finset.mem_filter.mp (sub l hl hp)).2,(Finset.mem_filter.mp (sub l hl hr)).2⟩
      · exact ⟨(Finset.mem_filter.mp (sub m hm hp)).2,(Finset.mem_filter.mp (sub m hm hr)).2⟩
    by_cases empty : lines S=∅
    · simp [empty]
    obtain ⟨l,hl⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have h1 := (Finset.card_le_card (sub l hl)).trans (hc l).le
    simpa using Nat.mul_le_mul h1 oneLine
  have pointBound (l : Fin N) :
      (P l).card ≤ ∑ S∈T, if l∈lines S then S.card else 0 := by
    let fam := T.filter fun S => l∈lines S
    have covered : P l ⊆ fam.biUnion id := by
      intro p hp
      obtain ⟨S,hS,hp',hsub⟩ := covers p l (Finset.mem_filter.mp hp).2
      refine Finset.mem_biUnion.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,?_⟩,hp'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub r hr⟩⟩
    have small := (Finset.card_le_card covered).trans Finset.card_biUnion_le
    simpa [fam,Finset.sum_filter] using small
  have tot : N*(q+1) ≤ T.card*(q+1) := calc
    N*(q+1) = ∑ l : Fin N, (P l).card := by simp [hc]
    _ ≤ ∑ l : Fin N, ∑ S∈T, if l∈lines S then S.card else 0 := Finset.sum_le_sum (fun l _ => pointBound l)
    _ = ∑ S∈T, S.card*(lines S).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      rw [←Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ ∑ _S∈T, (q+1) := Finset.sum_le_sum (fun S _ => val S)
    _ = T.card*(q+1) := by simp
  exact Nat.le_of_mul_le_mul_right tot (by omega)

end PEqualNP.Outside.L_meta_3310

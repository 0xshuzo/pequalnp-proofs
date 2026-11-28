import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17132

theorem rectLineCap {N k : Nat} (I : Fin N → Fin N → Prop)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (L : Finset (Fin N)) (P Y : Fin k → Finset (Fin N))
    (safe : ∀ i, ∀ p∈P i, ∀ l∈L, l∈Y i → I p l)
    (wide : ∀ l∈L, ∃ p r : Fin N, p≠r ∧ (∃ i, p∈P i ∧ l∈Y i) ∧ (∃ j, r∈P j ∧ l∈Y j)) :
    L.card ≤ (Finset.univ.filter (fun z : Fin k × Fin k => z.1≤z.2)).card := by
  classical
  let ok (l : Fin N) (z : Fin k × Fin k) :=
    z.1 ≤ z.2 ∧ l∈Y z.1 ∧ l∈Y z.2 ∧ ∃ p∈P z.1, ∃ r∈P z.2, p≠r
  by_cases h0 : L.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp h0]
    simp
  obtain ⟨l0,h0⟩ := h0
  obtain ⟨p0,r0,ne0,⟨i0,_,_⟩,⟨j0,_,_⟩⟩ := wide l0 h0
  letI : Nonempty (Fin k × Fin k) := ⟨(i0,j0)⟩
  have tags (l : Fin N) (h : l∈L) : ∃ z, ok l z := by
    obtain ⟨p,r,ne,⟨i,pi,li⟩,⟨j,rj,lj⟩⟩ := wide l h
    rcases le_total i j with le|le
    · exact ⟨(i,j),le,li,lj,p,pi,r,rj,ne⟩
    · exact ⟨(j,i),le,lj,li,r,rj,p,pi,ne.symm⟩
  choose! f hf using tags
  apply Finset.card_le_card_of_injOn f (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hf l hl).1⟩)
  intro l hl m hm e
  obtain ⟨_,li,lj,p,pp,r,rr,ne⟩ := hf l hl
  have mq : ok m (f l) := e.symm ▸ hf m hm
  exact (uniq p r ne).unique
    ⟨safe _ _ pp l hl li,safe _ _ rr l hl lj⟩
    ⟨safe _ _ pp m hm mq.2.1,safe _ _ rr m hm mq.2.2.1⟩

theorem thirteenCap (L : Finset (Fin N)) (I : Fin N → Fin N → Prop)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l)
    (P Y : Fin 13 → Finset (Fin N))
    (safe : ∀ i, ∀ p∈P i, ∀ l∈L, l∈Y i → I p l)
    (wide : ∀ l∈L, ∃ p r : Fin N, p≠r ∧ (∃ i, p∈P i ∧ l∈Y i) ∧ (∃ j, r∈P j ∧ l∈Y j)) :
    L.card ≤ 91 := by
  exact (rectLineCap I uniq L P Y safe wide).trans_eq (by decide +kernel)

end PEqualNP.Outside.L_meta_17132

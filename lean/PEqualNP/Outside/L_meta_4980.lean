import Mathlib
import PEqualNP.Defs

-- The partition count for lines through a point follows R_meta_2866_42.
theorem PEqualNP.Outside.L_meta_4980 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : Fin (x1 * x1) ↪ Fin x2) (x10 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x11 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x12 x13 : Fin (x1 + (1 : ℕ))), x12 ≠ x13 → Function.Bijective fun (x15 : Fin (x1 * x1)) => (x11 x12 x15, x11 x13 x15)) ∧ ∀ (x12 : Fin (x1 * x1)) (x13 : Fin (x1 + (1 : ℕ))) (x14 : Fin x1), x3 (x9 x12) (x10 (x13, x14)) ↔ x11 x13 x12 = x14 := by
  have pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (positive : 0 < q) (order : N = q^2+q+1)
      (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
    classical
    let through := Finset.univ.filter (fun l : Fin N => I p l)
    let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
    have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
      let full := Finset.univ.filter (fun r : Fin N => I r l)
      have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
      have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
      have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
      rw [same,Finset.card_erase_of_mem inFull,cardFull]
      omega
    have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
      intro l other k more different
      refine Finset.disjoint_left.mpr ?_
      intro r here there
      have throughL : I p l := (Finset.mem_filter.mp other).2
      have throughK : I p k := (Finset.mem_filter.mp more).2
      obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
      have rk := (Finset.mem_filter.mp there).2.1
      exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
    have together : through.biUnion rest = Finset.univ.erase p := by
      ext r
      constructor
      · intro seen
        obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
      · intro seen
        have diff := (Finset.mem_erase.mp seen).1
        obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
        exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
    have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
      rw [Nat.add_sub_cancel]
      ring
    have scale : through.card*q = (q+1)*q := by
      calc
        through.card*q = ∑ l ∈ through, q := by simp
        _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
        _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
        _ = (q+1)*q := by rw [together,rightSize]
    exact Nat.eq_of_mul_eq_mul_right positive scale
  intro q N I inst positive order degree unique
  classical
  let horizon : Fin N := ⟨0, by omega⟩
  let directions := Finset.univ.filter (fun p : Fin N => I p horizon)
  let affine : Finset (Fin N) := directionsᶜ
  have cdir : directions.card = q+1 :=
    (Fintype.card_subtype (fun p => I p horizon)).symm.trans (degree horizon)
  have caff : affine.card = q*q := by
    rw [show affine = directionsᶜ from rfl, Finset.card_compl, Fintype.card_fin, cdir, order, pow_two]
    omega
  let dir : Fin (q+1) ≃ directions :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe directions).trans cdir)).symm
  let pt : Fin (q*q) ≃ affine :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe affine).trans caff)).symm
  let P : Fin (q*q) ↪ Fin N := pt.toEmbedding.trans (Function.Embedding.subtype _)
  have on (i : Fin (q+1)) : I (dir i).val horizon :=
    (Finset.mem_filter.mp (dir i).property).2
  have off (p : Fin (q*q)) : ¬ I (P p) horizon := by
    have h := (pt p).property
    change ¬ I (pt p).val horizon
    simpa [affine, directions] using h
  let family (i : Fin (q+1)) :=
    (Finset.univ.filter (fun l : Fin N => I (dir i).val l)).erase horizon
  have cfam (i : Fin (q+1)) : (family i).card = q := by
    have hh : horizon ∈ Finset.univ.filter (fun l : Fin N => I (dir i).val l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,on i⟩
    change ((Finset.univ.filter (fun l : Fin N => I (dir i).val l)).erase horizon).card = q
    rw [Finset.card_erase_of_mem hh, pointDegree q N I positive order degree unique]
    omega
  let line (i : Fin (q+1)) : Fin q ≃ family i :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe (family i)).trans (cfam i))).symm
  let label (i : Fin (q+1)) (a : Fin q) : Fin N := (line i a).val
  have lineLaw (i : Fin (q+1)) (a : Fin q) :
      I (dir i).val (label i a) ∧ label i a ≠ horizon := by
    have h := Finset.mem_erase.mp (line i a).property
    exact ⟨(Finset.mem_filter.mp h.2).2,h.1⟩
  have recover (i j : Fin (q+1)) (a b : Fin q) (e : label i a = label j b) : i = j := by
    by_contra diff
    have hd : (dir i).val ≠ (dir j).val :=
      fun eq => diff (dir.injective (Subtype.ext eq))
    have both : I (dir j).val (label i a) := e.symm ▸ (lineLaw j b).1
    have ee : label i a = horizon := (unique _ _ hd).unique
      ⟨(lineLaw i a).1,both⟩ ⟨on i,on j⟩
    exact (lineLaw i a).2 ee
  let L : (Fin (q+1) × Fin q) ↪ Fin N :=
    ⟨fun u => label u.1 u.2, by
      rintro ⟨i,a⟩ ⟨j,b⟩ e
      have same := recover i j a b e
      subst j
      have he : a=b := (line i).injective (Subtype.ext e)
      exact Prod.ext rfl he⟩
  have per (i : Fin (q+1)) (p : Fin (q*q)) : ∃! a : Fin q, I (P p) (label i a) := by
    have different : (dir i).val ≠ P p :=
      fun e => off p (e ▸ on i)
    obtain ⟨l,⟨hl,hp⟩,only⟩ := unique _ _ different
    have neq : l ≠ horizon := fun e => off p (e ▸ hp)
    let t : family i :=
      ⟨l, Finset.mem_erase.mpr ⟨neq,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩⟩
    refine ⟨(line i).symm t,?_,?_⟩
    · change I (P p) ((line i) ((line i).symm t)).val
      rw [Equiv.apply_symm_apply]
      exact hp
    · intro b hb
      apply (line i).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact only (label i b) ⟨(lineLaw i b).1,hb⟩
  let coord (i : Fin (q+1)) (p : Fin (q*q)) := Classical.choose (per i p).exists
  have passes (i : Fin (q+1)) (p : Fin (q*q)) : I (P p) (label i (coord i p)) :=
    Classical.choose_spec (per i p).exists
  refine ⟨P,L,coord,?_,?_⟩
  · intro i j distinct
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_,by simp⟩
    intro p r eq
    by_contra ne
    have de : P p ≠ P r := fun e => ne (P.injective e)
    have ei : coord i p = coord i r := congrArg Prod.fst eq
    have ej : coord j p = coord j r := congrArg Prod.snd eq
    have hi : I (P r) (label i (coord i p)) := ei.symm ▸ passes i r
    have hj : I (P r) (label j (coord j p)) := ej.symm ▸ passes j r
    have f : label i (coord i p) = label j (coord j p) :=
      (unique _ _ de).unique ⟨passes i p,hi⟩ ⟨passes j p,hj⟩
    exact distinct (recover _ _ _ _ f)
  · intro p i a
    change I (P p) (label i a) ↔ coord i p = a
    exact ⟨fun hit => (per i p).unique (passes i p) hit,
      fun eq => eq ▸ passes i p⟩

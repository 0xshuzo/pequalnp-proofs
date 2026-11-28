import PEqualNP.Defs
namespace Lpcx178Sort
abbrev R := Fin 5
theorem sortedFive (f : R → Nat) (inj : Function.Injective f) (u v : Nat)
    (ne : u ≠ v) (atU : ∃ i, f i=u) (atV : ∃ i, f i=v) :
    ∃ e : R ≃ R, f (e 3)=u ∧ f (e 4)=v ∧
       ∀ i j : R, i.val<3 → j.val<3 → i.val<j.val → f (e i)<f (e j) := by
  classical
  let A := Finset.univ.image f
  have sizeA : A.card=5 := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]
  have mu : u ∈ A := by obtain ⟨i,he⟩:=atU; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
  have mv : v ∈ A := by obtain ⟨i,he⟩:=atV; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
  let B := (A.erase u).erase v
  have sizeB : B.card=3 := by
    change ((A.erase u).erase v).card=3
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm ne,mv⟩),Finset.card_erase_of_mem mu,sizeA]
  let order := B.orderIsoOfFin sizeB
  let g (i : R) : Nat := if h : i.val<3 then (order ⟨i.val,h⟩).val else if i=3 then u else v
  have low (i : R) (h : i.val<3) : g i∈B := by simpa [g,h] using (order ⟨i.val,h⟩).property
  have high (i : R) (h : ¬i.val<3) : i=3 ∨ i=4 := by
    by_cases eq : i.val=3
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr (Fin.ext (by omega))
  have gu : g 3=u := by simp [g]
  have gv : g 4=v := by simp [g]
  have diff (i : R) (h : i.val<3) : g i≠u ∧ g i≠v := by
    have id := Finset.mem_erase.mp (low i h)
    exact ⟨(Finset.mem_erase.mp id.2).1,id.1⟩
  have increasing (i j : R) (hi : i.val<3) (hj : j.val<3) (lt : i.val<j.val) : g i < g j := by
    have oo := order.strictMono (show (⟨i.val,hi⟩ : Fin 3) < ⟨j.val,hj⟩ from lt)
    simpa [g,hi,hj] using oo
  have gi : Function.Injective g := by
    intro i j eq
    by_cases hi : i.val<3
    · by_cases hj : j.val<3
      · by_contra neq
        rcases lt_or_gt_of_ne neq with lt|gt
        · exact (Nat.ne_of_lt (increasing i j hi hj lt)) eq
        · exact (Nat.ne_of_lt (increasing j i hj hi gt)) eq.symm
      · rcases high j hj with rfl|rfl
        · exact False.elim ((diff _ hi).1 (eq.trans gu))
        · exact False.elim ((diff _ hi).2 (eq.trans gv))
    · by_cases hj : j.val<3
      · rcases high i hi with rfl|rfl
        · exact False.elim ((diff _ hj).1 (eq.symm.trans gu))
        · exact False.elim ((diff _ hj).2 (eq.symm.trans gv))
      · rcases high i hi with rfl|rfl <;> rcases high j hj with rfl|rfl <;> first
          | rfl
          | exact False.elim (ne (gu.symm.trans (eq.trans gv)))
          | exact False.elim (ne (gu.symm.trans (eq.symm.trans gv)))
  have has (i : R) : ∃ j : R, f j=g i := by
    have m : g i∈A := by
      by_cases hi : i.val<3
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (low _ hi))
      · rcases high i hi with rfl|rfl
        · simpa only [gu] using mu
        · simpa only [gv] using mv
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp m
    exact ⟨j,eq⟩
  choose a ha using has
  have ai : Function.Injective a := by
    intro i j eq
    exact gi ((ha i).symm.trans ((congrArg f eq).trans (ha j)))
  let e := Equiv.ofBijective a ⟨ai,Finite.injective_iff_surjective.mp ai⟩
  refine ⟨e,(ha 3).trans gu,(ha 4).trans gv,?_⟩
  intro i j hi hj lt
  change f (a i) < f (a j)
  rw [ha i,ha j]
  exact increasing i j hi hj lt
end Lpcx178Sort

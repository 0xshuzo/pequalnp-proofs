import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4684_17
    (compile : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n) (E : Type)
      (D : Set E) (bad : E → Finset (Fin n)),
      (∀ e ∈ D, C.eval (bad e) = false) →
      ∃ G : Fin C.size → Bool → Set E, ∀ U, C.eval U = true →
        ∃ T : Set (Fin C.size),
          let can := fun (j : ℕ) (W : Set E) =>
            (∃ v ∈ U, ∀ e ∈ W, v ∉ bad e) ∨
            ∃ i ∈ T, i.val < j ∧ W ⊆ G i false ∪ G i true
          (∀ i ∈ T, ∀ b, can i.val (G i b)) ∧ can C.size D)
    (lower : ∀ (s : ℕ) (G : Fin s → Bool → Set (Fin 13 × Fin 13)),
      let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      (∀ X Y : Finset (Fin 13),
        (∀ l, l ∈ Y ↔ ∀ p ∈ X, ¬ I p l) →
        (∀ p ∉ X, ∃ l ∈ Y, I p l) →
        (¬∃ l, ∀ p ∈ X, I p l) → (¬∃ p, ∀ l ∈ Y, I p l) →
        ∃ T : Set (Fin s),
          let can := fun (j : ℕ) (W : Set (Fin 13 × Fin 13)) =>
            W = ∅ ∨ (∃ p ∉ X, ∀ e ∈ W, e.1 = p) ∨
            (∃ l ∉ Y, ∀ e ∈ W, e.2 = l) ∨
            ∃ i ∈ T, i.val < j ∧ W ⊆ G i false ∪ G i true
          (∀ i ∈ T, ∀ b, can i.val (G i b)) ∧ can s {e | I e.1 e.2}) →
      51 ≤ s) :
  ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x4, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ x7 ∈ x5, x6 = Fin.natAdd (13 : ℕ) x7);     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x5 x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x8 : Fin (26 : ℕ)) => !x4 x5 x6 x8) x7 = Bool.true};     have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x3 x8 x7};     (∀ (x7 x8 : Fin (13 : ℕ)), x3 x7 x8 → x1.eval (x5 {x7} {x8}) = Bool.false) → (∀ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ x11 ∈ x6 x8, x3 x9 x11) → (¬∃ (x10 : Fin (13 : ℕ)), ∀ x11 ∈ x8, x3 x11 x10) → (¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x6 x8, x3 x11 x12) → x1.eval (x5 x8 (x6 x8)) = Bool.true) → (51 : ℕ) ≤ x1.size := by
  intro C _
  dsimp only
  intro neg pos
  classical
  let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let row := fun (X Y : Finset (Fin 13)) (k : Fin 26) =>
    decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k = Fin.natAdd 13 l)
  let mask := fun X Y => Finset.univ.filter
    (fun i : Fin 27 => Fin.cases true (fun k => !(row X Y k)) i = true)
  let D : Set (Fin 13 × Fin 13) := {e | I e.1 e.2}
  let bad := fun e : Fin 13 × Fin 13 => mask {e.1} {e.2}
  have hn (e : Fin 13 × Fin 13) (he : e ∈ D) : C.eval (bad e) = false :=
    neg e.1 e.2 he
  obtain ⟨G, hg⟩ := compile 27 C (Fin 13 × Fin 13) D bad hn
  apply lower C.size G
  intro X Y hY closed noline nopencil
  let M := Finset.univ.filter (fun l => ∀ p ∈ X, ¬ I p l)
  have eq : Y = M := by ext l; simpa only [M,Finset.mem_filter,Finset.mem_univ,true_and] using hY l
  subst Y
  have hp : C.eval (mask X M) = true := pos X closed noline nopencil
  obtain ⟨T, sides, all⟩ := hg (mask X M) hp
  have raw (W : Set (Fin 13 × Fin 13)) (v : Fin 27) (hv : v ∈ mask X M)
      (off : ∀ e ∈ W, v ∉ bad e) :
      W = ∅ ∨ (∃ p ∉ X, ∀ e ∈ W, e.1 = p) ∨ ∃ l ∉ M, ∀ e ∈ W, e.2 = l := by
    have disj (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro h
      have hv' := congrArg Fin.val h
      change p.val = 13+l.val at hv'
      omega
    have eqLine (a b : Fin 13) : Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a=b := by
      constructor
      · intro h
        apply Fin.ext
        have h' := congrArg Fin.val h
        change 13+a.val = 13+b.val at h'
        omega
      · rintro rfl
        rfl
    have zero (A B : Finset (Fin 13)) : (0 : Fin 27) ∈ mask A B := by simp [mask]
    have succ (A B : Finset (Fin 13)) (k : Fin 26) : k.succ ∈ mask A B ↔
        ¬ ((∃ p ∈ A, k = Fin.castAdd 13 p) ∨ ∃ l ∈ B, k = Fin.natAdd 13 l) := by
      simp [mask,row]
    have left (A B : Finset (Fin 13)) (p : Fin 13) :
        (Fin.castAdd 13 p).succ ∈ mask A B ↔ p ∉ A := by
      rw [succ]
      constructor
      · intro absent present
        exact absent (Or.inl ⟨p,present,rfl⟩)
      · intro hp pair
        rcases pair with ⟨x,hx,hit⟩ | ⟨l,_,hit⟩
        · exact hp ((Fin.castAdd_inj.mp hit).symm ▸ hx)
        · exact disj p l hit
    have disjR (l p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := (disj p l).symm
    have right (A B : Finset (Fin 13)) (l : Fin 13) :
        (Fin.natAdd 13 l).succ ∈ mask A B ↔ l ∉ B := by
      rw [succ]
      constructor
      · intro absent present
        exact absent (Or.inr ⟨l,present,rfl⟩)
      · intro hl pair
        rcases pair with ⟨p,_,hit⟩ | ⟨x,hx,hit⟩
        · exact disjR l p hit
        · exact hl (((eqLine l x).mp hit).symm ▸ hx)
    revert hv off
    refine Fin.cases ?_ (fun k => ?_) v
    · intro _ h
      exact Or.inl (Set.eq_empty_iff_forall_notMem.mpr (fun e he => h e he (zero _ _)))
    · refine Fin.addCases (m := 13) (n := 13)
        (motive := fun a => a.succ ∈ mask X M → (∀ e ∈ W, a.succ ∉ bad e) →
          W = ∅ ∨ (∃ p ∉ X, ∀ e ∈ W, e.1 = p) ∨ ∃ l ∉ M, ∀ e ∈ W, e.2 = l)
        (fun p hp h => ?_) (fun l hl h => ?_) k
      · refine Or.inr (Or.inl ⟨p,(left _ _ _).1 hp,?_⟩)
        intro e he
        have hbad := h e he
        change _ ∉ mask {e.1} {e.2} at hbad
        by_contra neq
        apply hbad
        exact (left _ _ _).2 (by simpa [eq_comm] using neq)
      · refine Or.inr (Or.inr ⟨l,(right _ _ _).1 hl,?_⟩)
        intro e he
        have hbad := h e he
        change _ ∉ mask {e.1} {e.2} at hbad
        by_contra neq
        apply hbad
        exact (right _ _ _).2 (by simpa [eq_comm] using neq)
  refine ⟨T, ?_, ?_⟩
  · intro i hi b
    rcases sides i hi b with ⟨v,hv,off⟩ | old
    · rcases raw _ v hv off with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr old))
  · rcases all with ⟨v,hv,off⟩ | old
    · rcases raw _ v hv off with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr old))

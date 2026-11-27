import PEqualNP.Defs

namespace Address851

def size (K : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, K i

abbrev Cell (K : ℕ → ℕ) (L : ℕ) := (d : Fin L) × Fin (K d)

noncomputable def code (K : ℕ → ℕ) (L : ℕ) : Cell K L ≃ Fin (size K L) :=
  Fintype.equivFinOfCardEq (by simp [Cell, Fintype.card_sigma, size, Fin.sum_univ_eq_sum_range])

variable (K : ℕ → ℕ) {L : ℕ}

noncomputable def level (i : Fin (size K L)) : Fin L := ((code K L).symm i).1

noncomputable def idx (i : Fin (size K L)) : ℕ := ((code K L).symm i).2.val

noncomputable def place (b : Fin L) (k : ℕ) : Option (Fin (size K L)) :=
  if h : k < K b then some (code K L ⟨b,⟨k,h⟩⟩) else none

theorem place_some (b : Fin L) (k : ℕ) (i : Fin (size K L)) :
    place K b k = some i ↔ level K i = b ∧ idx K i = k := by
  obtain ⟨⟨d,t⟩,rfl⟩ := (code K L).surjective i
  simp only [level, idx, Equiv.symm_apply_apply]
  by_cases h : k < K b
  · simp only [place, dif_pos h, Option.some.injEq, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro he
      exact ⟨(congrArg (fun x : Cell K L => x.1) he).symm,
             (congrArg (fun x : Cell K L => x.2.val) he).symm⟩
    · rintro ⟨rfl,hk⟩
      subst k
      rfl
  · simp only [place, dif_neg h, reduceCtorEq, false_iff]
    rintro ⟨rfl,hk⟩
    exact h (hk ▸ t.isLt)

theorem place_self (i : Fin (size K L)) : place K (level K i) (idx K i) = some i :=
  (place_some ..).mpr ⟨rfl,rfl⟩

theorem rank_lt (i : Fin (size K L)) : idx K i < K (level K i) :=
  ((code K L).symm i).2.isLt

theorem width_le_size (l : Fin L) : K l ≤ size K L :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (K i)) (Finset.mem_range.mpr l.isLt)

theorem sum_level {R : Type} [AddCommMonoid R] (l : Fin L)
    (v : Fin (size K L) → R) :
    (∑ i, if level K i=l then v i else 0) =
        ∑ k : Fin (K l), v (code K L ⟨l,k⟩) := by
  classical
  calc
    _ = ∑ a : Cell K L, if a.1=l then v (code K L a) else 0 := by
      refine Fintype.sum_equiv (code K L).symm _ _ ?_
      intro i
      simp [level]
    _ = _ := by
      rw [Fintype.sum_sigma']
      simp

theorem rank_escape {n : Fin (size K L) → Bool → Option (Fin (size K L))}
    (hinc : ∀ i j, n i true = some j → idx K i < idx K j) (i : Fin (size K L)) :
    (fun x : Option (Fin (size K L)) => x.bind (fun s => n s true))^[size K L] (some i) = none := by
  let step := fun x : Option (Fin (size K L)) => x.bind (fun s => n s true)
  have h : ∀ t j, step^[t] (some i) = some j → t+idx K i ≤ idx K j := by
    intro t
    induction t with
    | zero =>
      intro j hj
      simp at hj
      simp [hj]
    | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply'] at hj
      cases he : step^[t] (some i) with
      | none =>
        rw [he] at hj
        cases hj
      | some v =>
        rw [he] at hj
        have h1 := hinc v j hj
        have h2 := ih v he
        omega
  change step^[size K L] (some i) = none
  cases he : step^[size K L] (some i) with
  | none => rfl
  | some v =>
    have h1 := h _ _ he
    have h2 := rank_lt K v
    have h3 := width_le_size K (level K v)
    omega

end Address851

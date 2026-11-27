import PEqualNP.Defs

namespace Harmonic851

variable {ι : Type} [Fintype ι]

def extend (v : ι → ℝ) (s : Option ι) : ℝ := s.elim 0 v

theorem maximum (n : ι → Bool → Option ι) (c : ι → Bool) (L : ℕ)
    (dies : ∀ i, (fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i) = none)
    (v : ι → ℝ) (harm : ∀ i, 2*v i = extend v (n i false) + extend v (n i true)) :
    ∀ i, v i ≤ 0 := by
  classical
  let f := extend v
  let step := fun x : Option ι => x.bind (fun j => n j (c j))
  obtain ⟨s, _, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Option ι)) f
    ⟨none, Finset.mem_univ _⟩
  have hub (x : Option ι) : f x ≤ f s := hm x (Finset.mem_univ _)
  have preserve (x : Option ι) (hx : f x = f s) : f (step x) = f s := by
    cases x with
    | none => exact hx
    | some i =>
      have h := harm i
      change 2*f (some i) = f (n i false) + f (n i true) at h
      change f (n i (c i)) = f s
      cases c i <;> linarith [hub (n i false), hub (n i true)]
  have along (k : ℕ) : f (step^[k] s) = f s := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact preserve _ ih
  have hzero : f s = 0 := by
    cases s with
    | none => rfl
    | some i =>
      have hc := along L
      change f ((fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i)) = f (some i) at hc
      rw [dies] at hc
      exact hc.symm
  intro i
  exact (hub (some i)).trans (le_of_eq hzero)

noncomputable def op (n : ι → Bool → Option ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := 2*v i - extend v (n i false) - extend v (n i true)
  map_add' v w := by
    ext i
    cases h : n i false <;> cases k : n i true <;>
      simp [extend, h, k] <;> ring
  map_smul' a v := by
    ext i
    cases h : n i false <;> cases k : n i true <;>
      simp [extend, h, k] <;> ring

theorem solve (n : ι → Bool → Option ι) (c : ι → Bool) (L : ℕ)
    (dies : ∀ i, (fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i) = none)
    (g : ι → Bool → ℝ) :
    ∃ v : ι → ℝ, ∀ i, 2*v i = ∑ bit : Bool, (n i bit).elim (g i bit) (fun k => v k) := by
  classical
  have hz (v : ι → ℝ) (hv : op n v = 0) : v = 0 := by
    have hh (i) : 2*v i = extend v (n i false) + extend v (n i true) := by
      have h := congrFun hv i
      change 2*v i - extend v (n i false) - extend v (n i true) = 0 at h
      linarith
    have hneg (i) : 2*(-v) i = extend (-v) (n i false) + extend (-v) (n i true) := by
      have h := hh i
      cases ha : n i false <;> cases hb : n i true <;>
        simp [extend, ha, hb] at * <;> linarith
    funext i
    have a := maximum n c L dies v hh i
    have b := maximum n c L dies (-v) hneg i
    change -v i ≤ 0 at b
    change v i = 0
    linarith
  have hi : Function.Injective (op n) := by
    intro v w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  have hs : Function.Surjective (op n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  obtain ⟨v,hv⟩ := hs (fun i => (n i false).elim (g i false) (fun _ => 0) +
      (n i true).elim (g i true) (fun _ => 0))
  refine ⟨v, fun i => ?_⟩
  have h := congrFun hv i
  change 2*v i - extend v (n i false) - extend v (n i true) = _ at h
  cases ha : n i false <;> cases hb : n i true <;>
    simp [Fintype.sum_bool, extend, ha, hb] at * <;> linarith

end Harmonic851

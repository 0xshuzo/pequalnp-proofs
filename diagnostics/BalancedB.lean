import PEqualNP.Defs

namespace Balanced32582

theorem price {b Z N q r m : Nat} (hb : 2 ≤ b) (hbudget : b * Z ≤ N)
    (hdiv : q * Z + r = N) (hr : r ≤ Z) (hl : q ≤ m) (hu : m ≤ q+1) :
    (b-1)*N ≤ b*Z*m ∧ b*Z*m ≤ (b+1)*N := by
  have h1 := Nat.mul_le_mul_left (b*Z) hl
  have h2 := Nat.mul_le_mul_left (b*Z) hu
  have h3 := Nat.mul_le_mul_left b hr
  have h4 := congrArg (fun t : Nat => b*t) hdiv
  have h5 := congrArg (fun t : Nat => t*N) (Nat.sub_add_cancel (show 1 ≤ b by omega))
  constructor <;> nlinarith

noncomputable section

theorem sampler {α T : Type} [Fintype α] [Fintype T] (b : Nat) (hb : 2 ≤ b)
    (hpos : 0 < Fintype.card α) (hbudget : b * Fintype.card α ≤ Fintype.card T) :
    ∃ g : T → α, ∀ a : α,
      let m := Nat.card {t : T // g t = a}
      (b-1)*Fintype.card T ≤ b*Fintype.card α*m ∧
      b*Fintype.card α*m ≤ (b+1)*Fintype.card T := by
  classical
  let Z := Fintype.card α
  let N := Fintype.card T
  let q := N / Z
  let r := N % Z
  have hr : r < Z := Nat.mod_lt _ hpos
  have hdiv : q * Z + r = N := by
    simpa [q, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div N Z
  let E : T ≃ ((Fin q × α) ⊕ Fin r) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact hdiv.symm)
  let inc : Fin r → α := fun j => (Fintype.equivFin α).symm ⟨j.val, lt_trans j.isLt hr⟩
  have hi : Function.Injective inc := by
    intro x y h
    apply Fin.ext
    have he := (Fintype.equivFin α).symm.injective h
    exact congrArg (fun z : Fin Z => z.val) he
  let pick : (Fin q × α) ⊕ Fin r → α := Sum.elim Prod.snd inc
  let g : T → α := fun t => pick (E t)
  refine ⟨g, fun a => ?_⟩
  let F := {t : T // g t = a}
  let enc : Fin q → F := fun i => ⟨E.symm (.inl (i,a)), by simp [g, pick]⟩
  have hin : Function.Injective enc := by
    intro i j hh
    have hh' := congrArg (fun t : F => E t.val) hh
    simpa [enc] using hh'
  have lo : q ≤ Nat.card F := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective enc hin
  let tag : (Fin q × α) ⊕ Fin r → Option (Fin q) := Sum.elim (fun v => some v.1) (fun _ => none)
  let dec : F → Option (Fin q) := fun t => tag (E t.val)
  have hout : Function.Injective dec := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ hh
    apply Subtype.ext
    apply E.injective
    change pick (E x) = a at hx
    change pick (E y) = a at hy
    change tag (E x) = tag (E y) at hh
    cases h₁ : E x with
    | inl u =>
      cases h₂ : E y with
      | inl v =>
        rw [h₁] at hx hh
        rw [h₂] at hy hh
        change u.2 = a at hx
        change v.2 = a at hy
        change some u.1 = some v.1 at hh
        exact congrArg Sum.inl (Prod.ext (Option.some.inj hh) (hx.trans hy.symm))
      | inr v => simp [h₁,h₂,tag] at hh
    | inr u =>
      cases h₂ : E y with
      | inl v => simp [h₁,h₂,tag] at hh
      | inr v =>
        rw [h₁] at hx
        rw [h₂] at hy
        exact congrArg Sum.inr (hi (hx.trans hy.symm))
  have up : Nat.card F ≤ q+1 := by
    simpa [Nat.card_eq_fintype_card, Nat.add_comm] using Fintype.card_le_of_injective dec hout
  exact price hb hbudget hdiv hr.le lo up

end
end Balanced32582

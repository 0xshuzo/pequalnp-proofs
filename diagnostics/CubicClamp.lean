import PEqualNP.Defs

namespace Cubic9806

def graph (x : Fin 14 → Bool) := (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def patch (m : Fin 8) (i : Fin 14) : Bool :=
  (decide (i = 5) && m.val.testBit 0) || (decide (i = 10) && m.val.testBit 1) ||
    (decide (i = 7) && m.val.testBit 2)

private theorem small : ∀ m : Fin 8, m ≠ 7 → graph (patch m) = true → m = 3 := by
  decide +kernel
private theorem bad : graph (patch 5) = false := by decide +kernel
private theorem good : graph (patch 7) = true := by decide +kernel
private theorem leMask : ∀ i : Fin 14, patch 5 i = true → patch 7 i = true := by decide +kernel

theorem cubic {X : Type} (F H : X → Bool) (cut : X → Bool → Bool)
    (eqn : ∀ x, cut x (!(H x)) = F x)
    (rail : ∀ x, cut x false = true → cut x true = true)
    (a b t : X) (cone : X → Prop)
    (hb : F b = false) (extra : cut b true = true) (tr : H b = true → H t = true)
    (ht : F t = true) (omitted : cut a false = false)
    (single : ∀ x, cone x → F x = true → x = a) :
    H b = true ∧ cut t false = true ∧ ∀ x, cone x → cut x false = false := by
  have on : H b = true := by
    cases h : H b with
    | true => rfl
    | false =>
      have e := eqn b
      simp only [h, Bool.not_false] at e
      rw [hb, extra] at e
      contradiction
  have top : cut t false = true := by
    have e := eqn t
    simpa [tr on, ht] using e
  refine ⟨on, top, ?_⟩
  intro x hx
  cases hc : cut x false with
  | false => rfl
  | true =>
    have f : F x = true := by
      rw [← eqn x]
      cases h : H x with
      | true => simpa [h] using hc
      | false => simpa [h] using rail x hc
    have xa := single x hx f
    subst x
    rw [omitted] at hc
    contradiction

theorem nearCorner (H : (Fin 14 → Bool) → Bool) (g : (Fin 14 → Bool) → Bool → Bool)
    (monoH : ∀ x y, (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (correct : ∀ x, g x (!(H x)) = graph x)
    (rail : ∀ x, g x false = true → g x true = true)
    (lost : g (patch 3) false = false) (extra : g (patch 5) true = true) :
    H (patch 5) = true ∧ g (patch 7) false = true ∧
      ∀ m : Fin 8, m ≠ 7 → g (patch m) false = false := by
  exact cubic (fun m => graph (patch m)) (fun m => H (patch m)) (fun m => g (patch m))
    (fun m => correct (patch m)) (fun m => rail (patch m)) 3 5 7 (fun m => m ≠ 7)
    bad extra (monoH _ _ leMask) good lost small

end Cubic9806

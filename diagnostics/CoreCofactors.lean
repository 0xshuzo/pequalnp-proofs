import Mathlib
import PEqualNP.Outside.L_meta_720

namespace CoreCofactors2732
open PEqualNP.Outside.L_meta_720
open PEqualNP.Outside.L_meta_720.PEqualNP.MetaComplexity.Loc
open PEqualNP.Outside.L_meta_720.PequalNP583

theorem two (i j : Fin 6) (hne : i ≠ j) {s : ℕ}
    (h : HasMonoSize 10 (source {i,j}) s) : 11 ≤ s := by
  have hres := Clean.relabel_mono (relabelResidual i j) _ _ h
  have he : (fun x => source {i,j} (x ∘ relabelResidual i j)) = residualModel (tailCase i j) :=
    funext (residualValue hne)
  rw [he] at hres
  exact residualLower hres.has

theorem one (j : Fin 6) {s : ℕ} (h : HasMonoSize 10 (source {j}) s) : 13 ≤ s := by
  obtain ⟨i, hi, t, small, hh⟩ := removeSpoke {j} (by simp) h
  have hne : i ≠ j := by simpa using hi
  have price := two i j hne hh
  omega

theorem allSeeds :
    (∀ s, HasMonoSize 10 (source ∅) s → 15 ≤ s) ∧
    (∀ (i : Fin 6) s, HasMonoSize 10 (source {i}) s → 13 ≤ s) ∧
    (∀ (i j : Fin 6), i ≠ j → ∀ s, HasMonoSize 10 (source {i,j}) s → 11 ≤ s) :=
  ⟨fun _ h => fullLower h, fun i _ h => one i h, fun i j ne _ h => two i j ne h⟩
end CoreCofactors2732

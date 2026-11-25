import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.Outside.L_meta_2135

namespace K2336
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def edge (z : Fin 5 → Bool) : Bool :=
  (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) ||
  (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)

def four : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[6,4]⟩,⟨.and,[5,7]⟩],8⟩

theorem witness : Monotone2 four ∧ ReadsBack 5 four ∧ four.size=4 ∧
    ∀ x : Fin 5→Bool, four.eval (List.ofFn x)=edge x := by
  have q : PEqualNP.TopForm.IsAO2 5 four := by decide +kernel
  exact ⟨fun g hg=>⟨q.1 g hg,(q.2.2 g hg).le⟩,q.2.1,rfl,by decide +kernel⟩

-- All five inputs are essential; this finite check uses the original six edge terms.
theorem all_essential : ∀ i∈(Finset.univ : Finset (Fin 5)), ∃ x : Fin 5→Bool,
    edge (Function.update x i (!x i)) ≠ edge x := by decide +kernel

-- The support bound even permits NOT gates, empty gates and arbitrary wire indices.
theorem lower (C : Circuit) (fan : FanInTwo C)
    (ev : ∀ x : Fin 5→Bool,C.eval (List.ofFn x)=edge x) : 4≤C.size := by
  have h := PEqualNP.MetaComplexity.Helpers.PermInputs.dep_lower_set 5 edge
    (Finset.univ : Finset (Fin 5)) all_essential C.size ⟨C,fan,le_rfl,ev⟩
  have card : (Finset.univ : Finset (Fin 5)).card=5 := by decide +kernel
  omega

theorem monoLower (C : Circuit) (mono : Monotone2 C)
    (ev : ∀ x : Fin 5→Bool,C.eval (List.ofFn x)=edge x) : 4≤C.size := by
  apply lower C _ ev
  intro g hg
  refine ⟨?_,(mono g hg).2⟩
  rcases (mono g hg).1 with h|h <;> simp [h]

theorem exact_size (s : ℕ) :
    (∃ C : Circuit, Monotone2 C ∧ ReadsBack 5 C ∧ C.size≤s ∧
      ∀ x : Fin 5→Bool,C.eval (List.ofFn x)=edge x) ↔ 4≤s := by
  constructor
  · rintro ⟨C,hm,_,hs,he⟩
    exact (monoLower C hm he).trans hs
  · intro h
    obtain ⟨hm,hr,hs,he⟩ := witness
    exact ⟨four,hm,hr,by rw [hs]; exact h,he⟩

theorem exact_negation : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) := by
  rintro ⟨C,hm,_,hs,he⟩
  have h := monoLower C hm he
  omega

theorem published_twin : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 3 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) := by
  rintro ⟨C,hm,hr,hs,he⟩
  have h := PEqualNP.Outside.L_meta_2135 C hm hr he
  omega

end K2336

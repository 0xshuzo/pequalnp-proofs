import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux

open scoped Classical
abbrev F := ZMod 2
abbrev W (ι : Type*) := ι → F

variable {ι κ : Type*} [Fintype ι]
variable (next : ι → ι) (h : ι → κ → F)

def Good (U : Submodule F (W ι)) : Prop :=
  (∀ x ∈ U, ∀ b, ∑ i, h i b * x i = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)

noncomputable def support (U : Submodule F (W ι)) : Finset ι :=
  Finset.univ.filter fun i => ∃ x ∈ U, x i ≠ 0

lemma mem_support (U : Submodule F (W ι)) (i : ι) :
    i ∈ support U ↔ ∃ x ∈ U, x i ≠ 0 := by simp [support]

lemma support_mono {U V : Submodule F (W ι)} (huv : U ≤ V) : support U ⊆ support V := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_support U i).mp hi
  exact (mem_support V i).mpr ⟨x,huv hx,hxi⟩

lemma bit_one {z : F} (hz : z ≠ 0) : z = 1 := by
  fin_cases z <;> first | rfl | contradiction

lemma adjacent_equal {U : Submodule F (W ι)} (hg : Good next h U)
    {i : ι} (hi : i ∈ support U) (hn : next i ∈ support U)
    {x : W ι} (hx : x ∈ U) : x i = x (next i) := by
  obtain ⟨u, hu, hui⟩ := (mem_support _ _).mp hi
  obtain ⟨v, hv, hvn⟩ := (mem_support _ _).mp hn
  have hu1 := bit_one hui
  have hv1 := bit_one hvn
  have hcheck := hg.2 u hu v hv i
  have hun : u (next i) ≠ 0 := by
    intro hz
    simp [hu1, hv1, hz] at hcheck
  have hu2 := bit_one hun
  simpa [hu1, hu2] using hg.2 x hx u hu i

def kernel (S : Finset ι) : Submodule F (W ι) where
  carrier := {x | (∀ b, ∑ i, h i b * x i = 0) ∧
    (∀ i, i ∉ S → x i = 0) ∧ (∀ i, i ∈ S → next i ∈ S → x i = x (next i))}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro b
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx.1 b, hy.1 b, zero_add]
    · intro i hi
      simp [hx.2.1 i hi, hy.2.1 i hi]
    · intro i hi hn
      simp [hx.2.2 i hi hn, hy.2.2 i hi hn]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro b
      calc
        (∑ i, h i b * (c • x) i) = ∑ i, c * (h i b * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          change h i b * (c * x i) = c * (h i b * x i)
          ring
        _ = 0 := by rw [← Finset.mul_sum, hx.1 b, mul_zero]
    · intro i hi
      simp [hx.2.1 i hi]
    · intro i hi hn
      simp [hx.2.2 i hi hn]

lemma good_kernel (S : Finset ι) : Good next h (kernel next h S) := by
  constructor
  · intro x hx
    exact hx.1
  · intro x hx y hy i
    by_cases hi : i ∈ S
    · by_cases hn : next i ∈ S
      · rw [hx.2.2 i hi hn, hy.2.2 i hi hn]
      · rw [hx.2.1 _ hn, hy.2.1 _ hn, mul_zero, zero_mul]
    · rw [hx.2.1 _ hi, hy.2.1 _ hi, zero_mul, mul_zero]

lemma le_kernel {U : Submodule F (W ι)} (hg : Good next h U) :
    U ≤ kernel next h (support U) := by
  intro x hx
  refine ⟨hg.1 x hx, ?_, ?_⟩
  · intro i hi
    by_contra hne
    exact hi ((mem_support _ _).mpr ⟨x,hx,hne⟩)
  · intro i hi hn
    exact adjacent_equal next h hg hi hn hx

lemma support_kernel_subset (S : Finset ι) : support (kernel next h S) ⊆ S := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_support _ _).mp hi
  by_contra hn
  exact hxi (hx.2.1 i hn)

lemma support_kernel {U : Submodule F (W ι)} (hg : Good next h U) :
    support (kernel next h (support U)) = support U :=
  Finset.Subset.antisymm (support_kernel_subset next h _) (support_mono (le_kernel next h hg))

theorem unique_at_max {U : Submodule F (W ι)} (hg : Good next h U)
    (maximal : ∀ V, Good next h V → support V = support U →
      Module.finrank F V ≤ Module.finrank F U) :
    kernel next h (support U) = U := by
  have hle := le_kernel next h hg
  have hdim := maximal _ (good_kernel next h _) (support_kernel next h hg)
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (Nat.le_antisymm (Submodule.finrank_mono hle) hdim)).symm

theorem common_max {U V : Submodule F (W ι)} (hu : Good next h U) (hv : Good next h V)
    (hs : support V = support U) (hr : Module.finrank F V = Module.finrank F U)
    (maximal : ∀ E, Good next h E → support E = support U →
      Module.finrank F E ≤ Module.finrank F U) : V = U := by
  have hle := le_kernel next h hv
  rw [hs, unique_at_max next h hu maximal] at hle
  exact Submodule.eq_of_le_of_finrank_eq hle hr

end PEqualNP.Outside.L_lib_912_aux

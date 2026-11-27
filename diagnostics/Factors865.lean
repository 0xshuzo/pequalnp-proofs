import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_865_aux
open scoped BigOperators
abbrev F := ZMod 2
abbrev W (n : Nat) := Fin n → F
def coord {n : Nat} (U : Submodule F (W n)) (i : Fin n) : U →ₗ[F] F :=
  (LinearMap.proj i).comp U.subtype
noncomputable def colors {n : Nat} (U : Submodule F (W n)) : Finset (U →ₗ[F] F) := by
  classical
  exact (Finset.univ.image (coord U)).erase 0

theorem mem_colors {n} {U : Submodule F (W n)} {c : U →ₗ[F] F} :
    c ∈ colors U ↔ c ≠ 0 ∧ ∃ i, coord U i=c := by
  classical
  simp [colors]

def encode {n : Nat} (U : Submodule F (W n)) : U →ₗ[F] (↥(colors U) → F) where
  toFun u c := c.val u
  map_add' u v := by funext c; exact map_add c.val u v
  map_smul' b u := by funext c; exact map_smul c.val b u

theorem encode_inj {n : Nat} (U : Submodule F (W n)) : Function.Injective (encode U) := by
  intro x y h
  apply Subtype.ext; funext i
  change coord U i x=coord U i y
  by_cases z : coord U i=0
  · rw [z];rfl
  · exact congrFun h ⟨coord U i,mem_colors.mpr ⟨z,i,rfl⟩⟩

theorem rank_le_colors {n : Nat} (U : Submodule F (W n)) :
    Module.finrank F U ≤ (colors U).card := by
  have rank := LinearMap.finrank_le_finrank_of_injective (encode_inj U)
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using rank

theorem colors_exact {n : Nat} (U : Submodule F (W n))
    (full : (colors U).card ≤ Module.finrank F U) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ c ∈ colors U, ∃ x ∈ U, ∀ i, x i = if coord U i=c then 1 else 0 := by
  classical
  have dim : Module.finrank F U = Module.finrank F (↥(colors U) → F) := by
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
    exact le_antisymm (rank_le_colors U) full
  have onto := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp (encode_inj U)
  intro c hc
  obtain ⟨x,eq⟩ := onto (fun d => if d.val=c then 1 else 0)
  refine ⟨x.val,x.property,?_⟩
  intro i
  by_cases hz : coord U i=0
  · have ho : (x.val i)=0 := by change coord U i x=0;rw [hz];rfl
    have nc := (mem_colors.mp hc).1
    simp [ho,hz,Ne.symm nc]
  · exact congrFun eq ⟨coord U i,mem_colors.mpr ⟨hz,i,rfl⟩⟩

theorem fiber_balance {n m : Nat} (U : Submodule F (W n)) (h : Fin n → Fin m → F)
    (full : (colors U).card ≤ Module.finrank F U)
    (checks : ∀ x ∈ U, ∀ b, ∑ i, h i b * x i = 0) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ c ∈ colors U, ∀ b, (∑ i ∈ Finset.univ.filter (fun i => coord U i=c), h i b) = 0 := by
  classical
  intro c hc b
  obtain ⟨x,hx,ev⟩ := colors_exact U full c hc
  have k := checks x hx b
  simpa only [ev,mul_ite,mul_one,mul_zero,Finset.sum_filter] using k

theorem isotropic_labels {n : Nat} (U : Submodule F (W n)) {i j : Fin n}
    (ortho : ∀ x ∈ U, ∀ y ∈ U, x i*y j=x j*y i) :
    coord U i=0 ∨ coord U j=0 ∨ coord U i=coord U j := by
  let L := coord U i
  let R := coord U j
  have bin : ∀ b : F, b=0 ∨ b=1 := by decide +kernel
  have det (u v : U) : L u * R v=R u * L v := ortho u u.property v v.property
  by_cases hL : L=0
  · exact Or.inl hL
  · have ex : ∃ u, L u ≠ 0 := by
      by_contra! h
      exact hL (LinearMap.ext fun u => h u)
    obtain ⟨u,hu⟩ := ex
    have Lu := (bin (L u)).resolve_left hu
    rcases bin (R u) with z | e
    · right;left;ext v
      exact (by simpa [Lu,z] using det u v : R v=0)
    · right;right;ext v
      exact (by simpa [Lu,e] using (det u v).symm : L v=R v)

end PEqualNP.Outside.L_lib_865_aux

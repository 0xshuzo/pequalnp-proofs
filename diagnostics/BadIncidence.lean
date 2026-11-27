import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux

abbrev Bin := ZMod 2
abbrev Plane (A : Type*) [AddCommGroup A] [Module Bin A] (d : ℕ) :=
  { U : Submodule Bin A // Module.finrank Bin U = d }

variable {A B : Type*} [AddCommGroup A] [Module Bin A] [FiniteDimensional Bin A]
variable [AddCommGroup B] [Module Bin B] [FiniteDimensional Bin B]

def pairMap (U : Submodule Bin A) (f : U →ₗ[Bin] B) : U →ₗ[Bin] A × B := U.subtype.prod f

lemma pairMap_inj (U : Submodule Bin A) (f : U →ₗ[Bin] B) :
    Function.Injective (pairMap U f) := by
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

def toPlane {d : ℕ} (p : (U : Plane A d) × (U.val →ₗ[Bin] B)) : Plane (A × B) d :=
  ⟨LinearMap.range (pairMap p.1.val p.2),
    (LinearMap.finrank_range_of_inj (pairMap_inj p.1.val p.2)).trans p.1.property⟩

lemma pair_le {U V : Submodule Bin A} (f : U →ₗ[Bin] B) (g : V →ₗ[Bin] B)
    (hle : LinearMap.range (pairMap U f) ≤ LinearMap.range (pairMap V g)) : U ≤ V := by
  intro x hx
  obtain ⟨v,hv⟩ := hle (LinearMap.mem_range_self (pairMap U f) ⟨x,hx⟩)
  have he : (v : A) = x := congrArg Prod.fst hv
  exact he ▸ v.property

lemma toPlane_injective (d : ℕ) :
    Function.Injective (toPlane (A := A) (B := B) (d := d)) := by
  rintro ⟨U,f⟩ ⟨V,g⟩ hh
  have hr : LinearMap.range (pairMap U.val f) = LinearMap.range (pairMap V.val g) :=
    congrArg Subtype.val hh
  have huv : U = V := Subtype.ext (le_antisymm (pair_le f g hr.le) (pair_le g f hr.ge))
  subst V
  suffices fe : f = g by subst g; rfl
  ext u
  obtain ⟨v,hv⟩ := hr.le (LinearMap.mem_range_self (pairMap U.val f) u)
  have he : v = u := Subtype.ext (congrArg Prod.fst hv)
  subst v
  exact (congrArg Prod.snd hv).symm

theorem grass_product (A B : Type*) [AddCommGroup A] [Module Bin A] [FiniteDimensional Bin A]
    [Finite A] [AddCommGroup B] [Module Bin B] [FiniteDimensional Bin B] [Finite B] (d : ℕ) :
    Nat.card (Plane A d) * 2 ^ (d * Module.finrank Bin B) ≤ Nat.card (Plane (A × B) d) := by
  classical
  letI : Fintype (Plane A d) := Fintype.ofFinite _
  letI (U : Plane A d) : Finite (U.val →ₗ[Bin] B) :=
    Finite.of_injective (fun f : U.val →ₗ[Bin] B => (f : U.val → B)) DFunLike.coe_injective
  have hf (U : Plane A d) : Nat.card (U.val →ₗ[Bin] B) = 2 ^ (d * Module.finrank Bin B) := by
    letI : Fintype (U.val →ₗ[Bin] B) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bin), ZMod.card,
      Module.finrank_linearMap, U.property]
  have hi := Nat.card_le_card_of_injective _ (toPlane_injective (A := A) (B := B) d)
  rw [Nat.card_sigma] at hi
  simpa [hf, Nat.card_eq_fintype_card] using hi

section Transport
open Finset
open scoped Classical

variable {X Y : Type*} [AddCommGroup X] [Module Bin X] [FiniteDimensional Bin X]
  [AddCommGroup Y] [Module Bin Y] [FiniteDimensional Bin Y]

lemma map_rank (f : X →ₗ[Bin] Y) (hi : Function.Injective f) (U : Submodule Bin X) :
    Module.finrank Bin (U.map f) = Module.finrank Bin U := by
  have hr : (f.comp U.subtype).range = U.map f := by
    ext x
    simp [LinearMap.mem_range, Submodule.mem_map]
  rw [←hr,LinearMap.finrank_range_of_inj (fun x y h => Subtype.ext (hi h))]

def plane_push (f : X →ₗ[Bin] Y) (hi : Function.Injective f) {d : ℕ} :
    Plane X d → Plane Y d :=
  fun U => ⟨U.val.map f,(map_rank f hi _).trans U.property⟩

lemma plane_push_inj (f : X →ₗ[Bin] Y) (hi : Function.Injective f) (d : ℕ) :
    Function.Injective (plane_push f hi (d := d)) := by
  intro U V hh
  have hm : U.val.map f = V.val.map f := congrArg Subtype.val hh
  apply Subtype.ext
  simpa only [Submodule.comap_map_eq_of_injective hi] using congrArg (Submodule.comap f) hm

lemma plane_card_congr [Finite X] [Finite Y] (h : Module.finrank Bin X = Module.finrank Bin Y) (d : ℕ) :
    Nat.card (Plane X d) = Nat.card (Plane Y d) := by
  let e : X ≃ₗ[Bin] Y := LinearEquiv.ofFinrankEq _ _ h
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_injective _ (plane_push_inj e.toLinearMap e.injective d)
  · exact Nat.card_le_card_of_injective _ (plane_push_inj e.symm.toLinearMap e.symm.injective d)

abbrev G (k d : ℕ) := Nat.card (Plane (Fin k → Bin) d)

theorem grass_gap {k D : ℕ} (h : k ≤ D) (d : ℕ) : G k d * (2^d)^(D-k) ≤ G D d := by
  let X := Fin k → Bin
  let Y := Fin (D-k) → Bin
  have hh : Module.finrank Bin (X × Y) = Module.finrank Bin (Fin D → Bin) := by
    simp only [X,Y,Module.finrank_prod,Module.finrank_fin_fun]
    omega
  have hi := grass_product X Y d
  rw [plane_card_congr hh d] at hi
  simpa only [G,X,Y,Module.finrank_fin_fun,←pow_mul] using hi

noncomputable def slice [Finite X] (E : Submodule Bin X) (d : ℕ) : Finset (Submodule Bin X) :=
  letI : Fintype (Submodule Bin X) := Fintype.ofFinite _
  univ.filter fun U : Submodule Bin X => Module.finrank Bin U = d ∧ U ≤ E

lemma mem_slice [Finite X] {U E : Submodule Bin X} {d : ℕ} :
    U ∈ slice E d ↔ Module.finrank Bin U = d ∧ U ≤ E := by simp [slice]

theorem slice_card [Finite X] (E : Submodule Bin X) (d : ℕ) :
    (slice E d).card = G (Module.finrank Bin E) d := by
  classical
  let f := E.subtype
  have hi : Function.Injective f := Subtype.val_injective
  let e : Plane E d ≃ ↥(slice E d) :=
    { toFun := fun U => ⟨U.val.map f, mem_slice.mpr ⟨(map_rank f hi _).trans U.property, by
        rintro _ ⟨x, _, rfl⟩
        exact x.property⟩⟩
      invFun := fun U => ⟨U.val.comap f, by
        have hle : U.val ≤ f.range := by
          intro x hx
          exact ⟨⟨x,(mem_slice.mp U.property).2 hx⟩,rfl⟩
        have hr := map_rank f hi (U.val.comap f)
        rw [Submodule.map_comap_eq_of_le hle, (mem_slice.mp U.property).1] at hr
        exact hr.symm⟩
      left_inv := fun U => Subtype.ext (Submodule.comap_map_eq_of_injective hi _)
      right_inv := fun U => Subtype.ext (Submodule.map_comap_eq_of_le (by
        intro x hx
        exact ⟨⟨x,(mem_slice.mp U.property).2 hx⟩,rfl⟩)) }
  calc
    (slice E d).card = Nat.card ↥(slice E d) := by simp
    _ = Nat.card (Plane E d) := Nat.card_congr e.symm
    _ = _ := plane_card_congr (by rw [Module.finrank_fin_fun]) d

theorem proper_slice [Finite X] {E F : Submodule Bin X} (h : E < F) (d : ℕ) :
    2^d * (slice E d).card ≤ (slice F d).card := by
  have hr : Module.finrank Bin E < Module.finrank Bin F :=
    lt_of_le_of_ne (Submodule.finrank_mono h.le) (fun e => h.ne (Submodule.eq_of_le_of_finrank_eq h.le e))
  rw [slice_card,slice_card,mul_comm]
  refine (Nat.mul_le_mul_left _ ?_).trans (grass_gap hr.le d)
  calc
    2^d = (2^d)^1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by omega)
end Transport


section BadInc
open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι]
abbrev Ambient (ι : Type*) := ι → Bin
noncomputable def suppB (E : Submodule Bin (Ambient ι)) : Finset ι :=
  univ.filter (fun i => ∃ x ∈ E, x i ≠ 0)
lemma suppB_mono {E V : Submodule Bin (Ambient ι)} (hle : V ≤ E) : suppB V ⊆ suppB E := by
  intro i hi
  obtain ⟨x,hx,hxi⟩ := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _,x,hle hx,hxi⟩

def silent (i : ι) : Submodule Bin (Ambient ι) where
  carrier := {x | x i = 0}
  zero_mem' := rfl
  add_mem' := fun {x y} hx hy => by change x i + y i = 0; rw [hx,hy,add_zero]
  smul_mem' := fun c x hx => by change c * x i = 0; rw [hx,mul_zero]

lemma joint_cost {α β : Type*} [DecidableEq β] (T : Finset α) (g : α → Finset β) (q C : ℕ)
    (h : ∀ x ∈ T, q*(g x).card ≤ C) : q*(T.biUnion g).card ≤ T.card*C := by
  calc
    _ ≤ q*(∑ x ∈ T,(g x).card) := Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ x ∈ T,q*(g x).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _x ∈ T,C := sum_le_sum h
    _ = _ := by simp

noncomputable def badInside (T : Finset (Submodule Bin (Ambient ι)))
    (E : Submodule Bin (Ambient ι)) (d : ℕ) : Finset (Submodule Bin (Ambient ι)) :=
  (slice E d).filter (fun U => suppB U ≠ suppB E ∨ ∃ F ∈ T, F ≠ E ∧ U ≤ F)

theorem cost_badInside (T : Finset (Submodule Bin (Ambient ι))) (E : Submodule Bin (Ambient ι))
    (d : ℕ) (ht : ∀ F ∈ T, Module.finrank Bin F = Module.finrank Bin E) :
    2^d*(badInside T E d).card ≤ (Fintype.card ι+T.card)*(slice E d).card := by
  classical
  let S := suppB E
  let C := fun i => slice (E ⊓ silent i) d
  let V := fun F => slice (E ⊓ F) d
  have hc (i : ι) (hi : i ∈ S) : 2^d*(C i).card ≤ (slice E d).card := by
    apply proper_slice
    apply lt_of_le_of_ne inf_le_left
    intro eq
    obtain ⟨x,hx,hxi⟩ := (mem_filter.mp hi).2
    have hmem : x ∈ E ⊓ silent i := eq.symm ▸ hx
    exact hxi hmem.2
  have hv (F : Submodule Bin (Ambient ι)) (hF : F ∈ T.erase E) :
      2^d*(V F).card ≤ (slice E d).card := by
    apply proper_slice
    apply lt_of_le_of_ne inf_le_left
    intro eq
    have hle : E ≤ F := eq ▸ (inf_le_right : E ⊓ F ≤ F)
    exact (mem_erase.mp hF).1 (Submodule.eq_of_le_of_finrank_eq hle (ht F (mem_erase.mp hF).2).symm).symm
  have sub : badInside T E d ⊆ S.biUnion C ∪ (T.erase E).biUnion V := by
    intro U hU
    obtain ⟨hs,hbad⟩ := mem_filter.mp hU
    obtain ⟨hd,hle⟩ := mem_slice.mp hs
    rcases hbad with h | ⟨F,hFT,hFE,hUF⟩
    · have hw : ∃ i ∈ S, i ∉ suppB U := by
        by_contra! hh
        exact h (Finset.Subset.antisymm (suppB_mono hle) hh)
      obtain ⟨i,hi,hn⟩ := hw
      apply mem_union_left
      refine mem_biUnion.mpr ⟨i,hi,mem_slice.mpr ⟨hd,le_inf hle ?_⟩⟩
      intro x hx
      change x i = 0
      by_contra hne
      exact hn (mem_filter.mpr ⟨mem_univ _,x,hx,hne⟩)
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨F,mem_erase.mpr ⟨hFE,hFT⟩,mem_slice.mpr ⟨hd,le_inf hle hUF⟩⟩
  have h1 := joint_cost S C (2^d) _ hc
  have h2 := joint_cost (T.erase E) V (2^d) _ hv
  have hcard1 : S.card ≤ Fintype.card ι := card_le_univ S
  have hcard2 : (T.erase E).card ≤ T.card := card_le_card (erase_subset _ _)
  calc
    _ ≤ 2^d*((S.biUnion C).card+((T.erase E).biUnion V).card) :=
      Nat.mul_le_mul_left _ ((card_le_card sub).trans (card_union_le _ _))
    _ ≤ (S.card+(T.erase E).card)*(slice E d).card := by
      rw [Nat.mul_add,Nat.add_mul]
      exact Nat.add_le_add h1 h2
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add hcard1 hcard2)
end BadInc

end PEqualNP.Outside.L_lib_912_aux

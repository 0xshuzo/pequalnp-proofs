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

end PEqualNP.Outside.L_lib_912_aux

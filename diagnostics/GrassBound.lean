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
  have hf (U : Plane A d) : Nat.card (U.val →ₗ[Bin] B) = 2 ^ (d * Module.finrank Bin B) := by
    letI : Fintype (U.val →ₗ[Bin] B) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bin), ZMod.card,
      Module.finrank_linearMap, U.property]
  have hi := Nat.card_le_card_of_injective _ (toPlane_injective (A := A) (B := B) d)
  rw [Nat.card_sigma] at hi
  simpa [hf, Nat.card_eq_fintype_card] using hi

end PEqualNP.Outside.L_lib_912_aux

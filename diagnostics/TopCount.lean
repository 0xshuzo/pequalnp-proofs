import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux

theorem grassmann_top (D : ℕ) :
    Nat.card {V : Submodule (ZMod 2) (Fin D → ZMod 2) // Module.finrank (ZMod 2) V = D} = 1 := by
  classical
  let T := {V : Submodule (ZMod 2) (Fin D → ZMod 2) // Module.finrank (ZMod 2) V = D}
  let e : T ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨⊤, by simp [Module.finrank_fin_fun]⟩
      left_inv := fun u => by
        apply Subtype.ext
        exact (Submodule.eq_top_of_finrank_eq (by rw [u.2, Module.finrank_fin_fun])).symm
      right_inv := fun u => by cases u; rfl }
  simpa using Nat.card_congr e

theorem exceptional_top {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (mixed : Finset (Submodule K V)) (D : ℕ)
    (support : Submodule K V → α) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let top := mixed.filter (fun U => Module.finrank K U = D)
    (top.filter (fun U => ¬ ∃ E ∈ top, U ≤ E ∧ support U = support E ∧
      ∀ E' ∈ top, U ≤ E' → E' = E)).card = 0 := by
  classical
  intro dec top
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro U hu
  obtain ⟨hU, hbad⟩ := Finset.mem_filter.mp hu
  apply hbad
  refine ⟨U, hU, le_rfl, rfl, ?_⟩
  intro E hE hle
  exact (Submodule.eq_of_le_of_finrank_eq hle
    ((Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hE).2.symm)).symm

def requested : Prop :=
∀ (t d : ℕ), 4 ≤ t →
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let D := a-5
  let top := mixed.filter (fun E : Submodule F W => Module.finrank F E = D)
  let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = d)
  let exceptional := layer.filter (fun U =>
    ¬ ∃ E ∈ top, U ≤ E ∧ supp U = supp E ∧
      ∀ E' ∈ top, U ≤ E' → E' = E)
  let model := 12*t*(7*t-1) *
    Nat.card {V : Submodule F (Fin D → F) // Module.finrank F V = d}
  d ≤ D → 2*n^2 ≤ 2^d →
    (Nat.dist layer.card model + exceptional.card) * 2^d ≤ 32*n^10*model

theorem top_count_necessary (hclaim : requested) :
∀ (t : ℕ), 4 ≤ t →
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let D := a-5
  let top := mixed.filter (fun E : Submodule F W => Module.finrank F E = D)
  2*n^2 ≤ 2^D → 32*n^10*(12*t*(7*t-1)) < 2^D → top.card = 12*t*(7*t-1) := by
  intro t ht dec F n a W inst next h good supp sites spaces mixed D top hsmall hlarge
  have hmain := hclaim t D ht le_rfl hsmall
  let exceptional := top.filter (fun U => ¬ ∃ E ∈ top, U ≤ E ∧ supp U = supp E ∧
    ∀ E' ∈ top, U ≤ E' → E' = E)
  let m := 12*t*(7*t-1)
  change (Nat.dist top.card (m * _) + exceptional.card) * 2^D ≤ 32*n^10*(m * _) at hmain
  rw [grassmann_top D, Nat.mul_one] at hmain
  have he : exceptional.card = 0 := exceptional_top mixed D supp
  rw [he, Nat.add_zero] at hmain
  by_contra hne
  have hd : 1 ≤ Nat.dist top.card m := by
    dsimp only [m]
    unfold Nat.dist
    omega
  have hm := Nat.mul_le_mul_right (2^D) hd
  rw [Nat.one_mul] at hm
  exact (Nat.not_le_of_gt hlarge) (hm.trans hmain)

end PEqualNP.Outside.L_lib_912_aux

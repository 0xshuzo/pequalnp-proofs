import PEqualNP.Defs
namespace Fibers468
open scoped BigOperators
abbrev K := ZMod 2
abbrev Vec (n : ℕ) := Fin n → K
abbrev Mat (a b : ℕ) := Fin a × Fin b → K
def outer {a b : ℕ} (u : Vec a) (v : Vec b) : Mat a b := fun xy => u xy.1 * v xy.2
def outerMap {a b : ℕ} (u : Vec a) : Vec b →ₗ[K] Mat a b where
  toFun := outer u
  map_add' f g := by funext xy; exact mul_add .. 
  map_smul' t f := by funext xy; change u xy.1*(t*f xy.2)=t*(u xy.1*f xy.2); ring
def fiber {a b : ℕ} (L : Submodule K (Mat a b)) (u : Vec a) : Submodule K (Vec b) :=
  L.comap (outerMap u)
theorem cardK (X : Type*) [AddCommGroup X] [Module K X] [Finite X] [Fintype X] :
    Fintype.card X=2^(Module.finrank K X) := by
  have h := Module.natCard_eq_pow_finrank (K:=K) (V:=X)
  simpa only [Nat.card_eq_fintype_card,Nat.card_zmod] using h

theorem fibers_budget {a b : ℕ} (L : Submodule K (Mat a b)) {ι : Type} [Fintype ι]
    (u : ι → Vec a) (li : LinearIndependent K u) :
    (∑ i, Module.finrank K (fiber L (u i))) ≤ Module.finrank K L := by
  classical
  let pack (f : (i : ι) → fiber L (u i)) : L :=
    ⟨∑ i, outer (u i) (f i).val, L.sum_mem (fun i _ => (f i).property)⟩
  have inject : Function.Injective pack := by
    intro f g eq
    have eqs : (∑ i, outer (u i) (f i).val) = ∑ i, outer (u i) (g i).val := congrArg Subtype.val eq
    funext i
    apply Subtype.ext
    funext y
    have id (x : Fin a) : (∑ i, u i x * (f i).val y) = ∑ i, u i x * (g i).val y := by
      simpa only [Finset.sum_apply,outer] using congrFun eqs (x,y)
    have zero : ∑ i, ((f i).val y-(g i).val y) • u i=0 := by
      funext x
      change (∑ i, ((f i).val y-(g i).val y) • u i) x=0
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sub_mul,Finset.sum_sub_distrib]
      simpa only [mul_comm,sub_eq_zero] using id x
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp li _ zero i)
  have h := Fintype.card_le_of_injective pack inject
  rw [Fintype.card_pi,cardK L] at h
  simp_rw [cardK (fiber L _)] at h
  rw [←Finset.prod_pow_eq_pow_sum] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp h

theorem heavy_count {a b d r : ℕ} (L : Submodule K (Mat a b))
    (bound : Module.finrank K L < (r+1)*(d+1)) :
    (Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))).card ≤ 2^r := by
  classical
  let heavy : Set (Vec a) := {u | d < Module.finrank K (fiber L u)}
  obtain ⟨B,sub,span,ind⟩ := exists_linearIndependent K heavy
  have h := fibers_budget L (fun i : B => i.val) ind
  have sumBound : Fintype.card B * (d+1) ≤ ∑ i : B, Module.finrank K (fiber L i.val) := by
    calc
      _ = ∑ _i : B, (d+1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => sub i.property)
  have br : Fintype.card B ≤ r := by
    by_contra! bad
    have sc := Nat.mul_le_mul_right (d+1) bad
    omega
  have sr : Module.finrank K (Submodule.span K heavy) ≤ r := by
    have eq := finrank_span_set_eq_card (R:=K) ind
    rw [span] at eq
    simpa [eq] using br
  let X := Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))
  let emb (x : X) : Submodule.span K heavy := ⟨x.val,Submodule.subset_span (Finset.mem_filter.mp x.property).2⟩
  have inject : Function.Injective emb := fun x y h => Subtype.ext (congrArg Subtype.val h)
  calc
    X.card = Fintype.card X := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Submodule.span K heavy) := Fintype.card_le_of_injective emb inject
    _ ≤ 2^r := by rw [cardK]; exact Nat.pow_le_pow_right (by decide) sr

end Fibers468

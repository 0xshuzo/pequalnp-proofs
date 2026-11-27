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
  simpa [Nat.card_eq_fintype_card,K] using h

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
  rw [Finset.prod_pow_eq_pow_sum] at h
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
    have sc : (r+1)*(d+1) ≤ Fintype.card B*(d+1) := Nat.mul_le_mul_right (d+1) bad
    omega
  have sr : Module.finrank K (Submodule.span K heavy) ≤ r := by
    have eq := finrank_span_set_eq_card (R:=K) ind
    rw [span] at eq
    simpa [eq] using br
  let X := Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))
  let emb (x : X) : Submodule.span K heavy := ⟨x.val,Submodule.subset_span (Finset.mem_filter.mp x.property).2⟩
  have inject : Function.Injective emb := fun x y h => Subtype.ext (congrArg (fun z : Submodule.span K heavy => z.val) h)
  calc
    X.card = Fintype.card X := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Submodule.span K heavy) := Fintype.card_le_of_injective emb inject
    _ ≤ 2^r := by rw [cardK]; exact Nat.pow_le_pow_right (by decide) sr

end Fibers468
namespace Fibers468
open scoped BigOperators
theorem matrixBound {a b d r : ℕ} (L : Submodule K (Mat a b))
    (bound : Module.finrank K L < (r+1)*(d+1)) :
    (Finset.univ.filter (fun z : Vec a × Vec b => outer z.1 z.2 ∈ L)).card ≤
      2^(a+d)+2^(r+b) := by
  classical
  let heavy := Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))
  let count (u : Vec a) := (Finset.univ.filter (fun v : Vec b => outer u v∈L)).card
  have cnt (u : Vec a) : count u = 2^Module.finrank K (fiber L u) := by
    change (Finset.univ.filter (fun v : Vec b => outer u v∈L)).card = _
    rw [← Fintype.card_subtype]
    exact cardK (fiber L u)
  have cb (u : Vec a) : count u ≤ (if u∈heavy then 2^b else 0) + 2^d := by
    split_ifs with h
    · have ub : count u ≤ Fintype.card (Vec b) := Finset.card_le_univ _
      simp [Vec] at ub
      omega
    · have small : Module.finrank K (fiber L u) ≤ d := by
        by_contra! bad
        exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩)
      rw [cnt,zero_add]
      exact Nat.pow_le_pow_right (by decide) small
  have splitCount : (Finset.univ.filter (fun z : Vec a × Vec b => outer z.1 z.2∈L)).card = ∑ u, count u := by
    simp only [count,Finset.card_filter,Fintype.sum_prod_type]
  rw [splitCount]
  calc
    _ ≤ ∑ u : Vec a, ((if u∈heavy then 2^b else 0) + 2^d) := Finset.sum_le_sum (fun i _ => cb i)
    _ = heavy.card * 2^b + 2^a * 2^d := by
      rw [Finset.sum_add_distrib,←Finset.sum_filter]
      simp [Vec,K]
    _ ≤ 2^r*2^b + 2^a * 2^d := Nat.add_le_add_right (Nat.mul_le_mul_right _ (heavy_count L bound)) _
    _ = _ := by rw [←pow_add,←pow_add,add_comm]
end Fibers468

namespace Uniform468
open scoped BigOperators
theorem pull_count {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Fintype X] [Fintype Y]
    (f : X →+ Y) (onto : Function.Surjective f) (B : Finset Y) :
    (Finset.univ.filter (fun x => f x∈B)).card * Fintype.card Y = B.card * Fintype.card X := by
  classical
  choose sec hs using onto
  let A := Finset.univ.filter (fun x => f x∈B)
  let e : (A × Y) ≃ (B × X) := {
    toFun := fun ⟨a,y⟩ => (⟨f a.val,(Finset.mem_filter.mp a.property).2⟩,a.val+sec y-sec (f a.val))
    invFun := fun ⟨y,x⟩ => (⟨x+sec y.val-sec (f x),Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hs,y.property]⟩⟩,f x)
    left_inv := by
      intro z; obtain ⟨a,y⟩ := z
      apply Prod.ext
      · apply Subtype.ext; dsimp; simp [hs] <;> abel
      · dsimp; simp [hs]
    right_inv := by
      intro z; obtain ⟨y,x⟩ := z
      apply Prod.ext
      · apply Subtype.ext; dsimp; simp [hs]
      · dsimp; simp [hs] <;> abel
  }
  simpa [A] using Fintype.card_congr e
end Uniform468
namespace Blocks468
open Fibers468
abbrev Idx (B n : ℕ) := Fin B × (Fin n ⊕ Fin n)
def restrictMap {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) : Vec m →+ (Vec n × Vec n) where
  toFun x := (fun i => x (e (j,.inl i)),fun i => x (e (j,.inr i)))
  map_zero' := rfl
  map_add' _ _ := rfl
theorem restrict_onto {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) :
    Function.Surjective (restrictMap e j) := by
  classical
  intro z
  let emb := fun i : Fin n ⊕ Fin n => e (j,i)
  have inj : Function.Injective emb := fun _ _ h => congrArg Prod.snd (e.injective h)
  let both := Sum.elim z.1 z.2
  let x : Vec m := Function.extend emb both (fun _ => 0)
  refine ⟨x,Prod.ext ?_ ?_⟩
  · funext i; exact inj.extend_apply both _ (Sum.inl i)
  · funext i; exact inj.extend_apply both _ (Sum.inr i)
def feature {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) (x : Vec m) : Mat n n :=
  outer ((restrictMap e j x).1) ((restrictMap e j x).2)
def admissible {B n m : ℕ} (e : Idx B n ↪ Fin m) (H : Finset (Vec m)) :=
  ∀ j, LinearIndepOn K (feature e j) (H : Set (Vec m))
theorem avoid {B t m D : ℕ} (bp : 0<B) (dp : 0<D) (num : 2*B*D ≤ 2^t)
    (e : Idx B (2*t) ↪ Fin m) (H : Finset (Vec m))
    (small : H.card < (t+1)*(t+1)) (old : admissible e H) :
    ∃ bad : Finset (Vec m), bad.card*D ≤ Fintype.card (Vec m) ∧
      ∀ v, v∉bad → admissible e (insert v H) := by
  classical
  let L (j : Fin B) := Submodule.span K ((feature e j) '' (H : Set (Vec m)))
  have dim (j : Fin B) : Module.finrank K (L j) < (t+1)*(t+1) := by
    apply lt_of_le_of_lt (finrank_span_le_card ..) ?_
    have sub : ((feature e j) '' (H : Set (Vec m))).toFinset ⊆ H.image (feature e j) := by
      intro x hx; simpa using hx
    exact ((Finset.card_le_card sub).trans Finset.card_image_le).trans_lt small
  let R (j : Fin B) := Finset.univ.filter (fun w : Vec (2*t) × Vec (2*t) => outer w.1 w.2 ∈ L j)
  let badAt (j : Fin B) := Finset.univ.filter (fun x : Vec m => restrictMap e j x ∈ R j)
  let Bad := Finset.univ.biUnion badAt
  refine ⟨Bad,?_,?_⟩
  · have per (j : Fin B) : (badAt j).card*(B*D) ≤ Fintype.card (Vec m) := by
      have pull := Uniform468.pull_count (restrictMap e j) (restrict_onto e j) (R j)
      change (badAt j).card * Fintype.card (Vec (2*t) × Vec (2*t)) = (R j).card*Fintype.card (Vec m) at pull
      have cap := matrixBound (L j) (dim j)
      change (R j).card ≤ 2^(2*t+t)+2^(t+2*t) at cap
      have num' : (R j).card*(B*D) ≤ Fintype.card (Vec (2*t) × Vec (2*t)) := by
        simp only [Vec,Fintype.card_prod,Fintype.card_fun,ZMod.card,Fintype.card_fin,←pow_add]
        rw [show 2*t+2*t=(2*t+t)+t by omega,pow_add]
        have s := Nat.mul_le_mul_left (2^(2*t+t)) num
        rw [Nat.add_comm t (2*t)] at cap
        nlinarith only [Nat.mul_le_mul_right (B*D) cap,s]
      have positive : 0<Fintype.card (Vec (2*t) × Vec (2*t)) := Fintype.card_pos
      apply Nat.le_of_mul_le_mul_right (show _ * Fintype.card (Vec (2*t) × Vec (2*t)) ≤ _ * Fintype.card (Vec (2*t) × Vec (2*t)) from ?_) positive
      calc
        _ = ((badAt j).card*Fintype.card (Vec (2*t) × Vec (2*t)))*(B*D) := by ring
        _ = ((R j).card*(B*D))*Fintype.card (Vec m) := by rw [pull]; ring
        _ ≤ _ := by simpa only [mul_comm] using Nat.mul_le_mul_right (Fintype.card (Vec m)) num'
    have sc := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => per j)
    rw [←Finset.sum_mul] at sc
    have whole := Nat.mul_le_mul_right (B*D) (Finset.card_biUnion_le : Bad.card ≤ ∑ j, (badAt j).card)
    have bound : (Bad.card*D)*B ≤ Fintype.card (Vec m)*B := by
      calc
        _ = Bad.card*(B*D) := by ring
        _ ≤ _ := whole.trans (by simpa [mul_comm] using sc)
    exact Nat.le_of_mul_le_mul_right bound bp
  · intro v hv j
    have no : feature e j v ∉ L j := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩⟩
    have vn : v∉H := fun h => no (Submodule.subset_span ⟨v,h,rfl⟩)
    rw [Finset.coe_insert]
    exact (linearIndepOn_insert (by simpa using vn)).2 ⟨old j,no⟩
theorem skipBlock {B n m : ℕ} (e : Idx B n ↪ Fin m) (S : Finset (Fin m)) (size : S.card<B) :
    ∃ j : Fin B, ∀ i, e (j,i) ∉ S := by
  classical
  by_contra! h
  choose i hi using h
  let f (j : Fin B) : S := ⟨e (j,i j),hi j⟩
  have inject : Function.Injective f := fun x y eq => congrArg Prod.fst (e.injective (congrArg Subtype.val eq))
  have bad := Fintype.card_le_of_injective f inject
  simp at bad
  omega
end Blocks468

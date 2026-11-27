import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30642_aux
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
def D {n} (g : V n → F) (a x : V n) : F := g (x+a)-g x
def T {n} (g : V n → F) (a b c : V n) := D (D (D g a) b) c 0
def Cubic {n} (g : V n → F) := ∀ a b c d x, D (D (D (D g a) b) c) d x=0
def Quad {n} (q : V n → F) := ∃ (s : F) (h : V n) (M : Fin n → V n),
    ∀ x, q x=s+dotProduct h x+∑ i,∑ j, M i j*x i*x j

set_option maxHeartbeats 600000 in
theorem quad_diff {n} {q : V n → F} (hq : Quad q) (u v w x : V n) :
    D (D (D q u) v) w x=0 := by
  obtain ⟨s,h,M,hq⟩ := hq
  simp only [D,hq,dotProduct,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
  ring

theorem map_dot {n} (h x u : V n) : dotProduct h (x+u)=dotProduct h x + dotProduct h u := by
  simp only [dotProduct, Pi.add_apply, mul_add,Finset.sum_add_distrib]

structure Features {n : ℕ} (g : V n → F) (r : ℕ) where
  A : Fin r × Fin 3 → V n
  q : V n → F
  hq : Quad q
  H : Fin r → V n → F
  co : Fin r → F
  start : Fin r → Fin 2 → F
  earlier : Fin r → Fin 2 → Fin r → F
  strict : ∀ i k j, i.val ≤ j.val → earlier i k j=0
  gate : ∀ i x, H i x =
    (start i 0+dotProduct (A (i,0)) x+∑ j, earlier i 0 j * H j x) *
    (start i 1+dotProduct (A (i,1)) x+∑ j, earlier i 1 j * H j x)
  out : ∀ x, g x=q x+∑ i, (co i+dotProduct (A (i,2)) x)*H i x

theorem same_prefix {n r} {g : V n → F} (S : Features g r) (u : V n) (m : ℕ)
    (zero : ∀ (i : Fin r), i.val<m → ∀ k : Fin 2, dotProduct (S.A (i,k.castSucc)) u=0) :
    ∀ (i : Fin r), i.val<m → ∀ x, S.H i (x+u)=S.H i x := by
  intro i
  induction i using Fin.strongInductionOn with
  | h i ih =>
    intro hi x
    have prev (k : Fin 2) : (∑ j, S.earlier i k j*S.H j (x+u)) = ∑ j, S.earlier i k j*S.H j x := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases lt : j.val<i.val
      · rw [ih j lt (by omega) x]
      · rw [S.strict i k j (by omega),zero_mul,zero_mul]
    rw [S.gate i (x+u),S.gate i x,map_dot,map_dot,prev,prev]
    have z₀ : dotProduct (S.A (i,0)) u=0 := zero i hi 0
    have z₁ : dotProduct (S.A (i,1)) u=0 := zero i hi 1
    rw [z₀,z₁,add_zero,add_zero]

def featureMap {n r} (A : Fin r × Fin 3 → V n) : V n →ₗ[F] (Fin r × Fin 3 → F) :=
  Matrix.mulVecLin (Matrix.of A)

theorem ker_in_rad {n r} {g : V n → F} (S : Features g r) (R : Submodule F (V n))
    (rad : ∀ u, u∈R ↔ ∀ v w, T g u v w=0) : LinearMap.ker (featureMap S.A) ≤ R := by
  intro u hu
  have zero (j) : dotProduct (S.A j) u=0 := congrFun (show featureMap S.A u=0 from hu) j
  have hH (i : Fin r) (x : V n) : S.H i (x+u)=S.H i x :=
    same_prefix S u r (fun i _ k => zero _) i i.isLt x
  have de : D g u = D S.q u := by
    funext x
    unfold D
    rw [S.out (x+u),S.out x]
    simp_rw [map_dot,zero,add_zero,hH]
    ring
  apply (rad u).mpr
  intro v w
  unfold T
  rw [de]
  exact quad_diff S.hq _ _ _ _

theorem feature_bound {n r} {g : V n → F} (S : Features g r) (R : Submodule F (V n))
    (rad : ∀ u, u∈R ↔ ∀ v w, T g u v w=0) :
    n-Module.finrank F R ≤ 3*r ∧
     (n-Module.finrank F R=3*r → Function.Surjective (featureMap S.A)) := by
  let P := featureMap S.A
  have hk := Submodule.finrank_mono (ker_in_rad S R rad)
  have hd := P.finrank_range_add_finrank_ker
  have hc := (LinearMap.range P).finrank_le
  have domain : Module.finrank F (V n)=n := Module.finrank_fin_fun ..
  have cod : Module.finrank F (Fin r × Fin 3 → F)=r*3 := by
    simp [Module.finrank_fintype_fun_eq_card]
  rw [domain] at hd
  rw [cod] at hc
  change Module.finrank F (LinearMap.ker P) ≤ _ at hk
  constructor
  · omega
  · intro hh
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [cod]
    omega

theorem independent_of_surjective {n r} {A : Fin r × Fin 3 → V n}
    (hA : Function.Surjective (featureMap A)) : LinearIndependent F A := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨u,hu⟩ := hA (Pi.single j 1)
  have E (k) : dotProduct (A k) u = (Pi.single j 1 : Fin r × Fin 3 → F) k := congrFun hu k
  let L : V n →ₗ[F] F := (LinearMap.proj (0 : Fin 1)).comp
    (Matrix.mulVecLin (Matrix.of (fun _ : Fin 1 => u)))
  have h (k) : L (A k) = (Pi.single j 1 : Fin r × Fin 3 → F) k :=
    (dotProduct_comm u (A k)).trans (E k)
  have he := congrArg L hc
  simp only [map_sum,map_smul,map_zero,h,smul_eq_mul] at he
  simpa [Pi.single_apply] using he
end PEqualNP.Outside.L_meta_30642_aux

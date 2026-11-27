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
  refine Fin.strong_induction_on (motive := fun i => i.val<m → ∀ x, S.H i (x+u)=S.H i x) ?_ i
  intro i ih
  all_goals
    intro hi x
    have prev (k : Fin 2) : (∑ j, S.earlier i k j*S.H j (x+u)) = ∑ j, S.earlier i k j*S.H j x := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases lt : j.val < i.val
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
    change Module.finrank F (LinearMap.range P)=r*3
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

section Axes
variable {n r : Nat} {g : V n → F} (S : Features g r)
variable (onto : Function.Surjective (featureMap S.A))

noncomputable def move (p : Fin r × Fin 3) : V n :=
  Classical.choose (onto (Pi.single p 1))
theorem dot_move (p t : Fin r × Fin 3) : dotProduct (S.A t) (move S onto p) = if p=t then 1 else 0 := by
  have e := congrFun (Classical.choose_spec (onto (Pi.single p 1))) t
  simpa [move,featureMap,Matrix.mulVecLin_apply,Matrix.mulVec,Pi.single_apply,eq_comm] using e

def operand (i : Fin r) (k : Fin 2) (x : V n) :=
  S.start i k + dotProduct (S.A (i,k.castSucc)) x + ∑ j, S.earlier i k j*S.H j x

theorem h_prev (i j : Fin r) (t : Fin 3) (hlt : j.val < i.val) (x : V n) :
    S.H j (x+move S onto (i,t))=S.H j x := by
  apply same_prefix S _ i.val _ j hlt x
  intro l hl k
  rw [dot_move,if_neg]
  intro h
  have e : i=l := congrArg Prod.fst h
  subst l
  omega

theorem op_at (i : Fin r) (k t : Fin 2) (x : V n) :
    operand S i k (x+move S onto (i,t.castSucc)) =
      operand S i k x + (if t=k then 1 else 0) := by
  unfold operand
  rw [map_dot,dot_move]
  have eq : (∑ j, S.earlier i k j * S.H j (x + move S onto (i,t.castSucc))) =
      ∑ j, S.earlier i k j * S.H j x := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases lt : j.val < i.val
    · rw [h_prev S onto i j t.castSucc lt]
    · rw [S.strict i k j (by omega),zero_mul,zero_mul]
  rw [eq]
  by_cases h : t=k
  · subst t; simp;ring
  · have hn : (i,t.castSucc)≠(i,k.castSucc) := fun e => h (Fin.ext (congrArg (fun z : Fin r × Fin 3 => z.2.val) e))
    simp [h,hn]

theorem gate_op (i : Fin r) (x : V n) : S.H i x=operand S i 0 x * operand S i 1 x := S.gate i x

theorem diff_H (i : Fin r) (k : Fin 2) :
    D (S.H i) (move S onto (i,k.castSucc)) = operand S i (1-k) := by
  funext x
  unfold D
  rw [gate_op S i (x+_),gate_op S i x,op_at S onto,op_at S onto]
  fin_cases k <;> simp <;> ring

theorem cross_H (i : Fin r) (x : V n) :
    D (D (S.H i) (move S onto (i,0))) (move S onto (i,1)) x=1 := by
  change D (D (S.H i) (move S onto (i,(0 : Fin 2).castSucc))) (move S onto (i,(1 : Fin 2).castSucc)) x=1
  rw [diff_H]
  change operand S i 1 (x+move S onto (i,(1 : Fin 2).castSucc)) - operand S i 1 x=1
  rw [op_at]
  simp

theorem coeff_fixed (i j : Fin r) (x : V n) : S.H j (x+move S onto (i,2))=S.H j x := by
  apply same_prefix S _ r _ j j.isLt x
  intro l _ k
  rw [dot_move,if_neg]
  intro eq
  have h := congrArg (fun z : Fin r × Fin 3 => z.2.val) eq
  have z := k.isLt
  change 2=k.val at h
  omega

theorem coeff_deriv (i : Fin r) : D g (move S onto (i,2)) =
    D S.q (move S onto (i,2)) + S.H i := by
  let u := move S onto (i,2)
  funext x
  change g (x+u)-g x=(S.q (x+u)-S.q x)+S.H i x
  rw [S.out (x+u),S.out x]
  have h (j : Fin r) :
      (S.co j+dotProduct (S.A (j,2)) (x+u))*S.H j (x+u) =
      (S.co j+dotProduct (S.A (j,2)) x)*S.H j x + (if j=i then S.H i x else 0) := by
    rw [map_dot,coeff_fixed S onto,dot_move]
    by_cases eq : j=i
    · subst j;simp;ring
    · simp [eq,Ne.symm eq]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem D_plus (f h : V n → F) (u : V n) : D (f+h) u = D f u + D h u := by
  funext x;simp only [D,Pi.add_apply];ring
theorem D_const (s : F) (u : V n) : D (fun _ => s) u = 0 := by
  funext x;simp [D]
theorem D_zero (u : V n) : D (0 : V n → F) u=0 := D_const 0 u

include onto in
theorem H_quadratic (hg : Cubic g) (i : Fin r) (a b c x : V n) :
    D (D (D (S.H i) a) b) c x=0 := by
  let u := move S onto (i,2)
  have h := hg u a b c x
  rw [show D g u=D S.q u+S.H i from coeff_deriv S onto i,D_plus,D_plus,D_plus] at h
  have k : D (D (D S.q u) a) b = 0 := funext (quad_diff S.hq u a b)
  simpa [k,D_zero] using h

include onto in
theorem operand_affine (hg : Cubic g) (i : Fin r) (k : Fin 2) (a b x : V n) :
    D (D (operand S i k) a) b x=0 := by
  have h := H_quadratic S onto hg i (move S onto (i,(1-k).castSucc)) a b x
  rw [diff_H] at h
  have v : (1:Fin 2)-(1-k)=k := by fin_cases k <;> decide
  simpa only [v] using h
end Axes

theorem second_operand {n r} {g : V n → F} (S : Features g r) (i : Fin r) (k : Fin 2) (a b x : V n) :
    D (D (operand S i k) a) b x = ∑ j, S.earlier i k j * D (D (S.H j) a) b x := by
  simp only [D,operand,map_dot,mul_sub,Finset.sum_sub_distrib]
  ring

theorem no_earlier {n r} {g : V n → F} (S : Features g r) (onto : Function.Surjective (featureMap S.A))
    (hg : Cubic g) (i : Fin r) (k : Fin 2) (j₀ : Fin r) : S.earlier i k j₀=0 := by
  classical
  by_contra hn
  let M := Finset.univ.filter (fun j => S.earlier i k j ≠ 0)
  have ne : M.Nonempty := ⟨j₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let j := M.max' ne
  have mj : j∈M := Finset.max'_mem M ne
  have nz := (Finset.mem_filter.mp mj).2
  let a := move S onto (j,0)
  let b := move S onto (j,1)
  have z := operand_affine S onto hg i k a b 0
  rw [second_operand] at z
  have one : D (D (S.H j) a) b 0=1 := cross_H S onto j 0
  rw [Finset.sum_eq_single j,one,mul_one] at z
  · exact nz z
  · intro t _ nt
    by_cases e : S.earlier i k t=0
    · rw [e,zero_mul]
    · have ht : t∈M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩
      have lt : t<j := lt_of_le_of_ne (Finset.le_max' M t ht) nt
      have prev : D (S.H t) a=0 := by
        funext x
        change S.H t (x+move S onto (j,0))-S.H t x=0
        rw [h_prev S onto j t 0 lt,sub_self]
      rw [prev,D_zero];simp
  · simp

theorem qadd {n} {f g : V n → F} (hf : Quad f) (hg : Quad g) :
    Quad (fun x => f x+g x) := by
  obtain ⟨s,h,M,he⟩ := hf
  obtain ⟨t,l,N,le⟩ := hg
  refine ⟨s+t,h+l,M+N,?_⟩
  intro x
  simp only [he,le,dotProduct,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring

theorem qzero (n : Nat) : Quad (fun _ : V n => (0:F)) := by
  exact ⟨0,0,0,by simp⟩

theorem qscale {n} {f : V n → F} (c : F) (hf : Quad f) :
    Quad (fun x => c*f x) := by
  obtain ⟨s,h,M,e⟩ := hf
  refine ⟨c*s,c • h,c • M,?_⟩
  intro x
  simp [e,dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_add,mul_assoc]

theorem qsum {n} {ι : Type*} [DecidableEq ι] (S : Finset ι) {f : ι → V n → F}
    (h : ∀ i∈S, Quad (f i)) : Quad (fun x => ∑ i∈S,f i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using qzero n
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact qadd (h i (by simp)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem qmul {n} (s t : F) (a b : V n) :
    Quad (fun x => (s+dotProduct a x)*(t+dotProduct b x)) := by
  refine ⟨s*t,s • b + t • a,fun i j => b i*a j,?_⟩
  intro x
  simp only [dotProduct, Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,mul_add,
    Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  simp only [mul_comm,mul_assoc,mul_left_comm]
  first | rfl | ring | simp only [Finset.sum_comm,add_assoc,add_left_comm,add_comm]

def Rest {n r} {g : V n → F} (S : Features g r) (i : Fin r) (x : V n) :=
  let a := dotProduct (S.A (i,0)) x
  let b := dotProduct (S.A (i,1)) x
  let c := dotProduct (S.A (i,2)) x
  S.start i 0*((S.start i 1+b)*(S.co i+c))+
    S.start i 1*(a*(S.co i+c))+S.co i*(a*b)

theorem quad_rest {n r} {g : V n → F} (S : Features g r) (i : Fin r) : Quad (Rest S i) := by
  have h := qadd (qadd (qscale (S.start i 0) (qmul (S.start i 1) (S.co i) (S.A (i,1)) (S.A (i,2))))
    (qscale (S.start i 1) (qmul 0 (S.co i) (S.A (i,0)) (S.A (i,2)))))
    (qscale (S.co i) (qmul 0 0 (S.A (i,0)) (S.A (i,1))))
  convert h using 1
  funext x
  simp only [Rest,zero_add]

def Splits {n} (g : V n → F) (c : Nat) := ∃ (A : Fin c × Fin 3 → V n) (q : V n → F),
    LinearIndependent F A ∧ Quad q ∧ ∀ x, g x=q x+∑ i, dotProduct (A (i,0)) x*dotProduct (A (i,1)) x*dotProduct (A (i,2)) x

theorem flatten {n r} {g : V n → F} (S : Features g r) (hg : Cubic g)
    (onto : Function.Surjective (featureMap S.A)) : Splits g r := by
  classical
  have zero := no_earlier S onto hg
  refine ⟨S.A,fun x => S.q x + ∑ i, Rest S i x,independent_of_surjective onto,
    qadd S.hq (qsum Finset.univ (fun i _ => quad_rest S i)),?_⟩
  intro x
  rw [S.out]
  have he (i : Fin r) : (S.co i+dotProduct (S.A (i,2)) x)*S.H i x =
    Rest S i x + dotProduct (S.A (i,0)) x*dotProduct (S.A (i,1)) x*dotProduct (S.A (i,2)) x := by
    rw [S.gate i x]
    simp only [zero,zero_mul,Finset.sum_const_zero,add_zero,Rest]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  ring

end PEqualNP.Outside.L_meta_30642_aux

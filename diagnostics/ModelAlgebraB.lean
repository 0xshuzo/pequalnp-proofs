import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_921
open scoped BigOperators
variable {κ ι : Type*} [Fintype κ] [Fintype ι]
private def ip (v x : κ → ℚ) : ℚ := ∑ r, v r*x r
private theorem ips (v x : κ → ℚ) : ip v x=ip x v := by simp only [ip,mul_comm]
private theorem ipa (v x y : κ → ℚ) : ip v (x+y)=ip v x+ip v y := by simp [ip,mul_add,Finset.sum_add_distrib]
private theorem ipd (v x y : κ → ℚ) : ip v (x-y)=ip v x-ip v y := by simp [ip,mul_sub,Finset.sum_sub_distrib]
private theorem ipm (v x : κ → ℚ) (c : ℚ) : ip v (c • x)=c*ip v x := by
  simp only [ip,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _; ring
private def ann (x : κ → ℚ) : Submodule ℚ (κ → ℚ) where
  carrier := {v | ip v x=0}
  zero_mem' := by simp [ip]
  add_mem' := by
    intro a b ha hb
    change ip a x=0 at ha
    change ip b x=0 at hb
    change ip (a+b) x=0
    rw [ips,ipa,ips x a,ips x b,ha,hb,add_zero]
  smul_mem' := by
    intro c v h
    change ip v x=0 at h
    change ip (c • v) x=0
    rw [ips,ipm,ips x v,h,mul_zero]
private theorem positive (x : κ → ℚ) (h : ip x x=0) : x=0 := by
  funext r
  have ge (k : κ) : 0≤x k*x k := mul_self_nonneg _
  have le : x r*x r ≤ ip x x := Finset.single_le_sum (fun k _ => ge k) (Finset.mem_univ r)
  rw [h] at le
  change x r=0
  nlinarith [ge r]
private theorem project (A : Finset (κ → ℚ)) (x : κ → ℚ) :
    ∃ y∈Submodule.span ℚ (A : Set (κ → ℚ)), ∀a∈A, ip a (x-y)=0 := by
  classical
  induction A using Finset.induction_on generalizing x with
  | empty => exact ⟨0,Submodule.zero_mem _,by simp⟩
  | @insert a S ha ih =>
    let K := Submodule.span ℚ (S : Set (κ → ℚ))
    let K' := Submodule.span ℚ ((insert a S : Finset (κ → ℚ)) : Set (κ → ℚ))
    have incl : K≤K' := Submodule.span_mono (by intro v hv; exact Finset.mem_insert_of_mem hv)
    have am : a∈K' := Submodule.subset_span (Finset.mem_insert_self _ _)
    obtain ⟨b,bm,hb⟩ := ih a
    obtain ⟨y,ym,hy⟩ := ih x
    let u := a-b
    have ku : K≤ann u := Submodule.span_le.mpr (by intro v hv; exact hb v hv)
    have ky : K≤ann (x-y) := Submodule.span_le.mpr (by intro v hv; exact hy v hv)
    have bu : ip b u=0 := ku bm
    have uu : ip u u=ip a u := by
      calc
        ip u u = ip u a-ip u b := ipd u a b
        _ = ip a u := by rw [ips u a,ips u b,bu,sub_zero]
    by_cases h : ip a u=0
    · have ab : a=b := sub_eq_zero.mp (positive u (uu.trans h))
      refine ⟨y,incl ym,?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vs
      · rw [ab]; exact ky bm
      · exact hy _ vs
    · let c := ip a (x-y)/ip a u
      refine ⟨y+c • u,K'.add_mem (incl ym) (K'.smul_mem _ (K'.sub_mem am (incl bm))),?_⟩
      intro v hv
      have e : x-(y+c • u)=(x-y)-c • u := by abel
      rw [e,ipd,ipm]
      rcases Finset.mem_insert.mp hv with rfl|vs
      · dsimp [c]; field_simp <;> ring
      · rw [hy _ vs,show ip v u=0 from hb _ vs,mul_zero,sub_self]
private def synth (B : ι → κ → ℚ) : (ι → ℚ) →ₗ[ℚ] (κ → ℚ) where
  toFun w r := ∑i,B i r*w i
  map_add' u v := by funext r; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c w := by
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
private theorem least (B : ι → κ → ℚ) :
    ∃w : ι → ℚ, ∀i, ∑ r,B i r*(∑j,B j r*w j)=∑r,B i r := by
  classical
  let S := Finset.univ.image B
  obtain ⟨y,hy,eq⟩ := project S (fun _ => 1)
  have sub : Submodule.span ℚ (S : Set (κ → ℚ))≤LinearMap.range (synth B) :=
    Submodule.span_le.mpr (by
      intro b hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      refine ⟨fun j => if j=i then 1 else 0,?_⟩
      funext r
      change (∑j,B j r*(if j=i then 1 else 0))=B i r
      simp [mul_ite])
  obtain ⟨w,rfl⟩ := sub hy
  refine ⟨w,fun i => ?_⟩
  have z := eq (B i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [ipd] at z
  have h : ip (B i) (fun _ => 1) = ∑r,B i r := by simp [ip]
  rw [h] at z
  exact (sub_eq_zero.mp z).symm
variable {κ ι : Type*} [Fintype κ] [Fintype ι]
private def load (B : ι → κ → ℚ) (w : ι → ℚ) (r : κ) := ∑i,B i r*w i
private def obj (x : κ → ℚ) : ℚ := ∑r,2*x r-x r*x r
private theorem mix (B : ι → κ → ℚ) (w : ι → ℚ) (y : κ → ℚ) :
    ip (load B w) y = ∑i,w i*ip (B i) y := by
  simp only [load,ip,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro r _; ring
private theorem drow (B : ι → κ → ℚ) (w : ι → ℚ) (i : ι) :
    ∑j,ip (B i) (B j)*w j=ip (B i) (load B w) := by
  rw [ips (B i) (load B w),mix]
  apply Finset.sum_congr rfl; intro j _; rw [ips (B i),mul_comm]
private theorem normalBest (B : ι → κ → ℚ) (w : ι → ℚ)
    (h : ∀ i,ip (B i) (load B w)=∑r,B i r) (v : ι → ℚ) :
    obj (load B v) ≤ obj (load B w) := by
  let y := load B w
  let x := load B v
  let one : κ → ℚ := fun _ => 1
  have ann' (u : ι → ℚ) : ip (load B u) (one-y)=0 := by
    rw [mix]
    apply Finset.sum_eq_zero
    intro i _
    rw [ipd,show ip (B i) one=∑r,B i r by simp [ip,one],show ip (B i) y=∑r,B i r from h i,sub_self,mul_zero]
  have cancel : ip (x-y) (one-y)=0 := by
    rw [ips,ipd,ips _ x,ips _ y,show ip x (one-y)=0 from ann' v,show ip y (one-y)=0 from ann' w,sub_self]
  have e : obj x-obj y=2*ip (x-y) (one-y)-∑r,(x r-y r)^2 := by
    simp only [obj,ip,←Finset.sum_sub_distrib,Finset.mul_sum,Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [one]
    ring
  have pos : 0≤∑r,(x r-y r)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change obj x≤obj y
  linarith
private theorem objForm (B : ι → κ → ℚ) (w : ι → ℚ)
    (bi : ∀i, ip (B i) (B i)=∑r,B i r) :
    (∑i,w i*(2*ip (B i) (B i)-∑j,ip (B i) (B j)*w j))=obj (load B w) := by
  let one : κ → ℚ := fun _ => 1
  have diag (i : ι) : ip (B i) (B i)=ip (B i) one := (bi i).trans (by simp [one,ip])
  simp only [diag,drow,mul_sub,Finset.sum_sub_distrib]
  have a : (∑i,w i*(2*ip (B i) one))=2*ip (load B w) one := by
    rw [mix,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [a,←mix]
  simp [obj,ip,one,Finset.sum_sub_distrib,Finset.mul_sum]
end PEqualNP.Outside.L_lib_921

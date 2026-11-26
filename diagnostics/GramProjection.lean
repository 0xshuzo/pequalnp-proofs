import PEqualNP.Defs
namespace Research9350.Mass
open Finset
abbrev V := Fin 21
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (r c : V) : Bool := !((board.getD r.val 0).testBit c.val)
def column (c r : V) : ℚ := if zeroCell r c then 1 else 0
def dual (c r : V) : ℚ := if zeroCell r c then 1 else -3
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem evaluate : ∀ i j : V, (∑ r : V, dual i r * column j r) =
    if i=j then 16 else 0 := by decide +kernel

def seed (j i : V) : ℚ := if j = i then 1 else 0
def u (r i : V) : ℚ := dual i r / 16 + 1/336
def v (c i : V) : ℚ := seed c i - 1/42
def dot (f g : V → ℚ) := ∑ i : V, f i * g i
def energy (f : V → ℚ) := ∑ i : V, (f i)^2
def space := V → ℚ
abbrev Operator := (V → ℚ) →ₗ[ℚ] (V → ℚ)

theorem dot_comm (f g : V → ℚ) : dot f g = dot g f :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _
theorem dot_sub_left (f g h : V → ℚ) : dot (f-g) h = dot f h - dot g h := by
  simp only [dot,Pi.sub_apply,sub_mul,sum_sub_distrib]
theorem dot_scale_left (a : ℚ) (f g : V → ℚ) : dot (a • f) g = a * dot f g := by
  simp only [dot,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_sum]
theorem dot_sub_right (f g h : V → ℚ) : dot f (g-h) = dot f g - dot f h := by
  rw [dot_comm,dot_sub_left,dot_comm g f,dot_comm h f]
theorem dot_scale_right (f : V → ℚ) (a : ℚ) (g : V → ℚ) : dot f (a • g) = a * dot f g := by
  rw [dot_comm,dot_scale_left,dot_comm]
theorem dot_seed (i : V) (f : V → ℚ) : dot (seed i) f = f i := by
  simp [dot,seed,ite_mul]
theorem norm_pos {f : V → ℚ} (nz : f ≠ 0) : 0 < dot f f := by
  have ex : ∃ i, f i ≠ 0 := by
    by_contra! no
    exact nz (funext no)
  obtain ⟨i,hi⟩ := ex
  have small := Finset.single_le_sum (s := (univ : Finset V))
    (f := fun j => f j * f j) (fun j _ => mul_self_nonneg (f j)) (mem_univ i)
  exact lt_of_lt_of_le (mul_self_pos.mpr hi) small

def gram (P : Operator) := ∀ f g, dot (P f) (P g) = dot f (P g)
def traceQ (P : Operator) := ∑ i : V, P (seed i) i

def subtractMode (P : Operator) (z : V → ℚ) : Operator where
  toFun := fun f => P f - (dot f z / dot z z) • z
  map_add' f g := by
    have eq : dot (f+g) z = dot f z + dot g z := by
      simp only [dot,Pi.add_apply,add_mul,sum_add_distrib]
    rw [map_add,eq,add_div,add_smul]
    abel
  map_smul' a f := by
    simp only [map_smul,dot_scale_left,smul_sub,smul_smul,RingHom.id_apply]
    congr 2
    ring

theorem gsOne (P : Operator) (hp : gram P) (w : V → ℚ) :
    ∃ Q : Operator, gram Q ∧ Q w = 0 ∧ (∀ f, P f = 0 → Q f = 0) ∧
      traceQ P - 1 ≤ traceQ Q := by
  classical
  by_cases hz : P w = 0
  · exact ⟨P,hp,hz,fun _ h => h,by linarith⟩
  let z := P w
  have nd : dot z z ≠ 0 := (norm_pos hz).ne'
  let Q := subtractMode P z
  have form (f : V → ℚ) : Q f = P f - (dot f z / dot z z) • z := rfl
  have proj (f : V → ℚ) : dot (P f) z = dot f z := hp f w
  have wp : dot w z = dot z z := (hp w w).symm
  refine ⟨Q,?_,?_,?_,?_⟩
  · intro f g
    rw [form f,form g,dot_sub_left,dot_scale_left]
    simp only [dot_sub_right,dot_scale_right]
    rw [hp f g,proj f,dot_comm z (P g),proj g]
    field_simp
    <;> ring
  · rw [form,wp,div_self nd,one_smul]
    exact sub_self z
  · intro f hf
    have zero : dot f z = 0 := by rw [← proj,hf]; simp [dot]
    rw [form,hf,zero,zero_div,zero_smul,sub_zero]
  · have tr : traceQ Q = traceQ P - 1 := by
      unfold traceQ
      simp only [form,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,dot_seed,sum_sub_distrib]
      have eq : (∑ i : V, z i / dot z z * z i) = 1 := by
        calc
          _ = (∑ i : V, z i * z i) / dot z z := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => by ring
          _ = 1 := div_self nd
      rw [eq]
    exact tr.ge

theorem gsList (W : List (V → ℚ)) : ∃ P : Operator, gram P ∧
    (∀ w ∈ W, P w = 0) ∧ 21 - (W.length : ℚ) ≤ traceQ P := by
  induction W with
  | nil =>
    refine ⟨LinearMap.id,fun _ _ => rfl,by simp,?_⟩
    have h : traceQ LinearMap.id = 21 := by decide +kernel
    simpa using h.ge
  | cons w W ih =>
    obtain ⟨P,hp,hkill,htrace⟩ := ih
    obtain ⟨Q,hq,hqw,keep,ht⟩ := gsOne P hp w
    refine ⟨Q,hq,?_,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hqw
      · exact keep _ (hkill _ hz)
    · simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith

end Research9350.Mass

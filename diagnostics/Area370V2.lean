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
theorem energy_exact : ∀ r c : V, zeroCell r c = true →
    (∑ i : V, (2*u r i-v c i)^2) = (187/112 : ℚ) := by decide +kernel

theorem energy_nonneg (f : V → ℚ) : 0 ≤ energy f :=
  Finset.sum_nonneg fun i _ => sq_nonneg (f i)

theorem contraction (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g)) (f : V → ℚ) :
    energy (P f) ≤ energy f := by
  have eq : energy (P f) = dot f (P f) := by
    simpa only [energy,dot,pow_two] using orth f f
  have split : energy (f - P f) = energy f + energy (P f) - 2 * dot f (P f) := by
    unfold energy dot
    simp only [Pi.sub_apply,mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have pos := energy_nonneg (f-P f)
  linarith

theorem cell_bound (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g))
    (r c : V) (h : zeroCell r c = true) :
    -(187/896 : ℚ) ≤ dot (v c) (P (u r)) := by
  let a := u r
  let b := v c
  have lower := contraction P orth ((2:ℚ) • a - b)
  have disc : energy ((2:ℚ) • a - b) = 187/112 := by
    simpa [energy,a,b] using energy_exact r c h
  have plus := energy_nonneg (P ((2:ℚ) • a + b))
  have split : energy (P ((2:ℚ) • a + b)) - energy (P ((2:ℚ) • a - b)) =
      8 * dot (P b) (P a) := by
    simp only [map_add,map_sub,map_smul,energy,dot,Pi.add_apply,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [orth] at split
  change -(187/896 : ℚ) ≤ dot b (P a)
  linarith

-- The linear map is a rational orthogonal projection onto a left kernel.
-- Its trace is the dimension of the space it fixes. The hypotheses record
-- those two linear-algebra facts explicitly.
theorem excess34 (D : V → V → Nat) (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (supp : ∀ r c, zeroCell r c = false → D r c = 0)
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g))
    (large : 7 ≤ ∑ i : V, P (seed i) i)
    (ann : ∀ i : V, P (seed i + ∑ r : V, ∑ c : V, ((D r c : ℚ) * v c i) • u r) = 0) :
    34 ≤ ∑ r : V, ∑ c : V, D r c := by
  have eq (i : V) : P (seed i) i +
      (∑ r : V, ∑ c : V, (D r c : ℚ) * (v c i * P (u r) i)) = 0 := by
    have e := congrFun (ann i) i
    simpa only [map_add,map_sum,map_smul,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,mul_assoc,Pi.zero_apply] using e
  have traceEq : (∑ i : V, P (seed i) i) +
      ∑ r : V, ∑ c : V, (D r c : ℚ) * dot (v c) (P (u r)) = 0 := by
    have es : (∑ i : V, P (seed i) i) +
        (∑ i : V, ∑ r : V, ∑ c : V, (D r c : ℚ) * (v c i * P (u r) i)) = 0 := by
      rw [← sum_add_distrib]
      simp [eq]
    convert es using 2
    unfold dot
    simp only [mul_sum]
    calc
      _ = ∑ r : V, ∑ i : V, ∑ c : V, (D r c : ℚ) * (v c i * P (u r) i) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have term (r c : V) : (D r c : ℚ) * (-(187/896 : ℚ)) ≤
      (D r c : ℚ) * dot (v c) (P (u r)) := by
    cases z : zeroCell r c with
    | false => simp [supp r c z]
    | true => exact mul_le_mul_of_nonneg_left (cell_bound P orth r c z) (by positivity)
  have total := sum_le_sum (s := (univ : Finset V)) fun r _ =>
    sum_le_sum (s := (univ : Finset V)) fun c _ => term r c
  simp only [← sum_mul] at total
  by_contra! low
  have weak : ∑ r : V, ∑ c : V, D r c ≤ 33 := by omega
  have small : (∑ r : V, ∑ c : V, (D r c : ℚ)) ≤ 33 := by exact_mod_cast weak
  linarith

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
            simp only [div_eq_mul_inv, Finset.sum_mul]
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

abbrev Box := Finset V × Finset V
def mark (A : Finset V) (r : V) : ℚ := if r ∈ A then 1 else 0
def zq (r c : V) : ℚ := if zeroCell r c then 1 else 0
def rowVec (b : Box) : V → ℚ := ∑ r : V, mark b.1 r • u r
def colScalar (b : Box) (i : V) := ∑ c : V, mark b.2 c * v c i
def actual {m : ℕ} (B : Fin m → Box) (r c : V) := ∑ j : Fin m, mark (B j).1 r * mark (B j).2 c

theorem frame : ∀ (i k : V), (∑ r : V, (∑ c : V, zq r c * v c i) * u r k) =
    seed i k := by decide +kernel

theorem frameVec (i : V) : seed i = ∑ r : V, ∑ c : V, (zq r c * v c i) • u r := by
  funext k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simpa only [Finset.sum_mul] using (frame i k).symm

theorem rotateSums {m : Nat} (f : V → V → Fin m → ℚ) :
    (∑ r : V, ∑ c : V, ∑ b : Fin m, f r c b) =
    ∑ b : Fin m, ∑ c : V, ∑ r : V, f r c b := by
  calc
    _ = ∑ r : V, ∑ b : Fin m, ∑ c : V, f r c b :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b : Fin m, ∑ r : V, ∑ c : V, f r c b := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem factorization {m : ℕ} (B : Fin m → Box) (i : V) :
    (∑ r : V, ∑ c : V, (actual B r c * v c i) • u r) =
    ∑ b : Fin m, colScalar (B b) i • rowVec (B b) := by
  funext k
  simp only [actual,colScalar,rowVec,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum]
  rw [rotateSums]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem representedMass {m : ℕ} (B : Fin m → Box) (bound : m ≤ 14) (D : V → V → Nat)
    (supp : ∀ r c, zeroCell r c = false → D r c = 0)
    (counts : ∀ r c, zq r c + (D r c : ℚ) = actual B r c) :
    34 ≤ ∑ r : V, ∑ c : V, D r c := by
  obtain ⟨P,orth,kill,trace⟩ := gsList (List.ofFn fun b : Fin m => rowVec (B b))
  apply excess34 D P supp orth
  · have lb : (m : ℚ) ≤ 14 := by exact_mod_cast bound
    simp only [List.length_ofFn] at trace
    unfold traceQ at trace
    linarith
  · intro i
    have split : seed i + (∑ r : V, ∑ c : V, ((D r c : ℚ) * v c i) • u r) =
        ∑ r : V, ∑ c : V, (actual B r c * v c i) • u r := by
      rw [frameVec i,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      rw [← add_smul,← add_mul,counts]
    rw [split,factorization,map_sum]
    apply Finset.sum_eq_zero
    intro b _
    have h : rowVec (B b) ∈ List.ofFn (fun j : Fin m => rowVec (B j)) := by
      exact List.mem_ofFn.mpr ⟨b,rfl⟩
    rw [map_smul,kill _ h,smul_zero]

def once (b : Box) (r c : V) : ℕ := if r ∈ b.1 ∧ c ∈ b.2 then 1 else 0
def tally {m : Nat} (B : Fin m → Box) (r c : V) : Nat := ∑ b : Fin m, once (B b) r c
def required (r c : V) : Nat := if zeroCell r c then 1 else 0

theorem tally_val {m : Nat} (B : Fin m → Box) (r c : V) :
    (tally B r c : ℚ) = actual B r c := by
  unfold tally actual
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  by_cases hr : r ∈ (B b).1 <;> by_cases hc : c ∈ (B b).2 <;>
    simp [once,mark,hr,hc]

theorem area370 (L : List Box) (small : L.length ≤ 14)
    (law : ∀ b ∈ L, ∀ r ∈ b.1, ∀ c ∈ b.2, zeroCell r c = true)
    (hits : ∀ r c, zeroCell r c = true → ∃ b ∈ L, r ∈ b.1 ∧ c ∈ b.2) :
    370 ≤ ∑ r : V, ∑ c : V, tally L.get r c := by
  classical
  let D (r c : V) := tally L.get r c - required r c
  have valid (r c : V) : required r c ≤ tally L.get r c := by
    cases z : zeroCell r c with
    | false => simp [required,z]
    | true =>
      obtain ⟨b,hb,hr,hc⟩ := hits r c z
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
      have le := Finset.single_le_sum (s := (Finset.univ : Finset (Fin L.length)))
        (f := fun j => once (L.get j) r c) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      change required r c ≤ ∑ j : Fin L.length, once (L.get j) r c
      rw [show required r c = 1 by simp [required,z]]
      have src : once (L.get i) r c = 1 := by simp [once,hi,hr,hc]
      rw [src] at le
      exact le
  have sumcell (r c : V) : required r c + D r c = tally L.get r c := by
    dsimp [D]
    have := valid r c
    omega
  have isolated (r c : V) (h : zeroCell r c = false) : D r c = 0 := by
    have eq : tally L.get r c = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have nd : ¬ (r∈(L.get b).1 ∧ c∈(L.get b).2) := by
        intro ⟨hr,hc⟩
        have f := law _ (List.get_mem L b) _ hr _ hc
        simp [h] at f
      simp [once,nd]
    simp [D,eq]
  have want := representedMass L.get small D isolated (fun r c => by
    rw [← tally_val]
    have z : (required r c : ℚ) = zq r c := by
      cases e : zeroCell r c <;> simp [required,zq,e]
    rw [← z]
    exact_mod_cast sumcell r c)
  have tot : (∑ r : V, ∑ c : V, required r c) = 336 := by decide +kernel
  have decomp : (∑ r : V, ∑ c : V, tally L.get r c) =
      (∑ r : V, ∑ c : V, required r c) + (∑ r : V, ∑ c : V, D r c) := by
    simp_rw [← sumcell]
    simp only [Finset.sum_add_distrib]
  omega

end Research9350.Mass

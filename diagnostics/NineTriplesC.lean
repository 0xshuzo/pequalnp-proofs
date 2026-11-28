import PEqualNP.Defs
namespace Research9341.Mass
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
theorem excess39 (D : V → V → Nat) (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (supp : ∀ r c, zeroCell r c = false → D r c = 0)
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g))
    (large : 8 ≤ ∑ i : V, P (seed i) i)
    (ann : ∀ i : V, P (seed i + ∑ r : V, ∑ c : V, ((D r c : ℚ) * v c i) • u r) = 0) :
    39 ≤ ∑ r : V, ∑ c : V, D r c := by
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
  have weak : ∑ r : V, ∑ c : V, D r c ≤ 38 := by omega
  have small : (∑ r : V, ∑ c : V, (D r c : ℚ)) ≤ 38 := by exact_mod_cast weak
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
    ∑ b : Fin m, ∑ r : V, ∑ c : V, f r c b := by
  calc
    _ = ∑ r : V, ∑ b : Fin m, ∑ c : V, f r c b :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

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

theorem representedMass {m : ℕ} (B : Fin m → Box) (bound : m ≤ 13) (D : V → V → Nat)
    (supp : ∀ r c, zeroCell r c = false → D r c = 0)
    (counts : ∀ r c, zq r c + (D r c : ℚ) = actual B r c) :
    39 ≤ ∑ r : V, ∑ c : V, D r c := by
  obtain ⟨P,orth,kill,trace⟩ := gsList (List.ofFn fun b : Fin m => rowVec (B b))
  apply excess39 D P supp orth
  · have lb : (m : ℚ) ≤ 13 := by exact_mod_cast bound
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

theorem area375 (L : List Box) (small : L.length ≤ 13)
    (law : ∀ b ∈ L, ∀ r ∈ b.1, ∀ c ∈ b.2, zeroCell r c = true)
    (hits : ∀ r c, zeroCell r c = true → ∃ b ∈ L, r ∈ b.1 ∧ c ∈ b.2) :
    375 ≤ ∑ r : V, ∑ c : V, tally L.get r c := by
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
      have src : once (L.get i) r c = 1 := by unfold once; rw [hi]; exact if_pos ⟨hr,hc⟩
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
      exact if_neg nd
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

end Research9341.Mass

namespace Research9341.Mass
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

def totalVec {m : Nat} (B : Fin m → Box) (i : V) : V → ℚ :=
  ∑ b : Fin m, colScalar (B b) i • rowVec (B b)

theorem singleFee (P : Operator) (hp : gram P) (x : V → ℚ) (i : V)
    (kill : P x = 0) (t : ℚ) :
    2*t*x i - t^2*(1-P (seed i) i) ≤ energy x := by
  let w := seed i-P (seed i)
  have self : dot w w = 1-P (seed i) i := by
    dsimp [w]
    rw [dot_sub_left,dot_sub_right,dot_sub_right,hp,dot_seed,dot_seed,
      dot_comm (P (seed i)) (seed i),dot_seed]
    simp [seed]
  have vanish : dot x (P (seed i)) = 0 := by
    rw [← hp,kill]; simp [dot]
  have cross : dot x w = x i := by
    dsimp [w]
    rw [dot_sub_right,vanish,sub_zero,dot_comm,dot_seed]
  have eq : energy (x - t • w) = energy x - 2*t*dot x w + t^2*dot w w := by
    simp only [energy,dot,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sum,
      ← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have pos := energy_nonneg (x - t • w)
  rw [eq,cross,self] at pos
  linarith

theorem physicalFee {m : Nat} (B : Fin m → Box) (t : ℚ) :
    2*t*(∑ i : V, totalVec B i i) - t^2*m ≤ ∑ i : V, energy (totalVec B i) := by
  obtain ⟨P,orth,kill,trace⟩ := gsList (List.ofFn fun b : Fin m => rowVec (B b))
  have ann (i : V) : P (totalVec B i) = 0 := by
    simp only [totalVec,map_sum,map_smul]
    apply Finset.sum_eq_zero
    intro b _
    have h : rowVec (B b) ∈ List.ofFn (fun j : Fin m => rowVec (B j)) :=
      List.mem_ofFn.mpr ⟨b,rfl⟩
    rw [kill _ h,smul_zero]
  have hs := sum_le_sum (s := (univ : Finset V)) fun i _ =>
    singleFee P orth (totalVec B i) i (ann i) t
  simp only [sum_sub_distrib, ← mul_sum, sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hs
  simp only [List.length_ofFn, traceQ] at trace
  have rem : (21:ℚ) - (∑ i : V, P (seed i) i) ≤ m := by linarith
  have price := mul_le_mul_of_nonneg_left rem (sq_nonneg t)
  change 2*t*(∑ i : V, totalVec B i i) - t^2*(21-(∑ i : V, P (seed i) i)) ≤ _ at hs
  exact (sub_le_sub_left price _).trans hs

theorem cutoff13 (e q tr norm : ℚ) (trace : tr = 21 + e/16)
    (upper : norm ≤ 21 + e/8 + q/4 - e^2/1792)
    (lower : 2*(21/10)*tr - (21/10)^2*13 ≤ norm) :
    84/5 ≤ q - e := by
  rw [trace] at lower
  nlinarith [sq_nonneg (e-504/5)]

theorem cutoff14 (e q tr norm : ℚ) (trace : tr = 21 + e/16)
    (upper : norm ≤ 21 + e/8 + q/4 - e^2/1792) (thin : q ≤ e)
    (lower : 2*2*tr - 2^2*14 ≤ norm) : e = 112 := by
  rw [trace] at lower
  nlinarith [sq_nonneg (e-112)]

end Research9341.Mass
namespace Research9341.Mass
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem gramU : ∀ r s : V, dot (u r) (u s) =
    (if r=s then (1/4 : ℚ) else 0)-5/448 := by decide +kernel
theorem gramV : ∀ c d : V, dot (v c) (v d) =
    (if c=d then (1 : ℚ) else 0)-1/28 := by decide +kernel
theorem crossUV : ∀ r c : V, zeroCell r c = true → dot (u r) (v c) = 1/16 := by
  decide +kernel

def mix (W : V → V → ℚ) (a : V → ℚ) : V → ℚ := ∑ r : V, a r • W r

theorem dotMix (W : V → V → ℚ) (a f : V → ℚ) :
    dot (mix W a) f = ∑ r : V, a r * dot (W r) f := by
  simp only [dot,mix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul,
    Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem mixEnergy (W : V → V → ℚ) (a : V → ℚ) (d k : ℚ)
    (g : ∀ r s, dot (W r) (W s) = (if r=s then d else 0)-k) :
    energy (mix W a) = d*energy a - k*(∑ r : V, a r)^2 := by
  have coord (r : V) : dot (W r) (mix W a) = a r*d-(∑ s : V, a s)*k := by
    rw [dot_comm,dotMix]
    simp only [g,mul_sub,mul_ite,mul_zero,Finset.sum_sub_distrib,← Finset.sum_mul]
    simp
  change (∑ i : V, (mix W a i)^2) = _
  simp only [pow_two]
  change dot (mix W a) (mix W a) = _
  rw [dotMix]
  simp only [coord,mul_sub,sum_sub_distrib,← sum_mul]
  have first : (∑ r : V, a r * (a r * d)) = d * energy a := by
    simp only [energy,Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [first]
  ring

def massQ (D : V → V → ℚ) := ∑ r : V, ∑ c : V, D r c
def normQ (D : V → V → ℚ) := ∑ r : V, energy (D r)
def byCol (D : V → V → ℚ) (c : V) := ∑ r : V, D r c
def byRow (D : V → V → ℚ) (r : V) := ∑ c : V, D r c
def colMix (D : V → V → ℚ) (i r : V) := mix v (D r) i
def perturb (D : V → V → ℚ) (i : V) := mix u (colMix D i)

theorem colTotal (D : V → V → ℚ) (i : V) :
    (∑ r : V, colMix D i r) = mix v (byCol D) i := by
  simp only [colMix,mix,byCol,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem normMoment (D : V → V → ℚ) :
    (∑ i : V, energy (perturb D i)) =
      normQ D/4 - energy (byRow D)/112 - 5*energy (byCol D)/448
       + 5*(massQ D)^2/12544 := by
  have inner (i : V) := mixEnergy u (colMix D i) _ _ gramU
  have each (r : V) := mixEnergy v (D r) _ _ gramV
  have outer := mixEnergy v (byCol D) _ _ gramV
  have sums : (∑ i : V, byCol D i) = massQ D := Finset.sum_comm
  rw [sums] at outer
  have swapped : (∑ i : V, energy (colMix D i)) = ∑ r : V, energy (mix v (D r)) := by
    simp only [energy,colMix]
    exact Finset.sum_comm
  have rowEnergy : (∑ r : V, (∑ c : V, D r c)^2) = energy (byRow D) := rfl
  simp only [perturb,inner,colTotal,sum_sub_distrib,← mul_sum,swapped,each,one_mul,rowEnergy]
  change _ - _ * energy (mix v (byCol D)) = _
  rw [outer]
  unfold normQ
  ring

theorem meanSq (a : V → ℚ) : (∑ r : V, a r)^2/21 ≤ energy a := by
  let e := ∑ r : V, a r
  have term (i : V) : (a i-e/21)^2 = (a i)^2 - (2*e/21)*a i + (e/21)^2 := by ring
  have pos := Finset.sum_nonneg (s := (univ : Finset V)) fun i _ => sq_nonneg (a i-e/21)
  simp only [term,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at pos
  change 0 ≤ energy a - 2*e/21*e + 21*(e/21)^2 at pos
  change e^2/21 ≤ energy a
  linarith only [show 0 ≤ energy a - e^2/21 by nlinarith only [pos]]

theorem upperMoment (D : V → V → ℚ) :
    (∑ i : V, energy (perturb D i)) ≤ normQ D/4 - (massQ D)^2/1792 := by
  have r := meanSq (byRow D)
  have c := meanSq (byCol D)
  change (massQ D)^2/21 ≤ energy (byRow D) at r
  rw [show (∑ i : V, byCol D i) = massQ D from Finset.sum_comm] at c
  rw [normMoment]
  linarith

end Research9341.Mass
namespace Research9341.Mass
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem perturbEntry (D : V → V → ℚ) (i k : V) :
    perturb D i k = ∑ r : V, ∑ c : V, D r c*(v c i * u r k) := by
  simp only [perturb,colMix,mix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul,mul_assoc]

theorem diagMoment (D : V → V → ℚ) (supp : ∀ r c, zeroCell r c=false → D r c=0) :
    (∑ i : V, perturb D i i) = massQ D/16 := by
  have cell (r c : V) : (∑ i : V, D r c*(v c i*u r i)) = D r c/16 := by
    rw [← Finset.mul_sum]
    change D r c * dot (v c) (u r) = _
    rw [dot_comm]
    cases h : zeroCell r c with
    | false => simp [supp r c h]
    | true => rw [crossUV r c h]; ring
  simp only [perturbEntry]
  rw [← rotateSums (fun r c (i : V) => D r c*(v c i * u r i))]
  simp only [cell, massQ, div_eq_mul_inv, Finset.sum_mul]

theorem squareSeed (x : V → ℚ) (i : V) :
    energy (seed i+x) = 1+2*x i+energy x := by
  have eq : energy (seed i+x) = energy (seed i)+2*dot (seed i) x+energy x := by
    simp only [energy,dot,Pi.add_apply,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have one : energy (seed i)=1 := by simp [energy,seed,ite_pow]
  rw [eq,one,dot_seed]

theorem splitPhysical {m : Nat} (B : Fin m → Box) (D : V → V → ℚ)
    (counts : ∀ r c, zq r c + D r c = actual B r c) (i : V) :
    totalVec B i = seed i + perturb D i := by
  unfold totalVec
  rw [← factorization,frameVec]
  funext k
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,perturbEntry]
  simp only [← counts,add_mul,Finset.sum_add_distrib,mul_assoc]

theorem excessPairs {m : Nat} (B : Fin m → Box) (small : m ≤ 13) (D : V → V → ℚ)
    (counts : ∀ r c, zq r c + D r c = actual B r c)
    (supp : ∀ r c, zeroCell r c=false → D r c=0) :
    84/5 ≤ normQ D - massQ D := by
  have fee := physicalFee B (21/10)
  have diag := diagMoment D supp
  have top := upperMoment D
  have tr : (∑ i : V, totalVec B i i) = 21+massQ D/16 := by
    simp only [splitPhysical B D counts,Pi.add_apply,seed,if_pos rfl,sum_add_distrib,diag]
    norm_num
  have en : (∑ i : V, energy (totalVec B i)) =
    21+massQ D/8+∑ i : V, energy (perturb D i) := by
    simp only [splitPhysical B D counts,squareSeed,sum_add_distrib,← mul_sum,diag]
    norm_num
    <;> ring
  apply cutoff13 (massQ D) (normQ D) (∑ i : V, totalVec B i i) (∑ i : V, energy (totalVec B i)) tr
  · rw [en]
    linarith
  · have smallQ : (m : ℚ) ≤ 13 := by exact_mod_cast small
    linarith

theorem physicalMoment (L : List Box) (small : L.length ≤ 13)
    (law : ∀ b ∈ L, ∀ r ∈ b.1, ∀ c ∈ b.2, zeroCell r c = true)
    (hits : ∀ r c, zeroCell r c = true → ∃ b ∈ L, r ∈ b.1 ∧ c ∈ b.2) :
    let D (r c : V) : ℚ := ((tally L.get r c - required r c : ℕ) : ℚ)
    84/5 ≤ normQ D - massQ D := by
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
      have src : once (L.get i) r c = 1 := by unfold once; rw [hi]; exact if_pos ⟨hr,hc⟩
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
      exact if_neg nd
    simp [D,eq]
  have want := excessPairs L.get small (fun r c => (D r c : ℚ)) (fun r c => by
    rw [← tally_val]
    have z : (required r c : ℚ) = zq r c := by
      cases e : zeroCell r c <;> simp [required,zq,e]
    rw [← z]
    exact_mod_cast sumcell r c) (fun r c h => by simp [isolated r c h])
  exact want

end Research9341.Mass
namespace Research9341.Mass
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

theorem chooseCut : ∀ n : Fin 14,
    let d : ℚ := ((n.val-1 : Nat) : ℚ)
    d^2-d ≤ 2*(n.val.choose 3 : ℚ) := by decide +kernel

theorem nineTriples (L : List Box) (small : L.length ≤ 13)
    (law : ∀ b ∈ L, ∀ r ∈ b.1, ∀ c ∈ b.2, zeroCell r c = true)
    (hits : ∀ r c, zeroCell r c = true → ∃ b ∈ L, r ∈ b.1 ∧ c ∈ b.2) :
    9 ≤ ∑ r : V, ∑ c : V, (tally L.get r c).choose 3 := by
  let D (r c : V) : ℚ := ((tally L.get r c - required r c : Nat) : ℚ)
  have lower : 84/5 ≤ normQ D-massQ D := physicalMoment L small law hits
  have point (r c : V) : (D r c)^2-D r c ≤ 2*((tally L.get r c).choose 3 : ℚ) := by
    have cap : tally L.get r c ≤ L.length := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L.length)))
        (fun i _ => show once (L.get i) r c ≤ 1 by unfold once; split <;> decide)
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
      change (∑ i : Fin L.length, once (L.get i) r c) ≤ L.length at h
      exact h
    cases hc : zeroCell r c with
    | true =>
      have h := chooseCut ⟨tally L.get r c,by omega⟩
      simpa [D,required,hc] using h
    | false =>
      have z : tally L.get r c = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        apply if_neg
        intro ⟨h,j⟩
        have wrong := law _ (List.get_mem L b) _ h _ j
        simp [hc] at wrong
      simp [D,z]
  have le := Finset.sum_le_sum (s := (Finset.univ : Finset V)) fun r _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset V)) fun c _ => point r c
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at le
  change normQ D-massQ D ≤ 2*(∑ r : V, ∑ c : V, ((tally L.get r c).choose 3 : ℚ)) at le
  by_contra! low
  have h : (∑ r : V, ∑ c : V, (tally L.get r c).choose 3) ≤ 8 := by omega
  have hh : (∑ r : V, ∑ c : V, ((tally L.get r c).choose 3 : ℚ)) ≤ 8 := by
    exact_mod_cast h
  linarith
end Research9341.Mass

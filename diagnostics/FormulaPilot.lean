import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3005.Rectangle

def seeds : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]

def triples : List (Fin 21 × Fin 21 × Fin 21) := [(0, 1, 2), (3, 4, 5), (6, 7, 8), (9, 10, 11), (12, 13, 14), (15, 16, 17), (18, 19, 20), (0, 3, 9), (1, 6, 18), (4, 15, 19), (2, 12, 16), (10, 13, 20), (7, 11, 17), (5, 8, 14)]

def weights : List (List Int) := [
  [0, 0, 0, 8, 0, 2, -1, 0, 8, -8, -1, 0, 2, -1, 2, -1, 0, 0, 2, -1, 2, 0, -1, 8, 0, 0, 2, -1, 8, -1, 0, 2, 0, 2, 0, 0, 0],
  [0, 0, 0, 8, 0, -1, 2, 0, -8, 8, -1, 0, -1, 2, 8, -1, 0, 0, -1, 2, 2, 0, -1, 2, 0, 0, -1, 2, 2, -1, 0, 2, 0, 8, 0, 0, 0],
  [0, 0, 0, -8, 0, -1, -1, 0, 8, 8, 2, 0, -1, -1, 2, 2, 0, 0, -1, -1, 8, 0, 2, 2, 0, 0, -1, -1, 2, 2, 0, 8, 0, 2, 0, 0, 0],
  [0, 0, 0, 2, 0, 8, -1, 0, 2, 8, -1, 0, 2, 2, -1, 2, 0, 0, 2, 2, -1, 0, 2, 8, 0, 0, 8, -1, -8, -1, 0, -1, 0, -1, 0, 0, 0],
  [0, 0, 0, -1, 0, 8, 2, 0, -1, 2, 2, 0, -1, 8, 2, 2, 0, 0, -1, 2, 2, 0, 8, 2, 0, 0, -8, -1, 8, -1, 0, -1, 0, -1, 0, 0, 0],
  [0, 0, 0, -1, 0, -8, -1, 0, -1, 2, -1, 0, -1, 2, -1, 8, 0, 0, -1, 8, -1, 0, 2, 2, 0, 0, 8, 2, 8, 2, 0, 2, 0, 2, 0, 0, 0],
  [0, 0, 0, 2, 0, 2, 2, 0, 8, 2, 2, 0, 2, 2, 8, 2, 0, 0, -1, 8, -1, 0, -1, -1, 0, 0, -1, 8, -1, -1, 0, -1, 0, -8, 0, 0, 0],
  [0, 0, 0, -1, 0, 2, -1, 0, 2, -1, 8, 0, 8, -1, 2, 2, 0, 0, 2, 8, 2, 0, 2, 2, 0, 0, -1, -8, -1, -1, 0, -1, 0, 8, 0, 0, 0],
  [0, 0, 0, -1, 0, 8, -1, 0, 2, -1, 2, 0, 2, -1, 2, 8, 0, 0, -1, -8, -1, 0, -1, -1, 0, 0, 2, 8, 2, 2, 0, 2, 0, 8, 0, 0, 0],
  [0, 0, 0, 2, 0, 2, 2, 0, 2, 8, 2, 0, 8, -1, -1, -1, 0, 0, 8, -1, -1, 0, -1, -8, 0, 0, 2, 2, 8, 2, 0, -1, 0, -1, 0, 0, 0],
  [0, 0, 0, -1, 0, -1, 8, 0, -1, 2, 2, 0, 8, 2, 2, 2, 0, 0, -8, -1, -1, 0, -1, 8, 0, 0, -1, 2, 2, 8, 0, 2, 0, -1, 0, 0, 0],
  [0, 0, 0, -1, 0, -1, 2, 0, -1, 2, 8, 0, -8, -1, -1, -1, 0, 0, 8, 2, 2, 0, 2, 8, 0, 0, -1, 8, 2, 2, 0, -1, 0, 2, 0, 0, 0],
  [0, 0, 0, 8, 0, 2, 2, 0, 2, 2, 2, 0, -1, -1, -1, 8, 0, 0, 2, 2, 8, 0, 2, -1, 0, 0, -1, -1, -1, 8, 0, -8, 0, -1, 0, 0, 0],
  [0, 0, 0, 2, 0, 2, 8, 0, -1, -1, -1, 0, 2, 2, 2, 8, 0, 0, 8, 2, 2, 0, -1, 2, 0, 0, -1, -1, -1, -8, 0, 8, 0, -1, 0, 0, 0],
  [0, 0, 0, 2, 0, 8, 2, 0, -1, -1, -1, 0, -1, -1, -1, -8, 0, 0, 2, 8, 2, 0, -1, -1, 0, 0, 2, 2, 2, 8, 0, 8, 0, 2, 0, 0, 0],
  [0, 0, 0, 2, 0, 2, 2, 0, -1, -1, 8, 0, 2, 8, 2, -1, 0, 0, -1, -1, 8, 0, -8, -1, 0, 0, 8, 2, 2, -1, 0, 2, 0, -1, 0, 0, 0],
  [0, 0, 0, 8, 0, -1, -1, 0, 2, 2, 8, 0, 2, 2, -1, 2, 0, 0, -1, -1, -8, 0, 8, -1, 0, 0, 2, 2, -1, 2, 0, 8, 0, -1, 0, 0, 0],
  [0, 0, 0, 2, 0, -1, -1, 0, -1, -1, -8, 0, 8, 2, -1, -1, 0, 0, 2, 2, 8, 0, 8, 2, 0, 0, 2, 8, -1, -1, 0, 2, 0, 2, 0, 0, 0],
  [0, 0, 0, 2, 0, -1, 8, 0, 8, 2, -1, 0, -1, 8, -8, -1, 0, 0, 2, 2, -1, 0, 2, -1, 0, 0, 2, 2, -1, 2, 0, -1, 0, 8, 0, 0, 0],
  [0, 0, 0, -1, 0, 2, 8, 0, 2, -1, 2, 0, -1, -8, 8, -1, 0, 0, 2, -1, 2, 0, 8, -1, 0, 0, 8, -1, 2, 2, 0, -1, 0, 2, 0, 0, 0],
  [0, 0, 0, -1, 0, -1, -8, 0, 2, -1, -1, 0, 2, 8, 8, 2, 0, 0, 8, -1, -1, 0, 2, 2, 0, 0, 2, -1, -1, 8, 0, 2, 0, 2, 0, 0, 0]]

abbrev V := Fin 14
abbrev P := Fin 21
abbrev N := Fin 37

def raw (v : V) := seeds.getD v.val 0
def cell (p : P) (n : N) := (weights.getD p.val []).getD n.val 0
def ends (v : V) := triples.getD v.val (0,0,0)
def pos (v : V) (p : P) := (raw v).testBit p.val
def neg (v : V) (n : N) := (raw v).testBit (21+n.val)
def selected (v : V) (a b c : Bool) (p : P) := ((p == (ends v).1) && a) ||
   ((p == (ends v).2.1) && b) || ((p == (ends v).2.2) && c)

def coeff (I : P → Bool) (n : N) : Int := ∑ p : P, if I p then cell p n else 0
def mass (I : P → Bool) (J : N → Bool) : Int := ∑ n : N, if J n then coeff I n else 0

lemma support : ∀ v p, pos v p = selected v true true true p := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
lemma certificate : ∀ (v : V) (a b c : Bool),
    (∑ n : N, if neg v n then 0 else max (coeff (selected v a b c) n) 0) ≤ 24 := by
  intro v
  fin_cases v <;> decide +kernel

lemma raw_bound (v : V) (I : P → Bool) (J : N → Bool)
    (hp : ∀ p, I p = true → pos v p = true) (hn : ∀ n, J n = true → neg v n = false) :
    mass I J ≤ 24 := by
  let x := (ends v).1
  let y := (ends v).2.1
  let z := (ends v).2.2
  have ext : selected v (I x) (I y) (I z) = I := by
    funext p
    change (((p == x && I x) || (p == y && I y)) || (p == z && I z)) = I p
    have necessary : I p = true → (p == x || p == y || p == z) = true := by
      intro h
      have accepted := hp p h
      rw [support] at accepted
      simpa only [selected,Bool.and_true,x,y,z] using accepted
    by_cases hx : p = x <;> by_cases hy : p = y <;> by_cases hz : p = z <;> cases hi : I p <;> simp_all
  have bound := certificate v (I x) (I y) (I z)
  rw [ext] at bound
  refine le_trans ?_ bound
  unfold mass
  apply Finset.sum_le_sum
  intro n _
  cases hj : J n with
  | false => cases neg v n <;> simp
  | true => simp [hn n hj]

lemma mass_left (I : P → Bool) (J : N → Bool) (B : P → Bool) :
    mass I J = mass (fun p => I p && B p) J + mass (fun p => I p && !B p) J := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  cases J n with
  | false => simp
  | true =>
    change coeff I n = coeff (fun p => I p && B p) n + coeff (fun p => I p && !B p) n
    unfold coeff
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    cases hi : I p <;> cases hb : B p <;> simp [hi,hb]

lemma mass_right (I : P → Bool) (J : N → Bool) (B : N → Bool) :
    mass I J = mass I (fun n => J n && !B n) + mass I (fun n => J n && B n) := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  cases hj : J n <;> cases hb : B n <;> simp [hj,hb]

inductive Formula where
  | var : V → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

def Formula.value (row : V → Bool) : Formula → Bool
  | .var x => row x
  | .and a b => a.value row && b.value row
  | .or a b => a.value row || b.value row

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .and a b | .or a b => a.leaves + b.leaves

def vp (f : Formula) (p : P) := f.value (fun v => pos v p)
def vn (f : Formula) (n : N) := f.value (fun v => neg v n)

theorem formula_bound (f : Formula) (I : P → Bool) (J : N → Bool)
    (hp : ∀ p, I p = true → vp f p = true) (hn : ∀ n, J n = true → vn f n = false) :
    mass I J ≤ 24 * (f.leaves : Int) := by
  induction f generalizing I J with
  | var v =>
    simpa [Formula.leaves] using raw_bound v I J hp hn
  | and a b ia ib =>
    have p (i : P) (hi : I i = true) : vp a i = true ∧ vp b i = true := Bool.and_eq_true_iff.mp (hp i hi)
    have l := ia I (fun n => J n && !vn a n) (fun i hi => (p i hi).1) (by
      intro n h
      have v := (Bool.and_eq_true_iff.mp h).2
      cases hh : vn a n <;> simp_all)
    have r := ib I (fun n => J n && vn a n) (fun i hi => (p i hi).2) (by
      intro n h
      obtain ⟨j,a'⟩ := Bool.and_eq_true_iff.mp h
      have v := hn n j
      change (vn a n && vn b n) = false at v
      simpa [a'] using v)
    rw [mass_right I J (vn a)]
    simpa only [Formula.leaves,Nat.cast_add,Int.mul_add] using add_le_add l r
  | or a b ia ib =>
    have q (n : N) (hj : J n = true) : vn a n = false ∧ vn b n = false := by
      have v := hn n hj
      change (vn a n || vn b n) = false at v
      cases ha : vn a n <;> cases hb : vn b n <;> simp_all
    have l := ia (fun p => I p && vp a p) J (fun i h => (Bool.and_eq_true_iff.mp h).2) (fun n h => (q n h).1)
    have r := ib (fun p => I p && !vp a p) J (by
      intro i h
      obtain ⟨ii,hh⟩ := Bool.and_eq_true_iff.mp h
      have v := hp i ii
      change (vp a i || vp b i) = true at v
      cases ha : vp a i <;> simp_all) (fun n h => (q n h).2)
    rw [mass_left I J (vp a)]
    simpa only [Formula.leaves,Nat.cast_add,Int.mul_add] using add_le_add l r

theorem sharp_bound (f : Formula) (hp : ∀ p, vp f p = true) (hn : ∀ n, vn f n = false) :
    28 ≤ f.leaves := by
  have total : mass (fun _ => true) (fun _ => true) = 672 := by decide +kernel
  have h := formula_bound f (fun _ => true) (fun _ => true) (fun p _ => hp p) (fun n _ => hn n)
  rw [total] at h
  omega

end PEqualNP.Outside.L_meta_3005.Rectangle

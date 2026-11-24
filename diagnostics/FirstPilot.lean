import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3005.Weighted

abbrev P := Fin 21
abbrev N := Fin 37
abbrev Matrix := P → N → Int

def coeff (w : Matrix) (I : P → Bool) (n : N) : Int := ∑ p : P, if I p then w p n else 0
def mass (w : Matrix) (I : P → Bool) (J : N → Bool) : Int := ∑ n : N, if J n then coeff w I n else 0

def configs : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (configs n).map (false :: ·) ++ (configs n).map (true :: ·)

lemma configs_mem (xs : List Bool) : xs ∈ configs xs.length := by
  induction xs with
  | nil => simp [configs]
  | cons x xs ih => cases x <;> simp [configs,ih]

def sel : List P → List Bool → P → Bool
  | a::as, b::bs, p => (p == a && b) || sel as bs p
  | _, _, _ => false

lemma sel_map (I : P → Bool) (xs : List P) (p : P) :
    sel xs (xs.map I) p = (xs.contains p && I p) := by
  induction xs with
  | nil => simp [sel]
  | cons a xs ih =>
    by_cases h : a = p
    · subst a
      cases hv : I p <;> simp [sel,ih,hv]
    · have h' := Ne.symm h
      simp [sel,ih,h,h',List.contains_cons]

def rows (word : Nat) := (List.finRange 21).filter fun p => word.testBit p.val

def good (w : Matrix) (M : Int) (word : Nat) : Bool :=
  (configs (rows word).length).all fun flags => decide
    ((∑ n : N, if word.testBit (21+n.val) then 0 else max (coeff w (sel (rows word) flags) n) 0) ≤ M)

lemma leaf_bound (w : Matrix) (M : Int) (word : Nat) (cert : good w M word = true)
    (I : P → Bool) (J : N → Bool)
    (hp : ∀ p, I p = true → word.testBit p.val = true)
    (hn : ∀ n, J n = true → word.testBit (21+n.val) = false) :
    mass w I J ≤ M := by
  let xs := rows word
  have eq : sel xs (xs.map I) = I := by
    funext p
    rw [sel_map]
    cases hi : I p with
    | false => simp
    | true =>
      have m : p ∈ xs := List.mem_filter.mpr ⟨by simp,hp p hi⟩
      simp [m]
  have mem : xs.map I ∈ configs xs.length := by simpa using configs_mem (xs.map I)
  have upper := of_decide_eq_true (List.all_eq_true.mp cert (xs.map I) mem)
  change (∑ n : N, if word.testBit (21+n.val) then 0 else max (coeff w (sel xs (xs.map I)) n) 0) ≤ M at upper
  rw [eq] at upper
  refine le_trans ?_ upper
  unfold mass
  apply Finset.sum_le_sum
  intro n _
  cases hj : J n with
  | false => cases word.testBit (21+n.val) <;> simp
  | true => simp [hn n hj]

lemma mass_left (w : Matrix) (I : P → Bool) (J : N → Bool) (B : P → Bool) :
    mass w I J = mass w (fun p => I p && B p) J + mass w (fun p => I p && !B p) J := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  cases J n with
  | false => simp
  | true =>
    change coeff w I n = coeff w (fun p => I p && B p) n + coeff w (fun p => I p && !B p) n
    unfold coeff
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    cases hi : I p <;> cases hb : B p <;> simp [hi,hb]

lemma mass_right (w : Matrix) (I : P → Bool) (J : N → Bool) (B : N → Bool) :
    mass w I J = mass w I (fun n => J n && !B n) + mass w I (fun n => J n && B n) := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  cases hj : J n <;> cases hb : B n <;> simp [hj,hb]

inductive Formula where
  | var : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

def Formula.value (row : Nat → Bool) : Formula → Bool
  | .var x => row x
  | .and a b => a.value row && b.value row
  | .or a b => a.value row || b.value row

def Formula.leaves : Formula → Nat
  | .var _ => 1
  | .and a b | .or a b => a.leaves + b.leaves

def vp (f : Formula) (p : P) := f.value (fun v => v.testBit p.val)
def vn (f : Formula) (n : N) := f.value (fun v => v.testBit (21+n.val))

def Exact (w : Matrix) (M : Int) : Formula → Prop
  | .var v => good w M v = true
  | .and a b | .or a b => Exact w M a ∧ Exact w M b

theorem formula_bound (w : Matrix) (M : Int) (f : Formula) (I : P → Bool) (J : N → Bool) (valid : Exact w M f)
    (hp : ∀ p, I p = true → vp f p = true) (hn : ∀ n, J n = true → vn f n = false) :
    mass w I J ≤ M * (f.leaves : Int) := by
  induction f generalizing I J with
  | var v =>
    simpa [Formula.leaves] using leaf_bound w M v valid I J hp hn
  | and a b ia ib =>
    have p (i : P) (hi : I i = true) : vp a i = true ∧ vp b i = true := Bool.and_eq_true_iff.mp (hp i hi)
    have l := ia I (fun n => J n && !vn a n) valid.1 (fun i hi => (p i hi).1) (by
      intro n h
      have v := (Bool.and_eq_true_iff.mp h).2
      cases hh : vn a n <;> simp_all)
    have r := ib I (fun n => J n && vn a n) valid.2 (fun i hi => (p i hi).2) (by
      intro n h
      obtain ⟨j,a'⟩ := Bool.and_eq_true_iff.mp h
      have v := hn n j
      change (vn a n && vn b n) = false at v
      simpa [a'] using v)
    rw [mass_right w I J (vn a)]
    simpa only [Formula.leaves,Nat.cast_add,Int.mul_add] using add_le_add l r
  | or a b ia ib =>
    have q (n : N) (hj : J n = true) : vn a n = false ∧ vn b n = false := by
      have v := hn n hj
      change (vn a n || vn b n) = false at v
      cases ha : vn a n <;> cases hb : vn b n <;> simp_all
    have l := ia (fun p => I p && vp a p) J valid.1 (fun i h => (Bool.and_eq_true_iff.mp h).2) (fun n h => (q n h).1)
    have r := ib (fun p => I p && !vp a p) J valid.2 (by
      intro i h
      obtain ⟨ii,hh⟩ := Bool.and_eq_true_iff.mp h
      have v := hp i ii
      change (vp a i || vp b i) = true at v
      cases ha : vp a i <;> simp_all) (fun n h => (q n h).2)
    rw [mass_left w I J (vp a)]
    simpa only [Formula.leaves,Nat.cast_add,Int.mul_add] using add_le_add l r


def Uses (S : List Nat) : Formula → Prop
  | .var v => v ∈ S
  | .and a b | .or a b => Uses S a ∧ Uses S b

lemma exact_of_uses {w : Matrix} {M : Int} {S : List Nat} (cert : S.all (good w M) = true)
    {f : Formula} (h : Uses S f) : Exact w M f := by
  induction f with
  | var v => exact List.all_eq_true.mp cert v h
  | and a b ia ib | or a b ia ib => exact ⟨ia h.1,ib h.2⟩

lemma cost_from {w : Matrix} {M : Int} {S : List Nat} {f : Formula} (uses : Uses S f)
    (cert : S.all (good w M) = true) (total : 26 * M < mass w (fun _ => true) (fun _ => true))
    (nonneg : 0 < M) (hp : ∀ p, vp f p = true) (hn : ∀ n, vn f n = false) : 27 ≤ f.leaves := by
  have h := formula_bound w M f (fun _ => true) (fun _ => true) (exact_of_uses cert uses)
    (fun p _ => hp p) (fun n _ => hn n)
  by_contra! small
  have l : (f.leaves : Int) ≤ 26 := by omega
  have le := mul_le_mul_of_nonneg_left l nonneg.le
  rw [mul_comm (26 : Int) M] at total
  omega

def A : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]

def table : List (List Int) := [
  [0, 0, -6, 0, 6, 0, 0, -6, 0, 0, 0, 0, 6, 0, 3, 0, 0, 0, 6, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0],
  [0, 0, 24, 0, 0, 0, 0, -12, 0, 0, 0, 0, -3, 0, 12, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0],
  [0, 0, -12, 0, 0, 0, 0, 24, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -3, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0],
  [0, 0, 6, 0, -6, 0, 0, 6, 0, 0, 0, 0, 6, 3, 0, 3, 0, 0, 6, 3, 0, 0, 3, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, -3, 12, 0, 0, 0, 0, -3, 0, 0, 0, 12, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 12, 0, 0, -3, 12, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 9, 0, 3, 0, 0, 3, 3, 9, 3, 0, 0, 0, 12, 0, 0, -3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, -12, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 6, 0, 12, -3, 3, 3, 0, 0, 0, 9, 3, 0, 3, 0, 0, 0, 0, -6, -3, 0, 0, -3, 0, 9, 0, 0, 0],
  [0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 9, 0, 0, 0, -12, -3, 0, 0, 0, 0, 0, 0, 6, 3, 0, 0, 3, 0, 12, 0, 0, 0],
  [0, 0, 6, 0, 6, 0, 0, 6, 0, 0, 0, 0, 12, -3, -3, -3, 0, 0, 12, -3, -3, 0, -3, 0, 0, 6, 0, 0, 0, 0, 0, -3, 0, -3, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 12, 3, 3, 3, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 3, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, -12, 0, 0, 0, 0, 0, 12, 3, 3, 0, 3, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 3, 0, 0, 0],
  [0, 0, 9, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, -3, 0, 12, 0, 0, 3, 3, 9, 0, 3, 0, 0, 0, 0, 0, 0, 6, 0, -12, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 6, 0, 0, -3, 0, 0, 0, 3, 3, 9, 0, 0, 12, 3, 3, 0, -3, 0, 0, 0, 0, 0, -3, -6, 0, 9, 0, -3, 0, 0, 0],
  [0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -12, 0, 0, 3, 9, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 12, 0, 3, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 9, 3, 0, 0, 0, 0, 0, 12, 0, -12, 0, 0, 9, 0, 0, 3, 0, 0, 3, 0, -3, 0, 0, 0],
  [0, 0, 9, 0, 0, 0, 0, 0, 0, 3, 6, 0, 3, 3, 0, 3, 0, 0, 0, -3, -12, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -6, 0, 12, 3, -3, -3, 0, 0, 0, 3, 9, 0, 9, 0, 0, 0, 0, 6, -3, 0, 0, 3, 0, 3, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 6, 9, 0, 3, 0, 0, 0, 12, -12, -3, 0, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, -12, 12, 0, 0, 0, 3, 0, 3, 0, 9, 0, 0, 9, 0, 0, 3, 0, 0, -3, 0, 3, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, -6, 0, 0, -3, 0, 0, 0, 9, 9, 3, 0, 0, 12, -3, -3, 0, 3, 0, 0, 0, 0, 0, -3, 6, 0, 3, 0, 3, 0, 0, 0]]

def sample (p : P) (n : N) := (table.getD p.val []).getD n.val 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma trial : A.all (good sample 24) = true := by decide +kernel

lemma case_one {f : Formula} (h : Uses A f) (p : ∀ i, vp f i = true) (n : ∀ j, vn f j = false) : 27 ≤ f.leaves :=
  cost_from h trial (by decide +kernel) (by decide) p n

end PEqualNP.Outside.L_meta_3005.Weighted

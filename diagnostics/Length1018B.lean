import PEqualNP.Defs
namespace L1018

abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Row (n : ℕ) := Finset (Edge n) × Bool

def ends {n} (e : Edge n) := ({e.1,e.2} : Finset (Fin n))
def choices {n} (E : Finset (Edge n)) (k : ℕ) := E.powerset.filter fun Q => Q.card=k ∧
  ∀ e∈Q, ∀ f∈Q, e≠f → Disjoint (ends e) (ends f)
def signed {n} (Q : Finset (Edge n)) (rows : List (Row n)) : ℤ :=
  ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : ℤ) -
  ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : ℤ)
def weight {n} (Q : Finset (Edge n)) : ℕ :=
  let V := Q.biUnion ends
  V.prod fun i => (V.filter (fun j => i<j)).prod fun j => (j.val-i.val)^2
def total {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :=
  (choices E k).sum fun Q => weight Q * (signed Q rows).natAbs^2

theorem weight_pos {n} (Q : Finset (Edge n)) : 0<weight Q := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (Nat.sub_pos_of_lt (Finset.mem_filter.mp hj).2) _

theorem detected {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    0<total k E rows ↔ ∃ Q∈choices E k, signed Q rows ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra no
    push_neg at no
    have nul : total k E rows=0 := Finset.sum_eq_zero (fun Q hQ => by simp [no Q hQ])
    omega
  · rintro ⟨Q,hQ,sgn⟩
    have t := Finset.single_le_sum (f:=fun S => weight S * (signed S rows).natAbs^2)
      (fun i _ => Nat.zero_le _) hQ
    have pos : 0 < (signed Q rows).natAbs := Int.natAbs_pos.mpr sgn
    exact (Nat.mul_pos (weight_pos Q) (pow_pos pos 2)).trans_le t

def term {n} (Q : Finset (Edge n)) (r : Row n) : ℤ :=
  if Q⊆r.1 then if r.2 then 1 else -1 else 0

theorem signed_sum {n} (Q : Finset (Edge n)) (rows : List (Row n)) :
    signed Q rows=(rows.map (term Q)).sum := by
  induction rows with
  | nil => simp [signed]
  | cons r rs ih =>
    rcases r with ⟨A,b⟩
    unfold signed at ih ⊢
    cases b <;> by_cases h : Q⊆A <;>
      simp [List.filter_cons,term,h] at ih ⊢ <;> omega

theorem total_cast {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) = ∑ Q∈choices E k, (weight Q : ℤ)*(signed Q rows)^2 := by
  simp only [total,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Int.natCast_natAbs,sq_abs]

theorem list_mul_sum (a : ℤ) (l : List ℤ) : a*l.sum=(l.map fun z=>a*z).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [mul_add,ih]

theorem pair_expand (l : List ℤ) : l.sum^2=(l.map (fun x => (l.map (fun y=>x*y)).sum)).sum := by
  rw [pow_two,list_mul_sum]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [mul_comm,list_mul_sum]

theorem total_pair_rows {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) =
      ∑ Q∈choices E k, (weight Q : ℤ)*
        (rows.map (fun r => (rows.map (fun s => term Q r * term Q s)).sum)).sum := by
  rw [total_cast]
  apply Finset.sum_congr rfl
  intro Q _
  rw [signed_sum,pair_expand]
  simp only [List.map_map,Function.comp_def]

theorem signed_bound {n} (Q : Finset (Edge n)) (rows : List (Row n)) :
    (signed Q rows).natAbs ≤ rows.length := by
  induction rows with
  | nil => simp [signed]
  | cons r rs ih =>
    rw [signed_sum] at ih ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have bound : (term Q r).natAbs≤1 := by
      unfold term
      by_cases h : Q⊆r.1
      · cases b : r.2 <;> simp [h,b]
      · simp [h]
    exact (Int.natAbs_add_le _ _).trans (by omega)

theorem choice_bound {n} (E : Finset (Edge n)) (k : ℕ) : (choices E k).card≤2^E.card := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset _)

theorem weight_bound {n} (Q : Finset (Edge n)) : weight Q≤(n+1)^(2*n*n) := by
  classical
  let V := Q.biUnion ends
  have vc : V.card≤n := by simpa using Finset.card_le_univ V
  have each (i : Fin n) :
      ((V.filter fun j => i<j).prod fun j => (j.val-i.val)^2) ≤ (n+1)^(2*n) := by
    let A := V.filter fun j => i<j
    calc
      _ ≤ ∏ _∈A, (n+1)^2 := Finset.prod_le_prod' fun j _ =>
         Nat.pow_le_pow_left (by have := j.isLt; omega) 2
      _ = (n+1)^(2*A.card) := by simp [pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ ((Finset.card_filter_le _ _).trans vc))
  calc
    _ ≤ ∏ _∈V,(n+1)^(2*n) := Finset.prod_le_prod' fun i _ => each i
    _ = (n+1)^(2*n*V.card) := by simp [pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ vc)

theorem total_bound {n k} (E : Finset (Edge n)) (rows : List (Row n)) :
    total k E rows ≤ 2^E.card * (n+1)^(2*n*n)*rows.length^2 := by
  calc
    _ ≤ ∑ _∈choices E k, (n+1)^(2*n*n)*rows.length^2 :=
      Finset.sum_le_sum fun Q _ => Nat.mul_le_mul (weight_bound Q) (Nat.pow_le_pow_left (signed_bound Q rows) 2)
    _ = (choices E k).card*((n+1)^(2*n*n)*rows.length^2) := by simp
    _ ≤ 2^E.card*((n+1)^(2*n*n)*rows.length^2) := Nat.mul_le_mul_right _ (choice_bound E k)
    _ = _ := by ring

theorem pow_dominates (n : ℕ) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n h => rw [pow_succ]; omega

theorem output_bits_bound {n k} (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows).log2 + 1 ≤ E.card + 2*n*n*n + 2*rows.length + 1 := by
  have hE : total k E rows ≤ 2 ^ (E.card + 2*n*n*n + 2*rows.length) := by
    calc
      _ ≤ _ := total_bound E rows
      _ ≤ 2^E.card*(2^n)^(2*n*n)*(2^rows.length)^2 := Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pow_dominates n) _))
        (Nat.pow_le_pow_left (Nat.le_trans (by omega) (pow_dominates rows.length)) 2)
      _ = _ := by simp only [←pow_mul,←pow_add]; congr 1 <;> ring
  let d := E.card + 2*n*n*n + 2*rows.length
  change (total k E rows).log2+1 ≤ d+1
  change total k E rows ≤ 2^d at hE
  by_cases z : total k E rows=0
  · simp [z]
  · have less : total k E rows < 2^(d+1) := by
      rw [pow_succ]
      have pos : 0 < 2^d := pow_pos (by decide) _
      omega
    exact (Nat.log2_lt z).mpr less

end L1018

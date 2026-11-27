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

def quadFactor {n} (a b : Fin n) : ℤ := ((a.val:ℤ) - b.val)^2
def above {n} (a b : Fin n) : ℤ := if a<b then quadFactor a b else 1
def vweight {n} (V : Finset (Fin n)) : ℤ := ∏ i∈V, ∏ j∈V, above i j
def hitFactor {n} (V : Finset (Fin n)) (x : ℤ) : ℤ := ∏ i∈V, (x-i.val)^2

theorem factor_symm {n} (a b : Fin n) : quadFactor a b=quadFactor b a := by
  unfold quadFactor
  ring
theorem vandermonde_nat {n} (Q : Finset (Edge n)) :
    (weight Q : ℤ)=vweight (Q.biUnion ends) := by
  classical
  simp only [weight,vweight,Nat.cast_prod,Nat.cast_pow,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  by_cases lt : i<j
  · simp only [above,lt,if_true,quadFactor]
    change (((j.val-i.val)^2 : ℕ) : ℤ) = ((i.val : ℤ)-j.val)^2
    rw [Nat.cast_pow,Nat.cast_sub (Fin.le_iff_val_le_val.mp lt.le)]
    ring
  · simp [above,lt]

theorem insert_weight {n} (V : Finset (Fin n)) (a : Fin n) (fresh : a∉V) :
    vweight (insert a V)=vweight V*hitFactor V a.val := by
  classical
  unfold vweight hitFactor
  simp only [Finset.prod_insert fresh,Finset.prod_mul_distrib]
  have aa : above a a=1 := if_neg (lt_irrefl _)
  rw [aa,one_mul]
  have single : (∏ i∈V,above a i)*(∏ i∈V,above i a)=∏ i∈V,((a.val:ℤ)-i.val)^2 := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have ne : a≠i := fun e => fresh (e.symm ▸ hi)
    rcases lt_or_gt_of_ne ne with lt|gt
    · simp [above,lt,not_lt.mpr lt.le,quadFactor]
    · simp only [above,gt,if_true,not_lt.mpr gt.le,if_false,one_mul]
      exact factor_symm i a
  rw [←single]
  ring

theorem edge_extension {n} (V : Finset (Fin n)) (a b : Fin n) (ab : a≠b) :
    (if a∈V ∨ b∈V then (0:ℤ) else vweight (insert a (insert b V))) =
      vweight V * quadFactor a b * hitFactor V a.val * hitFactor V b.val := by
  classical
  have van (j : Fin n) (hj : j∈V) : hitFactor V j.val=0 := by
    apply Finset.prod_eq_zero hj
    simp
  by_cases ha : a∈V
  · simp [ha,van a ha]
  by_cases hb : b∈V
  · simp [hb,van b hb]
  have none : a∉insert b V := by simp [ab,ha]
  rw [if_neg (not_or_intro ha hb),insert_weight _ _ none,insert_weight _ _ hb]
  simp only [hitFactor,Finset.prod_insert hb,quadFactor]
  ring

def sign {n} (r : Row n) : ℤ := if r.2 then 1 else -1
def kernel {n} (k : ℕ) (F : Finset (Edge n)) : ℤ := ∑ Q∈choices F k, (weight Q : ℤ)

theorem term_product {n} (Q : Finset (Edge n)) (r s : Row n) :
    term Q r * term Q s=(if Q⊆r.1 ∧ Q⊆s.1 then sign r * sign s else 0) := by
  by_cases hr : Q⊆r.1 <;> by_cases hs : Q⊆s.1 <;> simp [term,sign,hr,hs]

theorem choices_meet {n} (k : ℕ) (E X Y : Finset (Edge n)) :
    choices (E∩X∩Y) k = (choices E k).filter (fun Q => Q⊆X ∧ Q⊆Y) := by
  classical
  ext Q
  simp only [choices,Finset.mem_filter,Finset.mem_powerset,Finset.subset_inter_iff]
  tauto

theorem swap_sum {α β : Type} (S : Finset α) (r : List β) (f : α→β→ℤ) :
    (∑ a∈S, (r.map (f a)).sum)=(r.map (fun v => ∑ a∈S, f a v)).sum := by
  induction r with
  | nil => simp
  | cons a r ih => simp [Finset.sum_add_distrib,ih]

theorem fixed_pair {n} (k : ℕ) (E : Finset (Edge n)) (r s : Row n) :
    (∑ Q∈choices E k, (weight Q : ℤ)*(term Q r*term Q s)) =
      sign r * sign s * kernel k (E∩r.1∩s.1) := by
  classical
  rw [kernel,choices_meet,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [term_product]
  split <;> ring

theorem expanded_kernel {n} (k : ℕ) (E : Finset (Edge n)) (rows : List (Row n)) :
    (total k E rows : ℤ) =
      (rows.map fun r => (rows.map fun s => sign r * sign s * kernel k (E∩r.1∩s.1)).sum).sum := by
  rw [total_pair_rows]
  have push (Q : Finset (Edge n)) :
      (weight Q:ℤ)*(rows.map (fun r => (rows.map (fun s => term Q r * term Q s)).sum)).sum =
        (rows.map fun r => (rows.map fun s => (weight Q:ℤ)*(term Q r*term Q s)).sum).sum := by
    rw [list_mul_sum]
    simp only [List.map_map,Function.comp_def,list_mul_sum]
  simp_rw [push]
  rw [swap_sum]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [swap_sum]
  congr 1
  apply List.map_congr_left
  intro s _
  exact fixed_pair k E r s

end L1018

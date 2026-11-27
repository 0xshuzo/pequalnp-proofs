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

theorem mem_choices {n k} (E Q : Finset (Edge n)) :
    Q∈choices E k ↔ Q⊆E ∧ Q.card=k ∧ ∀ e∈Q, ∀ f∈Q,e≠f → Disjoint (ends e) (ends f) := by
  simp [choices]

def compatible {n} (e : Edge n) (Q : Finset (Edge n)) : Prop := ∀ f∈Q, Disjoint (ends e) (ends f)

instance {n} (e : Edge n) (Q : Finset (Edge n)) : Decidable (compatible e Q) :=
  inferInstanceAs (Decidable (∀ f∈Q, Disjoint (ends e) (ends f)))

theorem split_choices {n} (E : Finset (Edge n)) (e : Edge n) (fresh : e∉E) (t : ℕ) :
    choices (insert e E) (t+1) = choices E (t+1) ∪
      ((choices E t).filter (compatible e)).image (insert e) := by
  classical
  ext Q
  rw [mem_choices,Finset.mem_union,mem_choices,Finset.mem_image]
  constructor
  · rintro ⟨sub,sz,sep⟩
    by_cases h : e∈Q
    · right
      refine ⟨Q.erase e,Finset.mem_filter.mpr ⟨(mem_choices _ _).mpr ⟨?_,?_,?_⟩,?_⟩,
        Finset.insert_erase h⟩
      · intro f hf
        rcases Finset.mem_erase.mp hf with ⟨ne,mem⟩
        exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
      · rw [Finset.card_erase_of_mem h,sz]
        omega
      · intro f hf g hg ne
        exact sep f (Finset.mem_of_mem_erase hf) g (Finset.mem_of_mem_erase hg) ne
      · intro f hf
        have p := Finset.mem_erase.mp hf
        exact sep e h f p.2 p.1.symm
    · left
      exact ⟨fun f hf => (Finset.mem_insert.mp (sub hf)).resolve_left
         (fun eq => h (eq ▸ hf)),sz,sep⟩
  · rintro (⟨sub,sz,sep⟩|⟨R,hR,rfl⟩)
    · exact ⟨sub.trans (Finset.subset_insert _ _),sz,sep⟩
    · obtain ⟨hr,ok⟩ := Finset.mem_filter.mp hR
      obtain ⟨sub,sz,sep⟩ := (mem_choices _ _).mp hr
      have no : e∉R := fun h => fresh (sub h)
      refine ⟨Finset.insert_subset_insert _ sub,by rw [Finset.card_insert_of_notMem no,sz],?_⟩
      intro f hf g hg ne
      rcases Finset.mem_insert.mp hf with rfl|hf
      · rcases Finset.mem_insert.mp hg with rfl|hg
        · exact (ne rfl).elim
        · exact ok g hg
      · rcases Finset.mem_insert.mp hg with rfl|hg
        · exact (ok f hf).symm
        · exact sep f hf g hg ne

theorem sum_choice_step {n} (E : Finset (Edge n)) (e : Edge n) (fresh : e∉E) (t : ℕ)
    (F : Finset (Edge n) → ℤ) :
    (∑ Q∈choices (insert e E) (t+1),F Q) =
     (∑ Q∈choices E (t+1),F Q) +
     ∑ Q∈choices E t, (if compatible e Q then F (insert e Q) else 0) := by
  classical
  have miss {j} {Q : Finset (Edge n)} (h : Q∈choices E j) : e∉Q :=
    fun he => fresh (((mem_choices E Q).mp h).1 he)
  rw [split_choices _ _ fresh,Finset.sum_union,Finset.sum_image,Finset.sum_filter]
  · intro Q hQ R hR eq
    have q := miss (Finset.mem_filter.mp hQ).1
    have r := miss (Finset.mem_filter.mp hR).1
    simpa [q,r] using congrArg (fun S : Finset (Edge n) => S.erase e) eq
  · apply Finset.disjoint_left.mpr
    intro Q hQ hR
    rcases Finset.mem_image.mp hR with ⟨R,_,rfl⟩
    exact miss hQ (Finset.mem_insert_self _ _)

end L1018

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
end L1018

namespace Zero1018
open Turing

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

/-- Push the symbols of a list one after the other, then halt. -/
def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

/-- The program: erase the input, then write `l`. -/
def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

/-- The machine. -/
def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

/-- Configurations of the machine. -/
abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a


def zeroM : TM2ComputableAux Bool Bool where
  tm := constList [false]
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

theorem finite_zero (i : zeroM.tm.K) : Finite (zeroM.tm.Γ i) := inferInstanceAs (Finite Bool)

theorem zero_runs (a : List Bool) (k : ℕ) :
    Nonempty (TM2OutputsInTime zeroM.tm (a.map zeroM.inputAlphabet.invFun)
        (some ([false].map zeroM.outputAlphabet.invFun)) (2^(1*(k+1))*(a.length+2)^1)) := by
  refine ⟨{ steps := a.length+1, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l=l := fun l => by simp
    exact (congrArg (fun x => (flip bind (TM2.step (constListProg [false])))^[a.length+1]
      (some (initList (constList [false]) x))) (hm a)).trans
      ((constList_run [false] a).trans
        (congrArg (fun x => some (haltList (constList [false]) x)) (hm [false]).symm))
  · simp only [one_mul,pow_one]
    exact (by omega : a.length+1≤a.length+2).trans (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0 < 2) _))

theorem matches_card {n} (Q : Finset (L1018.Edge n))
    (strict : ∀ e∈Q, e.1<e.2)
    (sep : ∀ e∈Q,∀ f∈Q,e≠f → Disjoint (L1018.ends e) (L1018.ends f)) :
    (Q.biUnion L1018.ends).card=2*Q.card := by
  classical
  rw [Finset.card_biUnion (fun e he f hf neq => sep e he f hf neq)]
  have two (e : L1018.Edge n) (he : e∈Q) : (L1018.ends e).card=2 := by
    simp [L1018.ends,Finset.card_insert_of_notMem,ne_of_lt (strict e he)]
  simp [Finset.sum_congr rfl two,Nat.mul_comm]

theorem zero_sparse {n k} (E : Finset (L1018.Edge n)) (rows : List (L1018.Row n))
    (strict : ∀ e∈E, e.1<e.2) (tooLarge : E.card < k ∨ n < 2*k) :
    L1018.total k E rows=0 := by
  classical
  have void : L1018.choices E k=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q h
    obtain ⟨hsub,sz,sep⟩ := Finset.mem_filter.mp h
    have sub := Finset.mem_powerset.mp hsub
    have bound := Finset.card_le_card sub
    have exactCard := matches_card Q (fun e he => strict e (sub he)) sep
    have lim := Finset.card_le_univ (Q.biUnion L1018.ends)
    simp only [Fintype.card_fin] at lim
    omega
  simp [L1018.total,void]

theorem exact_zero_branch {n k} (x : List Bool) (E : Finset (L1018.Edge n))
    (rows : List (L1018.Row n)) (hz : L1018.total k E rows=0) :
    (0<L1018.total k E rows ↔ ∃ Q∈L1018.choices E k, L1018.signed Q rows≠0) ∧
    Nonempty (TM2OutputsInTime zeroM.tm (x.map zeroM.inputAlphabet.invFun)
       (some (((List.range ((L1018.total k E rows).log2+1)).map
         (fun i => (L1018.total k E rows).testBit i)).map zeroM.outputAlphabet.invFun))
       (2^(1*(k+1))*(x.length+2)^1)) := by
  refine ⟨L1018.detected k E rows, ?_⟩
  rw [hz]
  exact zero_runs x k

end Zero1018

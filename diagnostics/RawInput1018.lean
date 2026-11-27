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

namespace L1018

def header (n : ℕ) : List Bool := List.replicate n true ++ [false]
def pairs (n : ℕ) : List (Edge n) := (List.finRange n).flatMap fun i =>
  ((List.finRange n).filter fun j => decide (i<j)).map fun j => (i,j)
def mask {n} (E : Finset (Edge n)) : List Bool := (pairs n).map fun e => decide (e∈E)
def encode {n} (k : ℕ) (E : Finset (Edge n)) (rs : List (Row n)) : List Bool :=
  header n ++ header k ++ mask E ++ header rs.length ++ rs.flatMap (fun r => r.2::mask r.1)

def readHead : List Bool → ℕ × List Bool
  | [] => (0,[])
  | false::w => (0,w)
  | true::w => let h := readHead w; (h.1+1,h.2)

theorem read_header (n : ℕ) (w : List Bool) : readHead (header n++w)=(n,w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change readHead (List.replicate (n+1) true ++ [false] ++ w)=_
    rw [List.replicate_succ,List.cons_append,List.cons_append,readHead]
    change ((readHead (header n++w)).1+1,(readHead (header n++w)).2)=_
    rw [ih]

def readSet {α : Type*} [DecidableEq α] : List α → List Bool → Finset α × List Bool
  | [],w => (∅,w)
  | _::es, [] => readSet es []
  | e::es,b::w => let h := readSet es w; (if b then insert e h.1 else h.1,h.2)

theorem set_parse {α : Type*} [DecidableEq α] (A : Finset α) (es : List α) (w : List Bool) :
    readSet es ((es.map fun e => decide (e∈A))++w)=(es.toFinset∩A,w) := by
  induction es with
  | nil => simp [readSet]
  | cons e es ih =>
    simp only [List.map_cons,List.cons_append,readSet,ih,List.toFinset_cons]
    by_cases h : e∈A
    · simp only [h,decide_true,Bool.true_eq,if_true,Prod.mk.injEq,and_true]
      ext x
      simp only [Finset.mem_insert,Finset.mem_inter]
      aesop
    · simp only [h,decide_false,Bool.false_eq_true,if_false,Prod.mk.injEq,and_true]
      ext x
      simp only [Finset.mem_insert,Finset.mem_inter]
      aesop

theorem pair_mem {n} (e : Edge n) : e∈pairs n ↔ e.1<e.2 := by
  rcases e with ⟨a,b⟩
  simp [pairs]

def trimmed {n} (A : Finset (Edge n)) := (pairs n).toFinset∩A
def trimRow {n} (r : Row n) : Row n := (trimmed r.1,r.2)

def readRows (n : ℕ) : ℕ → List Bool → List (Row n)
  | 0,_ => []
  | _+1,[] => []
  | m+1,b::w => let r := readSet (pairs n) w; (r.1,b)::readRows n m r.2

theorem row_parse {n} (rs : List (Row n)) (w : List Bool) :
    readRows n rs.length (rs.flatMap (fun r => r.2::mask r.1)++w)=rs.map trimRow := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,List.cons_append,readRows,mask,set_parse,List.map_cons]
    exact congrArg (fun l => trimRow r::l) ih

def runWord (w : List Bool) : List Bool :=
  let n := readHead w
  let k := readHead n.2
  let E := readSet (pairs n.1) k.2
  let cnt := readHead E.2
  let m := total k.1 E.1 (readRows n.1 cnt.1 cnt.2)
  (List.range (m.log2+1)).map fun i => m.testBit i

theorem trim_eq {n} (E : Finset (Edge n)) (strict : ∀ e∈E,e.1<e.2) : trimmed E=E := by
  ext e
  simp only [trimmed,Finset.mem_inter,List.mem_toFinset,pair_mem]
  exact ⟨And.right,fun h=>⟨strict e h,h⟩⟩

theorem term_trim {n} (Q : Finset (Edge n)) (hq : ∀ e∈Q,e.1<e.2) (r : Row n) :
    term Q (trimRow r)=term Q r := by
  have sub : Q⊆(pairs n).toFinset := fun e h => List.mem_toFinset.mpr ((pair_mem e).mpr (hq e h))
  simp only [term,trimRow,trimmed,Finset.subset_inter_iff,sub,true_and]

theorem total_trim {n} (k : ℕ) (E : Finset (Edge n)) (strict : ∀ e∈E,e.1<e.2) (rs : List (Row n)) :
    total k E (rs.map trimRow)=total k E rs := by
  apply Finset.sum_congr rfl
  intro Q hQ
  have sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
  have sem : signed Q (rs.map trimRow)=signed Q rs := by
    rw [signed_sum,signed_sum,List.map_map]
    congr 1
    apply List.map_congr_left
    exact fun r _ => term_trim Q (fun e h => strict e (sub h)) r
  rw [sem]

theorem runWord_correct {n} (k : ℕ) (E : Finset (Edge n)) (rs : List (Row n)) (strict : ∀ e∈E,e.1<e.2) :
    runWord (encode k E rs)=
      (List.range ((total k E rs).log2+1)).map fun i => (total k E rs).testBit i := by
  simp only [runWord,encode,List.append_assoc,read_header,mask,set_parse]
  change (List.range ((total k (trimmed E) (readRows n rs.length (rs.flatMap _))).log2+1)).map _=_
  have row := row_parse rs []
  simp only [List.append_nil] at row
  rw [row,trim_eq E strict,total_trim k E strict]
end L1018

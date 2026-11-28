import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx9792Formula

inductive Formula (V : Type) where
  | input (v : V)
  | conj (a b : Formula V)
  | disj (a b : Formula V)

def Formula.eval {V} : Formula V → (V → Bool) → Bool
  | .input v, x => x v
  | .conj a b, x => a.eval x && b.eval x
  | .disj a b, x => a.eval x || b.eval x

def Formula.gates {V} : Formula V → Nat
  | .input _ => 0
  | .conj a b | .disj a b => a.gates+b.gates+1

structure Rectangle (V X Y : Type) where
  label : V
  row : X → Bool
  col : Y → Bool

def table {V X Y : Type} (p : X → V → Bool) (n : Y → V → Bool) :
    Formula V → (X → Bool) → (Y → Bool) → List (Rectangle V X Y)
  | .input v, a, b => [⟨v,a,b⟩]
  | .conj t u, a, b =>
    table p n t a (fun j => b j && !t.eval (n j)) ++
    table p n u a (fun j => b j && t.eval (n j))
  | .disj t u, a, b =>
    table p n t (fun i => a i && t.eval (p i)) b ++
    table p n u (fun i => a i && !t.eval (p i)) b

theorem size {V X Y} (p : X → V → Bool) (n : Y → V → Bool) (t : Formula V)
    (a : X → Bool) (b : Y → Bool) : (table p n t a b).length = t.gates+1 := by
  induction t generalizing a b with
  | input v => rfl
  | conj t u ht hu => simp only [table,List.length_append,ht,hu,Formula.gates]; omega
  | disj t u ht hu => simp only [table,List.length_append,ht,hu,Formula.gates]; omega

def whereHit {V X Y} (i : X) (j : Y) (q : Rectangle V X Y) : Bool := q.row i && q.col j

theorem partition {V X Y} (p : X → V → Bool) (n : Y → V → Bool) (t : Formula V)
    (a : X → Bool) (b : Y → Bool) (i : X) (j : Y) :
    ((table p n t a b).filter (whereHit i j)).length = (if a i && b j then 1 else 0) := by
  induction t generalizing a b with
  | input v => cases h : a i <;> cases k : b j <;> simp [table,whereHit,h,k]
  | conj t u ht hu =>
    simp only [table,List.filter_append,List.length_append,ht,hu]
    cases h : a i <;> cases k : b j <;> cases v : t.eval (n j) <;> rfl
  | disj t u ht hu =>
    simp only [table,List.filter_append,List.length_append,ht,hu]
    cases h : a i <;> cases k : b j <;> cases v : t.eval (p i) <;> rfl

theorem labelCorrect {V X Y} (p : X → V → Bool) (n : Y → V → Bool) (t : Formula V)
    (a : X → Bool) (b : Y → Bool)
    (hp : ∀ i, a i=true → t.eval (p i)=true) (hn : ∀ j, b j=true → t.eval (n j)=false)
    (q : Rectangle V X Y) (mem : q ∈ table p n t a b) :
    (∀ i, q.row i=true → p i q.label=true) ∧ (∀ j, q.col j=true → n j q.label=false) := by
  induction t generalizing a b with
  | input v =>
    have eq : q = ⟨v,a,b⟩ := by simpa [table] using mem
    subst q
    exact ⟨hp,hn⟩
  | conj t u ht hu =>
    rcases List.mem_append.mp mem with m|m
    · apply ht _ _ _ _ m
      · intro i hi
        exact (Bool.and_eq_true_iff.mp (hp i hi)).1
      · intro j hj
        simpa using (Bool.and_eq_true_iff.mp hj).2
    · apply hu _ _ _ _ m
      · intro i hi
        exact (Bool.and_eq_true_iff.mp (hp i hi)).2
      · intro j hj
        obtain ⟨hb,hit⟩ := Bool.and_eq_true_iff.mp hj
        have h := hn j hb
        simpa [Formula.eval,hit] using h
  | disj t u ht hu =>
    rcases List.mem_append.mp mem with m|m
    · apply ht _ _ _ _ m
      · intro i hi
        exact (Bool.and_eq_true_iff.mp hi).2
      · intro j hj
        have h := hn j hj
        cases z : t.eval (n j) <;> simp_all [Formula.eval]
    · apply hu _ _ _ _ m
      · intro i hi
        obtain ⟨ha,miss⟩ := Bool.and_eq_true_iff.mp hi
        have hh := hp i ha
        have z : t.eval (p i)=false := by simpa using miss
        simpa [Formula.eval,z] using hh
      · intro j hj
        have h := hn j hj
        cases z : u.eval (n j) <;> simp_all [Formula.eval]

end PEqualNP.Outside.Pcx9792Formula

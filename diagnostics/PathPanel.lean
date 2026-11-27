import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9743.PathPanel

-- Six rows: a positive minterm, each marked variable removed, a negative
-- maximal assignment, and each marked variable inserted.
def bits (a b c d e f : Bool) : Nat :=
  a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat + 16*e.toNat + 32*f.toNat

def shape (a y c z b : Bool) : Bool := (y && (a || c)) || (z && (b || c))

theorem pathValues :
  bits (shape false true true false false) (shape false false true false false)
    (shape false true false false false) (shape true false false true false)
    (shape true true false true false) (shape true false true true false) = 49 := by decide

def codes : List (Nat × Nat) := [(0, 0),
(0, 7),
(0, 56),
(0, 63),
(1, 0),
(1, 5),
(1, 7),
(1, 16),
(1, 21),
(1, 23),
(1, 56),
(1, 61),
(1, 63),
(2, 0),
(2, 3),
(2, 7),
(2, 32),
(2, 35),
(2, 39),
(2, 56),
(2, 59),
(2, 63),
(3, 0),
(3, 1),
(3, 3),
(3, 5),
(3, 7),
(3, 16),
(3, 17),
(3, 19),
(3, 21),
(3, 23),
(3, 32),
(3, 33),
(3, 35),
(3, 37),
(3, 39),
(3, 48),
(3, 51),
(3, 53),
(3, 55),
(3, 56),
(3, 57),
(3, 59),
(3, 61),
(3, 63)]
def join (d : Bool) (x y : Nat) := if d then x ||| y else x &&& y

def paired (s t : Nat × Nat) : Bool :=
  ((s.1 &&& t.1) != 0) || ([false,true].all fun d =>
    codes.contains (s.1 ||| t.1, join d s.2 t.2))

theorem closed : (codes.all fun s => codes.all (paired s)) = true := by decide +kernel

inductive Expression : Nat → Nat → Prop
  | other {x : Nat} (allowed : x ∈ [0,7,56,63]) : Expression 0 x
  | first : Expression 1 21
  | second : Expression 2 35
  | branch {i j x y : Nat} (d : Bool) (dis : (i &&& j) = 0)
      (left : Expression i x) (right : Expression j y) : Expression (i ||| j) (join d x y)

theorem inCodes {a x : Nat} (h : Expression a x) : (a,x) ∈ codes := by
  induction h with
  | other allowed =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with h | h | h | h <;> subst_vars <;> decide
  | first => decide
  | second => decide
  | @branch i j x y d dis _ _ hl hr =>
    have v := List.all_eq_true.mp (List.all_eq_true.mp closed (i,x) hl) (j,y) hr
    have g : ([false,true].all fun k => codes.contains (i ||| j, join k x y)) = true := by
      simpa [paired, dis] using v
    have ok : d ∈ [false,true] := by cases d <;> decide
    simpa using (List.all_eq_true.mp g d ok)

theorem noTarget : (codes.all (fun p => p.2 != 49)) = true := by decide

theorem pathNeedsRepeatedMarkedInput {a : Nat} (h : Expression a 49) : False := by
  have bad := List.all_eq_true.mp noTarget (a,49) (inCodes h)
  simp at bad

end PEqualNP.Outside.L_meta_9743.PathPanel

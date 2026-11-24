import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3005.Private

abbrev V := Fin 14
abbrev P := Fin 21
abbrev N := Fin 37

def seeds : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
def casesTable : List (P × N) := [
  (1, 2), (0, 1), (1, 2), (0, 1), (0, 1), (0, 1), (1, 2), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1),
  (0, 1), (1, 2), (0, 3), (0, 1), (0, 5), (0, 1), (0, 8), (0, 1), (0, 12), (0, 1), (0, 18), (0, 1), (0, 26), (0, 1),
  (4, 4), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (4, 4), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1),
  (3, 1), (4, 4), (3, 3), (3, 1), (3, 5), (3, 1), (3, 8), (3, 1), (3, 12), (3, 1), (3, 18), (3, 1), (3, 26), (3, 1),
  (7, 17), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (6, 2), (7, 17), (6, 2),
  (6, 3), (6, 2), (6, 2), (7, 17), (6, 6), (6, 2), (6, 9), (6, 2), (6, 13), (6, 2), (6, 19), (6, 2), (6, 27), (6, 2),
  (10, 11), (9, 1), (10, 11), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1), (9, 1),
  (9, 1), (10, 11), (9, 3), (9, 1), (9, 5), (9, 1), (9, 8), (9, 1), (9, 12), (9, 1), (9, 18), (9, 1), (9, 26), (9, 1),
  (13, 11), (12, 7), (12, 7), (12, 7), (12, 7), (12, 7), (12, 7), (12, 7), (13, 11), (12, 7), (13, 11), (12, 7), (12, 7), (12, 7),
  (12, 8), (12, 7), (12, 9), (12, 7), (12, 10), (12, 7), (12, 7), (13, 11), (12, 15), (12, 7), (12, 22), (12, 7), (12, 29), (12, 7),
  (15, 4), (15, 4), (16, 7), (15, 4), (15, 4), (15, 4), (15, 4), (15, 4), (15, 4), (15, 4), (16, 7), (15, 4), (16, 7), (15, 4),
  (15, 5), (15, 4), (15, 6), (15, 4), (15, 4), (16, 7), (15, 10), (15, 4), (15, 14), (15, 4), (15, 20), (15, 4), (15, 28), (15, 4),
  (19, 4), (18, 2), (18, 2), (18, 2), (19, 4), (18, 2), (18, 2), (18, 2), (18, 2), (18, 2), (18, 2), (18, 2), (18, 3), (18, 2),
  (18, 3), (18, 2), (18, 2), (19, 4), (18, 6), (18, 2), (18, 9), (18, 2), (18, 13), (18, 2), (18, 19), (18, 2), (18, 27), (18, 2),
  (0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
  (3, 2), (0, 0), (3, 2), (0, 0), (0, 4), (0, 0), (3, 7), (0, 0), (0, 11), (0, 0), (0, 17), (0, 0), (0, 25), (0, 0),
  (1, 0), (6, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0),
  (6, 1), (1, 0), (1, 4), (1, 0), (1, 4), (1, 0), (6, 7), (1, 0), (1, 11), (1, 0), (1, 17), (1, 0), (1, 25), (1, 0),
  (4, 0), (4, 0), (4, 0), (15, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0), (4, 0),
  (15, 1), (4, 0), (4, 2), (4, 0), (4, 7), (4, 0), (4, 7), (4, 0), (4, 11), (4, 0), (4, 17), (4, 0), (15, 25), (4, 0),
  (2, 0), (12, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0),
  (12, 1), (2, 0), (12, 2), (2, 0), (2, 4), (2, 0), (2, 11), (2, 0), (2, 11), (2, 0), (2, 17), (2, 0), (2, 25), (2, 0),
  (10, 0), (10, 0), (10, 0), (10, 0), (10, 0), (10, 0), (10, 0), (13, 0), (10, 0), (10, 0), (10, 0), (10, 0), (10, 0), (10, 0),
  (13, 1), (10, 0), (10, 2), (10, 0), (10, 4), (10, 0), (10, 7), (10, 0), (13, 17), (10, 0), (13, 17), (10, 0), (10, 25), (10, 0),
  (7, 0), (7, 0), (7, 0), (7, 0), (7, 0), (11, 0), (7, 0), (7, 0), (7, 0), (7, 0), (7, 0), (7, 0), (7, 0), (7, 0),
  (7, 1), (7, 0), (11, 2), (7, 0), (7, 4), (7, 0), (7, 7), (7, 0), (7, 11), (7, 0), (11, 25), (7, 0), (11, 25), (7, 0),
  (5, 0), (5, 0), (5, 0), (8, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0), (5, 0),
  (8, 1), (5, 0), (5, 2), (5, 0), (8, 4), (5, 0), (5, 7), (5, 0), (5, 11), (5, 0), (5, 17), (5, 0), (5, 0), (5, 0)]

def var (v : V) := seeds.getD v.val 0
def pair (x y : V) (d : Bool) := if d then var x &&& var y else var x ||| var y
def sep (word : Nat) (p : P) (n : N) := word.testBit p.val = true ∧ word.testBit (21+n.val) = false
def unique (x : V) (p : P) (n : N) := ∀ u : V, sep (var u) p n → u = x

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma chart : ∀ (x y : V) (d : Bool), x ≠ y →
    let a := casesTable.getD (28*x.val + 2*y.val + (if d then 1 else 0)) (0,0)
    sep (var x) a.1 a.2 ∧ unique x a.1 a.2 ∧ ¬ sep (pair x y d) a.1 a.2 := by
  intro x
  fin_cases x <;> unfold unique sep <;> decide +kernel

lemma challenge (x y : V) (d : Bool) (xy : x ≠ y) : ∃ p : P, ∃ n : N,
    sep (var x) p n ∧ unique x p n ∧ ¬ sep (pair x y d) p n := by
  exact ⟨_,_,chart x y d xy⟩

lemma incident {x y z : V} {p : P} {n : N} {d : Bool} (pr : unique x p n) (h : sep (pair y z d) p n) :
    y = x ∨ z = x := by
  unfold pair sep at h
  cases d <;> simp only [ite_true,Bool.false_eq_true,ite_false,Nat.testBit_and,Nat.testBit_or] at h
  all_goals
    by_contra! absent
    have no1 : ¬ sep (var y) p n := fun hy => absent.1 (pr y hy)
    have no2 : ¬ sep (var z) p n := fun hz => absent.2 (pr z hz)
    unfold sep at no1 no2
    cases h1 : (var y).testBit p.val <;> cases h2 : (var y).testBit (21+n.val) <;>
      cases h3 : (var z).testBit p.val <;> cases h4 : (var z).testBit (21+n.val) <;> simp_all

abbrev Gate := V × V × Bool

def eval (g : Gate) := pair g.1 g.2.1 g.2.2
def touches (g : Gate) (x : V) := g.1 = x ∨ g.2.1 = x

lemma at_least_two (R : Finset V) (S : Finset Gate)
    (distinct : ∀ g ∈ S, g.1 ≠ g.2.1)
    (separates : ∀ p : P, ∀ n : N, (∃ r ∈ R, sep (var r) p n) ∨ ∃ g ∈ S, sep (eval g) p n)
    (x : V) (absent : x ∉ R) : ∃ g ∈ S, ∃ h ∈ S, g ≠ h ∧ touches g x ∧ touches h x := by
  have lift {p : P} {n : N} (pr : unique x p n) : ∃ g ∈ S, sep (eval g) p n ∧ touches g x := by
    rcases separates p n with ⟨r,hr,rs⟩ | ⟨g,hg,gs⟩
    · exact (absent (pr r rs ▸ hr)).elim
    · exact ⟨g,hg,gs,incident pr gs⟩
  have other : ∃ y : V, x ≠ y := by
    by_cases x0 : x = 0
    · exact ⟨1,by subst x; decide⟩
    · exact ⟨0,x0⟩
  obtain ⟨y,hy⟩ := other
  obtain ⟨p,n,_,pr,_⟩ := challenge x y false hy
  obtain ⟨g,hg,_,gx⟩ := lift pr
  have second : ∃ p : P, ∃ n : N, unique x p n ∧ ¬ sep (eval g) p n := by
    rcases gx with h | h
    · obtain ⟨p,n,_,u,v⟩ := challenge g.1 g.2.1 g.2.2 (distinct g hg)
      exact ⟨p,n,h ▸ u,v⟩
    · obtain ⟨p,n,_,u,v⟩ := challenge g.2.1 g.1 g.2.2 (Ne.symm (distinct g hg))
      have comm : pair g.1 g.2.1 g.2.2 = pair g.2.1 g.1 g.2.2 := by
        cases g.2.2 <;> simp [pair,Nat.and_comm,Nat.or_comm]
      exact ⟨p,n,h ▸ u,fun e => v (comm ▸ e)⟩
  obtain ⟨p',n',u,v⟩ := second
  obtain ⟨h,hh,hs,hx⟩ := lift u
  exact ⟨g,hg,h,hh,fun e => v (e.symm ▸ hs),gx,hx⟩

end PEqualNP.Outside.L_meta_3005.Private

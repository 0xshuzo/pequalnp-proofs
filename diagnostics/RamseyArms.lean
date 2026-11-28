import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9743.RamseyArms
abbrev I := Fin 5
abbrev Row := Fin 32
def bit (r : Row) (i : I) := r.val.testBit i.val
def separated (a b : Row) : Bool :=
  (List.finRange 5).all fun i => (List.finRange 5).all fun j =>
    decide (i=j) || !(bit a i == bit b i && bit a j == bit b j && bit a i == bit a j)
def avoid (chosen : List Row) : Nat → Bool
  | 0 => false
  | n+1 => (List.finRange 32).all fun r =>
      !(chosen.all fun a => separated r a) || avoid (r::chosen) n

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem noFive : avoid [] 5=true := by decide +kernel

def code (f : I→Bool) : Row := ⟨(Bool.toNat (f 0)+2*Bool.toNat (f 1)+
  4*Bool.toNat (f 2)+8*Bool.toNat (f 3)+16*Bool.toNat (f 4))%32,by omega⟩
theorem decode : ∀f : I→Bool, ∀i : I,bit (code f) i=f i := by decide +kernel

theorem step {xs : List Row} {n : Nat} (ok : avoid xs (n+1)=true) (x : Row)
    (sep : ∀a∈xs,separated x a=true) : avoid (x::xs) n=true := by
  have h := List.all_eq_true.mp ok x (by simp)
  have v : (xs.all fun a => separated x a)=true := List.all_eq_true.mpr sep
  simpa [v] using h

theorem obstruction (r : I→Row) (ok : ∀i j : I,i≠j → separated (r i) (r j)=true) : False := by
  have a:=step noFive (r 0) (by simp)
  have b:=step a (r 1) (by simpa using ok 1 0 (by decide))
  have c:=step b (r 2) (by simp [ok 2 0 (by decide),ok 2 1 (by decide)])
  have d:=step c (r 3) (by simp [ok 3 0 (by decide),ok 3 1 (by decide),ok 3 2 (by decide)])
  have e:=step d (r 4) (by simp [ok 4 0 (by decide),ok 4 1 (by decide),ok 4 2 (by decide),ok 4 3 (by decide)])
  exact Bool.noConfusion e

variable {P L : Type}
def NoSquare (g : P→L→Bool) : Prop := ∀p q l m,p≠q → l≠m →
  g p l=true → g p m=true → g q l=true → g q m=true → False

theorem fivePairs (g : P→L→Bool) (sq : NoSquare g)
    (p q : I→P) (l m : I→L) (ip : Function.Injective p) (iq : Function.Injective q)
    (il : Function.Injective l) (im : Function.Injective m)
    (cross : ∀i j,g (p i) (m j)=true ∨ g (q j) (l i)=true) : False := by
  let r (i : I) := code (fun j => g (p i) (m j))
  apply obstruction r
  intro i j ne
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro b _
  by_cases eq : a=b
  · simp [eq]
  · rw [show decide (a=b)=false by simp [eq]]
    change (!(bit (r i) a == bit (r j) a && bit (r i) b == bit (r j) b && bit (r i) a == bit (r i) b))=true
    simp only [r,decode]
    cases ia : g (p i) (m a) <;> cases ja : g (p j) (m a) <;>
      cases ib : g (p i) (m b) <;> cases jb : g (p j) (m b) <;> try decide
    · exact (sq (q a) (q b) (l i) (l j) (fun h => eq (iq h)) (fun h => ne (il h))
        ((cross i a).resolve_left (by simp [ia])) ((cross j a).resolve_left (by simp [ja]))
        ((cross i b).resolve_left (by simp [ib])) ((cross j b).resolve_left (by simp [jb]))).elim
    · exact (sq (p i) (p j) (m a) (m b) (fun h => ne (ip h)) (fun h => eq (im h))
        ia ib ja jb).elim

end PEqualNP.Outside.L_meta_9743.RamseyArms

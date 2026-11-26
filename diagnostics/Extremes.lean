import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9939.Extremes

abbrev Data := Fin 8 → Bool
def low (a : Fin 8) : Data := fun i => decide (i=a)
def high (a : Fin 8) : Data := fun i => decide (i≠a)
def grows (f : Fin 8 → Data → Bool) := ∀ a x y,
    (∀ i, x i = true → y i = true) → f a x = true → f a y = true

theorem sharp (f : Fin 8 → Data → Bool) (mono : grows f) :
    (∀ a d, f a d = d a) ↔ (∀ a, f a (low a) = true ∧ f a (high a) = false) := by
  constructor
  · intro h a
    simp [h,low,high]
  · intro check a d
    rcases check a with ⟨lo,hi⟩
    cases val : d a with
    | true =>
      apply mono a (low a) d _ lo
      intro i p
      have eq : i=a := of_decide_eq_true p
      simpa [eq] using val
    | false =>
      cases ev : f a d with
      | false => rfl
      | true =>
        have bad := mono a d (high a) (by
          intro i h
          apply decide_eq_true
          intro eq
          subst i
          rw [val] at h
          contradiction) ev
        rw [hi] at bad
        contradiction

def paired (a : Fin 8) (d : Data) (i : Fin 11) : Bool :=
  if i.val < 3 then a.val.testBit i.val else d (Fin.ofNat 8 (i.val-3))
def addr (x : Fin 11 → Bool) : Fin 8 := Fin.ofNat 8
  ((x 0).toNat + 2*(x 1).toNat + 4*(x 2).toNat)
def dataOf (x : Fin 11 → Bool) (j : Fin 8) := x ⟨3+j.val,by omega⟩
def named (x : Fin 11 → Bool) := (List.ofFn x).getD
  (3+(1*(x 0).toNat+2*(x 1).toNat+4*(x 2).toNat)) false

theorem recover (x : Fin 11 → Bool) : paired (addr x) (dataOf x)=x := by
  funext i
  fin_cases i <;> simp [paired,addr,dataOf] <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp_all [Bool.toNat]

theorem named_reads (x : Fin 11 → Bool) : named x = dataOf x (addr x) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [named,dataOf,addr,h0,h1,h2,List.getD_eq_getElem?_getD]

theorem all_inputs (f : (Fin 11 → Bool) → Bool)
    (mono : grows (fun a d => f (paired a d)))
    (tests : ∀a, f (paired a (low a))=true ∧ f (paired a (high a))=false) :
    ∀x,f x=named x := by
  intro x
  have h := (sharp _ mono).mpr tests (addr x) (dataOf x)
  rw [recover] at h
  exact h.trans (named_reads x).symm

end PEqualNP.Outside.L_meta_9939.Extremes

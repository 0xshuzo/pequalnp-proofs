import Mathlib
import PEqualNP.Outside.L_meta_4127

namespace Unique1479
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4127_aux

def legal (n : Nat) (C : Circuit) :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
       ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<n+j ∧ b<n+j

def rule (n : Nat) (C : Circuit) (v : List Bool) (d : Nat → Bool) :=
  ∀ j (g : Gate) a b, C.gates[j]?=some g → g.inputs=[a,b] →
    (g.op=.and → d (n+j)=((v.getD a false && d b) || (d a && v.getD b false))) ∧
    (g.op=.or → d (n+j)=(d a || d b))

theorem unique (n : Nat) (C : Circuit) (shape : legal n C)
    (v : List Bool) (d e : Nat → Bool) (base : ∀ i<n, d i=e i)
    (dr : rule n C v d) (er : rule n C v e) :
    ∀ i<n+C.size, d i=e i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases h : i<n
    · exact base i h
    let j := i-n
    have hj : j<C.gates.length := by change i<n+C.gates.length at hi; dsimp [j]; omega
    have pos : n+j=i := by dsimp [j]; omega
    have get := List.getElem?_eq_getElem (l:=C.gates) hj
    obtain ⟨op,a,b,inputs,_,ha,hb⟩ := shape j _ get
    have da := ih a (by omega) (by omega)
    have db := ih b (by omega) (by omega)
    have hd := dr j _ a b get inputs
    have he := er j _ a b get inputs
    rw [← pos]
    rcases op with hop|hop
    · rw [hd.1 hop,he.1 hop,da,db]
    · rw [hd.2 hop,he.2 hop,da,db]

theorem output_valid (n : Nat) (C : Circuit) (x : Fin n → Bool)
    (accepted : C.eval (List.ofFn x)=true) : C.output<n+C.size := by
  by_contra! outside
  have len := fd_len stB C.gates (List.ofFn x)
  rw [List.length_ofFn] at len
  change (fd stB C.gates (List.ofFn x)).getD C.output false=true at accepted
  change n+C.gates.length≤C.output at outside
  rw [List.getD_eq_default _ _ (by omega)] at accepted
  contradiction

theorem output_internal (n : Nat) (C : Circuit)
    (rejected : ∀ i : Fin n, C.eval (List.ofFn fun j : Fin n => decide (j=i))=false) :
    n≤C.output := by
  by_contra! raw
  let i : Fin n := ⟨C.output,raw⟩
  set x : Fin n → Bool := fun j => decide (j=i)
  have off := rejected i
  change (fd stB C.gates (List.ofFn x)).getD C.output false=false at off
  rw [fd_keep _ _ _ _ _ (by simpa using raw)] at off
  rw [List.getD_eq_getElem _ _ (by simpa using raw),List.getElem_ofFn] at off
  have on : x ⟨C.output,raw⟩=true := decide_eq_true rfl
  exact Bool.noConfusion (on.symm.trans off)

end Unique1479

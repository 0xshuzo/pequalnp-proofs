import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.CyclicHull
open PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
abbrev B := V → Bool
def board (a : Fin 5 → Nat) (x : V) : Bool := a x.1 == x.2.val
def first : B := board ![1,0,0,2,3]
def second : B := board ![2,0,0,3,1]
def endpoint (e : Fin 2) : Fin 5 := if e=0 then 1 else 2
def other (e : Fin 2) : Fin 5 := if e=0 then 2 else 1
def leftHole (t : Fin 3) : Nat := if t=1 then 3 else 2
def rightHole (t : Fin 3) : Nat := if t=0 then 3 else 1
def assignment (e : Fin 2) (t : Fin 3) (p : Fin 5) : Nat :=
  if p=0 then 4 else if p=endpoint e then t.val+1 else if p=other e then 0
  else if p=3 then leftHole t else rightHole t
def repair (e : Fin 2) (t : Fin 3) : B := board (assignment e t)

theorem uniqueFault : ∀ (e : Fin 2) (t : Fin 3),
    (∀ h : Fin 4,repair e t (0,h)=false) ∧
    (∀ p : Fin 5, p≠0 → ∃ h : Fin 4,repair e t (p,h)=true) ∧
    (∀ i j : Fin 5,∀ h : Fin 4,repair e t (i,h)=true → repair e t (j,h)=true → i=j) := by
  decide +kernel

theorem lookup : ∀ (e : Fin 2) (t : Fin 3) (v : V),
    repair e t v=first v ∨ repair e t v=second v ∨
    (v.1=endpoint e ∧ repair e t v=(t.val+1 == v.2.val)) := by
  decide +kernel

theorem merge (e : Fin 2) (t : Fin 3) (z : B)
    (one : ∀ h : Fin 4,z (endpoint e,h)=(t.val+1 == h.val))
    {W : Type} (coords : W → V) (C : Clause W)
    (a : ¬ ClauseSat (fun v => first (coords v)) C)
    (b : ¬ ClauseSat (fun v => second (coords v)) C)
    (c : ¬ ClauseSat (fun v => z (coords v)) C) :
    ¬ ClauseSat (fun v => repair e t (coords v)) C := by
  intro sat
  obtain ⟨l,hl,truth⟩ := sat
  rcases lookup e t (coords l.1) with ha|hb|⟨he,hv⟩
  · exact a ⟨l,hl,ha.symm.trans truth⟩
  · exact b ⟨l,hl,hb.symm.trans truth⟩
  · have hz : z (coords l.1)=(t.val+1 == (coords l.1).2.val) := by
      exact (congrArg (fun p => z (p,(coords l.1).2)) he).trans (one _)
    exact c ⟨l,hl,(hz.trans hv.symm).trans truth⟩

end PEqualNP.Outside.L_pcx_166.CyclicHull

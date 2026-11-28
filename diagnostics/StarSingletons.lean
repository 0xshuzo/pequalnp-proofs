import PEqualNP.Defs

namespace Research9755.StarSingletons

abbrev V := Fin 8
abbrev X := V → Bool
abbrev Wire := X → Bool

def singletonRow (i : V) : X := fun j => decide (j=i)
def coreEdges : List (V × V) :=
  [(0,1),(0,5),(1,2),(1,6),(2,7),(3,5),(3,6),(4,6),(4,7),(5,7)]
def K (x : X) := coreEdges.any fun p => x p.1 && x p.2
def a (x : X) := x 2 || x 3
def b (x : X) := x 0 || x 4
def edge (i j : V) := coreEdges.contains (i,j) || coreEdges.contains (j,i)
def bits (f : Wire) (i : V) := f (singletonRow i)
def BankSignal (f : Wire) : Prop :=
  (∀i,bits f i=false) ∨
  (∃j,∀i,bits f i=true → i=j) ∨
  (∃j,∀i,bits f i=true → edge j i=true)

theorem coreSilent : ∀i,K (singletonRow i)=false := by decide +kernel
theorem nonAdjacentA : ∀j,¬(edge j 2=true ∧ edge j 3=true) := by decide +kernel
theorem nonAdjacentB : ∀j,¬(edge j 0=true ∧ edge j 4=true) := by decide +kernel

theorem twoA {f : Wire} (h : ∀i,bits f i=bits a i) : ¬BankSignal f := by
  have p : bits f 2=true := (h 2).trans (by decide)
  have q : bits f 3=true := (h 3).trans (by decide)
  rintro (s|⟨j,s⟩|⟨j,s⟩)
  · exact Bool.noConfusion (p.symm.trans (s 2))
  · have no : (2 : V)≠3 := by decide
    exact no ((s 2 p).trans (s 3 q).symm)
  · exact nonAdjacentA j ⟨s 2 p,s 3 q⟩

theorem twoB {f : Wire} (h : ∀i,bits f i=bits b i) : ¬BankSignal f := by
  have p : bits f 0=true := (h 0).trans (by decide)
  have q : bits f 4=true := (h 4).trans (by decide)
  rintro (s|⟨j,s⟩|⟨j,s⟩)
  · exact Bool.noConfusion (p.symm.trans (s 0))
  · have no : (0 : V)≠4 := by decide
    exact no ((s 0 p).trans (s 4 q).symm)
  · exact nonAdjacentB j ⟨s 0 p,s 4 q⟩

theorem price {p q : Wire} (hp : ∀x,K x=false → p x=a x)
    (hq : ∀x,K x=false → q x=b x) :
    ¬BankSignal p ∧ ¬BankSignal q ∧ p≠q := by
  have pa : ∀i,bits p i=bits a i := fun i => hp _ (coreSilent i)
  have qb : ∀i,bits q i=bits b i := fun i => hq _ (coreSilent i)
  refine ⟨twoA pa,twoB qb,?_⟩
  intro e
  have h : bits a 2=bits b 2 := (pa 2).symm.trans ((congrArg (fun t : Wire => bits t 2) e).trans (qb 2))
  exact (by decide : bits a 2≠bits b 2) h

theorem oneExtraImpossible {S : List Wire} (all : ∀f∈S,BankSignal f)
    (extra p q : Wire) (hp : ∀x,K x=false → p x=a x)
    (hq : ∀x,K x=false → q x=b x)
    (pt : p∈extra::S) (qt : q∈extra::S) : False := by
  obtain ⟨np,nq,diff⟩ := price hp hq
  rcases List.mem_cons.mp pt with pe|ps
  · rcases List.mem_cons.mp qt with qe|qs
    · exact diff (pe.trans qe.symm)
    · exact nq (all _ qs)
  · exact np (all _ ps)
end Research9755.StarSingletons

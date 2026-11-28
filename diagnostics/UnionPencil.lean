import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007_UnionPencil
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] {k : Nat}

def legalLine (S : Fin k → Finset V) (l : Finset V) : Prop :=
  ∀p∉l, ∃i, p∈S i ∧ Disjoint (S i) l

def unionLine (S : Fin k → Finset V) (l : Finset V) : Prop :=
  ∃ I : Finset (Fin k), l=univ \ I.biUnion S

theorem legalLine_iff (S : Fin k → Finset V) (l : Finset V) :
    legalLine S l ↔ unionLine S l := by
  classical
  constructor
  · intro ok
    let I := (univ : Finset (Fin k)).filter (fun i => Disjoint (S i) l)
    refine ⟨I,?_⟩
    ext p
    simp only [mem_sdiff,mem_univ,true_and]
    constructor
    · intro hp hit
      obtain ⟨i,hi,occ⟩:=mem_biUnion.mp hit
      exact disjoint_left.mp (mem_filter.mp hi).2 occ hp
    · intro hn
      by_contra miss
      obtain ⟨i,occ,disj⟩:=ok p miss
      exact hn (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,disj⟩,occ⟩)
  · rintro ⟨I,rfl⟩ p hp
    have mem : p∈I.biUnion S := by simpa using hp
    obtain ⟨i,hi,occ⟩:=mem_biUnion.mp mem
    refine ⟨i,occ,disjoint_left.mpr ?_⟩
    intro q qin out
    exact (mem_sdiff.mp out).2 (mem_biUnion.mpr ⟨i,hi,qin⟩)

def oneMore (S : Fin k → Finset V) (X l : Finset V) : Prop :=
  ∀p∉l, (∃i,p∈S i ∧ Disjoint (S i) l) ∨ (p∈X ∧ Disjoint X l)

theorem through_added {S : Fin k → Finset V} {X l : Finset V} {p : V}
    (hx : p∈X) (hl : p∈l) (h : oneMore S X l) : unionLine S l := by
  apply (legalLine_iff S l).1
  intro q hq
  rcases h q hq with ans|extra
  · exact ans
  · exact False.elim (disjoint_left.mp extra.2 hx hl)

def pencilCandidate (S : Fin k → Finset V) (p : V) : Prop :=
  ∃ L : Fin 6 → Finset V, (∀i,p∈L i ∧ (L i).card=6 ∧ unionLine S (L i)) ∧
    (∀q,q≠p → ∃! i,q∈L i)

theorem row_can_be_added {S : Fin k → Finset V} {X : Finset V} {p : V} (hx : p∈X)
    (L : Fin 6 → Finset V) (on : ∀i,p∈L i) (size : ∀i,(L i).card=6)
    (parallel : ∀q,q≠p → ∃! i,q∈L i) (fit : ∀i,oneMore S X (L i)) :
    pencilCandidate S p :=
  ⟨L,fun i=>⟨on i,size i,through_added hx (on i) (fit i)⟩,parallel⟩

def canRepair (S : Fin k → Finset V) (X l : Finset V) : Prop :=
  legalLine S l ∨ (Disjoint X l ∧ ∀q∉l, (∀i,Disjoint (S i) l → q∉S i) → q∈X)

theorem oneMore_iff (S : Fin k → Finset V) (X l : Finset V) :
    oneMore S X l ↔ canRepair S X l := by
  classical
  constructor
  · intro h
    by_cases d : Disjoint X l
    · right
      refine ⟨d,?_⟩
      intro q hq wait
      rcases h q hq with ⟨i,occ,dis⟩|⟨occ,_⟩
      · exact False.elim (wait i dis occ)
      · exact occ
    · exact Or.inl (fun q hq=>(h q hq).resolve_right (fun bad=>d bad.2))
  · rintro (base|⟨dis,rem⟩) q hq
    · exact Or.inl (base q hq)
    · by_cases own : ∃i,q∈S i ∧ Disjoint (S i) l
      · exact Or.inl own
      · exact Or.inr ⟨rem q hq (fun i d qi=>own ⟨i,qi,d⟩),dis⟩

end PEqualNP.Outside.L_meta_10007_UnionPencil

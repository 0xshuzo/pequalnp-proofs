import PEqualNP.Defs

namespace Research10009.Secants
abbrev V := Fin 31
abbrev K := Fin 6
abbrev Box := Finset V × Finset V
def rows : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def blank (i j : V) := !((rows.getD i.val 0).testBit j.val)
def a (i : K) : V := (#[12,16,18,21,28,29] : Array V)[i.val]!
def l (i j : K) : V := (#[19,11,7,16,1,18,11,15,22,20,23,5,7,22,13,25,17,24,16,20,25,10,27,28,1,23,17,27,3,4,18,5,24,28,4,2] : Array V)[6*i.val+j.val]!
theorem geometry : ∀p q r : K,p≠q → p≠r →
    blank (a p) (l q r)=true ∧ blank (a q) (l q r)=false ∧ blank (a r) (l q r)=false := by decide +kernel
theorem separateRows : ∀p q : V,p≠q → ∃ j : V,blank p j=true ∧ blank q j=false := by decide +kernel
def Legal (L : List Box) := ∀ b∈L,∀ i∈b.1,∀ j∈b.2,blank i j=true
def Covers (L : List Box) := ∀ i j : V,blank i j=true → ∃ b∈L,i∈b.1 ∧ j∈b.2
theorem twoBlockers {L : List Box} (ok : Legal L) (cv : Covers L) (p q r : K)
    (pq : p≠q) (pr : p≠r) : ∃ b∈L,a p∈b.1 ∧ a q∉b.1 ∧ a r∉b.1 := by
  obtain ⟨cp,cq,cr⟩ := geometry p q r pq pr
  obtain ⟨b,mem,ip,jp⟩ := cv _ _ cp
  refine ⟨b,mem,ip,?_,?_⟩
  · intro iq
    exact Bool.noConfusion ((ok b mem _ iq _ jp).symm.trans cq)
  · intro ir
    exact Bool.noConfusion ((ok b mem _ ir _ jp).symm.trans cr)
def Private (p : K) (b : Box) := a p∈b.1 ∧ ∀ q : K,q≠p → a q∉b.1
theorem twoSlots {L : List Box} (ok : Legal L) (cv : Covers L) (p : K) (b d : Box)
    (ab : a p∈b.1) (ad : a p∈d.1)
    (only : ∀t∈L,a p∈t.1 → t=b ∨ t=d) : Private p b ∨ Private p d := by
  classical
  by_contra bad
  have nb : ¬ (∀q : K,q≠p → a q∉b.1) := fun h => bad (Or.inl ⟨ab,h⟩)
  have nd : ¬ (∀q : K,q≠p → a q∉d.1) := fun h => bad (Or.inr ⟨ad,h⟩)
  push_neg at nb nd
  obtain ⟨q,nq,bq⟩ := nb
  obtain ⟨r,nr,dr⟩ := nd
  obtain ⟨t,ht,tp,tq,tr⟩ := twoBlockers ok cv p q r nq.symm nr.symm
  rcases only t ht tp with eq|eq
  · exact tq (eq.symm ▸ bq)
  · exact tr (eq.symm ▸ dr)
theorem forcedStar {L : List Box} (ok : Legal L) (cv : Covers L) (p : V) (b : Box)
    (hb : b∈L) (inrow : p∈b.1) (only : ∀t∈L,p∈t.1 → t=b) :
    b.1={p} ∧ (∀j : V,j∈b.2 ↔ blank p j=true) := by
  have columns (j : V) (hp : blank p j=true) : j∈b.2 := by
    obtain ⟨t,ht,tp,tj⟩ := cv _ _ hp
    exact only t ht tp ▸ tj
  constructor
  · ext q
    simp only [Finset.mem_singleton]
    constructor
    · intro hq
      by_contra neq
      obtain ⟨j,pj,qj⟩ := separateRows p q (Ne.symm neq)
      exact Bool.noConfusion ((ok b hb q hq j (columns j pj)).symm.trans qj)
    · rintro rfl
      exact inrow
  · intro j
    exact ⟨fun hj => ok b hb _ inrow _ hj,columns j⟩
end Research10009.Secants

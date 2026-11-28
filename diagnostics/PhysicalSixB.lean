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

namespace Research10009.SixTags
abbrev K := Fin 6
abbrev F := K → Bool
def Small (w : F) := ∃a b : K, ∀k : K,w k=true → k=a ∨ k=b
instance (w : F) : Decidable (Small w) := by unfold Small; infer_instance
def holes (w : F) (i : Fin 3) : K :=
  ((List.finRange 6).filter (fun k => !w k)).getD i.val 0
theorem counts : ∀w : F, Small w ∨ ∀k : K,w k=false → ∃i : Fin 3,holes w i=k := by decide +kernel
def tag (v : Fin 3 → Bool) : Fin 3 :=
  let n := (if v 0 then 1 else 0) + (if v 1 then 2 else 0) + (if v 2 then 4 else 0)
  (#[0,0,1,0,2,2,1,0] : Array (Fin 3))[n]!
theorem chain : ∀u v : Fin 3 → Bool,tag u=tag v →
    (∀i,u i=true → v i=true) ∨ (∀i,v i=true → u i=true) := by decide +kernel
def other (p : K) (i : Fin 4) : K :=
  if h : i.val<p.val then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
theorem different : ∀p : K,∀i : Fin 4,other p i≠p := by decide +kernel
theorem distinct : ∀p : K,∀i j : Fin 4,other p i=other p j → i=j := by decide +kernel
def Strong (W : K → F) := ∀p q r : K,p≠q → p≠r → ∃i : K,
    W p i=true ∧ W q i=false ∧ W r i=false

theorem low (W : K→F) (ok : Strong W) (p : K) : Small (W p) := by
  rcases counts (W p) with yes|few
  · exact yes
  · let cut (i : Fin 4) (k : Fin 3) := W (other p i) (holes (W p) k)
    let code (i : Fin 4) := tag (cut i)
    have inj : Function.Injective code := by
      intro i j eq
      by_contra bad
      have ne : other p i≠other p j := fun h => bad (distinct p i j h)
      have diff (a b : Fin 4) (hne : other p a≠other p b) :
          ¬∀k : Fin 3,cut a k=true → cut b k=true := by
        intro le
        obtain ⟨t,wa,wp,wb⟩ := ok (other p a) p (other p b) (different p a) hne
        obtain ⟨k,hk⟩ := few t wp
        have fa : cut a k=true := by simpa [cut,hk] using wa
        have fb : cut b k=false := by simpa [cut,hk] using wb
        exact Bool.noConfusion ((le k fa).symm.trans fb)
      rcases chain (cut i) (cut j) eq with d|d
      · exact diff i j ne d
      · exact diff j i ne.symm d
    have void := Fintype.card_le_of_injective code inj
    simp at void

theorem own (W : K→F) (ok : Strong W) (p : K) :
    ∃k : K,W p k=true ∧ ∀q : K,q≠p → W q k=false := by
  classical
  by_contra none
  have use (k : K) : ∃q : K,q≠p ∧ (W p k=true → W q k=true) := by
    by_cases h : W p k=true
    · by_contra bad
      apply none
      refine ⟨k,h,?_⟩
      intro q nq
      cases eq : W q k with
      | false => rfl
      | true => exact (bad ⟨q,nq,fun _ => eq⟩).elim
    · exact ⟨other p 0,different p 0,fun z => (h z).elim⟩
  obtain ⟨a,b,h⟩ := low W ok p
  obtain ⟨q,nq,cq⟩ := use a
  obtain ⟨r,nr,cr⟩ := use b
  obtain ⟨i,wi,wq,wr⟩ := ok p q r nq.symm nr.symm
  rcases h i wi with e|e
  · subst i
    exact Bool.noConfusion ((cq wi).symm.trans wq)
  · subst i
    exact Bool.noConfusion ((cr wi).symm.trans wr)

theorem permutation (W : K→F) (ok : Strong W) :
    ∃j : K→K,Function.Bijective j ∧ ∀p i,W p i=true ↔ i=j p := by
  classical
  choose j has uniq using own W ok
  have inj : Function.Injective j := by
    intro p q eq
    by_contra ne
    have no := uniq p q (Ne.symm ne)
    rw [eq,has q] at no
    contradiction
  have sur := Finite.surjective_of_injective inj
  refine ⟨j,⟨inj,sur⟩,?_⟩
  intro p i
  constructor
  · intro yes
    obtain ⟨q,rfl⟩:=sur i
    by_contra ne
    have nq : p≠q := fun h => ne (h ▸ rfl)
    exact Bool.noConfusion (yes.symm.trans (uniq q p nq))
  · rintro rfl
    exact has p
end Research10009.SixTags

namespace Research10009.PhysicalSix
open Research10009.Secants
theorem forcedSix {L : List Box} (ok : Legal L) (cv : Covers L)
    (slots : Fin 6 → Box) (exh : ∀b∈L,(∃p : K,a p∈b.1) → ∃j,b=slots j) :
    ∀p : K,∃b∈L,b.1={a p} ∧ (∀c : V,c∈b.2 ↔ blank (a p) c=true) := by
  classical
  let W (p j : K) := decide (a p∈(slots j).1)
  have strong : Research10009.SixTags.Strong W := by
    intro p q r pq pr
    obtain ⟨b,mem,ap,aq,ar⟩ := twoBlockers ok cv p q r pq pr
    obtain ⟨i,rfl⟩ := exh b mem ⟨p,ap⟩
    exact ⟨i,by simpa [W] using ap,by simpa [W] using aq,by simpa [W] using ar⟩
  obtain ⟨j,_,which⟩ := Research10009.SixTags.permutation W strong
  intro p
  have only (t : Box) (ht : t∈L) (pt : a p∈t.1) : t=slots (j p) := by
    obtain ⟨i,eq⟩ := exh t ht ⟨p,pt⟩
    rw [eq] at pt
    have h : W p i=true := by simpa [W] using pt
    exact eq.trans (congrArg slots ((which p i).mp h))
  let q := Research10009.SixTags.other p 0
  have diff : p≠q := Ne.symm (Research10009.SixTags.different p 0)
  obtain ⟨b,hb,ap,_,_⟩ := twoBlockers ok cv p q q diff diff
  exact ⟨b,hb,forcedStar ok cv _ b hb ap (fun t ht hp => (only t ht hp).trans (only b hb ap).symm)⟩
end Research10009.PhysicalSix

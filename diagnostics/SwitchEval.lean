import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset

structure Frame (V U : Type) where
  form : Finset V → Finset U
  flip : Finset V → Bool

variable {V U : Type} [DecidableEq V] [DecidableEq U]
def imageEq (T : Frame V U) (q : LinEq V) : LinEq U :=
  (T.form q.1, if T.flip q.1 then !q.2 else q.2)
def top (T : Frame V U) (C : LinClause V) : Prop :=
  (∅, false) ∈ C.image (imageEq T)
def body (T : Frame V U) (C : LinClause V) : LinClause U :=
  (C.image (imageEq T)).erase (∅,true)

theorem other {T : Frame V U} {C R : LinClause V} {q : LinEq V} (inc : C.erase q ⊆ R) :
    (body T C).erase (imageEq T q) ⊆ body T R := by
  intro w hw
  obtain ⟨different,hw⟩ := mem_erase.mp hw
  obtain ⟨nonfalse,hc⟩ := mem_erase.mp hw
  obtain ⟨z,hz,ez⟩ := mem_image.mp hc
  have neq : z ≠ q := fun eq => different (ez.symm.trans (congrArg (imageEq T) eq))
  exact mem_erase.mpr ⟨nonfalse,mem_image.mpr ⟨z,inc (mem_erase.mpr ⟨neq,hz⟩),ez⟩⟩

theorem topPivot {T : Frame V U} {C R : LinClause V} {q : LinEq V} (inc : C.erase q ⊆ R)
    (c : top T C) (r : ¬top T R) : imageEq T q=(∅,false) := by
  obtain ⟨z,hz,ez⟩ := mem_image.mp c
  by_cases e : z=q
  · simpa only [← e] using ez
  · exact False.elim (r (mem_image.mpr ⟨z,inc (mem_erase.mpr ⟨e,hz⟩),ez⟩))

def Options (A B R : LinClause U) : Prop :=
  A⊆R ∨ B⊆R ∨ ∃ E, E⊆R ∧ (IsLinResolvent A B E ∨ IsLinResolvent B A E)

theorem splitOptions (T : Frame V U) {C D R : LinClause V}
    (res : IsLinResolvent C D R) (A B : LinClause U) (ac : A⊆body T C) (bd : B⊆body T D) :
    Options A B (body T R) := by
  obtain ⟨f,_,_,rfl⟩ := res
  let R := C.erase (f,false) ∪ D.erase (f,true)
  have left := other (T:=T) (show C.erase (f,false) ⊆ R from subset_union_left)
  have right := other (T:=T) (show D.erase (f,true) ⊆ R from subset_union_right)
  let p := imageEq T (f,false)
  let q := imageEq T (f,true)
  change Options A B (body T R)
  unfold Options
  by_cases ha : p∈A
  · by_cases hb : q∈B
    · have e : A.erase p ∪ B.erase q ⊆ body T R := by
        apply union_subset
        · intro x hx
          exact left (mem_erase.mpr ⟨(mem_erase.mp hx).1,ac (mem_erase.mp hx).2⟩)
        · intro x hx
          exact right (mem_erase.mpr ⟨(mem_erase.mp hx).1,bd (mem_erase.mp hx).2⟩)
      refine Or.inr (Or.inr ⟨_,e,?_⟩)
      cases h : T.flip f with
      | false =>
        left
        exact ⟨T.form f,by simpa [p,imageEq,h] using ha,by simpa [q,imageEq,h] using hb,
          by simp [p,q,imageEq,h]⟩
      | true =>
        right
        exact ⟨T.form f,by simpa [q,imageEq,h] using hb,by simpa [p,imageEq,h] using ha,
          by simp [p,q,imageEq,h,union_comm]⟩
    · right; left
      intro x hx
      exact right (mem_erase.mpr ⟨fun eq => hb (by change imageEq T (f,true) ∈ B; simpa only [eq] using hx),bd hx⟩)
  · left
    intro x hx
    exact left (mem_erase.mpr ⟨fun eq => ha (by change imageEq T (f,false) ∈ A; simpa only [eq] using hx),ac hx⟩)

theorem dropParent (T : Frame V U) {C D R : LinClause V} (res : IsLinResolvent C D R)
    (nt : ¬top T R) :
    (top T C → ¬top T D ∧ body T D ⊆ body T R) ∧
    (top T D → ¬top T C ∧ body T C ⊆ body T R) := by
  obtain ⟨f,_,_,rfl⟩ := res
  let R := C.erase (f,false) ∪ D.erase (f,true)
  have cl := topPivot (T:=T) (show C.erase (f,false) ⊆ R from subset_union_left)
  have dr := topPivot (T:=T) (show D.erase (f,true) ⊆ R from subset_union_right)
  have lc := other (T:=T) (show C.erase (f,false) ⊆ R from subset_union_left)
  have rd := other (T:=T) (show D.erase (f,true) ⊆ R from subset_union_right)
  constructor
  · intro tc
    have eq := cl tc nt
    have opp : imageEq T (f,true) = (∅,true) := by
      cases h : T.flip f <;> simp [imageEq,h] at eq ⊢ <;> simp [eq]
    have impossible (h : top T D) : False := by
      have bad := congrArg Prod.snd ((dr h nt).symm.trans opp)
      exact Bool.noConfusion bad
    refine ⟨impossible,?_⟩
    intro x hx
    exact rd (mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (e.trans opp),hx⟩)
  · intro td
    have eq := dr td nt
    have opp : imageEq T (f,false) = (∅,true) := by
      cases h : T.flip f <;> simp [imageEq,h] at eq ⊢ <;> simp [eq]
    have impossible (h : top T C) : False := by
      have bad := congrArg Prod.snd ((cl h nt).symm.trans opp)
      exact Bool.noConfusion bad
    refine ⟨impossible,?_⟩
    intro x hx
    exact lc (mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (e.trans opp),hx⟩)
end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 5 × Fin 4
abbrev Little := Fin 4 × Fin 3
def emb (p : Fin 5) (h : Fin 4) (z : Little) : Big := (p.succAbove z.1,h.succAbove z.2)
theorem injT : ∀ p h (u v : Little), emb p h u=emb p h v → u=v := by decide +kernel
theorem awayT : ∀ p h (u : Little), emb p h u≠(p,h) := by decide +kernel
def face (p : Fin 5) (h : Fin 4) : Frame Big Little :=
  ⟨fun f => univ.filter fun z => emb p h z∈f, fun f => decide ((p,h)∈f)⟩
def extend (p : Fin 5) (h : Fin 4) (x : Little→Bool) (z : Big) :=
  decide (z=(p,h) ∨ ∃ u, emb p h u=z ∧ x u=true)

theorem faceEval (p : Fin 5) (h : Fin 4) (x : Little→Bool) (q : LinEq Big) :
    LinEqSat (extend p h x) q ↔ LinEqSat x (imageEq (face p h) q) := by
  classical
  rcases q with ⟨f,b⟩
  let K := ((face p h).form f).filter fun z => x z=true
  let I := K.image (emb p h)
  have ik : I.card=K.card := card_image_of_injective _ (injT p h)
  have memI (z : Big) : z∈I ↔ ∃ u, emb p h u=z ∧ emb p h u∈f ∧ x u=true := by
    change z∈K.image (emb p h) ↔ _
    simp only [mem_image, K, mem_filter, face, mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,e⟩
      exact ⟨u,e,hu⟩
    · rintro ⟨u,e,hu⟩
      exact ⟨u,hu,e⟩
  have off : (p,h)∉I := fun hh => by obtain ⟨u,e,_⟩ := (memI _).1 hh; exact awayT p h u e
  let D := f.filter fun z => extend p h x z=true
  have memD (z : Big) : z∈D ↔ z∈f ∧ (z=(p,h) ∨ ∃ u, emb p h u=z ∧ x u=true) := by
    simp [D,extend]
  by_cases pin : (p,h)∈f
  · have eq : D=insert (p,h) I := by
      ext z
      rw [memD,mem_insert,memI]
      constructor
      · rintro ⟨hz,e|⟨u,e,on⟩⟩
        · exact Or.inl e
        · exact Or.inr ⟨u,e,by simpa only [e] using hz,on⟩
      · rintro (e|⟨u,e,hu,on⟩)
        · exact ⟨by simpa only [e] using pin,Or.inl e⟩
        · exact ⟨by simpa only [e] using hu,Or.inr ⟨u,e,on⟩⟩
    have cards : D.card=K.card+1 := by rw [eq,card_insert_of_notMem off,ik]
    change (Odd D.card ↔ b=true) ↔ (Odd K.card ↔ (if decide ((p,h)∈f) then !b else b)=true)
    rw [cards]
    cases b <;> simp [pin,Nat.odd_iff] <;> omega
  · have eq : D=I := by
      ext z
      rw [memD,memI]
      constructor
      · rintro ⟨hz,e|⟨u,e,on⟩⟩
        · exact False.elim (pin (by simpa only [e] using hz))
        · exact ⟨u,e,by simpa only [e] using hz,on⟩
      · rintro ⟨u,e,hu,on⟩
        exact ⟨by simpa only [e] using hu,Or.inr ⟨u,e,on⟩⟩
    change (Odd D.card ↔ b=true) ↔ (Odd K.card ↔ (if decide ((p,h)∈f) then !b else b)=true)
    simp [eq,ik,pin]

end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
variable {U : Type} [DecidableEq U]
def parityOn (s : Finset U) (x : U→Bool) : Bool :=
  decide (Odd ((s.filter fun u=>x u=true).card))
theorem parityEq (s : Finset U) (b : Bool) (x : U→Bool) :
    LinEqSat x (s,b) ↔ parityOn s x=b := by cases b <;> simp [parityOn,LinEqSat]
theorem parityAdd (s : Finset U) (u : U) (hu : u∉s) (x : U→Bool) :
    parityOn (insert u s) x = (parityOn s x ^^ x u) := by
  cases h : x u
  · simp [parityOn,filter_insert,h]
  · have off : u∉s.filter (fun v=>x v=true) := fun m=>hu (mem_filter.mp m).1
    by_cases od : Odd ((s.filter fun v=>x v=true).card)
    · have no : ¬Odd ((s.filter fun v=>x v=true).card+1) := by
        rw [Nat.odd_iff] at od ⊢; omega
      simp [parityOn,filter_insert,h,card_insert_of_notMem off,od,no]
    · have yes : Odd ((s.filter fun v=>x v=true).card+1) := by
        rw [Nat.odd_iff] at od ⊢; omega
      simp [parityOn,filter_insert,h,card_insert_of_notMem off,od,yes]
theorem parityXor (s : Finset U) (x y : U→Bool) :
    parityOn s (fun u=>x u ^^ y u) = (parityOn s x ^^ parityOn s y) := by
  induction s using Finset.induction_on with
  | empty => simp [parityOn]
  | @insert a s h ih =>
    rw [parityAdd _ _ h,parityAdd _ _ h,parityAdd _ _ h,ih]
    cases parityOn s x <;> cases parityOn s y <;> cases x a <;> cases y a <;> rfl
def toggled (f : Finset U) (u : U) := if u∈f then f.erase u else insert u f
theorem parityToggled (s : Finset U) (u : U) (x : U→Bool) :
    parityOn (toggled s u) x= (parityOn s x ^^ x u) := by
  by_cases m : u∈s
  · have a := parityAdd (s.erase u) u (notMem_erase u s) x
    rw [insert_erase m] at a
    simp only [toggled,if_pos m,a]
    cases parityOn (s.erase u) x <;> cases x u <;> rfl
  · simpa [toggled,m] using parityAdd s u m x
def sectionMask (p : Fin 5) (h : Fin 4) (u : Little) (z : Big) := decide (
    (z.1=p ∨ z.1=(emb p h u).1) ∧ (z.2=h ∨ z.2=(emb p h u).2))
def switched (p : Fin 5) (h : Fin 4) (u : Little) : Frame Big Little :=
  ⟨fun f=>if parityOn f (sectionMask p h u) then toggled ((face p h).form f) u else (face p h).form f,
    (face p h).flip⟩
def swLift (p : Fin 5) (h : Fin 4) (u : Little) (x : Little→Bool) (z : Big) :=
  extend p h x z ^^ (x u && sectionMask p h u z)
theorem switchEval (p : Fin 5) (h : Fin 4) (u : Little) (x : Little→Bool) (q : LinEq Big) :
    LinEqSat (swLift p h u x) q ↔ LinEqSat x (imageEq (switched p h u) q) := by
  rcases q with ⟨f,b⟩
  have base := faceEval p h x (f,b)
  change LinEqSat _ (f,b) ↔ LinEqSat _ ((face p h).form f,if (face p h).flip f then !b else b) at base
  rw [parityEq,parityEq] at base
  change LinEqSat _ (f,b) ↔ LinEqSat _ ((switched p h u).form f,if (face p h).flip f then !b else b)
  rw [parityEq,parityEq]
  change parityOn f (fun z=>extend p h x z ^^ (x u && sectionMask p h u z))=b ↔ _
  rw [parityXor]
  cases ux : x u with
  | false =>
    have zero : parityOn f (fun _=>false)=false := by simp [parityOn]
    cases ck : parityOn f (sectionMask p h u) <;> simpa [switched,ck,parityToggled,ux,zero] using base
  | true =>
    cases ck : parityOn f (sectionMask p h u)
    · simpa [switched,ck,ux] using base
    · simp only [Bool.true_and,ck,switched,if_true,parityToggled,ux]
      cases parityOn f (extend p h x) <;> cases parityOn ((face p h).form f) x <;>
        cases b <;> cases (face p h).flip f <;> simp_all
end PEqualNP.Outside.L_pcx_178.Restrict

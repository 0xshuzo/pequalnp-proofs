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
variable {V U : Type} [DecidableEq V] [DecidableEq U]

instance topDec (T : Frame V U) (C : LinClause V) : Decidable (top T C) :=
  inferInstanceAs (Decidable ((∅,false) ∈ C.image (imageEq T)))

theorem body_semantic (T : Frame V U) (lift : (U→Bool) → V→Bool)
    (eval : ∀ x q, LinEqSat (lift x) q ↔ LinEqSat x (imageEq T q))
    (x : U→Bool) (C : LinClause V) : LinClauseSat x (body T C) ↔ LinClauseSat (lift x) C := by
  constructor
  · rintro ⟨w,hw,sw⟩
    obtain ⟨q,hq,eq⟩ := mem_image.mp (mem_erase.mp hw).2
    exact ⟨q,hq,(eval x q).2 (by simpa only [eq] using sw)⟩
  · rintro ⟨q,hq,sq⟩
    have on := (eval x q).1 sq
    refine ⟨_,mem_erase.mpr ⟨?_,mem_image_of_mem _ hq⟩,on⟩
    intro e
    rw [e] at on
    simpa [LinEqSat] using on

theorem topOn (T : Frame V U) {C : LinClause V} (h : top T C) (x : U→Bool) :
    LinClauseSat x (body T C) :=
  ⟨(∅,false),mem_erase.mpr ⟨by simp,h⟩,by simp [LinEqSat]⟩

end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
variable {V U : Type} [DecidableEq V] [DecidableEq U]
def rev (q : LinEq U) : LinEq U := (q.1,!q.2)
theorem revRev (q : LinEq U) : rev (rev q)=q := by rcases q with ⟨a,b⟩; cases b <;> rfl
def marked (B : LinClause U) : Prop := (∅,false)∈B ∨ ∃q∈B, rev q∈B
instance decMarked (B : LinClause U) : Decidable (marked B) :=
  inferInstanceAs (Decidable ((∅,false)∈B ∨ ∃q∈B, rev q∈B))
theorem monoMarked {B D : LinClause U} (le : B⊆D) : marked B → marked D := by
  rintro (c|⟨q,m,n⟩)
  · exact Or.inl (le c)
  · exact Or.inr ⟨q,le m,le n⟩
theorem markedSat {B : LinClause U} (h : marked B) (x : U→Bool) : LinClauseSat x B := by
  rcases h with c|⟨⟨s,b⟩,m,n⟩
  · exact ⟨_,c,by simp [LinEqSat]⟩
  · by_cases a : Odd (s.filter (fun v => x v=true)).card
    · cases b
      · exact ⟨_,n,by simpa [LinEqSat,rev] using a⟩
      · exact ⟨_,m,by simpa [LinEqSat] using a⟩
    · cases b
      · exact ⟨_,m,by simpa [LinEqSat] using a⟩
      · exact ⟨_,n,by simpa [LinEqSat,rev] using a⟩

theorem oppositeMember {B R : LinClause U} {p : LinEq U}
    (cut : B.erase p ⊆ R) (cl : ¬marked R) (m : marked B) :
    p=(∅,false) ∨ rev p∈R := by
  have leftover {q} (mem : q∈B) (different : q≠p) : q∈R := cut (mem_erase.mpr ⟨different,mem⟩)
  rcases m with con|⟨q,on,off⟩
  · by_cases eq : (∅,false)=p
    · exact Or.inl eq.symm
    · exact False.elim (cl (Or.inl (leftover con eq)))
  · have noEq (v : LinEq U) : rev v ≠ v := by rcases v with ⟨s,b⟩; cases b <;> simp [rev]
    by_cases qp : q=p
    · subst p
      exact Or.inr (leftover off (noEq q))
    · by_cases op : rev q=p
      · have eq : rev p=q := by rw [←op,revRev]
        exact Or.inr (eq.symm ▸ leftover on qp)
      · exact False.elim (cl (Or.inr ⟨q,leftover on qp,leftover off op⟩))

theorem markedForward {B D R : LinClause U} {p : LinEq U}
    (l : B.erase p⊆R) (r : D.erase (rev p)⊆R) (nonFalse : (∅,true)∉D)
    (cl : ¬marked R) (mb : marked B) : ¬marked D ∧ D⊆R := by
  have inc : D⊆R := by
    intro q hq
    by_cases e : q=rev p
    · subst q
      rcases oppositeMember l cl mb with a|a
      · subst p
        exact False.elim (nonFalse hq)
      · exact a
    · exact r (mem_erase.mpr ⟨e,hq⟩)
  exact ⟨fun h => cl (monoMarked inc h),inc⟩
def dirty (T : Frame V U) (C : LinClause V) := marked (body T C)
instance decDirty (T : Frame V U) (C : LinClause V) : Decidable (dirty T C) := decMarked _
theorem dirtyDrop (T : Frame V U) {C D R : LinClause V} (res : IsLinResolvent C D R)
    (nt : ¬dirty T R) :
    (dirty T C → ¬dirty T D ∧ body T D⊆body T R) ∧
    (dirty T D → ¬dirty T C ∧ body T C⊆body T R) := by
  obtain ⟨f,_,_,rfl⟩:=res
  let R := C.erase (f,false) ∪ D.erase (f,true)
  let p := imageEq T (f,false)
  have op : imageEq T (f,true)=rev p := by cases e : T.flip f <;> simp [p,rev,imageEq,e]
  have l := other (T:=T) (show C.erase (f,false) ⊆ R from subset_union_left)
  have r := other (T:=T) (show D.erase (f,true) ⊆ R from subset_union_right)
  change (body T C).erase p⊆body T R at l
  rw [op] at r
  constructor
  · exact markedForward l r (by simp [body]) nt
  · apply markedForward r _ (by simp [body]) nt
    simpa only [revRev] using l
end PEqualNP.Outside.L_pcx_178.Restrict

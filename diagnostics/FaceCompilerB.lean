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

inductive Charged (T : Frame V U) (F : Set (LinClause V)) : List (LinClause V) → Nat → Prop
| nil : Charged T F [] 0
| ax {π n A} : Charged T F π n → A ∈ F →
    Charged T F (A::π) (n + if top T A then 0 else 1)
| weak {π n C A} : Charged T F π n → C∈π → (∀ a, LinClauseSat a C → LinClauseSat a A) →
    Charged T F (A::π) (n + if top T A then 0 else 1)
| res {π n C D A} : Charged T F π n → C∈π → D∈π → IsLinResolvent C D A →
    Charged T F (A::π) (n + if top T A ∨ top T C ∨ top T D then 0 else 1)

theorem chooseCharge (T : Frame V U) {F : Set (LinClause V)} {π} (der : IsLinDerivation F π) :
    ∃ n≤π.length, Charged T F π n := by
  induction der with
  | nil => exact ⟨0,by simp,.nil⟩
  | @ax π A d ha ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n+(if top T A then 0 else 1),by simp only [List.length_cons]; split <;> omega,.ax h ha⟩
  | @weak π C A d hc w ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n+(if top T A then 0 else 1),by simp only [List.length_cons]; split <;> omega,.weak h hc w⟩
  | @res π C D A d hc hd rule ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n+(if top T A ∨ top T C ∨ top T D then 0 else 1),by simp only [List.length_cons]; split <;> omega,.res h hc hd rule⟩

def Reps (T : Frame V U) (π : List (LinClause V)) (ρ : List (LinClause U)) : Prop :=
  ∀ C∈π, ¬top T C → ∃ A∈ρ, A⊆body T C

private theorem skip {T : Frame V U} {π ρ} (old : Reps T π ρ) {C}
    (new : ¬top T C → ∃ A∈ρ, A⊆body T C) : Reps T (C::π) ρ := by
  intro D hd
  rcases List.mem_cons.mp hd with rfl|tail
  · exact new
  · exact old D tail

private theorem added {T : Frame V U} {π ρ} (old : Reps T π ρ) {C} {A : LinClause U}
    (sub : A⊆body T C) : Reps T (C::π) (A::ρ) := by
  apply skip
  · intro D hd nt
    obtain ⟨a,ha,hsub⟩ := old D hd nt
    exact ⟨a,List.mem_cons_of_mem _ ha,hsub⟩
  · exact fun _ => ⟨A,List.mem_cons_self,sub⟩

theorem compile (T : Frame V U) (lift : (U→Bool) → V→Bool)
    (eval : ∀ x q, LinEqSat (lift x) q ↔ LinEqSat x (imageEq T q))
    (F : Set (LinClause V)) (G : Set (LinClause U)) (anchor : LinClause U) (ax : anchor∈G)
    (axes : ∀ C∈F, ¬top T C → body T C∈G) {π n} (der : Charged T F π n) :
    ∃ ρ, IsLinDerivation G ρ ∧ anchor∈ρ ∧ ρ.length≤n+1 ∧ Reps T π ρ := by
  classical
  induction der with
  | nil => exact ⟨[anchor],.ax .nil ax,by simp,by simp,by simp [Reps]⟩
  | @ax π n C d ha ih =>
    obtain ⟨ρ,proof,anc,le,rep⟩ := ih
    by_cases t : top T C
    · exact ⟨ρ,proof,anc,by simpa [t] using le,skip rep (fun f => False.elim (f t))⟩
    · exact ⟨_,.ax proof (axes C ha t),List.mem_cons_of_mem _ anc,
        by simp only [if_neg t,List.length_cons]; omega,added rep (Subset.rfl)⟩
  | @weak π n C A d hc w ih =>
    obtain ⟨ρ,proof,anc,le,rep⟩ := ih
    by_cases ta : top T A
    · exact ⟨ρ,proof,anc,by simpa [ta] using le,skip rep (fun f => False.elim (f ta))⟩
    · have haveParent : ∃ D∈ρ, ∀ x, LinClauseSat x D → LinClauseSat x (body T C) := by
        by_cases tc : top T C
        · exact ⟨anchor,anc,fun x _ => topOn T tc x⟩
        · obtain ⟨D,mem,sub⟩ := rep C hc tc
          exact ⟨D,mem,fun x ⟨q,m,h⟩ => ⟨q,sub m,h⟩⟩
      obtain ⟨D,mem,imp⟩ := haveParent
      have valid (x) (h : LinClauseSat x D) : LinClauseSat x (body T A) :=
        (body_semantic T lift eval x A).2 (w (lift x) ((body_semantic T lift eval x C).1 (imp x h)))
      exact ⟨_,.weak proof mem valid,List.mem_cons_of_mem _ anc,
        by simp only [if_neg ta,List.length_cons]; omega,added rep Subset.rfl⟩
  | @res π n C D A d hc hd rule ih =>
    obtain ⟨ρ,proof,anc,le,rep⟩ := ih
    by_cases ta : top T A
    · exact ⟨ρ,proof,anc,by simpa [ta] using le,skip rep (fun f => False.elim (f ta))⟩
    have direct := dropParent T rule ta
    by_cases tc : top T C
    · obtain ⟨B,mem,sub⟩ := rep D hd (direct.1 tc).1
      exact ⟨ρ,proof,anc,by simpa [tc] using le,skip rep (fun _ => ⟨B,mem,sub.trans (direct.1 tc).2⟩)⟩
    by_cases td : top T D
    · obtain ⟨B,mem,sub⟩ := rep C hc (direct.2 td).1
      exact ⟨ρ,proof,anc,by simpa [td] using le,skip rep (fun _ => ⟨B,mem,sub.trans (direct.2 td).2⟩)⟩
    obtain ⟨B,mb,bc⟩ := rep C hc tc
    obtain ⟨E,me,ed⟩ := rep D hd td
    have newLe : ρ.length+1 ≤ (n+if top T A ∨ top T C ∨ top T D then 0 else 1)+1 := by
      simp only [ta,tc,td,false_or,if_false]; omega
    rcases splitOptions T rule B E bc ed with h|h|⟨Z,sub,rr⟩
    · exact ⟨ρ,proof,anc,by omega,skip rep (fun _ => ⟨B,mb,h⟩)⟩
    · exact ⟨ρ,proof,anc,by omega,skip rep (fun _ => ⟨E,me,h⟩)⟩
    · have line : IsLinDerivation G (Z::ρ) := rr.elim (fun h => .res proof mb me h) (fun h => .res proof me mb h)
      exact ⟨_,line,List.mem_cons_of_mem _ anc,by simpa using newLe,added rep sub⟩
end PEqualNP.Outside.L_pcx_178.Restrict

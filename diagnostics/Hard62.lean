import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_compile
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

private theorem twoCompatible {R : Clause V} (no : ∃a,¬ClauseSat a R)
    {l m : Literal V} (hl : l∉R) (hm : m∉R) (ok : l.1=m.1 → l.2=m.2) :
    ∃a,¬ClauseSat a R ∧ a l.1=l.2 ∧ a m.1=m.2 := by
  obtain ⟨z,hz⟩:=no
  let a (i : V) := if i=l.1 then l.2 else if i=m.1 then m.2 else z i
  have la : a l.1=l.2 := by simp [a]
  have ma : a m.1=m.2 := by
    by_cases h : m.1=l.1
    · simp [a,h,ok h.symm]
    · simp [a,h]
  refine ⟨a,?_,la,ma⟩
  rintro ⟨i,hi,h⟩
  by_cases e : i.1=l.1
  · have f : i=l := Prod.ext e (by rw [←h,e,la])
    exact hl (f ▸ hi)
  by_cases e' : i.1=m.1
  · have f : i=m := Prod.ext e' (by rw [←h,e',ma])
    exact hm (f ▸ hi)
  exact hz ⟨i,hi,by simpa [a,e,e'] using h⟩

private theorem ordinaryWeak {C R : Clause V} (nt : ∃a,¬ClauseSat a R)
    (wk : ∀a,ClauseSat a C → ClauseSat a R) : C⊆R := by
  intro l hl
  by_contra miss
  obtain ⟨a,no,on,_⟩:=twoCompatible nt miss miss (fun _=>rfl)
  exact no (wk a ⟨l,hl,on⟩)

private theorem ordinaryPair {C D R : Clause V} (nt : ∃a,¬ClauseSat a R)
    (hr : ∀a,ClauseSat a C → ClauseSat a D → ClauseSat a R) :
    C⊆R ∨ D⊆R ∨ ∃T,T⊆R ∧ (IsResolvent C D T ∨ IsResolvent D C T) := by
  classical
  by_cases cs : C⊆R
  · exact Or.inl cs
  by_cases ds : D⊆R
  · exact Or.inr (Or.inl ds)
  right;right
  obtain ⟨l,lc,lr⟩:=Finset.not_subset.mp cs
  obtain ⟨m,md,mr⟩:=Finset.not_subset.mp ds
  have cross {i j : Literal V} (ic : i∈C) (jd : j∈D) (ir : i∉R) (jr : j∉R) :
      i.1=j.1 ∧ i.2≠j.2 := by
    by_contra! fail
    obtain ⟨a,no,ia,ja⟩:=twoCompatible nt ir jr fail
    exact no (hr a ⟨i,ic,ia⟩ ⟨j,jd,ja⟩)
  have ex:=cross lc md lr mr
  have cpart : C.erase l ⊆ R := by
    intro i hi
    obtain ⟨ne,ic⟩:=Finset.mem_erase.mp hi
    by_contra ir
    have f:=cross ic md ir mr
    apply ne
    apply Prod.ext (f.1.trans ex.1.symm)
    cases a:i.2 <;> cases b:l.2 <;> cases c:m.2 <;> simp_all
  have dpart : D.erase m ⊆ R := by
    intro i hi
    obtain ⟨ne,di⟩:=Finset.mem_erase.mp hi
    by_contra ir
    have f:=cross lc di lr ir
    apply ne
    apply Prod.ext (f.1.symm.trans ex.1)
    cases a:i.2 <;> cases b:l.2 <;> cases c:m.2 <;> simp_all
  refine ⟨C.erase l ∪ D.erase m,Finset.union_subset cpart dpart,?_⟩
  rcases l with ⟨v,b⟩;rcases m with ⟨w,d⟩
  change v=w ∧ b≠d at ex
  obtain ⟨rfl,hn⟩:=ex
  cases b <;> cases d <;> simp at hn
  · exact Or.inr ⟨v,md,lc,Finset.union_comm _ _⟩
  · exact Or.inl ⟨v,lc,md,rfl⟩

inductive Log (F : Set (LinClause V)) :
    List (LinClause V × LinClause V) → List (LinClause V) → Prop where
| nil : Log F [] []
| ax {W π C} : Log F W π → C∈F → Log F W (C::π)
| res {W π C D R} : Log F W π → C∈π → D∈π → IsLinResolvent C D R → Log F W (R::π)
| weak {W π C D} : Log F W π → C∈π → (∀a,LinClauseSat a C → LinClauseSat a D) →
    Log F ((C,D)::W) (D::π)

theorem hasLog {F : Set (LinClause V)} {π} (h : IsLinDerivation F π) : ∃W,Log F W π := by
  induction h with
  | nil => exact ⟨[],.nil⟩
  | ax _ ax ih => obtain ⟨W,ih⟩:=ih;exact ⟨W,.ax ih ax⟩
  | res _ c d r ih => obtain ⟨W,ih⟩:=ih;exact ⟨W,.res ih c d r⟩
  | weak _ c w ih => obtain ⟨W,ih⟩:=ih;exact ⟨_,.weak ih c w⟩

private def SatAll (R : Clause V) := ∀a,ClauseSat a R
private def Track (ρ : List (Clause V)) (R : Clause V) := SatAll R ∨ ∃T∈ρ,T⊆R
private theorem up {C D : Clause V} {a : V→Bool} (cd : C⊆D) :
    ClauseSat a C → ClauseSat a D := fun ⟨l,hl,hit⟩=>⟨l,cd hl,hit⟩

theorem compile {F : Set (Clause V)} {W π} (h : Log (linOfClause '' F) W π)
    (m : LinClause V→Clause V) (axes : ∀A∈F,m (linOfClause A)=A)
    (res : ∀C D R,IsLinResolvent C D R → ∀a,ClauseSat a (m C) → ClauseSat a (m D) → ClauseSat a (m R))
    (weakens : ∀p∈W,∀a,ClauseSat a (m p.1) → ClauseSat a (m p.2)) :
    ∃ρ, IsDerivation F ρ ∧ ρ.length+W.length≤π.length ∧ ∀A∈π,Track ρ (m A) := by
  classical
  induction h with
  | nil => exact ⟨[],.nil,by simp,by simp⟩
  | @ax W π Q _ ax ih =>
    obtain ⟨ρ,der,len,tr⟩:=ih weakens
    obtain ⟨P,fp,rfl⟩:=ax
    refine ⟨P::ρ,.ax der fp,by simp <;> omega,?_⟩
    intro A hA
    rcases List.mem_cons.mp hA with rfl|old
    · exact Or.inr ⟨P,List.mem_cons_self,by rw [axes _ fp]⟩
    · rcases tr _ old with t|⟨T,mem,sub⟩
      · exact Or.inl t
      · exact Or.inr ⟨T,List.mem_cons_of_mem _ mem,sub⟩
  | @weak W π C D _ cm _ ih =>
    obtain ⟨ρ,der,len,tr⟩:=ih (fun p hp=>weakens p (List.mem_cons_of_mem _ hp))
    refine ⟨ρ,der,by simp <;> omega,?_⟩
    intro A hA
    rcases List.mem_cons.mp hA with eq|old
    · subst A
      by_cases t : SatAll (m D)
      · exact Or.inl t
      have nt : ∃a,¬ClauseSat a (m D) := by simpa [SatAll] using t
      have w:=weakens (C,D) List.mem_cons_self
      rcases tr C cm with full|⟨T,tm,ts⟩
      · exact (t (fun a=>w a (full a))).elim
      · exact Or.inr ⟨T,tm,ordinaryWeak nt (fun a h=>w a (up ts h))⟩
    · exact tr _ old
  | @res W π C D R _ cm dm step ih =>
    obtain ⟨ρ,der,len,tr⟩:=ih weakens
    have semantic:=res C D R step
    suffices work : ∃σ,IsDerivation F σ ∧ σ.length≤ρ.length+1 ∧
        (∀T∈ρ,T∈σ) ∧ Track σ (m R) by
      obtain ⟨σ,sd,sl,inc,src⟩:=work
      refine ⟨σ,sd,by simp <;> omega,?_⟩
      intro A hA
      rcases List.mem_cons.mp hA with rfl|old
      · exact src
      · rcases tr _ old with t|⟨T,mem,sub⟩
        · exact Or.inl t
        · exact Or.inr ⟨T,inc _ mem,sub⟩
    have keep (q : Track ρ (m R)) : ∃σ,IsDerivation F σ ∧ σ.length≤ρ.length+1 ∧
        (∀T∈ρ,T∈σ) ∧ Track σ (m R) := ⟨ρ,der,by omega,fun _ h=>h,q⟩
    by_cases t : SatAll (m R)
    · exact keep (Or.inl t)
    have nt : ∃a,¬ClauseSat a (m R) := by simpa [SatAll] using t
    rcases tr C cm with cfull|⟨A,am,asub⟩ <;> rcases tr D dm with dfull|⟨B,bm,bsub⟩
    · exact (t (fun a=>semantic a (cfull a) (dfull a))).elim
    · exact keep (Or.inr ⟨B,bm,ordinaryWeak nt (fun a h=>semantic a (cfull a) (up bsub h))⟩)
    · exact keep (Or.inr ⟨A,am,ordinaryWeak nt (fun a h=>semantic a (up asub h) (dfull a))⟩)
    · rcases ordinaryPair nt (fun a ha hb => semantic a (up asub ha) (up bsub hb)) with s|s|⟨T,sub,rr⟩
      · exact keep (Or.inr ⟨A,am,s⟩)
      · exact keep (Or.inr ⟨B,bm,s⟩)
      · have td : IsDerivation F (T::ρ) := by
          rcases rr with rr|rr
          · exact .res der am bm rr
          · exact .res der bm am rr
        exact ⟨T::ρ,td,by simp,fun a h=>List.mem_cons_of_mem _ h,Or.inr ⟨T,List.mem_cons_self,sub⟩⟩

end PEqualNP.Outside.L_pcx_121_compile
namespace PEqualNP.Outside.L_pcx_121_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_121_compile
variable {V : Type} [DecidableEq V]

def exotic (q : LinEq V) : Prop := q.1.card≠1
abbrev extras (C : LinClause V) := C.filter (fun q=>q.1.card≠1)
def atoms (q : LinEq V) : Clause V := q.1.image (fun v=>(v,q.2))
def plainPart (C : LinClause V) : Clause V := (C.filter (fun q=>q.1.card=1)).biUnion atoms
def imageC (M : LinEq V→Clause V) (C : LinClause V) :=
  plainPart C ∪ (extras C).biUnion M
def Real (x : V→Bool) (C : LinClause V) : Prop := ∃q∈extras C,LinEqSat x q

theorem realParts (x : V→Bool) (C : LinClause V) :
    LinClauseSat x C ↔ ClauseSat x (plainPart C) ∨ Real x C := by
  have atom (q : LinEq V) (single : q.1.card=1) : LinEqSat x q ↔ ClauseSat x (atoms q) := by
    rcases q with ⟨s,b⟩
    obtain ⟨v,eq⟩:=Finset.card_eq_one.mp single
    change s={v} at eq
    subst s
    cases hx:x v <;> cases b <;> simp [atoms,LinEqSat,ClauseSat,Finset.filter_singleton,hx]
  constructor
  · rintro ⟨q,hq,on⟩
    by_cases one : q.1.card=1
    · obtain ⟨l,hl,hit⟩:=(atom q one).1 on
      exact Or.inl ⟨l,Finset.mem_biUnion.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,one⟩,hl⟩,hit⟩
    · exact Or.inr ⟨q,Finset.mem_filter.mpr ⟨hq,one⟩,on⟩
  · rintro (⟨l,hl,lit⟩|⟨q,hq,on⟩)
    · obtain ⟨q,hq,ll⟩:=Finset.mem_biUnion.mp hl
      obtain ⟨mem,one⟩:=Finset.mem_filter.mp hq
      exact ⟨q,mem,(atom q one).2 ⟨l,ll,lit⟩⟩
    · exact ⟨q,(Finset.mem_filter.mp hq).1,on⟩

theorem imageParts (M : LinEq V→Clause V) (x : V→Bool) (C : LinClause V) :
    ClauseSat x (imageC M C) ↔ ClauseSat x (plainPart C) ∨ ∃q∈extras C,ClauseSat x (M q) := by
  unfold ClauseSat imageC
  simp only [Finset.mem_union,Finset.mem_biUnion]
  grind

theorem plainLift (C : Clause V) (M : LinEq V→Clause V) : imageC M (linOfClause C)=C := by
  ext l
  simp only [imageC,plainPart,extras,atoms,linOfClause,Finset.mem_union,Finset.mem_biUnion,
    Finset.mem_filter,Finset.mem_image,Finset.card_singleton]
  constructor
  · rintro (⟨q,⟨⟨l',hl,rfl⟩,_⟩,v,hh,rfl⟩|⟨q,⟨⟨l',hl,rfl⟩,hn⟩,_⟩)
    · have eq : v=l'.1 := Finset.mem_singleton.mp hh
      subst v
      exact hl
    · simp at hn
  · intro hl
    exact Or.inl ⟨({l.1},l.2),⟨⟨l,hl,rfl⟩,by simp⟩,l.1,by simp,rfl⟩

theorem imageEmpty (M : LinEq V→Clause V) : imageC M ∅=∅ := by
  simp [imageC,plainPart]

def DisjointSigns (M : LinEq V→Clause V) := ∀ (f : Finset V) x,
  ClauseSat x (M (f,false)) → ¬ClauseSat x (M (f,true))

def atomImage (M : LinEq V→Clause V) (q : LinEq V) :=
  if q.1.card=1 then atoms q else M q

theorem imageAtom (M : LinEq V→Clause V) (x : V→Bool) (C : LinClause V) :
    ClauseSat x (imageC M C) ↔ ∃q∈C,ClauseSat x (atomImage M q) := by
  rw [imageParts]
  unfold plainPart ClauseSat
  simp only [Finset.mem_biUnion,Finset.mem_filter]
  constructor
  · rintro (⟨l,⟨q,⟨m,one⟩,hl⟩,hit⟩|⟨q,⟨m,one⟩,l,hl,hit⟩)
    · exact ⟨q,m,l,by simpa [atomImage,one] using hl,hit⟩
    · exact ⟨q,m,l,by simpa [atomImage,one] using hl,hit⟩
  · rintro ⟨q,m,l,hl,hit⟩
    by_cases one:q.1.card=1
    · exact Or.inl ⟨l,⟨q,⟨m,one⟩,by simpa [atomImage,one] using hl⟩,hit⟩
    · exact Or.inr ⟨q,⟨m,one⟩,l,by simpa [atomImage,one] using hl,hit⟩

theorem validRes (M : LinEq V→Clause V) (ok : DisjointSigns M)
    (C D R : LinClause V) (hr : IsLinResolvent C D R) (x : V→Bool)
    (sc : ClauseSat x (imageC M C)) (sd : ClauseSat x (imageC M D)) :
    ClauseSat x (imageC M R) := by
  obtain ⟨f,lf,rf,rfl⟩:=hr
  obtain ⟨q,hq,on⟩:=(imageAtom M x C).1 sc
  obtain ⟨r,hr,on'⟩:=(imageAtom M x D).1 sd
  apply (imageAtom M x _).2
  by_cases eq:q=(f,false)
  · by_cases eq':r=(f,true)
    · subst q;subst r
      by_cases one : f.card=1
      · obtain ⟨v,rfl⟩:=Finset.card_eq_one.mp one
        simp [atomImage,atoms,ClauseSat] at on on'
        grind
      · exact (ok f x (by simpa [atomImage,one] using on) (by simpa [atomImage,one] using on')).elim
    · exact ⟨r,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨eq',hr⟩),on'⟩
  · exact ⟨q,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hq⟩),on⟩

def AllEarlier (W : List (LinClause V × LinClause V)) (C : LinClause V) :=
  ∀q∈extras C,∃a∈W,q∈extras a.2

inductive Ordered : List (LinClause V × LinClause V)→Prop where
| nil : Ordered []
| cons {P D W} : Ordered W → AllEarlier W P → Ordered ((P,D)::W)

theorem history {F : Set (Clause V)} {W π} (h : Log (linOfClause '' F) W π) :
    Ordered W ∧ ∀C∈π,AllEarlier W C := by
  induction h with
  | nil => exact ⟨.nil,by simp⟩
  | ax _ ax ih =>
    refine ⟨ih.1,?_⟩
    intro C hc
    rcases List.mem_cons.mp hc with rfl|old
    · obtain ⟨A,_,rfl⟩:=ax
      intro q hq
      obtain ⟨mem,non⟩:=Finset.mem_filter.mp hq
      obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp mem
      simp at non
    · exact ih.2 _ old
  | res _ cm dm rr ih =>
    refine ⟨ih.1,?_⟩
    intro A ha
    rcases List.mem_cons.mp ha with rfl|old
    · obtain ⟨f,_,_,rfl⟩:=rr
      intro q hq
      obtain ⟨mem,non⟩:=Finset.mem_filter.mp hq
      rcases Finset.mem_union.mp mem with l|r
      · exact ih.2 _ cm q (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase l,non⟩)
      · exact ih.2 _ dm q (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase r,non⟩)
    · exact ih.2 _ old
  | weak _ cm _ ih =>
    refine ⟨.cons ih.1 (ih.2 _ cm),?_⟩
    intro A ha q hq
    rcases List.mem_cons.mp ha with rfl|old
    · exact ⟨_,List.mem_cons_self,hq⟩
    · obtain ⟨a,am,aq⟩:=ih.2 _ old q hq
      exact ⟨a,List.mem_cons_of_mem _ am,aq⟩


def hits (sigma : Finset V → Bool) (C : LinClause V) : Prop :=
  ∃q∈extras C, sigma q.1=q.2

def topAt (v : V) : Clause V := {(v,false),(v,true)}

theorem topSat (v : V) (x : V→Bool) : ClauseSat x (topAt v) := by
  cases h:x v
  · exact ⟨(v,false),by simp [topAt],h⟩
  · exact ⟨(v,true),by simp [topAt],h⟩

def asGuard (v : V) (sigma : Finset V → Bool) (q : LinEq V) : Clause V :=
  if sigma q.1=q.2 then topAt v else ∅

theorem guardAtom (v : V) (sigma : Finset V → Bool) (q : LinEq V) (x : V→Bool) :
    ClauseSat x (asGuard v sigma q) ↔ sigma q.1=q.2 := by
  by_cases h:sigma q.1=q.2
  · simp [asGuard,h,topSat]
  · simp [asGuard,h,ClauseSat]

theorem guardDisjoint (v : V) (sigma : Finset V→Bool) : DisjointSigns (asGuard v sigma) := by
  intro f x a b
  have u:= (guardAtom v sigma (f,false) x).1 a
  have w:= (guardAtom v sigma (f,true) x).1 b
  exact Bool.noConfusion (u.symm.trans w)

theorem guardClause (v : V) (sigma : Finset V→Bool) (C : LinClause V) (x : V→Bool) :
    ClauseSat x (imageC (asGuard v sigma) C) ↔ ClauseSat x (plainPart C) ∨ hits sigma C := by
  simp only [imageParts,guardAtom,hits]

def guarded (sigma : Finset V→Bool) (P D : LinClause V) : Prop :=
  hits sigma D ∨ (∀x, ClauseSat x (plainPart D)) ∨
    ((∀x, ClauseSat x (plainPart P) → ClauseSat x (plainPart D)) ∧ ¬hits sigma P)

theorem guarded_iff (v : V) (sigma : Finset V→Bool) (P D : LinClause V) :
    guarded sigma P D ↔
      ∀x, ClauseSat x (imageC (asGuard v sigma) P) → ClauseSat x (imageC (asGuard v sigma) D) := by
  simp only [guardClause,guarded]
  constructor
  · rintro (target|taut|⟨impl,source⟩) x hx
    · exact Or.inr target
    · exact Or.inl (taut x)
    · exact Or.inl (impl x (hx.resolve_right source))
  · intro ok
    by_cases ht : hits sigma D
    · exact Or.inl ht
    by_cases hp : hits sigma P
    · exact Or.inr (Or.inl (fun x=>(ok x (Or.inr hp)).resolve_right ht))
    · exact Or.inr (Or.inr ⟨fun x hx=>(ok x (Or.inl hx)).resolve_right ht,hp⟩)

theorem guardCollapse (v : V) (sigma : Finset V→Bool) {F : Set (Clause V)} {W π}
    (h : Log (linOfClause '' F) W π) (ok : ∀p∈W,guarded sigma p.1 p.2)
    (empty : (∅ : LinClause V)∈π) :
    ∃ρ, IsRefutation F ρ ∧ ρ.length+W.length≤π.length := by
  let M:=asGuard v sigma
  obtain ⟨ρ,der,len,track⟩:=compile h (imageC M) (fun A _=>plainLift A M)
    (validRes M (guardDisjoint v sigma)) (fun p hp=>(guarded_iff v sigma p.1 p.2).1 (ok p hp))
  refine ⟨ρ,⟨der,?_⟩,len⟩
  have tr:=track ∅ empty
  rw [imageEmpty] at tr
  rcases tr with t|⟨C,mem,sub⟩
  · exact False.elim (by simpa [ClauseSat] using t (fun _=>false))
  · have eq : C=∅ := Finset.Subset.antisymm sub (Finset.empty_subset _)
    exact eq ▸ mem
end PEqualNP.Outside.L_pcx_121_image


namespace PEqualNP.Outside.L_pcx_121_substitution
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_121_compile PEqualNP.Outside.L_pcx_121_image
variable {V : Type} [DecidableEq V]

def inv (l : Literal V) : Literal V := (l.1,!l.2)

theorem inv_inv (l : Literal V) : inv (inv l)=l := by cases l with | mk v b => cases b <;> rfl

theorem opposite {A B : Clause V} (disj : ∀x,ClauseSat x A → ¬ClauseSat x B)
    {l t : Literal V} (hl : l∈A) (ht : t∈B) : t=inv l := by
  let x : V→Bool := fun v=>if v=l.1 then l.2 else t.2
  have ls : x l.1=l.2 := by simp [x]
  have never := disj x ⟨l,hl,ls⟩
  have ne : x t.1≠t.2 := fun h=>never ⟨t,ht,h⟩
  by_cases eq : t.1=l.1
  · have diff : l.2≠t.2 := by simpa [x,eq] using ne
    apply Prod.ext
    · exact eq
    · change t.2= !l.2
      cases ha:l.2 <;> cases hb:t.2 <;> simp_all
  · exact (ne (by simp [x,eq])).elim

theorem shape {A B : Clause V} :
    (∀x,ClauseSat x A → ¬ClauseSat x B) ↔
      A=∅ ∨ B=∅ ∨ ∃l : Literal V,A={l} ∧ B={inv l} := by
  constructor
  · intro ok
    by_cases a : A=∅
    · exact Or.inl a
    by_cases b : B=∅
    · exact Or.inr (Or.inl b)
    obtain ⟨l,hl⟩:=Finset.nonempty_iff_ne_empty.mpr a
    obtain ⟨t,ht⟩:=Finset.nonempty_iff_ne_empty.mpr b
    have tt:=opposite ok hl ht
    refine Or.inr (Or.inr ⟨l,?_,?_⟩)
    · ext j
      simp only [Finset.mem_singleton]
      constructor
      · intro h
        have e:inv j=inv l:=(opposite ok h ht).symm.trans tt
        simpa only [inv_inv] using congrArg inv e
      · rintro rfl;exact hl
    · ext j
      simp only [Finset.mem_singleton]
      constructor
      · exact opposite ok hl
      · rintro rfl;exact tt ▸ ht
  · rintro (rfl|rfl|⟨l,rfl,rfl⟩) x hx hy
    · simpa [ClauseSat] using hx
    · simpa [ClauseSat] using hy
    · obtain ⟨u,hu,uh⟩:=hx
      obtain ⟨v,hv,vh⟩:=hy
      have ue : u=l := Finset.mem_singleton.mp hu
      have ve : v=inv l := Finset.mem_singleton.mp hv
      have p : x l.1=l.2 := ue ▸ uh
      have q : x l.1= !l.2 := by simpa only [ve,inv] using vh
      cases hs:l.2 <;> simp_all


end PEqualNP.Outside.L_pcx_121_substitution



namespace PEqualNP.Outside.L_pcx_121_hard
open PEqualNP.Outside.L_pcx_121_compile PEqualNP.Outside.L_pcx_121_image PEqualNP.Outside.L_pcx_121_substitution

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 4 × Fin 3

def par (a : VV → Bool) (f : Finset VV) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset VV) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : VV → Bool) (s t : Finset VV) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega

def sdl : List (LinEq VV) → Finset VV
  | [] => ∅
  | e :: l => symmDiff e.1 (sdl l)

def xbl : List (LinEq VV) → Bool
  | [] => false
  | e :: l => xor (!e.2) (xbl l)

theorem par_sdl (a : VV → Bool) (L : List (LinEq VV)) (h : ∀ e ∈ L, ¬ LinEqSat a e) :
    (par a (sdl L) ↔ xbl L = true) := by
  induction L with
  | nil => simp [par, sdl, xbl]
  | cons e l ih =>
    obtain ⟨f, b⟩ := e
    have he := h (f, b) (List.mem_cons_self ..)
    have hl := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he2 : par a f ↔ ¬ (b = true) := by
      unfold LinEqSat at he; unfold par; simp only at he; tauto
    simp only [sdl, xbl]
    rw [par_sd, hl, he2]
    cases b <;> cases xbl l <;> simp

def okB (q : LinEq VV) (D : LinClause VV) (L : List (LinEq VV)) : Bool :=
  L.all (fun e => decide (e ∈ D)) && decide (q.1 = sdl L) && (q.2 == !(xbl L))

theorem weak_cert (C D : LinClause VV) (certs : List (List (LinEq VV)))
    (h : ∀ q ∈ C, ∃ L ∈ certs, okB q D L = true) :
    ∀ a : VV → Bool, LinClauseSat a C → LinClauseSat a D := by
  intro a ⟨q, hq, hs⟩
  obtain ⟨L, _, hok⟩ := h q hq
  simp only [okB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hD, h1⟩, h2⟩ := hok
  by_contra hn
  have hn' : ∀ e ∈ L, ¬ LinEqSat a e := fun e he hse => hn ⟨e, hD e he, hse⟩
  have hp := par_sdl a L hn'
  unfold LinEqSat at hs
  rw [h1] at hs
  change par a (sdl L) ↔ q.2 = true at hs
  rw [hp, h2] at hs
  cases xbl L <;> simp at hs



set_option maxHeartbeats 0
set_option maxRecDepth 100000

def l0 : LinClause VV := ({(({(0, 0)} : Finset VV), true), (({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true)} : LinClause VV)
def l1 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(1, 2)} : Finset VV), true)} : LinClause VV)
def l2 : LinClause VV := ({(({(2, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), true)} : LinClause VV)
def l3 : LinClause VV := ({(({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l4 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(1, 0)} : Finset VV), false)} : LinClause VV)
def l5 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)
def l6 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : LinClause VV)
def l7 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), false)} : LinClause VV)
def l8 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : LinClause VV)
def l9 : LinClause VV := ({(({(2, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), false)} : LinClause VV)
def l10 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(1, 1)} : Finset VV), false)} : LinClause VV)
def l11 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false)} : LinClause VV)
def l12 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)
def l13 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(2, 1)} : Finset VV), false)} : LinClause VV)
def l14 : LinClause VV := ({(({(1, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)
def l15 : LinClause VV := ({(({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), false)} : LinClause VV)
def l16 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), false)} : LinClause VV)
def l17 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), false)} : LinClause VV)
def l18 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : LinClause VV)
def l19 : LinClause VV := ({(({(1, 2)} : Finset VV), false), (({(2, 2)} : Finset VV), false)} : LinClause VV)
def l20 : LinClause VV := ({(({(1, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : LinClause VV)
def l21 : LinClause VV := ({(({(2, 2)} : Finset VV), false), (({(3, 2)} : Finset VV), false)} : LinClause VV)
def l22 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), false)} : LinClause VV)
def l23 : LinClause VV := ({(({(1, 2)} : Finset VV), false), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l24 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l25 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l26 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l27 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l28 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l29 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l30 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l31 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(2, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l32 : LinClause VV := ({(({(1, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l33 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l34 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l35 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l36 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l37 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), false), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l38 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l39 : LinClause VV := ({(({(1, 1)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l40 : LinClause VV := ({(({(1, 0)} : Finset VV), true), (({(1, 2)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l41 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 0)} : Finset VV), false), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l42 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 1)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l43 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), false), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l44 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 1)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l45 : LinClause VV := ({(({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), true), (({(3, 2)} : Finset VV), true)} : LinClause VV)
def l46 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(2, 0)} : Finset VV), true), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l47 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(3, 0)} : Finset VV), true)} : LinClause VV)
def l48 : LinClause VV := ({(({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true), (({(3, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)} : LinClause VV)
def l49 : LinClause VV := ({(({(3, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)} : LinClause VV)
def l50 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)} : LinClause VV)
def l51 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), true), (({(2, 2)} : Finset VV), true)} : LinClause VV)
def l52 : LinClause VV := ({(({(0, 2)} : Finset VV), false), (({(1, 2)} : Finset VV), true)} : LinClause VV)
def l53 : LinClause VV := ({(({(0, 2)} : Finset VV), false)} : LinClause VV)
def l54 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(1, 1)} : Finset VV), true), (({(3, 1)} : Finset VV), true)} : LinClause VV)
def l55 : LinClause VV := ({(({(0, 1)} : Finset VV), false), (({(1, 1)} : Finset VV), true)} : LinClause VV)
def l56 : LinClause VV := ({(({(0, 1)} : Finset VV), false)} : LinClause VV)
def l57 : LinClause VV := ({(({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)} : LinClause VV)
def l58 : LinClause VV := ({(({(0, 0)} : Finset VV), false), (({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true)} : LinClause VV)
def l59 : LinClause VV := ({(({(0, 1)} : Finset VV), true), (({(0, 2)} : Finset VV), true)} : LinClause VV)
def l60 : LinClause VV := ({(({(0, 2)} : Finset VV), true)} : LinClause VV)
def l61 : LinClause VV := (∅ : LinClause VV)

def p0 : List (LinClause VV) := [l0]
def p1 : List (LinClause VV) := l1 :: p0
def p2 : List (LinClause VV) := l2 :: p1
def p3 : List (LinClause VV) := l3 :: p2
def p4 : List (LinClause VV) := l4 :: p3
def p5 : List (LinClause VV) := l5 :: p4
def p6 : List (LinClause VV) := l6 :: p5
def p7 : List (LinClause VV) := l7 :: p6
def p8 : List (LinClause VV) := l8 :: p7
def p9 : List (LinClause VV) := l9 :: p8
def p10 : List (LinClause VV) := l10 :: p9
def p11 : List (LinClause VV) := l11 :: p10
def p12 : List (LinClause VV) := l12 :: p11
def p13 : List (LinClause VV) := l13 :: p12
def p14 : List (LinClause VV) := l14 :: p13
def p15 : List (LinClause VV) := l15 :: p14
def p16 : List (LinClause VV) := l16 :: p15
def p17 : List (LinClause VV) := l17 :: p16
def p18 : List (LinClause VV) := l18 :: p17
def p19 : List (LinClause VV) := l19 :: p18
def p20 : List (LinClause VV) := l20 :: p19
def p21 : List (LinClause VV) := l21 :: p20
def p22 : List (LinClause VV) := l22 :: p21
def p23 : List (LinClause VV) := l23 :: p22
def p24 : List (LinClause VV) := l24 :: p23
def p25 : List (LinClause VV) := l25 :: p24
def p26 : List (LinClause VV) := l26 :: p25
def p27 : List (LinClause VV) := l27 :: p26
def p28 : List (LinClause VV) := l28 :: p27
def p29 : List (LinClause VV) := l29 :: p28
def p30 : List (LinClause VV) := l30 :: p29
def p31 : List (LinClause VV) := l31 :: p30
def p32 : List (LinClause VV) := l32 :: p31
def p33 : List (LinClause VV) := l33 :: p32
def p34 : List (LinClause VV) := l34 :: p33
def p35 : List (LinClause VV) := l35 :: p34
def p36 : List (LinClause VV) := l36 :: p35
def p37 : List (LinClause VV) := l37 :: p36
def p38 : List (LinClause VV) := l38 :: p37
def p39 : List (LinClause VV) := l39 :: p38
def p40 : List (LinClause VV) := l40 :: p39
def p41 : List (LinClause VV) := l41 :: p40
def p42 : List (LinClause VV) := l42 :: p41
def p43 : List (LinClause VV) := l43 :: p42
def p44 : List (LinClause VV) := l44 :: p43
def p45 : List (LinClause VV) := l45 :: p44
def p46 : List (LinClause VV) := l46 :: p45
def p47 : List (LinClause VV) := l47 :: p46
def p48 : List (LinClause VV) := l48 :: p47
def p49 : List (LinClause VV) := l49 :: p48
def p50 : List (LinClause VV) := l50 :: p49
def p51 : List (LinClause VV) := l51 :: p50
def p52 : List (LinClause VV) := l52 :: p51
def p53 : List (LinClause VV) := l53 :: p52
def p54 : List (LinClause VV) := l54 :: p53
def p55 : List (LinClause VV) := l55 :: p54
def p56 : List (LinClause VV) := l56 :: p55
def p57 : List (LinClause VV) := l57 :: p56
def p58 : List (LinClause VV) := l58 :: p57
def p59 : List (LinClause VV) := l59 :: p58
def p60 : List (LinClause VV) := l60 :: p59
def p61 : List (LinClause VV) := l61 :: p60

theorem d0 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p0 :=
  Log.ax Log.nil ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((0 : Fin 4), j), true))), Set.mem_union_left _ ⟨0, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d1 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p1 :=
  Log.ax d0 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((1 : Fin 4), j), true))), Set.mem_union_left _ ⟨1, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d2 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p2 :=
  Log.ax d1 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((2 : Fin 4), j), true))), Set.mem_union_left _ ⟨2, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d3 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p3 :=
  Log.ax d2 ((Set.mem_image _ _ _).2 ⟨(Finset.univ.image (fun j : Fin 3 => (((3 : Fin 4), j), true))), Set.mem_union_left _ ⟨3, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d4 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p4 :=
  Log.ax d3 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((1 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d5 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p5 :=
  Log.ax d4 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((2 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d6 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p6 :=
  Log.ax d5 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d7 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p7 :=
  Log.ax d6 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (0 : Fin 3)), false), (((2 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d8 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p8 :=
  Log.ax d7 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d9 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p9 :=
  Log.ax d8 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (0 : Fin 3)), false), (((3 : Fin 4), (0 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 0, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d10 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p10 :=
  Log.ax d9 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((1 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d11 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p11 :=
  Log.ax d10 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((2 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d12 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p12 :=
  Log.ax d11 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d13 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p13 :=
  Log.ax d12 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (1 : Fin 3)), false), (((2 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d14 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p14 :=
  Log.ax d13 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d15 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p15 :=
  Log.ax d14 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (1 : Fin 3)), false), (((3 : Fin 4), (1 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 1, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d16 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p16 :=
  Log.ax d15 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((1 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 1, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d17 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p17 :=
  Log.ax d16 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((2 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 2, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d18 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p18 :=
  Log.ax d17 ((Set.mem_image _ _ _).2 ⟨({(((0 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨0, 3, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d19 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p19 :=
  Log.ax d18 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (2 : Fin 3)), false), (((2 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 2, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d20 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p20 :=
  Log.ax d19 ((Set.mem_image _ _ _).2 ⟨({(((1 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨1, 3, 2, by decide, rfl⟩, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d21 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p21 :=
  Log.ax d20 ((Set.mem_image _ _ _).2 ⟨({(((2 : Fin 4), (2 : Fin 3)), false), (((3 : Fin 4), (2 : Fin 3)), false)} : Clause VV), Set.mem_union_right _ ⟨2, 3, 2, by decide, rfl⟩, by decide +kernel⟩)


theorem d22 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p22 := Log.res (C := l14) (D := l1) d21 (by decide +kernel) (by decide +kernel) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d23 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p23 := Log.res (C := l20) (D := l3) d22 (by decide +kernel) (by decide +kernel) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d24 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p24 := Log.res (C := l22) (D := l3) d23 (by decide +kernel) (by decide +kernel) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d25 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p25 := Log.res (C := l21) (D := l24) d24 (by decide +kernel) (by decide +kernel) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d26 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p26 := Log.res (C := l19) (D := l25) d25 (by decide +kernel) (by decide +kernel) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d27 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p27 := Log.res (C := l23) (D := l1) d26 (by decide +kernel) (by decide +kernel) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d28 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p28 := Log.res (C := l13) (D := l27) d27 (by decide +kernel) (by decide +kernel) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d29 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p29 := Log.res (C := l15) (D := l28) d28 (by decide +kernel) (by decide +kernel) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d30 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p30 := Log.res (C := l26) (D := l2) d29 (by decide +kernel) (by decide +kernel) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d31 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p31 := Log.res (C := l29) (D := l30) d30 (by decide +kernel) (by decide +kernel) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d32 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p32 := Log.res (C := l8) (D := l3) d31 (by decide +kernel) (by decide +kernel) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d33 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p33 := Log.res (C := l7) (D := l27) d32 (by decide +kernel) (by decide +kernel) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d34 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p34 := Log.res (C := l9) (D := l33) d33 (by decide +kernel) (by decide +kernel) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d35 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p35 := Log.res (C := l32) (D := l1) d34 (by decide +kernel) (by decide +kernel) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d36 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p36 := Log.res (C := l21) (D := l35) d35 (by decide +kernel) (by decide +kernel) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d37 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p37 := Log.res (C := l19) (D := l36) d36 (by decide +kernel) (by decide +kernel) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d38 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p38 := Log.res (C := l34) (D := l2) d37 (by decide +kernel) (by decide +kernel) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d39 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p39 := Log.res (C := l37) (D := l38) d38 (by decide +kernel) (by decide +kernel) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d40 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p40 := Log.res (C := l9) (D := l24) d39 (by decide +kernel) (by decide +kernel) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d41 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p41 := Log.res (C := l7) (D := l40) d40 (by decide +kernel) (by decide +kernel) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d42 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p42 := Log.res (C := l13) (D := l35) d41 (by decide +kernel) (by decide +kernel) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d43 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p43 := Log.res (C := l15) (D := l42) d42 (by decide +kernel) (by decide +kernel) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d44 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p44 := Log.res (C := l41) (D := l2) d43 (by decide +kernel) (by decide +kernel) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d45 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p45 := Log.res (C := l43) (D := l44) d44 (by decide +kernel) (by decide +kernel) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d46 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p46 := Log.res (C := l4) (D := l31) d45 (by decide +kernel) (by decide +kernel) ⟨({(1, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d47 : Log ((fun C => linOfClause C) '' PHP 4 3) [] p47 := Log.res (C := l5) (D := l46) d46 (by decide +kernel) (by decide +kernel) ⟨({(2, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

def cert48 : List (List (LinEq VV)) := [[(({(3, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(0, 1)} : Finset VV), true)], [(({(0, 2)} : Finset VV), true)]]
theorem d48 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l0,l48)] p48 := by
  refine Log.weak (C := l0) d47 (by decide +kernel) (weak_cert l0 l48 cert48 ?_)
  intro q hq
  simp only [l0, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨[(({(3, 0)} : Finset VV), true), (({(0, 0), (3, 0)} : Finset VV), true)], by decide +kernel, by decide +kernel⟩
  · exact ⟨[(({(0, 1)} : Finset VV), true)], by decide +kernel, by decide +kernel⟩
  · exact ⟨[(({(0, 2)} : Finset VV), true)], by decide +kernel, by decide +kernel⟩

def cert49 : List (List (LinEq VV)) := [[(({(3, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)], [(({(3, 0)} : Finset VV), false)]]
theorem d49 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l6,l49),(l0,l48)] p49 := by
  refine Log.weak (C := l6) d48 (by decide +kernel) (weak_cert l6 l49 cert49 ?_)
  intro q hq
  simp only [l6, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(3, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), true)], by decide +kernel, by decide +kernel⟩
  · exact ⟨[(({(3, 0)} : Finset VV), false)], by decide +kernel, by decide +kernel⟩

def cert50 : List (List (LinEq VV)) := [[(({(0, 0)} : Finset VV), false)], [(({(0, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)]]
theorem d50 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p50 := by
  refine Log.weak (C := l47) d49 (by decide +kernel) (weak_cert l47 l50 cert50 ?_)
  intro q hq
  simp only [l47, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨[(({(0, 0)} : Finset VV), false)], by decide +kernel, by decide +kernel⟩
  · exact ⟨[(({(0, 0)} : Finset VV), false), (({(0, 0), (3, 0)} : Finset VV), false)], by decide +kernel, by decide +kernel⟩

theorem d51 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p51 := Log.res (C := l18) (D := l45) d50 (by decide +kernel) (by decide +kernel) ⟨({(3, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d52 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p52 := Log.res (C := l17) (D := l51) d51 (by decide +kernel) (by decide +kernel) ⟨({(2, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d53 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p53 := Log.res (C := l16) (D := l52) d52 (by decide +kernel) (by decide +kernel) ⟨({(1, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d54 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p54 := Log.res (C := l11) (D := l39) d53 (by decide +kernel) (by decide +kernel) ⟨({(2, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d55 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p55 := Log.res (C := l12) (D := l54) d54 (by decide +kernel) (by decide +kernel) ⟨({(3, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d56 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p56 := Log.res (C := l10) (D := l55) d55 (by decide +kernel) (by decide +kernel) ⟨({(1, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d57 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p57 := Log.res (C := l49) (D := l48) d56 (by decide +kernel) (by decide +kernel) ⟨({(3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d58 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p58 := Log.res (C := l50) (D := l57) d57 (by decide +kernel) (by decide +kernel) ⟨({(0, 0), (3, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d59 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p59 := Log.res (C := l58) (D := l0) d58 (by decide +kernel) (by decide +kernel) ⟨({(0, 0)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d60 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p60 := Log.res (C := l56) (D := l59) d59 (by decide +kernel) (by decide +kernel) ⟨({(0, 1)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem d61 : Log ((fun C => linOfClause C) '' PHP 4 3) [(l47,l50),(l6,l49),(l0,l48)] p61 := Log.res (C := l53) (D := l60) d60 (by decide +kernel) (by decide +kernel) ⟨({(0, 2)} : Finset VV), by decide +kernel, by decide +kernel, by decide +kernel⟩


abbrev W := VV
def f : Finset W := {(0,0),(3,0)}
def asg (x : Nat) (p : W) := x.testBit (3*p.1.val+p.2.val)
def sites : List (LinClause W × LinClause W) := [(l47,l50),(l6,l49),(l0,l48)]
theorem forced {M : LinEq W→Clause W}
    (ok : ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2))
    {P D : LinClause W} (inW : (P,D)∈sites) {x : W→Bool} {b : Bool}
    (starts : ClauseSat x (plainPart P)) (ends : ¬ClauseSat x (plainPart D))
    (only : extras D={(f,b)}) : ClauseSat x (M (f,b)) := by
  have h:=ok (P,D) inW x ((imageParts M x P).2 (Or.inl starts))
  obtain rejected|⟨q,hq,yes⟩ := (imageParts M x D).1 h
  · exact (ends rejected).elim
  · rw [only,Finset.mem_singleton] at hq
    exact hq ▸ yes
def words0 : List Nat := [513, 4095]
theorem h0 {M : LinEq W→Clause W} (ok : ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2)) : ∀ v∈words0,ClauseSat (asg v) (M (f,false)) := by
  intro v hv
  simp only [words0,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl
  · exact forced ok (P:=l47) (D:=l50) (by decide +kernel) (by unfold ClauseSat; decide +kernel) (by unfold ClauseSat; decide +kernel) (by decide +kernel)
  · exact forced ok (P:=l47) (D:=l50) (by decide +kernel) (by unfold ClauseSat; decide +kernel) (by unfold ClauseSat; decide +kernel) (by decide +kernel)
def words1 : List Nat := [1, 4094]
theorem h1 {M : LinEq W→Clause W} (ok : ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2)) : ∀ v∈words1,ClauseSat (asg v) (M (f,true)) := by
  intro v hv
  simp only [words1,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl
  · exact forced ok (P:=l0) (D:=l48) (by decide +kernel) (by unfold ClauseSat; decide +kernel) (by unfold ClauseSat; decide +kernel) (by decide +kernel)
  · exact forced ok (P:=l6) (D:=l49) (by decide +kernel) (by unfold ClauseSat; decide +kernel) (by unfold ClauseSat; decide +kernel) (by decide +kernel)
theorem collision : ∀ v : W, (words0.any (fun x=>words1.any (fun y=>asg x v==asg y v)))=true := by decide +kernel

theorem noImage (M : LinEq W→Clause W) (disj : DisjointSigns M) :
    ¬(∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2)) := by
  intro ok
  have z:=h0 ok
  have o:=h1 ok
  rcases shape.mp (disj f) with left|right|⟨l,neg,pos⟩
  · have t:=z _ (show words0.head!∈words0 by decide +kernel)
    simpa [left,ClauseSat] using t
  · have t:=o _ (show words1.head!∈words1 by decide +kernel)
    simpa [right,ClauseSat] using t
  · obtain ⟨x,hx,hit⟩:=List.any_eq_true.mp (collision l.1)
    obtain ⟨y,hy,same⟩:=List.any_eq_true.mp hit
    have v0:=z x hx
    have v1:=o y hy
    rw [neg] at v0
    rw [pos] at v1
    obtain ⟨a,ha,va⟩:=v0
    obtain ⟨b,hb,vb⟩:=v1
    have ea : a=l:=Finset.mem_singleton.mp ha
    have eb : b=inv l:=Finset.mem_singleton.mp hb
    have sx : asg x l.1=l.2:=ea ▸ va
    have sy : asg y l.1= !l.2:=by simpa only [eb,inv] using vb
    have eql : asg x l.1=asg y l.1:=beq_iff_eq.mp same
    cases hs:l.2 <;> simp_all
theorem complete62 :
    ∃ π : List (LinClause W), Log (linOfClause '' PHP 4 3) sites π ∧
    (∅ : LinClause W)∈π ∧ π.length=62 ∧
    ¬∃ M : LinEq W→Clause W,DisjointSigns M ∧
       ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2) := by
  refine ⟨p61,d61,List.Mem.head _,by decide +kernel,?_⟩
  rintro ⟨M,disj,ok⟩
  exact noImage M disj ok
end PEqualNP.Outside.L_pcx_121_hard

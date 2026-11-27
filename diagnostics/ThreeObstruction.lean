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
    apply Prod.ext eq
    change t.2= !l.2
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

namespace PEqualNP.Outside.L_pcx_121_five
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_121_compile PEqualNP.Outside.L_pcx_121_image
open PEqualNP.Outside.L_pcx_121_substitution
abbrev W := Fin 4 × Fin 3
def asg (x : Nat) (p : W) := x.testBit (3*p.1.val+p.2.val)
def f : Finset W := {(0,0),(1,0)}
def p0 : LinClause W := {({(1,0)},true),({(1,1)},true),({(1,2)},true)}
def d0 : LinClause W := {({(0,0)},false),({(1,1)},true),({(1,2)},true),({(0,0),(1,0)},false)}
def p1 : LinClause W := {({(1,0)},false),({(2,0)},false)}
def d1 : LinClause W := {({(0,0)},true),({(2,0)},false),({(0,0),(1,0)},false)}
def p2 : LinClause W := {({(1,0)},false),({(3,0)},false)}
def d2 : LinClause W := {({(0,0)},true),({(3,0)},false),({(0,0),(1,0)},false)}
def p3 : LinClause W := {({(1,0)},true),({(1,1)},true),({(1,2)},true)}
def d3 : LinClause W := {({(0,0)},true),({(1,1)},true),({(1,2)},true),({(0,0),(1,0)},true)}
def p4 : LinClause W := {({(0,0)},false),({(1,0)},false)}
def d4 : LinClause W := {({(0,0)},false),({(0,0),(1,0)},true)}
def sites : List (LinClause W × LinClause W) := [(p0,d0),(p3,d3),(p4,d4)]

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
def words0 : List Nat := [9]
theorem h0 {M : LinEq W→Clause W} (ok : ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2)) : ∀ v∈words0,ClauseSat (asg v) (M (f,false)) := by
  intro v hv
  simp only [words0,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl
  · exact forced ok (P:=p0) (D:=d0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def words1 : List Nat := [8, 4087]
theorem h1 {M : LinEq W→Clause W} (ok : ∀p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2)) : ∀ v∈words1,ClauseSat (asg v) (M (f,true)) := by
  intro v hv
  simp only [words1,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl
  · exact forced ok (P:=p3) (D:=d3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact forced ok (P:=p4) (D:=d4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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



def cert0 : List (List (LinEq W)) := [[({(0,0)},false),({(0,0),(1,0)},false)],[({(1,1)},true)],[({(1,2)},true)]]
theorem legal0 : ∀ x,LinClauseSat x p0→LinClauseSat x d0 := by
  apply weak_cert p0 d0 cert0
  intro q hq
  simp only [p0,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl
  · exact ⟨[({(0,0)},false),({(0,0),(1,0)},false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[({(1,1)},true)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[({(1,2)},true)],by decide +kernel,by decide +kernel⟩
def cert3 : List (List (LinEq W)) := [[({(0,0)},true),({(0,0),(1,0)},true)],[({(1,1)},true)],[({(1,2)},true)]]
theorem legal3 : ∀ x,LinClauseSat x p3→LinClauseSat x d3 := by
  apply weak_cert p3 d3 cert3
  intro q hq
  simp only [p3,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl
  · exact ⟨[({(0,0)},true),({(0,0),(1,0)},true)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[({(1,1)},true)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[({(1,2)},true)],by decide +kernel,by decide +kernel⟩
def cert4 : List (List (LinEq W)) := [[({(0,0)},false)],[({(0,0)},false),({(0,0),(1,0)},true)]]
theorem legal4 : ∀ x,LinClauseSat x p4→LinClauseSat x d4 := by
  apply weak_cert p4 d4 cert4
  intro q hq
  simp only [p4,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl
  · exact ⟨[({(0,0)},false)],by decide +kernel,by decide +kernel⟩
  · exact ⟨[({(0,0)},false),({(0,0),(1,0)},true)],by decide +kernel,by decide +kernel⟩

abbrev F := linOfClause '' PHP 4 3

theorem rowAx : p0∈F := by
  refine ⟨Finset.univ.image (fun j : Fin 3=>(((1 : Fin 4),j),true)),Or.inl ⟨1,rfl⟩,?_⟩
  decide +kernel

theorem colAx : p4∈F := by
  let A : Clause W := {(((0 : Fin 4),(0 : Fin 3)),false),(((1 : Fin 4),(0 : Fin 3)),false)}
  refine ⟨A,Or.inr ⟨0,1,0,by decide,rfl⟩,?_⟩
  decide +kernel

theorem legalPrefix : Log F [(p4,d4),(p3,d3),(p0,d0)] [d4,d3,d0,p4,p0] := by
  have a : Log F [] [p4,p0] := .ax (.ax .nil rowAx) colAx
  have b := Log.weak a (show p0∈[p4,p0] by simp) legal0
  have c := Log.weak b (show p3∈[d0,p4,p0] by simp [p3,p0]) legal3
  exact Log.weak c (by simp) legal4

theorem threeFail : (∃π,Log F [(p4,d4),(p3,d3),(p0,d0)] π) ∧
    ¬∃M : LinEq W→Clause W,DisjointSigns M ∧
      ∀ p∈sites,∀x,ClauseSat x (imageC M p.1)→ClauseSat x (imageC M p.2) := by
  refine ⟨⟨_,legalPrefix⟩,?_⟩
  rintro ⟨M,d,h⟩
  exact noImage M d h
end PEqualNP.Outside.L_pcx_121_five

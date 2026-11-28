import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_118
import PEqualNP.Outside.L_pcx_150


namespace PEqualNP.Outside.L_pcx_119_compile
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

end PEqualNP.Outside.L_pcx_119_compile
namespace PEqualNP.Outside.L_pcx_119_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_119_compile
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

end PEqualNP.Outside.L_pcx_119_image

namespace PEqualNP.Outside.L_pcx_119_analysis
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

def Exception (P A : Clause V) (x : V→Bool) := ClauseSat x P ∧ ¬ClauseSat x A

def flip (x : V→Bool) (v : V) (i : V) := if i=v then !(x i) else x i

theorem opposite {x : V→Bool} {f : Finset V} {v : V} (hv : v∈f) (b : Bool) :
    LinEqSat (flip x v) (f,b) ↔ ¬LinEqSat x (f,b) := by
  let S := (f.erase v).filter (fun i=>x i=true)
  have nv : v∉S := by simp [S]
  have h0 : f.filter (fun i=>x i=true) = (if x v then insert v S else S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S]
    · cases hx : x v <;> simp [hx,S,he]
  have h1 : f.filter (fun i=>flip x v i=true) = (if x v then S else insert v S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S,flip]
    · cases hx : x v <;> simp [hx,S,he,flip]
  unfold LinEqSat
  change (Odd (f.filter (fun i=>flip x v i=true)).card ↔ b=true) ↔
    ¬(Odd (f.filter (fun i=>x i=true)).card ↔ b=true)
  rw [h0,h1]
  cases xx : x v <;> cases b <;> simp [xx,Finset.card_insert_of_notMem nv,Nat.odd_iff] <;> omega

private theorem flippedValue {x y : V→Bool} {v : V} (ne : x v≠y v) : flip x v v=y v := by
  unfold flip
  cases hx:x v <;> cases hy:y v <;> simp_all

private theorem guard {A : Clause V} {x y : V→Bool} {v : V} (ne : x v≠y v)
    (hx : ¬ClauseSat x A) (hy : ¬ClauseSat y A) : ¬ClauseSat (flip x v) A := by
  rintro ⟨l,hl,lit⟩
  by_cases eq : l.1=v
  · have haveY : y l.1=l.2 := by rwa [eq,flippedValue ne,←eq] at lit
    exact hy ⟨l,hl,haveY⟩
  · exact hx ⟨l,hl,by simpa [flip,eq] using lit⟩

theorem exceptionCoordinate {P A : Clause V} {f : Finset V} {b : Bool}
    (side : ∀x,Exception P A x → LinEqSat x (f,b)) {v : V} (hv : v∈f)
    {x y : V→Bool} (hx : Exception P A x) (hy : Exception P A y) : x v=y v := by
  by_contra ne
  have failure {a d : V→Bool} (ha : Exception P A a) (hd : Exception P A d)
      (dif : a v≠d v) : ¬ClauseSat (flip a v) P := by
    intro wins
    exact ((opposite hv b).1 (side _ ⟨wins,guard dif ha.2 hd.2⟩)) (side _ ha)
  have fx := failure hx hy ne
  have fy := failure hy hx (Ne.symm ne)
  obtain ⟨l,hl,lit⟩ := hy.1
  have same : l.1=v := by
    by_contra nn
    exact fy ⟨l,hl,by simpa [flip,nn] using lit⟩
  exact fx ⟨l,hl,by rw [same,flippedValue ne,←same];exact lit⟩

def RawTest (t : (V→Bool)→Bool) :=
  (∃ b : Bool,t=fun _=>b) ∨ ∃(v : V)(b : Bool),t=fun x=>decide (x v=b)

theorem separator {P A Q B : Clause V} {f : Finset V}
    (left : ∀x,Exception P A x → LinEqSat x (f,false))
    (right : ∀x,Exception Q B x → LinEqSat x (f,true)) :
    ∃t : (V→Bool)→Bool, RawTest t ∧
      (∀x,Exception P A x → t x=false) ∧ ∀x,Exception Q B x → t x=true := by
  classical
  by_cases l : ∃x,Exception P A x
  · obtain ⟨a,ha⟩:=l
    by_cases r : ∃x,Exception Q B x
    · obtain ⟨d,hd⟩:=r
      have diff : ∃v∈f,a v≠d v := by
        by_contra! eq
        have fs : f.filter (fun i=>a i=true)=f.filter (fun i=>d i=true) := by
          ext i
          by_cases hi : i∈f
          · simp [hi,eq i hi]
          · simp [hi]
        have h0:=left a ha
        have h1:=right d hd
        unfold LinEqSat at h0 h1
        simp only [Bool.false_eq_true,iff_false,iff_true] at h0 h1
        exact h0 (fs ▸ h1)
      obtain ⟨v,hv,ne⟩:=diff
      refine ⟨fun x=>decide (x v=d v),Or.inr ⟨v,d v,rfl⟩,?_,?_⟩
      · intro x hx
        simp [exceptionCoordinate left hv hx ha,ne]
      · intro x hx
        simp [exceptionCoordinate right hv hx hd]
    · exact ⟨fun _=>false,Or.inl ⟨false,rfl⟩,fun _ _=>rfl,fun x hx=>False.elim (r ⟨x,hx⟩)⟩
  · exact ⟨fun _=>true,Or.inl ⟨true,rfl⟩,fun x hx=>False.elim (l ⟨x,hx⟩),fun _ _=>rfl⟩

end PEqualNP.Outside.L_pcx_119_analysis
namespace PEqualNP.Outside.L_pcx_119_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_119_analysis PEqualNP.Outside.L_pcx_119_compile
variable {V : Type} [DecidableEq V]

def yesC (v : V) : Clause V := {(v,true),(v,false)}
private theorem topYes (v : V) (x : V→Bool) : ClauseSat x (yesC v) := by
  cases hx:x v
  · exact ⟨(v,false),by simp [yesC],hx⟩
  · exact ⟨(v,true),by simp [yesC],hx⟩

private theorem noEmpty (x : V→Bool) : ¬ClauseSat x (∅ : Clause V) := by simp [ClauseSat]
private theorem whenPlain {C : LinClause V} (k : extras C=∅) (x : V→Bool) :
    LinClauseSat x C ↔ ClauseSat x (plainPart C) := by simp [realParts,Real,k]
private theorem imagePlain {C : LinClause V} (k : extras C=∅) (M : LinEq V→Clause V) (x : V→Bool) :
    ClauseSat x (imageC M C) ↔ ClauseSat x (plainPart C) := by simp [imageParts,k]

private def compatible (s : Finset (LinEq V)) := ∀f,(f,false)∈s → (f,true)∉s
private def oppositeEq (d e : LinEq V) := d.1=e.1 ∧ d.2≠e.2
private def chosen (s : Finset (LinEq V)) (A : Clause V) (q : LinEq V) : Clause V :=
  if q∈s then A else ∅
private theorem chosenDisj {s : Finset (LinEq V)} (cs : compatible s) (A : Clause V) :
    DisjointSigns (chosen s A) := by
  intro f x hl hr
  by_cases l : (f,false)∈s
  · have r:=cs f l
    exact noEmpty x (by simpa [chosen,r] using hr)
  · exact noEmpty x (by simpa [chosen,l] using hl)
private theorem chosenGood (s : Finset (LinEq V)) (v : V) {q : LinEq V} {D : LinClause V}
    (hq : q∈s) (hd : q∈extras D) (x : V→Bool) : ClauseSat x (imageC (chosen s (yesC v)) D) := by
  apply (imageParts _ _ _).2
  exact Or.inr ⟨q,hd,by simpa [chosen,hq] using topYes v x⟩
private theorem oneCompatible (q : LinEq V) : compatible {q} := by
  intro f a b
  simp only [Finset.mem_singleton] at a b
  have := congrArg Prod.snd (a.trans b.symm)
  contradiction
private theorem pairCompatible {d e : LinEq V} (h : ¬oppositeEq d e) : compatible {d,e} := by
  intro f a b
  simp only [Finset.mem_insert,Finset.mem_singleton] at a b
  rcases a with eq|eq <;> rcases b with eq'|eq'
  · have impossible := congrArg Prod.snd (eq.trans eq'.symm)
    contradiction
  · apply h
    rw [←eq,←eq']
    exact ⟨rfl,by intro k; cases k⟩
  · apply h
    rw [←eq,←eq']
    exact ⟨rfl,by intro k; cases k⟩
  · have impossible := congrArg Prod.snd (eq.trans eq'.symm)
    contradiction

abbrev RealWeak (P D : LinClause V) := ∀x,LinClauseSat x P → LinClauseSat x D
abbrev ImageWeak (M : LinEq V→Clause V) (P D : LinClause V) :=
  ∀x,ClauseSat x (imageC M P) → ClauseSat x (imageC M D)

private theorem binaryParity {f : Finset V} {b : Bool} (x : V→Bool) :
    ¬LinEqSat x (f,!b) ↔ LinEqSat x (f,b) := by cases b <;> simp [LinEqSat]

private theorem concrete (v0 : V) {t : (V→Bool)→Bool} (ht : RawTest t) :
    ∃G : Bool→Clause V,∀s x,ClauseSat x (G s) ↔ t x=s := by
  rcases ht with ⟨b,rfl⟩|⟨v,b,rfl⟩
  · refine ⟨fun s=>if b=s then yesC v0 else ∅,?_⟩
    intro s x
    by_cases h:b=s <;> simp [h,topYes,noEmpty]
  · refine ⟨fun s=>{(v,if s then b else !b)},?_⟩
    intro s x
    cases s <;> cases b <;> cases hv:x v <;> simp [ClauseSat,hv]

private theorem signedSep {P A Q B : Clause V} {f : Finset V} {b : Bool}
    (l : ∀x,Exception P A x → LinEqSat x (f,b))
    (r : ∀x,Exception Q B x → LinEqSat x (f,!b)) :
    ∃t,RawTest t ∧ (∀x,Exception P A x → t x=b) ∧ ∀x,Exception Q B x → t x= !b := by
  cases b
  · exact separator l r
  · obtain ⟨t,g,h0,h1⟩:=separator r l
    exact ⟨t,g,h1,h0⟩

private theorem singlePair (v0 : V) {P D Q E : LinClause V} {f : Finset V} {b : Bool}
    (p0 : extras P=∅) (ed : extras D={(f,b)}) (ee : extras E={(f,!b)})
    (qsub : extras Q ⊆ extras D) (pd : RealWeak P D) (qe : RealWeak Q E) :
    ∃M,DisjointSigns M ∧ ImageWeak M P D ∧ ImageWeak M Q E := by
  classical
  let B := if (f,b)∈extras Q then yesC v0 else plainPart Q
  have l (x : V→Bool) (hx : Exception (plainPart P) (plainPart D) x) : LinEqSat x (f,b) := by
    obtain h|h:=(realParts x D).1 (pd x ((whenPlain p0 x).2 hx.1))
    · exact (hx.2 h).elim
    · simpa [Real,ed] using h
  have r (x : V→Bool) (hx : Exception B (plainPart E) x) : LinEqSat x (f,!b) := by
    by_contra fail
    have old:LinClauseSat x Q := by
      apply (realParts _ _).2
      by_cases has : (f,b)∈extras Q
      · exact Or.inr ⟨_,has,(binaryParity x).1 fail⟩
      · exact Or.inl (by simpa [B,has] using hx.1)
    obtain yes|yes:=(realParts x E).1 (qe x old)
    · exact hx.2 yes
    · exact fail (by simpa [Real,ee] using yes)
  obtain ⟨t,ht,tl,tr⟩:=signedSep l r
  obtain ⟨G,gg⟩:=concrete v0 ht
  let M (q : LinEq V) : Clause V := if q.1=f then G q.2 else ∅
  have test (s : Bool) (x : V→Bool) : ClauseSat x (M (f,s)) ↔ t x=s := by simpa [M] using gg s x
  refine ⟨M,?_,?_,?_⟩
  · intro k x a c
    by_cases h:k=f
    · subst k
      have := ((test _ x).1 a).symm.trans ((test _ x).1 c)
      contradiction
    · exact noEmpty x (by simpa [M,h] using a)
  · intro x xp
    apply (imageParts _ _ _).2
    by_cases yes : ClauseSat x (plainPart D)
    · exact Or.inl yes
    · exact Or.inr ⟨(f,b),by simp [ed],(test b x).2 (tl x ⟨(imagePlain p0 M x).1 xp,yes⟩)⟩
  · intro x xq
    apply (imageParts _ _ _).2
    by_cases yes : ClauseSat x (plainPart E)
    · exact Or.inl yes
    · have active : ClauseSat x B := by
        by_cases has : (f,b)∈extras Q
        · simpa [B,has] using topYes v0 x
        · obtain old|⟨q,hq,_⟩:=(imageParts _ _ _).1 xq
          · simpa [B,has] using old
          · have eq : q=(f,b) := by simpa [ed] using qsub hq
            exact (has (eq ▸ hq)).elim
      exact Or.inr ⟨(f,!b),by simp [ee],(test _ _).2 (tr x ⟨active,yes⟩)⟩

theorem twoImages (v0 : V) {P D Q E : LinClause V} (p0 : extras P=∅)
    (qsub : extras Q⊆extras D) (pd : RealWeak P D) (qe : RealWeak Q E) :
    ∃M,DisjointSigns M ∧ ImageWeak M P D ∧ ImageWeak M Q E := by
  classical
  by_cases dnon : (extras D).Nonempty
  · obtain ⟨d,dd⟩:=dnon
    by_cases enon : (extras E).Nonempty
    · obtain ⟨e,ee⟩:=enon
      by_cases pair : ∃q∈extras D,∃r∈extras E,¬oppositeEq q r
      · obtain ⟨q,qd,r,re,ok⟩:=pair
        exact ⟨chosen {q,r} (yesC v0),chosenDisj (pairCompatible ok) _,
          fun x _=>chosenGood {q,r} v0 (by simp) qd x,
          fun x _=>chosenGood {q,r} v0 (by simp) re x⟩
      · push_neg at pair
        have op:=pair d dd e ee
        have oe : e=(d.1,!d.2) := by
          apply Prod.ext
          · exact op.1.symm
          change e.2= !d.2
          cases hd:d.2 <;> cases he:e.2 <;> simp_all [oppositeEq]
        have ds : extras D={d} := by
          ext q
          simp only [Finset.mem_singleton]
          constructor
          · intro hq
            have h:=pair q hq e ee
            apply Prod.ext (h.1.trans op.1.symm)
            cases h1:q.2 <;> cases h2:d.2 <;> cases h3:e.2 <;> simp_all [oppositeEq]
          · rintro rfl;exact dd
        have es : extras E={e} := by
          ext q
          simp only [Finset.mem_singleton]
          constructor
          · intro hq
            have h:=pair d dd q hq
            apply Prod.ext (h.1.symm.trans op.1)
            cases h1:q.2 <;> cases h2:d.2 <;> cases h3:e.2 <;> simp_all [oppositeEq]
          · rintro rfl;exact ee
        exact singlePair v0 p0 ds (es.trans (congrArg _ oe)) qsub pd qe
    · have ez:extras E=∅ := Finset.not_nonempty_iff_eq_empty.mp enon
      by_cases missing : ∃q∈extras D,q∉extras Q
      · obtain ⟨q,qd,qn⟩:=missing
        let M:=chosen {q} (yesC v0)
        refine ⟨M,chosenDisj (oneCompatible q) _,fun x _=>chosenGood {q} v0 (by simp) qd x,?_⟩
        intro x xq
        apply (imagePlain ez M x).2
        apply (whenPlain ez x).1
        apply qe x
        apply (realParts _ _).2
        rcases (imageParts _ _ _).1 xq with h|⟨i,iq,on⟩
        · exact Or.inl h
        · have ne:i≠q := fun eq=>qn (eq ▸ iq)
          exact (noEmpty x (by simpa [M,chosen,ne] using on)).elim
      · push_neg at missing
        have transfer (x : V→Bool) {q : LinEq V} (qd : q∈extras D) (on : LinEqSat x q) :
            ClauseSat x (plainPart E) :=
          (whenPlain ez x).1 (qe x ((realParts x Q).2 (Or.inr ⟨q,missing q qd,on⟩)))
        by_cases clean : compatible (extras D)
        · let M:=chosen (extras D) (plainPart E)
          refine ⟨M,chosenDisj clean _,?_,?_⟩
          · intro x xp
            apply (imageParts _ _ _).2
            rcases (realParts _ _).1 (pd x ((whenPlain p0 x).2 ((imagePlain p0 M x).1 xp))) with h|⟨q,dq,on⟩
            · exact Or.inl h
            · exact Or.inr ⟨q,dq,by simpa [M,chosen,dq] using transfer x dq on⟩
          · intro x xq
            apply (imagePlain ez M x).2
            obtain p|⟨q,iq,on⟩:=(imageParts _ _ _).1 xq
            · exact (whenPlain ez x).1 (qe x ((realParts x Q).2 (Or.inl p)))
            · simpa [M,chosen,qsub iq] using on
        · have clash : ∃f,(f,false)∈extras D ∧ (f,true)∈extras D := by
            unfold compatible at clean
            push_neg at clean
            exact clean
          obtain ⟨f,h0,h1⟩:=clash
          refine ⟨chosen {d} (yesC v0),chosenDisj (oneCompatible d) _,
            fun x _=>chosenGood {d} v0 (by simp) dd x,?_⟩
          intro x _
          apply (imagePlain ez _ x).2
          by_cases pos:LinEqSat x (f,true)
          · exact transfer x h1 pos
          · exact transfer x h0 ((binaryParity (b:=false) x).1 pos)
  · have dz : extras D=∅ := Finset.not_nonempty_iff_eq_empty.mp dnon
    have qz : extras Q=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun q h=>by simpa [dz] using qsub h)
    have first (M : LinEq V→Clause V) : ImageWeak M P D :=
      fun x h=>(imagePlain dz M x).2 ((whenPlain dz x).1 (pd x ((whenPlain p0 x).2 ((imagePlain p0 M x).1 h))))
    by_cases enon:(extras E).Nonempty
    · obtain ⟨e,ee⟩:=enon
      exact ⟨chosen {e} (yesC v0),chosenDisj (oneCompatible e) _,first _,
        fun x _=>chosenGood {e} v0 (by simp) ee x⟩
    · have ez : extras E=∅ := Finset.not_nonempty_iff_eq_empty.mp enon
      let M : LinEq V→Clause V := fun _=>∅
      exact ⟨M,fun _ x h=>False.elim (noEmpty x h),first M,
        fun x h=>(imagePlain ez M x).2 ((whenPlain ez x).1 (qe x ((whenPlain qz x).2 ((imagePlain qz M x).1 h))))⟩

end PEqualNP.Outside.L_pcx_119_image
namespace PEqualNP.Outside.L_pcx_119_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_119_compile
variable {V : Type} [DecidableEq V]

private theorem realLog {F : Set (LinClause V)} {W π} (h : Log F W π) :
    ∀p∈W,RealWeak p.1 p.2 := by
  induction h with
  | nil => simp
  | ax _ _ ih => exact ih
  | res _ _ _ _ ih => exact ih
  | weak _ _ wk ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl|old
    · exact wk
    · exact ih _ old

private theorem tailOrder {p : LinClause V × LinClause V} {W} (ok : Ordered (p::W)) :
    Ordered W ∧ AllEarlier W p.1 := by cases ok;constructor <;> assumption
private theorem noPrior {P : LinClause V} (h : AllEarlier [] P) : extras P=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  simpa using h q hq

theorem twoWeakRefutation (v0 : V) {F : Set (Clause V)} {W π}
    (h : Log (linOfClause '' F) W π) (few : W.length≤2) (empty : (∅ : LinClause V)∈π) :
    ∃ρ, IsRefutation F ρ ∧ ρ.length+W.length≤π.length := by
  classical
  have ordered := (history h).1
  have wk := realLog h
  have maps : ∃M : LinEq V→Clause V,DisjointSigns M ∧ ∀p∈W, ImageWeak M p.1 p.2 := by
    rcases W with _|⟨⟨Q,E⟩,W⟩
    · exact ⟨fun _=>∅,fun _ x h=>False.elim (by simpa [ClauseSat] using h),by simp⟩
    rcases W with _|⟨⟨P,D⟩,W⟩
    · have q0:=noPrior (tailOrder ordered).2
      have ee : extras (∅ : LinClause V)=∅ := by simp [extras]
      obtain ⟨M,ok,_,valid⟩:=twoImages v0 (P:=∅) (D:=∅) ee (by rw [q0,ee]) (fun _ a=>a) (wk (Q,E) (by simp))
      refine ⟨M,ok,?_⟩
      intro p hp
      have eq:p=(Q,E) := by simpa using hp
      exact eq ▸ valid
    have emptyW : W=[] := by
      have sz : W.length=0 := by
        change W.length+1+1≤2 at few
        omega
      exact List.length_eq_zero_iff.mp sz
    subst W
    have qprior := (tailOrder ordered).2
    have p0 := noPrior (tailOrder (tailOrder ordered).1).2
    have qd : extras Q⊆extras D := by
      intro q hq
      simpa using qprior q hq
    obtain ⟨M,ok,vp,vq⟩:=twoImages v0 p0 qd (wk (P,D) (by simp)) (wk (Q,E) (by simp))
    refine ⟨M,ok,?_⟩
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · exact vq
    · exact vp
  obtain ⟨M,disj,weakens⟩:=maps
  obtain ⟨ρ,der,len,track⟩:=compile h (imageC M) (fun A _=>plainLift A M) (validRes M disj) weakens
  refine ⟨ρ,⟨der,?_⟩,len⟩
  have tr:=track ∅ empty
  rw [imageEmpty] at tr
  rcases tr with t|⟨C,mem,sub⟩
  · exact False.elim (by simpa [ClauseSat] using t (fun _=>false))
  · have eq : C=∅ := Finset.Subset.antisymm sub (Finset.empty_subset _)
    exact eq ▸ mem

end PEqualNP.Outside.L_pcx_119_image

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
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
variable {V U : Type} [DecidableEq V] [DecidableEq U]
inductive Paid (T : Frame V U) (F : Set (LinClause V)) : List (LinClause V) → Nat → Prop
| nil : Paid T F [] 0
| ax {π n A} : Paid T F π n → A ∈ F →
    Paid T F (A::π) n
| weak {π n C A} : Paid T F π n → C∈π → (∀ a, LinClauseSat a C → LinClauseSat a A) →
    Paid T F (A::π) (n + if top T A then 0 else 1)
| res {π n C D A} : Paid T F π n → C∈π → D∈π → IsLinResolvent C D A →
    Paid T F (A::π) (n + if top T A ∨ top T C ∨ top T D then 0 else 1)

theorem choosePaid (T : Frame V U) {F : Set (LinClause V)} {π} (der : IsLinDerivation F π) :
    ∃ n≤π.length, Paid T F π n := by
  induction der with
  | nil => exact ⟨0,by simp,.nil⟩
  | @ax π A d ha ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n,by simp only [List.length_cons]; omega,.ax h ha⟩
  | @weak π C A d hc w ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n+(if top T A then 0 else 1),by simp only [List.length_cons]; split <;> omega,.weak h hc w⟩
  | @res π C D A d hc hd rule ih =>
    obtain ⟨n,le,h⟩ := ih
    exact ⟨n+(if top T A ∨ top T C ∨ top T D then 0 else 1),by simp only [List.length_cons]; split <;> omega,.res h hc hd rule⟩

theorem prepaid (T : Frame V U) (lift : (U→Bool) → V→Bool)
    (eval : ∀ x q, LinEqSat (lift x) q ↔ LinEqSat x (imageEq T q))
    (F : Set (LinClause V)) (G : Set (LinClause U)) (anchor : LinClause U) (initial : List (LinClause U))
    (validInitial : IsLinDerivation G initial) (rootMem : anchor∈initial)
    (axes : ∀ C∈F, ¬top T C → body T C∈initial) {π n} (der : Paid T F π n) :
    ∃ ρ, IsLinDerivation G ρ ∧ (∀ A∈initial, A∈ρ) ∧ ρ.length≤n+initial.length ∧ Reps T π ρ := by
  classical
  induction der with
  | nil => exact ⟨initial,validInitial,fun _ h => h,by simp,by simp [Reps]⟩
  | @ax π n C d ha ih =>
    obtain ⟨ρ,proof,anc,le,rep⟩ := ih
    exact ⟨ρ,proof,anc,le,skip rep (fun nt => ⟨_,anc _ (axes C ha nt),Subset.rfl⟩)⟩
  | @weak π n C A d hc w ih =>
    obtain ⟨ρ,proof,anc,le,rep⟩ := ih
    by_cases ta : top T A
    · exact ⟨ρ,proof,anc,by simpa [ta] using le,skip rep (fun f => False.elim (f ta))⟩
    · have haveParent : ∃ D∈ρ, ∀ x, LinClauseSat x D → LinClauseSat x (body T C) := by
        by_cases tc : top T C
        · exact ⟨anchor,anc _ rootMem,fun x _ => topOn T tc x⟩
        · obtain ⟨D,mem,sub⟩ := rep C hc tc
          exact ⟨D,mem,fun x ⟨q,m,h⟩ => ⟨q,sub m,h⟩⟩
      obtain ⟨D,mem,imp⟩ := haveParent
      have valid (x) (h : LinClauseSat x D) : LinClauseSat x (body T A) :=
        (body_semantic T lift eval x A).2 (w (lift x) ((body_semantic T lift eval x C).1 (imp x h)))
      exact ⟨_,.weak proof mem valid,(fun Z m => List.mem_cons_of_mem _ (anc Z m)),
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
    have newLe : ρ.length+1 ≤ (n+if top T A ∨ top T C ∨ top T D then 0 else 1)+initial.length := by
      simp only [ta,tc,td,false_or,if_false]; omega
    rcases splitOptions T rule B E bc ed with h|h|⟨Z,sub,rr⟩
    · exact ⟨ρ,proof,anc,by omega,skip rep (fun _ => ⟨B,mb,h⟩)⟩
    · exact ⟨ρ,proof,anc,by omega,skip rep (fun _ => ⟨E,me,h⟩)⟩
    · have line : IsLinDerivation G (Z::ρ) := rr.elim (fun h => .res proof mb me h) (fun h => .res proof me mb h)
      exact ⟨_,line,(fun Z m => List.mem_cons_of_mem _ (anc Z m)),by simpa using newLe,added rep sub⟩
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

def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) := {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (LinClause (Fin m × Fin n)) :=
  (univ.image (fun i => linOfClause (pigeon m n i))) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => linOfClause (collision m n v.1 v.2.1 v.2.2)))
theorem raw_spec {m n : Nat} {C : LinClause (Fin m×Fin n)} :
    C∈raw m n ↔ C∈linOfClause '' PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact ⟨_,Or.inl ⟨i,rfl⟩,rfl⟩
    · exact ⟨_,Or.inr ⟨i,k,j,ne,rfl⟩,rfl⟩
  · rintro ⟨A,(⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩),rfl⟩
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem rowTable : ∀ p h (i : Fin 5), top (face p h) (linOfClause (pigeon 5 4 i)) ∨
    body (face p h) (linOfClause (pigeon 5 4 i))∈raw 4 3 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem pairTable : ∀ p h (i k : Fin 5) (j : Fin 4), i≠k →
    top (face p h) (linOfClause (collision 5 4 i k j)) ∨
    body (face p h) (linOfClause (collision 5 4 i k j))∈raw 4 3 := by decide +kernel
theorem axTable (p h) (C : LinClause Big) (hc : C∈linOfClause '' PHP 5 4) :
    top (face p h) C ∨ body (face p h) C∈raw 4 3 := by
  rcases hc with ⟨A,(⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩),rfl⟩
  · exact rowTable p h i
  · exact pairTable p h i k j ne
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem removed : ∀ p h, ((raw 5 4).filter (top (face p h))).card=23 := by decide +kernel
end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset
private theorem axiomsDer {U : Type} [DecidableEq U] (G : Set (LinClause U)) (L : List (LinClause U))
    (mem : ∀ A∈L,A∈G) : IsLinDerivation G L := by
  induction L with
  | nil => exact .nil
  | cons A L ih => exact .ax (ih (fun B h => mem B (List.mem_cons_of_mem _ h))) (mem A List.mem_cons_self)

theorem twentySix (p : Fin 5) (h : Fin 4) {π n} (empty : (∅:LinClause Big)∈π)
    (cost : Paid (face p h) (linOfClause '' PHP 5 4) π n) : 26≤n := by
  classical
  let G := linOfClause '' PHP 4 3
  let initial := (raw 4 3).toList
  let anchor := linOfClause (pigeon 4 3 0)
  have anchorRaw : anchor∈raw 4 3 := raw_spec.mpr ⟨_,Or.inl ⟨0,rfl⟩,rfl⟩
  have inBank : anchor∈initial := mem_toList.mpr anchorRaw
  have valid : IsLinDerivation G initial := axiomsDer G initial
    (fun _ m => raw_spec.mp (mem_toList.mp m))
  have axes (C) (m : C∈linOfClause '' PHP 5 4) (nt : ¬top (face p h) C) :
      body (face p h) C∈initial := mem_toList.mpr ((axTable p h C m).resolve_left nt)
  obtain ⟨ρ,der,_,len,rep⟩ := prepaid (face p h) _ (faceEval p h) _ _ anchor initial valid inBank axes cost
  obtain ⟨E,mem,sub⟩ := rep _ empty (by simp [top])
  have e : E=∅ := eq_empty_iff_forall_notMem.mpr (fun z hz => by simpa [body] using sub hz)
  have ref : IsLinRefutation (PHP 4 3) ρ := ⟨der,e ▸ mem⟩
  have size : (raw 4 3).card=22 := by decide +kernel
  have lsize : initial.length=22 := by simpa only [initial,Finset.length_toList] using size
  by_contra! small
  exact PEqualNP.Outside.L_pcx_118 ⟨ρ,ref,by omega⟩
end PEqualNP.Outside.L_pcx_178.Restrict

namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset PEqualNP.Outside.L_pcx_119_compile
variable {V U : Type} [DecidableEq V] [DecidableEq U]
inductive Ledger (T : Frame V U) (F : Set (LinClause V)) : List (LinClause V) → Nat → Nat → Prop
| nil : Ledger T F [] 0 0
| ax {π w r A} : Ledger T F π w r → A∈F → Ledger T F (A::π) w r
| weak {π w r C A} : Ledger T F π w r → C∈π → (∀ a, LinClauseSat a C → LinClauseSat a A) →
    Ledger T F (A::π) (w + if top T A then 0 else 1) r
| res {π w r C D A} : Ledger T F π w r → C∈π → D∈π → IsLinResolvent C D A →
    Ledger T F (A::π) w (r + if top T A ∨ top T C ∨ top T D then 0 else 1)
theorem projectedLog (T : Frame V U) (lift : (U→Bool) → V→Bool)
    (eval : ∀ x q, LinEqSat (lift x) q ↔ LinEqSat x (imageEq T q))
    (F : Set (LinClause V)) (G : Set (LinClause U)) (anchor : LinClause U) (initial : List (LinClause U))
    (validInitial : Log G [] initial) (rootMem : anchor∈initial)
    (axes : ∀ C∈F, ¬top T C → body T C∈initial) {π w r} (der : Ledger T F π w r) :
    ∃ W ρ, Log G W ρ ∧ W.length=w ∧ (∀ A∈initial, A∈ρ) ∧ ρ.length≤w+r+initial.length ∧ Reps T π ρ := by
  classical
  induction der with
  | nil => exact ⟨[],initial,validInitial,rfl,fun _ h => h,by simp,by simp [Reps]⟩
  | @ax π w r C d ha ih =>
    obtain ⟨W,ρ,proof,wl,anc,le,rep⟩ := ih
    exact ⟨W,ρ,proof,wl,anc,le,skip rep (fun nt => ⟨_,anc _ (axes C ha nt),Subset.rfl⟩)⟩
  | @weak π w r C A d hc wk ih =>
    obtain ⟨W,ρ,proof,wl,anc,le,rep⟩ := ih
    by_cases ta : top T A
    · exact ⟨W,ρ,proof,by simpa [ta] using wl,anc,by simpa [ta] using le,skip rep (fun f => False.elim (f ta))⟩
    · have haveParent : ∃ D∈ρ, ∀ x, LinClauseSat x D → LinClauseSat x (body T C) := by
        by_cases tc : top T C
        · exact ⟨anchor,anc _ rootMem,fun x _ => topOn T tc x⟩
        · obtain ⟨D,mem,sub⟩ := rep C hc tc
          exact ⟨D,mem,fun x ⟨q,m,h⟩ => ⟨q,sub m,h⟩⟩
      obtain ⟨D,mem,imp⟩ := haveParent
      have valid (x) (h : LinClauseSat x D) : LinClauseSat x (body T A) :=
        (body_semantic T lift eval x A).2 (wk (lift x) ((body_semantic T lift eval x C).1 (imp x h)))
      exact ⟨_,_,.weak proof mem valid,by simp [wl,ta],(fun Z m => List.mem_cons_of_mem _ (anc Z m)),
        by simp only [if_neg ta,List.length_cons]; omega,added rep Subset.rfl⟩
  | @res π w r C D A d hc hd rule ih =>
    obtain ⟨W,ρ,proof,wl,anc,le,rep⟩ := ih
    by_cases ta : top T A
    · exact ⟨W,ρ,proof,wl,anc,by simpa [ta] using le,skip rep (fun f => False.elim (f ta))⟩
    have direct := dropParent T rule ta
    by_cases tc : top T C
    · obtain ⟨B,mem,sub⟩ := rep D hd (direct.1 tc).1
      exact ⟨W,ρ,proof,wl,anc,by simpa [tc] using le,skip rep (fun _ => ⟨B,mem,sub.trans (direct.1 tc).2⟩)⟩
    by_cases td : top T D
    · obtain ⟨B,mem,sub⟩ := rep C hc (direct.2 td).1
      exact ⟨W,ρ,proof,wl,anc,by simpa [td] using le,skip rep (fun _ => ⟨B,mem,sub.trans (direct.2 td).2⟩)⟩
    obtain ⟨B,mb,bc⟩ := rep C hc tc
    obtain ⟨E,me,ed⟩ := rep D hd td
    have newLe : ρ.length+1 ≤ w+(r+if top T A ∨ top T C ∨ top T D then 0 else 1)+initial.length := by
      simp only [ta,tc,td,false_or,if_false]; omega
    rcases splitOptions T rule B E bc ed with h|h|⟨Z,sub,rr⟩
    · exact ⟨W,ρ,proof,wl,anc,by omega,skip rep (fun _ => ⟨B,mb,h⟩)⟩
    · exact ⟨W,ρ,proof,wl,anc,by omega,skip rep (fun _ => ⟨E,me,h⟩)⟩
    · have line : Log G W (Z::ρ) := rr.elim (fun h => .res proof mb me h) (fun h => .res proof me mb h)
      exact ⟨W,_,line,wl,(fun Z m => List.mem_cons_of_mem _ (anc Z m)),by simpa using newLe,added rep sub⟩

end PEqualNP.Outside.L_pcx_178.Restrict
namespace PEqualNP.Outside.L_pcx_178.Restrict
open PEqualNP.ProofComplexity Finset PEqualNP.Outside.L_pcx_119_compile
private theorem rawLog {U : Type} [DecidableEq U] (G : Set (LinClause U)) (L : List (LinClause U))
    (mem : ∀ A∈L,A∈G) : Log G [] L := by
  induction L with
  | nil => exact .nil
  | cons A L ih => exact .ax (ih (fun B h => mem B (List.mem_cons_of_mem _ h))) (mem A List.mem_cons_self)

theorem thirtyBinary (p : Fin 5) (h : Fin 4) {π w r} (empty : (∅:LinClause Big)∈π)
    (cost : Ledger (face p h) (linOfClause '' PHP 5 4) π w r) (few : w≤2) : 30≤r := by
  classical
  let G := linOfClause '' PHP 4 3
  let initial := (raw 4 3).toList
  let anchor := linOfClause (pigeon 4 3 0)
  have anchorRaw : anchor∈raw 4 3 := raw_spec.mpr ⟨_,Or.inl ⟨0,rfl⟩,rfl⟩
  have inBank : anchor∈initial := mem_toList.mpr anchorRaw
  have valid : Log G [] initial := rawLog G initial
    (fun _ m => raw_spec.mp (mem_toList.mp m))
  have axes (C) (m : C∈linOfClause '' PHP 5 4) (nt : ¬top (face p h) C) :
      body (face p h) C∈initial := mem_toList.mpr ((axTable p h C m).resolve_left nt)
  obtain ⟨W,ρ,der,wl,_,len,rep⟩ := projectedLog (face p h) _ (faceEval p h) _ _ anchor initial valid inBank axes cost
  obtain ⟨E,mem,sub⟩ := rep _ empty (by simp [top])
  have e : E=∅ := eq_empty_iff_forall_notMem.mpr (fun z hz => by simpa [body] using sub hz)
  have sz : (raw 4 3).card=22 := by decide +kernel
  have lsize : initial.length=22 := by simpa only [initial,Finset.length_toList] using sz
  obtain ⟨σ,ref,ole⟩ := PEqualNP.Outside.L_pcx_119_image.twoWeakRefutation ((0,0):Little) der (by omega) (e ▸ mem)
  by_contra! small
  exact PEqualNP.Outside.L_pcx_150 ⟨σ,ref,by omega⟩

inductive FaceLedger (F : Set (LinClause Big)) :
    List (LinClause Big) → (Big→Nat) → (Big→Nat) → Prop
| nil : FaceLedger F [] (fun _=>0) (fun _=>0)
| ax {π w r A} : FaceLedger F π w r → A∈F → FaceLedger F (A::π) w r
| weak {π w r C A} : FaceLedger F π w r → C∈π → (∀ a, LinClauseSat a C → LinClauseSat a A) →
    FaceLedger F (A::π) (fun z => w z + if top (face z.1 z.2) A then 0 else 1) r
| res {π w r C D A} : FaceLedger F π w r → C∈π → D∈π → IsLinResolvent C D A →
    FaceLedger F (A::π) w (fun z => r z + if top (face z.1 z.2) A ∨ top (face z.1 z.2) C ∨ top (face z.1 z.2) D then 0 else 1)

theorem oneSchedule {F π} (d : IsLinDerivation F π) : ∃w r, FaceLedger F π w r := by
  induction d with
  | nil => exact ⟨_,_,.nil⟩
  | ax _ m ih => obtain ⟨w,r,d⟩:=ih; exact ⟨_,_,.ax d m⟩
  | weak _ m s ih => obtain ⟨w,r,d⟩:=ih; exact ⟨_,_,.weak d m s⟩
  | res _ a b s ih => obtain ⟨w,r,d⟩:=ih; exact ⟨_,_,.res d a b s⟩

theorem atFace {F π w r} (d : FaceLedger F π w r) (z : Big) :
    Ledger (face z.1 z.2) F π (w z) (r z) := by
  induction d with
  | nil => exact .nil
  | ax _ m ih => exact .ax ih m
  | weak _ m s ih => exact .weak ih m s
  | res _ a b s ih => exact .res ih a b s

theorem oldFee {V U : Type} [DecidableEq V] [DecidableEq U] {F π w r} {T : Frame V U}
    (d : Ledger T F π w r) : Paid T F π (w+r) := by
  induction d with
  | nil => exact .nil
  | ax _ m ih => exact .ax ih m
  | weak _ m s ih => simpa only [Nat.add_right_comm] using Paid.weak ih m s
  | res _ a b s ih => simpa only [Nat.add_assoc] using Paid.res ih a b s

theorem sameTracePrices {π} (ref : IsLinRefutation (PHP 5 4) π) :
    ∃w r, FaceLedger (linOfClause '' PHP 5 4) π w r ∧
       ∀ z, 26≤w z + r z ∧ (w z ≤ 2 → 30 ≤ r z) := by
  obtain ⟨w,r,s⟩:=oneSchedule ref.1
  exact ⟨w,r,s,fun z => ⟨twentySix z.1 z.2 ref.2 (oldFee (atFace s z)),thirtyBinary z.1 z.2 ref.2 (atFace s z)⟩⟩
end PEqualNP.Outside.L_pcx_178.Restrict

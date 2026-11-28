import PEqualNP.Defs

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

namespace Pcx180Bridge
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
abbrev LC := LinClause V
abbrev OC := Clause V
def liftLit (l : Literal V) : LinEq V := ({l.1},l.2)

inductive Counted (F : Set (LinClause V)) : Nat → List (LinClause V) → Prop where
| nil : Counted F 0 []
| ax {k π C} : Counted F k π → C ∈ F → Counted F k (C::π)
| res {k π C D R} : Counted F k π → C ∈ π → D ∈ π → IsLinResolvent C D R → Counted F k (R::π)
| weak {k π C D} : Counted F k π → C ∈ π →
    (∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D) → Counted F (k+1) (D::π)

theorem countedExists {F : Set (LinClause V)} {π} (h : IsLinDerivation F π) :
    ∃ k, Counted F k π := by
  induction h with
  | nil => exact ⟨0,.nil⟩
  | ax _ hc ih => obtain ⟨k,h⟩ := ih; exact ⟨k,.ax h hc⟩
  | res _ hc hd hr ih => obtain ⟨k,h⟩ := ih; exact ⟨k,.res h hc hd hr⟩
  | weak _ hc hw ih => obtain ⟨k,h⟩ := ih; exact ⟨k+1,.weak h hc hw⟩

def Plain (A : LinClause V) := ∀ q ∈ A, ∃ v : V, q.1 = {v}
def BadMark (e : Option (LinEq V)) := ∀ q, e=some q → q.1.card≠1
def Taut (A : LinClause V) := ∃ v : V, liftLit (v,true) ∈ A ∧ liftLit (v,false) ∈ A
def Good (e : Option (LinEq V)) (ρ : List (Clause V)) (A : LinClause V) : Prop :=
  (∃ q ∈ A, e = some q) ∨ Taut A ∨ ∃ B ∈ ρ, ∀ l ∈ B, liftLit l ∈ A

theorem expandGood {e : Option (LinEq V)} {ρ σ : List (Clause V)} {A B : LinClause V}
    (h : Good e ρ A) (mem : ∀ c ∈ ρ, c ∈ σ) (inc : A ⊆ B) : Good e σ B := by
  rcases h with ⟨q,hq,eq⟩ | ⟨v,ht,hf⟩ | ⟨Q,hQ,hsub⟩
  · exact Or.inl ⟨q,inc hq,eq⟩
  · exact Or.inr (Or.inl ⟨v,inc ht,inc hf⟩)
  · exact Or.inr (Or.inr ⟨Q,mem _ hQ,fun l hl => inc (hsub l hl)⟩)

theorem oldmark {e d : Option (LinEq V)} {ρ : List (Clause V)} {A : LinClause V}
    (bad : BadMark e) (p : Plain A) (h : Good e ρ A) : Good d ρ A := by
  rcases h with ⟨q,hq,eq⟩|ordinary
  · obtain ⟨v,hv⟩ := p q hq
    exact False.elim (bad q eq (by simp [hv]))
  · exact Or.inr ordinary

theorem noWeakPlain {F : Set (Clause V)} {k π} (h : Counted (linOfClause '' F) k π) :
    k=0 → ∀ A∈π, Plain A := by
  induction h with
  | nil => simp
  | ax _ hA ih =>
    intro hk A hA'
    rcases List.mem_cons.mp hA' with rfl|ha
    · obtain ⟨B,_,rfl⟩ := hA
      intro q hq
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
      exact ⟨l.1,rfl⟩
    · exact ih hk _ ha
  | res _ hc hd hr ih =>
    intro hk A hA
    rcases List.mem_cons.mp hA with rfl|ha
    · obtain ⟨f,_,_,rfl⟩ := hr
      intro q hq
      rcases Finset.mem_union.mp hq with hq|hq
      · exact ih hk _ hc q (Finset.mem_of_mem_erase hq)
      · exact ih hk _ hd q (Finset.mem_of_mem_erase hq)
    · exact ih hk _ ha
  | weak => intro hz; omega

theorem satSingle (a : V → Bool) (v : V) (b : Bool) :
    LinEqSat a (liftLit (v,b)) ↔ a v=b := by
  cases av : a v <;> cases b <;> simp [liftLit,LinEqSat,Finset.filter_singleton,av]

theorem plainWeak {A B : LinClause V} (pa : Plain A) (pb : Plain B)
    (h : ∀ a : V → Bool, LinClauseSat a A → LinClauseSat a B) : Taut B ∨ A ⊆ B := by
  classical
  by_cases ht : Taut B
  · exact Or.inl ht
  right
  intro q hq
  obtain ⟨v,hv⟩ := pa q hq
  rcases q with ⟨q,b⟩
  change q={v} at hv
  subst q
  by_contra absent
  let a : V → Bool := fun w => if w=v then b else decide (liftLit (w,false) ∈ B)
  have here : a v=b := by simp [a]
  obtain ⟨⟨s,t⟩,hs,sat⟩ := h a ⟨liftLit (v,b),hq,(satSingle a v b).mpr here⟩
  obtain ⟨w,hw⟩ := pb (s,t) hs
  change s={w} at hw
  subst s
  have aw := (satSingle a w t).mp sat
  by_cases eq : w=v
  · subst w
    rw [here] at aw
    subst t
    exact absent hs
  · cases t with
    | false =>
      have mem : liftLit (w,false) ∈ B := hs
      simp [a,eq,mem] at aw
    | true =>
      have outside : liftLit (w,false) ∉ B := fun hit => ht ⟨w,hs,hit⟩
      simp [a,eq,outside] at aw

theorem lift_inj {p q : Literal V} (h : liftLit p = liftLit q) : p=q := by
  obtain ⟨p,b⟩ := p
  obtain ⟨q,c⟩ := q
  simpa [liftLit] using h

theorem simulateRes {F : Set (Clause V)} {ρ : List (Clause V)} (dρ : IsDerivation F ρ)
    {e : Option (LinEq V)} {C D R : LinClause V} (gc : Good e ρ C) (gd : Good e ρ D)
    (bad : BadMark e) (res : IsLinResolvent C D R) :
    ∃ σ, IsDerivation F σ ∧ σ.length ≤ ρ.length + 1 ∧
      (∀ c∈ρ, c∈σ) ∧ Good e σ R := by
  obtain ⟨f,hf,ht,hr⟩ := res
  have left {q : LinEq V} (hq : q∈C) (ne : q≠(f,false)) : q∈R := by
    rw [hr]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hq⟩)
  have right {q : LinEq V} (hq : q∈D) (ne : q≠(f,true)) : q∈R := by
    rw [hr]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hq⟩)
  have keep (h : Good e ρ R) : ∃ σ, IsDerivation F σ ∧ σ.length ≤ ρ.length+1 ∧
      (∀ c∈ρ,c∈σ) ∧ Good e σ R :=
    ⟨ρ,dρ,by omega,fun _ h => h,h⟩
  by_cases lp : (f,false)∈R
  · exact keep (expandGood gc (fun _ h => h) (by
      intro q h
      by_cases eq : q=(f,false)
      · simpa [eq] using lp
      · exact left h eq))
  by_cases rp : (f,true)∈R
  · exact keep (expandGood gd (fun _ h => h) (by
      intro q h
      by_cases eq : q=(f,true)
      · simpa [eq] using rp
      · exact right h eq))
  rcases gc with ⟨q,hq,eq⟩ | ⟨v,hv,hv'⟩ | ⟨A,hA,a⟩
  · by_cases neq : q=(f,false)
    · subst q
      rcases gd with ⟨z,hz,ez⟩ | ⟨v,hv,hv'⟩ | ⟨A,hA,a⟩
      · have zf : z=(f,false) := Option.some.inj (ez.symm.trans eq)
        subst z
        exact (lp (right hz (by simp))).elim
      · by_cases vq : liftLit (v,true) = (f,true)
        · have vf : liftLit (v,false) = (f,false) := by simpa [liftLit] using vq
          exact (lp (vf ▸ right hv' (by simp [liftLit]))).elim
        · exact keep (Or.inr (Or.inl ⟨v,right hv vq,right hv' (by simp [liftLit])⟩))
      · by_cases ex : ∃ l∈A, liftLit l=(f,true)
        · obtain ⟨l,_,hl⟩ := ex
          have hh : ({l.1}:Finset V)=f := congrArg Prod.fst hl
          exact False.elim (bad (f,false) eq (by change f.card=1; rw [←hh]; simp))
        · exact keep (Or.inr (Or.inr ⟨A,hA,fun l hl => right (a l hl) (fun he => ex ⟨l,hl,he⟩)⟩))
    · exact keep (Or.inl ⟨q,left hq neq,eq⟩)
  · by_cases vq : liftLit (v,false) = (f,false)
    · have vt : liftLit (v,true) = (f,true) := by simpa [liftLit] using vq
      exact (rp (vt ▸ left hv (by simp [liftLit]))).elim
    · exact keep (Or.inr (Or.inl ⟨v,left hv (by simp [liftLit]),left hv' vq⟩))
  · rcases gd with ⟨q,hq,eq⟩ | ⟨v,hv,hv'⟩ | ⟨B,hB,b⟩
    · by_cases neq : q=(f,true)
      · by_cases ex : ∃ l∈A, liftLit l=(f,false)
        · obtain ⟨l,_,hl⟩ := ex
          have hh : ({l.1}:Finset V)=f := congrArg Prod.fst hl
          subst q
          exact False.elim (bad (f,true) eq (by change f.card=1; rw [←hh]; simp))
        · exact keep (Or.inr (Or.inr ⟨A,hA,fun l hl => left (a l hl) (fun he => ex ⟨l,hl,he⟩)⟩))
      · exact keep (Or.inl ⟨q,right hq neq,eq⟩)
    · by_cases vq : liftLit (v,true) = (f,true)
      · have vf : liftLit (v,false) = (f,false) := by simpa [liftLit] using vq
        exact (lp (vf ▸ right hv' (by simp [liftLit]))).elim
      · exact keep (Or.inr (Or.inl ⟨v,right hv vq,right hv' (by simp [liftLit])⟩))
    · by_cases qa : ∃ l∈A, liftLit l=(f,false)
      · obtain ⟨l,hl,he⟩ := qa
        obtain ⟨w,s⟩ := l
        have hs : s=false := congrArg Prod.snd he
        subst s
        have hform : ({w} : Finset V)=f := congrArg Prod.fst he
        subst f
        by_cases hb' : (w,true) ∈ B
        · let Q := B.erase (w,true) ∪ A.erase (w,false)
          have rr : IsResolvent B A Q := ⟨w,hb',hl,rfl⟩
          refine ⟨Q::ρ,.res dρ hB hA rr,by simp,fun c hc => List.mem_cons_of_mem Q hc,
            Or.inr (Or.inr ⟨Q,by simp,?_⟩)⟩
          intro l h
          rcases Finset.mem_union.mp h with h|h
          · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
            exact right (b l mem) (fun eq => ne (lift_inj eq))
          · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
            exact left (a l mem) (fun eq => ne (lift_inj eq))
        · exact keep (Or.inr (Or.inr ⟨B,hB,fun l hl => right (b l hl)
              (fun he => hb' (lift_inj (q := (w,true)) he ▸ hl))⟩))
      · exact keep (Or.inr (Or.inr ⟨A,hA,fun l hl => left (a l hl)
          (fun he => qa ⟨l,hl,he⟩)⟩))

theorem simulateOne {F : Set (Clause V)} {k π} (h : Counted (linOfClause '' F) k π) :
    k ≤ 1 → ∃ ρ e, IsDerivation F ρ ∧ ρ.length ≤ π.length ∧ BadMark e ∧
    ∀ A ∈ π, Good e ρ A := by
  induction h with
  | nil =>
    intro _
    exact ⟨[],none,.nil,by simp,by simp [BadMark],by simp⟩
  | @ax k π A hp hax ih =>
    intro hk
    obtain ⟨ρ,e,dρ,sz,bad,rep⟩ := ih hk
    obtain ⟨B,hB,rfl⟩ := hax
    refine ⟨B::ρ,e,.ax dρ hB,by simpa using sz,bad,?_⟩
    intro T hT
    rcases List.mem_cons.mp hT with rfl|hT
    · exact Or.inr (Or.inr ⟨B,by simp,fun l hl => Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩)
    · exact expandGood (rep T hT) (fun c hc => List.mem_cons_of_mem B hc) (by intro _ h; exact h)
  | @res k π A B R hp ha hb hr ih =>
    intro hk
    obtain ⟨ρ,e,dρ,sz,bad,rep⟩ := ih hk
    obtain ⟨σ,dσ,sz',mem,new⟩ := simulateRes dρ (rep _ ha) (rep _ hb) bad hr
    refine ⟨σ,e,dσ,by simp only [List.length_cons]; omega,bad,?_⟩
    intro T hT
    rcases List.mem_cons.mp hT with rfl|hT
    · exact new
    · exact expandGood (rep T hT) mem (by intro _ h; exact h)
  | @weak k π A B hp ha hw ih =>
    intro hk
    have zero : k=0 := by omega
    have plain := noWeakPlain hp zero
    obtain ⟨ρ,e,dρ,sz,bad,rep⟩ := ih (by omega)
    by_cases pb : Plain B
    · refine ⟨ρ,e,dρ,by simp only [List.length_cons]; omega,bad,?_⟩
      intro T hT
      rcases List.mem_cons.mp hT with rfl|hT
      · rcases plainWeak (plain _ ha) pb hw with ht|inc
        · exact Or.inr (Or.inl ht)
        · exact expandGood (rep _ ha) (fun _ h => h) inc
      · exact rep T hT
    · unfold Plain at pb
      push_neg at pb
      obtain ⟨q,hq,hn⟩ := pb
      have exotic : q.1.card ≠ 1 := by
        intro one
        obtain ⟨w,hw⟩ := Finset.card_eq_one.mp one
        exact hn w hw
      refine ⟨ρ,some q,dρ,by simp only [List.length_cons]; omega,?_,?_⟩
      · rintro z eq
        have he : q=z := Option.some.inj eq
        exact he ▸ exotic
      · intro T hT
        rcases List.mem_cons.mp hT with rfl|hT
        · exact Or.inl ⟨q,hq,rfl⟩
        · exact oldmark bad (plain T hT) (rep T hT)

theorem oneWeakRefutation {F : Set (Clause V)} {k π} (h : Counted (linOfClause '' F) k π)
    (hk : k≤1) (empty : (∅ : LinClause V) ∈ π) :
    ∃ ρ, IsRefutation F ρ ∧ ρ.length ≤ π.length := by
  obtain ⟨ρ,e,dρ,sz,_,rep⟩ := simulateOne h hk
  rcases rep _ empty with ⟨q,hq,_⟩|⟨v,hv,_⟩|⟨B,hB,sub⟩
  · simp at hq
  · simp at hv
  · have eq : B=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun l hl => by
      have := sub l hl
      simpa using this)
    exact ⟨ρ,⟨dρ,eq ▸ hB⟩,sz⟩
end Pcx180Bridge

namespace Pcx180Price

open PEqualNP.ProofComplexity
theorem snd_res {V : Type} [DecidableEq V] {C D R : LinClause V} (h : IsLinResolvent C D R) (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)

section gen
variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι] (F : Set (LinClause V)) (Pt : ι → (V → Bool) → Prop)
  (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R)

def Hit (K : Finset ι) (N : Finset (LinClause V)) : Prop := ∀ k ∈ K, ∃ a, Pt k a ∧ ∃ R ∈ N, ¬ LinClauseSat a R

theorem hit_step {K : Finset ι} {N Q : Finset (LinClause V)} {R : LinClause V} (h : Hit Pt K N)
    (hq : ∀ a, ¬ LinClauseSat a R → ∃ D ∈ Q, ¬ LinClauseSat a D) : Hit Pt K (N.erase R ∪ Q) := by
  intro k hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  by_cases e : M = R
  · subst e
    obtain ⟨D, hD, hd⟩ := hq a hs
    exact ⟨a, ha, D, Finset.mem_union_right _ hD, hd⟩
  · exact ⟨a, ha, M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hM⟩), hs⟩

theorem hit_ax {K : Finset ι} {N : Finset (LinClause V)} {R : LinClause V} (h : Hit Pt K N) (k0 : ι)
    (hk0 : ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R) : Hit Pt (K.erase k0) (N.erase R) := by
  intro k hk
  obtain ⟨hne, hk⟩ := Finset.mem_erase.1 hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  refine ⟨a, ha, M, Finset.mem_erase.2 ⟨?_, hM⟩, hs⟩
  rintro rfl
  exact hs (hk0 k hne a ha)

theorem card_step (N Q : Finset (LinClause V)) (R : LinClause V) (hR : R ∈ N) : (N.erase R ∪ Q).card + 1 ≤ N.card + Q.card := by
  have h1 := Finset.card_union_le (N.erase R) Q
  have h2 := Finset.card_erase_of_mem hR
  have h3 := Finset.card_pos.2 ⟨R, hR⟩
  omega

theorem tl {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) : ∀ M ∈ N.erase R, M ∈ π := by
  intro M hM
  obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hM
  rcases List.mem_cons.1 (h M h2) with e | e
  · exact absurd e h1
  · exact e

theorem tln {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) (hR : R ∉ N) : ∀ M ∈ N, M ∈ π := by
  intro M hM
  rcases List.mem_cons.1 (h M hM) with e | e
  · subst e; exact absurd hM hR
  · exact e

include H in
theorem countedPrice {k : Nat} {π : List (LinClause V)} (hπ : Pcx180Bridge.Counted F k π) : ∀ (N : Finset (LinClause V)) (K : Finset ι),
    (∀ M ∈ N, M ∈ π) → Hit Pt K N → 2 * K.card + k ≤ π.length + N.card := by
  induction hπ with
  | nil =>
    intro N K hN hK
    have : K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨_, _, M, hM, _⟩ := hK k hk
      have := hN M hM
      simp at this
    simp [this]
  | @ax k π C hπ hC ih =>
    intro N K hN hK
    by_cases hR : C ∈ N
    · obtain ⟨k0, hk0⟩ := H C hC
      have := ih (N.erase C) (K.erase k0) (tl hN) (hit_ax Pt hK k0 hk0)
      have h2 := Finset.card_erase_of_mem hR
      have h3 := Finset.card_pos.2 ⟨C, hR⟩
      have h4 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      rw [List.length_cons]
      omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega
  | @res k π C D R hπ hC hD hr ih =>
    intro N K hN hK
    by_cases hR : R ∈ N
    · have hh := hit_step Pt (Q := {C, D}) hK (R := R) (fun a ha => by
        rcases snd_res hr a ha with h | h
        · exact ⟨C, by simp, h⟩
        · exact ⟨D, by simp, h⟩)
      have := ih _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl <;> assumption) hh
      have h2 := card_step N {C, D} R hR
      have h3 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega
  | @weak k π C D hπ hC hw ih =>
    intro N K hN hK
    by_cases hR : D ∈ N
    · have hh := hit_step Pt (Q := {C}) hK (R := D) (fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩)
      have := ih _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_singleton] at h
          subst h; exact hC) hh
      have h2 := card_step N {C} D hR
      rw [Finset.card_singleton] at h2
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega

end gen


abbrev W := Fin 5 × Fin 4
def asg (m : ℕ) : W → Bool := fun v => m.testBit (4 * v.1.val + v.2.val)
def ptl : List (List ℕ) := [[541200, 99360, 137280, 270720], [541185, 99330, 137220, 270600], [540705, 98370, 135300, 270360], [525345, 67650, 131460, 262680], [33825, 6210, 8580, 16920], [541201], [540961], [529441], [99361], [540946], [529426], [99346], [528706], [98626], [71746], [540962], [541202], [533522], [164882], [541217], [533537], [164897], [533057], [164417], [141377], [532804], [533524], [541204], [295444], [533569], [541249], [295489], [541729], [295969], [280609], [270728], [272408], [295448], [541208], [272513], [295553], [541313], [296993], [542753], [558113]]
def pts (k : Fin 45) : List ℕ := ptl.getD k.val []
def Pt (k : Fin 45) (a : W → Bool) : Prop := ∃ m ∈ pts k, a = asg m
def hidx : List ℕ := [0, 0, 0, 0, 5, 15, 25, 35, 6, 16, 26, 36, 7, 17, 27, 37, 8, 18, 28, 38, 5, 15, 25, 35, 0, 0, 0, 0, 9, 19, 29, 39, 10, 20, 30, 40, 11, 21, 31, 41, 6, 16, 26, 36, 9, 19, 29, 39, 0, 0, 0, 0, 12, 22, 32, 42, 13, 23, 33, 43, 7, 17, 27, 37, 10, 20, 30, 40, 12, 22, 32, 42, 0, 0, 0, 0, 14, 24, 34, 44, 8, 18, 28, 38, 11, 21, 31, 41, 13, 23, 33, 43, 14, 24, 34, 44, 0, 0, 0, 0]
def kH (i i' : Fin 5) (j : Fin 4) : Fin 45 := ⟨(hidx.getD (20 * i.val + 4 * i'.val + j.val) 0) % 45, Nat.mod_lt _ (by norm_num)⟩
def kP (i : Fin 5) : Fin 45 := ⟨i.val, by omega⟩

def satb (a : W → Bool) (C : LinClause W) : Bool :=
  decide (∃ q ∈ C, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))
theorem satb_sat {a : W → Bool} {C : LinClause W} (h : satb a C = true) : LinClauseSat a C := by
  unfold satb at h
  rw [decide_eq_true_eq] at h
  exact h

theorem factP : ∀ i : Fin 5, ∀ k, k ≠ kP i → ∀ m ∈ pts k,
    satb (asg m) (linOfClause (Finset.univ.image (fun j : Fin 4 => ((i, j), true)))) = true := by decide +kernel
theorem factH : ∀ (i i' : Fin 5) (j : Fin 4), i ≠ i' → ∀ k, k ≠ kH i i' j → ∀ m ∈ pts k,
    satb (asg m) (linOfClause {((i, j), false), ((i', j), false)}) = true := by decide +kernel
theorem factV : ∀ v : W, ∃ i : Fin 45, ∃ m ∈ pts i, ∃ m' ∈ pts i, asg m v = true ∧ asg m' v = false := by decide +kernel
theorem factE : ∀ k : Fin 45, pts k ≠ [] := by decide +kernel

def FF : Set (LinClause W) := (fun C => linOfClause C) '' PHP 5 4

theorem HH : ∀ R ∈ FF, ∃ k0 : Fin 45, ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R := by
  rintro R ⟨C, hC, rfl⟩
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩
  · exact ⟨kP i, fun k hk a ⟨m, hm, e⟩ => e ▸ satb_sat (factP i k hk m hm)⟩
  · exact ⟨kH i i' j, fun k hk a ⟨m, hm, e⟩ => e ▸ satb_sat (factH i i' j hne k hk m hm)⟩

theorem hF1 : ∀ R ∈ FF, ∀ q ∈ R, q.1.card = 1 := by
  rintro R ⟨C, hC, rfl⟩ q hq
  simp only [linOfClause, Finset.mem_image] at hq
  obtain ⟨l, _, rfl⟩ := hq
  simp

theorem exP (k : Fin 45) : ∃ a, Pt k a := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ (factE k)
  exact ⟨_, m, hm, rfl⟩

end Pcx180Price



namespace Pcx180Ord

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev LiteralSat (a : V → Bool) (l : Literal V) : Prop := a l.1 = l.2

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

theorem colAx_comm (i k : Row) (j : Hole) : colAx i k j = colAx k i j :=
  Finset.pair_comm ((i, j), false) ((k, j), false)

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem collisionNoPos {N : C} (hN : Coll N) (v : V) : (v, true) ∉ N := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem collisionOther {N : C} {v : V} (hN : Coll N) (hv : (v, false) ∈ N) :
    ∃ u : V, u ≠ v ∧ (u, false) ∈ N := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  rcases hv' with rfl | rfl
  · exact ⟨(k, j), fun e => hik (congrArg Prod.fst e).symm, by simp [colAx]⟩
  · exact ⟨(i, j), fun e => hik (congrArg Prod.fst e), by simp [colAx]⟩

theorem collisionNonempty {N : C} (hN : Coll N) : N ≠ ∅ := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem col_same_hole {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) : v.2 = u.2 := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl <;> rfl

theorem col_eq_colAx {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) (huv : u ≠ v) :
    v.1 ≠ u.1 ∧ v.2 = u.2 ∧ N = colAx v.1 u.1 u.2 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl
  · exact (huv rfl).elim
  · exact ⟨hik, rfl, rfl⟩
  · exact ⟨hik.symm, rfl, colAx_comm i k j⟩
  · exact (huv rfl).elim

theorem negLeft {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ P) :
    (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hu⟩)

theorem negRight {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ N)
    (hne : u ≠ v) : (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simpa using hne, hu⟩)

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 5 4 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

theorem indispensablePHP {B : C} : B ∈ PHP 5 4 ↔
    (∃ r : Row, B = rowAx r Finset.univ) ∨ Collision Finset.univ Finset.univ B := by
  change ((∃ r : Row, B = rowAx r Finset.univ) ∨
    (∃ i k : Row, ∃ j : Hole, i ≠ k ∧ B = colAx i k j)) ↔ _
  constructor
  · rintro (hr | ⟨i, k, j, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _, hik, he⟩
  · rintro (hr | ⟨i, _, k, _, j, _, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, k, j, hik, he⟩

theorem indispensableSatRow {a : V → Bool} {J : Finset Hole} {r : Row} {j : Hole}
    (hj : j ∈ J) (h : a (r, j) = true) : ClauseSat a (rowAx r J) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, hj, rfl⟩, h⟩

theorem indispensableSatCol {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

def ValidMatch (i k : Row) (j : Hole) (f : Row → Hole) : Prop :=
  (∀ r, r ≠ i → r ≠ k → f r ≠ j) ∧
  (∀ r₁ r₂, r₁ ≠ i → r₁ ≠ k → r₂ ≠ i → r₂ ≠ k → f r₁ = f r₂ → r₁ = r₂)

def validMatchB (i k : Row) (j : Hole) (f : Row → Hole) : Bool :=
  ((List.finRange 5).all fun r => decide (r = i) || decide (r = k) || decide (f r ≠ j)) &&
  ((List.finRange 5).all fun r₁ => (List.finRange 5).all fun r₂ =>
    decide (r₁ = i) || decide (r₁ = k) || decide (r₂ = i) || decide (r₂ = k) ||
    decide (f r₁ ≠ f r₂) || decide (r₁ = r₂))

theorem validMatch_of_bool {i k : Row} {j : Hole} {f : Row → Hole}
    (h : validMatchB i k j f = true) : ValidMatch i k j f := by
  unfold validMatchB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_⟩
  · intro r hri hrk
    rcases h.1 r with (h1 | h2) | h3
    · exact (hri h1).elim
    · exact (hrk h2).elim
    · exact h3
  · intro r₁ r₂ h1i h1k h2i h2k heq
    rcases h.2 r₁ r₂ with (((((h1 | h2) | h3) | h4) | h5) | h6)
    · exact (h1i h1).elim
    · exact (h1k h2).elim
    · exact (h2i h3).elim
    · exact (h2k h4).elim
    · exact (h5 heq).elim
    · exact h6

def colModel (i k : Row) (j : Hole) (f : Row → Hole) : V → Bool :=
  fun w => if w.1 = i ∨ w.1 = k then decide (w.2 = j) else decide (f w.1 = w.2)

theorem colModel_unsat {i k : Row} {j : Hole} {f : Row → Hole} :
    ¬ ClauseSat (colModel i k j f) (colAx i k j) := by
  rintro ⟨l, hl, hal⟩
  simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl <;> simp [colModel] at hal

theorem colModel_sat_other {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, D ≠ colAx i k j → ClauseSat (colModel i k j f) D := by
  intro D hD hne
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | ⟨r, _, s, _, q, _, hrs, rfl⟩
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · apply indispensableSatCol
    rintro ⟨hr, hs⟩
    by_cases hri : r = i ∨ r = k <;> by_cases hsi : s = i ∨ s = k
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      subst hr
      apply hne
      rcases hri with hri' | hri' <;> rcases hsi with hsi' | hsi'
      · exact (hrs (hri'.trans hsi'.symm)).elim
      · rw [hri', hsi']
      · rw [hri', hsi']; exact colAx_comm k i q
      · exact (hrs (hri'.trans hsi'.symm)).elim
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hsi
      exact hf.1 s hsi.1 hsi.2 (hs.trans hr)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri
      exact hf.1 r hri.1 hri.2 (hr.trans hs)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri hsi
      exact hrs (hf.2 r s hri.1 hri.2 hsi.1 hsi.2 (hr.trans hs.symm))

theorem colModel_sat_rows {i k : Row} {j : Hole} {f : Row → Hole}
    (_hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat (colModel i k j f) D := by
  intro D hD hnc
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | hc
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · exact (hnc hc).elim

theorem colModel_sat_cols {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D, Coll D → D ≠ colAx i k j → ClauseSat (colModel i k j f) D :=
  fun D hD hne => colModel_sat_other hf D (collisionPHP hD) hne

theorem exists_validMatch (i k : Row) (hik : i ≠ k) (j : Hole) :
    ∃ f : Row → Hole, ValidMatch i k j f := by
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hc : (((Finset.univ : Finset Row).erase i).erase k).card =
      ((Finset.univ : Finset Hole).erase j).card := by
    rw [Finset.card_erase_of_mem hkm, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
  let e : ↥(((Finset.univ : Finset Row).erase i).erase k) ≃
      ↥((Finset.univ : Finset Hole).erase j) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  refine ⟨fun r => if hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k
      then (e ⟨r, hr⟩).1 else 0, ?_, ?_⟩
  · intro r hri hrk
    have hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
    simp only [hr, ↓reduceDIte]
    exact (Finset.mem_erase.mp (e ⟨r, hr⟩).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    have hr₁ : r₁ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩
    have hr₂ : r₂ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩
    simp only [hr₁, hr₂, ↓reduceDIte] at heq
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_map (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) (hqj : q₀ ≠ j) :
    ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ = q₀ := by
  let A : Finset Row := (((Finset.univ : Finset Row).erase i).erase k).erase r₀
  let B : Finset Hole := ((Finset.univ : Finset Hole).erase j).erase q₀
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hrm : r₀ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
    Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
  have hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j :=
    Finset.mem_erase.mpr ⟨hqj, Finset.mem_univ _⟩
  have hc : A.card = B.card := by
    dsimp only [A, B]
    rw [Finset.card_erase_of_mem hrm, Finset.card_erase_of_mem hkm,
      Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem (Finset.mem_univ j)]
    decide +kernel
  let e : ↥A ≃ ↥B := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let f : Row → Hole := fun r =>
    if r = r₀ then q₀ else if hr : r ∈ A then (e ⟨r, hr⟩).1 else 0
  refine ⟨f, ⟨?_, ?_⟩, by simp [f]⟩
  · intro r hri' hrk'
    by_cases hr0 : r = r₀
    · simp [f, hr0, hqj]
    · have hrA : r ∈ A := Finset.mem_erase.mpr
        ⟨hr0, Finset.mem_erase.mpr ⟨hrk', Finset.mem_erase.mpr ⟨hri', Finset.mem_univ _⟩⟩⟩
      simp only [f, hr0, hrA, ↓reduceIte, ↓reduceDIte]
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (e ⟨r, hrA⟩).2).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    by_cases h1 : r₁ = r₀ <;> by_cases h2 : r₂ = r₀
    · exact h1.trans h2.symm
    · have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₂, hr₂A⟩).2).1 heq.symm).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₁, hr₁A⟩).2).1 heq).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_avoid (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) : ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ ≠ q₀ := by
  have hne : (((Finset.univ : Finset Hole).erase j).erase q₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hc : (((Finset.univ : Finset Hole).erase j).erase q₀).card = 0 := by simp [he]
    have h1 : ((Finset.univ : Finset Hole).erase j).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
    have h2 : (((Finset.univ : Finset Hole).erase j).erase q₀).card ≥ 2 := by
      have := Finset.card_erase_le (a := q₀) (s := (Finset.univ : Finset Hole).erase j)
      by_cases hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j
      · rw [Finset.card_erase_of_mem hqm, h1]
      · rw [Finset.erase_eq_of_notMem hqm, h1]; omega
    omega
  obtain ⟨q₁, hq₁⟩ := hne
  have hq₁q₀ : q₁ ≠ q₀ := (Finset.mem_erase.mp hq₁).1
  have hq₁j : q₁ ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hq₁).2).1
  obtain ⟨f, hf, hfr⟩ := exists_validMatch_map i k r₀ hik hri hrk j q₁ hq₁j
  exact ⟨f, hf, hfr.symm ▸ hq₁q₀⟩

theorem indispensableRowModel (i : Row) :
    ∃ a : V → Bool, ¬ ClauseSat a (rowAx i Finset.univ) ∧
      ∀ R ∈ PHP 5 4, R ≠ rowAx i Finset.univ → ClauseSat a R := by
  have hc : ((Finset.univ : Finset Row).erase i).card = (Finset.univ : Finset Hole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; decide +kernel
  let e : ↥((Finset.univ : Finset Row).erase i) ≃ ↥(Finset.univ : Finset Hole) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let a : V → Bool := fun w =>
    if hr : w.1 ∈ (Finset.univ : Finset Row).erase i then decide ((e ⟨w.1, hr⟩ : Hole) = w.2)
    else false
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    have hnot : i ∉ (Finset.univ : Finset Row).erase i := Finset.notMem_erase i Finset.univ
    simp only [a, hnot, ↓reduceDIte] at hal
    cases hal
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, j, _, hrs, rfl⟩
    · have hri : r ≠ i := fun he => hne (congrArg (fun r => rowAx r Finset.univ) he)
      have hr : r ∈ (Finset.univ : Finset Row).erase i := Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩
      exact indispensableSatRow (Finset.mem_univ (e ⟨r, hr⟩).1) (by simp only [a, hr, ↓reduceDIte, decide_true])
    · apply indispensableSatCol
      rintro ⟨hr, hs⟩
      by_cases hri : r ∈ (Finset.univ : Finset Row).erase i <;>
        by_cases hsi : s ∈ (Finset.univ : Finset Row).erase i
      · simp only [a, hri, hsi, ↓reduceDIte, decide_eq_true_eq] at hr hs
        exact hrs (congrArg Subtype.val (e.injective (Subtype.ext (hr.trans hs.symm))))
      · simp only [a, hsi, ↓reduceDIte] at hs; cases hs
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr

theorem critical {B : C} (hB : B ∈ PHP 5 4) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 5 4, D ≠ B → ClauseSat a D := by
  rcases indispensablePHP.mp hB with ⟨i, rfl⟩ | ⟨i, _, k, _, j, _, hik, rfl⟩
  · exact indispensableRowModel i
  · obtain ⟨f, hf⟩ := exists_validMatch i k hik j
    exact ⟨colModel i k j f, colModel_unsat, colModel_sat_other hf⟩

def holeColBank (j : Hole) : Finset C :=
  ((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)).image
    (fun p => colAx p.1 p.2 j)

theorem mem_holeColBank {j : Hole} {B : C} :
    B ∈ holeColBank j ↔ ∃ i k : Row, i ≠ k ∧ B = colAx i k j := by
  unfold holeColBank
  constructor
  · intro hB
    obtain ⟨⟨i, k⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, k, ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, k, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem holeColBank_card (j : Hole) : (holeColBank j).card = 10 := by
  have hinj : Set.InjOn (fun p : Row × Row => colAx p.1 p.2 j)
      (((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)) : Set _) := by
    intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    have m2 : ((k1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold holeColBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Coll B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _,
      ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, _, k, _, j, _, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem collisionBank_card : collisionBank.card = 40 := by
  have hinj : Set.InjOn (fun p : Row × Row × Hole => colAx p.1 p.2.1 p.2.2)
      (((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)) : Set _) := by
    intro ⟨i1, k1, j1⟩ h1 ⟨i2, k2, j2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    have m2 : ((k1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold collisionBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def axiomBank : Finset C :=
  (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) ∪ collisionBank

theorem mem_axiomBank (B : C) : B ∈ axiomBank ↔ B ∈ PHP 5 4 := by
  rw [indispensablePHP]
  simp only [axiomBank, Finset.mem_union, mem_collisionBank, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h

theorem axiomBank_card : axiomBank.card = 45 := by
  have hdisj : Disjoint (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) collisionBank := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hB1
    have hc : Coll (rowAx r Finset.univ) := (mem_collisionBank _).mp hB2
    exact collisionNoPos hc (r, 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hrow : (Finset.univ.image (fun r : Row => rowAx r Finset.univ)).card = 5 := by
    have hinj : Function.Injective (fun r : Row => rowAx r Finset.univ) := by
      intro r1 r2 heq
      dsimp only at heq
      have hm : ((r1, (0 : Hole)), true) ∈ rowAx r2 Finset.univ :=
        heq ▸ Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨_, _, he⟩ := Finset.mem_image.mp hm
      exact (Prod.mk.inj (Prod.mk.inj he).1).1.symm
    rw [Finset.card_image_of_injective _ hinj]
    decide +kernel
  unfold axiomBank
  rw [Finset.card_union_of_disjoint hdisj, hrow, collisionBank_card]

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

inductive Step where
  | ax (R : C)
  | col (N : C) (v u : V) (R : C)
  | non (v : V) (R : C)
  deriving DecidableEq

def clauseOf : Step → C
  | Step.ax R => R
  | Step.col _ _ _ R => R
  | Step.non _ R => R

inductive ValidTrace : List Step → Prop
  | nil : ValidTrace []
  | ax {tr : List Step} {R : C} :
      ValidTrace tr → R ∈ PHP 5 4 → ValidTrace (Step.ax R :: tr)
  | col {tr : List Step} {P N R : C} {v u : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      Coll N → (v, true) ∈ P → (v, false) ∈ N →
      u ≠ v → (u, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.col N v u R :: tr)
  | non {tr : List Step} {P N R : C} {v : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      ¬ Coll N → (v, true) ∈ P → (v, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.non v R :: tr)

theorem of_isDerivation {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃ tr : List Step, tr.map clauseOf = π ∧ ValidTrace tr := by
  classical
  induction h with
  | nil => exact ⟨[], rfl, ValidTrace.nil⟩
  | @ax π R _ hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    exact ⟨Step.ax R :: tr, by simp [clauseOf, hmap], ValidTrace.ax htr hR⟩
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    obtain ⟨v, hp, hn, heq⟩ := hR
    by_cases hcol : Coll N
    · obtain ⟨u, huv, hu⟩ := collisionOther hcol hn
      exact ⟨Step.col N v u R :: tr, by simp [clauseOf, hmap],
        ValidTrace.col htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn huv hu heq⟩
    · exact ⟨Step.non v R :: tr, by simp [clauseOf, hmap],
        ValidTrace.non htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn heq⟩

theorem ValidTrace.tail {s : Step} {tr : List Step} (h : ValidTrace (s :: tr)) : ValidTrace tr := by
  cases h <;> assumption

theorem ValidTrace.drop {tr : List Step} (h : ValidTrace tr) : ∀ k : ℕ, ValidTrace (tr.drop k) := by
  induction tr with
  | nil => intro k; simp [ValidTrace.nil]
  | cons s tl ih =>
    intro k
    cases k with
    | zero => exact h
    | succ k' => exact ih h.tail k'

theorem ValidTrace.col_mem_info {tr : List Step} (h : ValidTrace tr) {N : C} {v u : V} {R : C}
    (hm : Step.col N v u R ∈ tr) :
    Coll N ∧ (v, false) ∈ N ∧ (u, false) ∈ N ∧ u ≠ v ∧ N ∈ holeColBank u.2 := by
  induction h with
  | nil => cases hm
  | ax _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'
  | @col tr' P N' R' v' u' _ _ _ hcol _ hn huv hu _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
      obtain ⟨hne, hhole, hax⟩ := col_eq_colAx hcol hn hu huv
      exact ⟨hcol, hn, hu, huv, mem_holeColBank.mpr ⟨v.1, u.1, hne, hax⟩⟩
    · exact ih hm'
  | non _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'

theorem masterControl {tr : List Step} (h : ValidTrace tr)
    (a : V → Bool) (B₀ : C) (T : Finset V)
    (hrows : ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat a D)
    (hcols : ∀ D, Coll D → D ≠ B₀ → ClauseSat a D)
    (h1 : ∀ v u R, Step.col B₀ v u R ∈ tr → u ∈ T)
    (h2 : ∀ v R, Step.non v R ∈ tr → v ∈ T → (∀ w ∈ T, (w, false) ∉ R) → ClauseSat a R) :
    ∀ Q ∈ tr.map clauseOf, ¬ Coll Q → (∀ w ∈ T, (w, false) ∉ Q) → ClauseSat a Q := by
  induction h with
  | nil => intro Q hQ; simp at hQ
  | @ax tr R _ hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v u R' hm => h1 v u R' (List.mem_cons_of_mem _ hm))
                   (fun v R' hm => h2 v R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hnc ⊢; exact hrows R hR hnc
    · exact ih' Q hQ hnc hT
  | @col tr P N R v u _ hP hN hcol hp hn huv hu hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v' u' R' hm => h1 v' u' R' (List.mem_cons_of_mem _ hm))
                   (fun v' R' hm => h2 v' R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hT ⊢
      have sP : ClauseSat a P :=
        ih' P hP (fun hc => collisionNoPos hc v hp) (fun w hw hwf => hT w hw (negLeft hR hwf))
      have hne : N ≠ B₀ := by
        intro heq
        subst heq
        have huT : u ∈ T := h1 v u R (by simp)
        exact hT u huT (negRight hR hu huv)
      exact satResolve hR sP (hcols N hcol hne)
    · exact ih' Q hQ hnc hT
  | @non tr P N R v _ hP hN hncN hp hn hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v' u' R' hm => h1 v' u' R' (List.mem_cons_of_mem _ hm))
                   (fun v' R' hm => h2 v' R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hT ⊢
      by_cases hv : v ∈ T
      · exact h2 v R (by simp) hv hT
      · have sP : ClauseSat a P :=
          ih' P hP (fun hc => collisionNoPos hc v hp) (fun w hw hwf => hT w hw (negLeft hR hwf))
        have sN : ClauseSat a N :=
          ih' N hN hncN (fun w hw hwf =>
            hT w hw (negRight hR hwf (fun heq => hv (heq ▸ hw))))
        exact satResolve hR sP sN
    · exact ih' Q hQ hnc hT

def isAxStep : Step → Bool
  | Step.ax _ => true
  | _ => false

def isColHole (j : Hole) : Step → Bool
  | Step.col _ _ u _ => decide (u.2 = j)
  | _ => false

def isNonHole (j : Hole) : Step → Bool
  | Step.non v _ => decide (v.2 = j)
  | _ => false

def isColOf (B : C) : Step → Bool
  | Step.col N _ _ _ => decide (N = B)
  | _ => false

def isNonOf (v₀ : V) : Step → Bool
  | Step.non v _ => decide (v = v₀)
  | _ => false

def colCount (tr : List Step) (B : C) : ℕ := tr.countP (isColOf B)
def nonCount (tr : List Step) (v : V) : ℕ := tr.countP (isNonOf v)

def holeCost (tr : List Step) (j : Hole) : ℕ :=
  tr.countP (isColHole j) + tr.countP (isNonHole j)

theorem length_decomp (tr : List Step) :
    tr.length = tr.countP isAxStep + ∑ j : Hole, holeCost tr j := by
  induction tr with
  | nil => simp [holeCost]
  | cons s tl ih =>
    unfold holeCost at ih ⊢
    simp only [List.length_cons, List.countP_cons]
    cases s with
    | ax R =>
      simp only [isAxStep, isColHole, isNonHole, ↓reduceIte, Bool.false_eq_true, add_zero]
      omega
    | col N v u R =>
      have hax : isAxStep (Step.col N v u R) = false := rfl
      have h1 : ∀ j : Hole,
          (tl.countP (isColHole j) + if isColHole j (Step.col N v u R) = true then 1 else 0) +
            (tl.countP (isNonHole j) + if isNonHole j (Step.col N v u R) = true then 1 else 0) =
          (tl.countP (isColHole j) + tl.countP (isNonHole j)) +
            (if u.2 = j then 1 else 0) := by
        intro j; by_cases h : u.2 = j <;> simp [isColHole, isNonHole, h]; omega
      simp only [hax, Bool.false_eq_true, ↓reduceIte, add_zero]
      simp_rw [h1]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      omega
    | non v R =>
      have hax : isAxStep (Step.non v R) = false := rfl
      have h1 : ∀ j : Hole,
          (tl.countP (isColHole j) + if isColHole j (Step.non v R) = true then 1 else 0) +
            (tl.countP (isNonHole j) + if isNonHole j (Step.non v R) = true then 1 else 0) =
          (tl.countP (isColHole j) + tl.countP (isNonHole j)) +
            (if v.2 = j then 1 else 0) := by
        intro j; by_cases h : v.2 = j <;> simp [isColHole, isNonHole, h]; omega
      simp only [hax, Bool.false_eq_true, ↓reduceIte, add_zero]
      simp_rw [h1]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      omega

def axFinset : List Step → Finset C
  | [] => ∅
  | Step.ax R :: tl => insert R (axFinset tl)
  | _ :: tl => axFinset tl

theorem axFinset_card_le (tr : List Step) : (axFinset tr).card ≤ tr.countP isAxStep := by
  induction tr with
  | nil => simp [axFinset]
  | cons s tl ih =>
    cases s with
    | ax R =>
      simp only [axFinset, List.countP_cons, isAxStep, ↓reduceIte]
      have := Finset.card_insert_le R (axFinset tl)
      omega
    | col _ _ _ _ => simp only [axFinset, List.countP_cons, isAxStep, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | non _ _ => simp only [axFinset, List.countP_cons, isAxStep, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih

theorem absorbs_axFinset {tr : List Step} (h : ValidTrace tr) :
    Absorbs (tr.map clauseOf) (axFinset tr) := by
  induction h with
  | nil => intro a _ Q hQ; simp at hQ
  | @ax tr R _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq]; exact ha R (Finset.mem_insert_self _ _) hR
    · exact ih a (fun B hB hB' => ha B (Finset.mem_insert_of_mem hB) hB') Q hQ
  | @col tr P N R v u _ hP hN _ _ _ _ _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact satResolve hR (ih a ha P hP) (ih a ha N hN)
    · exact ih a ha Q hQ
  | @non tr P N R v _ hP hN _ _ _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact satResolve hR (ih a ha P hP) (ih a ha N hN)
    · exact ih a ha Q hQ

theorem ax_lower {tr : List Step} (h : ValidTrace tr) (he : (∅ : C) ∈ tr.map clauseOf) :
    45 ≤ tr.countP isAxStep := by
  have hsub := requiredAxioms (absorbs_axFinset h) he
  have h1 := Finset.card_le_card hsub
  rw [axiomBank_card] at h1
  have h2 := axFinset_card_le tr
  omega

theorem sum_colCount_hole {tr : List Step} (h : ValidTrace tr) (j : Hole) :
    ∑ B ∈ holeColBank j, colCount tr B = tr.countP (isColHole j) := by
  induction h with
  | nil => simp [colCount]
  | ax _ _ ih =>
    simp only [colCount, List.countP_cons, isColOf, isColHole, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact ih
  | @col tr' P N R v u htr' _ _ hcol _ hn huv hu _ ih =>
    simp only [colCount] at ih ⊢
    simp only [List.countP_cons]
    rw [Finset.sum_add_distrib, ih]
    have hdelta : (∑ B ∈ holeColBank j, if isColOf B (Step.col N v u R) = true then 1 else 0) =
        (if isColHole j (Step.col N v u R) = true then 1 else 0) := by
      have hmem : N ∈ holeColBank u.2 := by
        obtain ⟨hne, _, hax⟩ := col_eq_colAx hcol hn hu huv
        exact mem_holeColBank.mpr ⟨v.1, u.1, hne, hax⟩
      by_cases hj : u.2 = j
      · subst hj
        have hrh : (if isColHole u.2 (Step.col N v u R) = true then 1 else 0) = 1 := by
          simp [isColHole]
        rw [hrh, Finset.sum_eq_single N]
        · simp [isColOf]
        · intro B _ hBN
          simp [isColOf, hBN.symm]
        · intro hNmem; exact (hNmem hmem).elim
      · have hrh : (if isColHole j (Step.col N v u R) = true then 1 else 0) = 0 := by
          simp [isColHole, hj]
        rw [hrh]
        apply Finset.sum_eq_zero
        intro B hB
        have hne : N ≠ B := by
          intro heq
          subst heq
          obtain ⟨i, k, _, hax⟩ := mem_holeColBank.mp hB
          have hu' : (u, false) ∈ colAx i k j := hax ▸ hu
          simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu'
          rcases hu' with h' | h' <;> exact hj (congrArg Prod.snd h')
        simp [isColOf, hne]
    rw [hdelta]
  | non _ _ _ _ _ _ _ ih =>
    simp only [colCount, List.countP_cons, isColOf, isColHole, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact ih

theorem sum_nonCount_hole (tr : List Step) (j : Hole) :
    ∑ k : Row, nonCount tr (k, j) = tr.countP (isNonHole j) := by
  induction tr with
  | nil => simp [nonCount]
  | cons s tl ih =>
    cases s with
    | ax _ => simp only [nonCount, List.countP_cons, isNonOf, isNonHole, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | col _ _ _ _ => simp only [nonCount, List.countP_cons, isNonOf, isNonHole, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | non v R =>
      simp only [nonCount] at ih ⊢
      simp only [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      congr 1
      by_cases hj : v.2 = j
      · subst hj
        have hrh : (if isNonHole v.2 (Step.non v R) = true then 1 else 0) = 1 := by
          simp [isNonHole]
        rw [hrh, Finset.sum_eq_single v.1]
        · simp [isNonOf]
        · intro k _ hkv
          have hne : v ≠ (k, v.2) := fun h => hkv (congrArg Prod.fst h).symm
          simp [isNonOf, hne]
        · intro hm; exact (hm (Finset.mem_univ _)).elim
      · have hrh : (if isNonHole j (Step.non v R) = true then 1 else 0) = 0 := by
          simp [isNonHole, hj]
        rw [hrh]
        apply Finset.sum_eq_zero
        intro k _
        have hne : v ≠ (k, j) := fun h => hj (congrArg Prod.snd h)
        simp [isNonOf, hne]

theorem getElem_eq_of_fin_eq {α : Type*} {l : List α} {j : ℕ} {hj : j < l.length}
    {i : Fin l.length} (heq : (⟨j, hj⟩ : Fin l.length) = i) : l[j]'hj = l[i] := by
  cases heq; rfl

theorem mem_drop_iff {α : Type*} (l : List α) (k : ℕ) (x : α) :
    x ∈ l.drop k ↔ ∃ i : Fin l.length, k ≤ i.1 ∧ l[i] = x := by
  constructor
  · intro hx
    obtain ⟨j, hjlt, hj⟩ := List.getElem_of_mem hx
    rw [List.length_drop] at hjlt
    have hlt : k + j < l.length := by omega
    refine ⟨⟨k + j, hlt⟩, Nat.le_add_right k j, ?_⟩
    simpa [List.getElem_drop] using hj
  · rintro ⟨i, hki, rfl⟩
    have hlt : i.1 - k < (l.drop k).length := by rw [List.length_drop]; omega
    have hidx : k + (i.1 - k) = i.1 := by omega
    have hget : (l.drop k)[i.1 - k]'hlt = l[i] := by
      simp only [List.getElem_drop, hidx]
      rfl
    rw [← hget]
    exact List.getElem_mem hlt

theorem mem_of_mem_drop {α : Type*} {l : List α} {k : ℕ} {x : α} (h : x ∈ l.drop k) : x ∈ l := by
  obtain ⟨i, _, rfl⟩ := (mem_drop_iff l k x).mp h
  exact List.getElem_mem i.2

theorem countP_eq_one_unique_idx {α : Type*} (l : List α) (p : α → Bool) (h : l.countP p = 1) :
    ∃ i : Fin l.length, p l[i] = true ∧ ∀ j : Fin l.length, p l[j] = true → j = i := by
  induction l with
  | nil => simp at h
  | cons a tl ih =>
    simp only [List.countP_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte] at h
      have h0 : tl.countP p = 0 := by omega
      refine ⟨⟨0, by simp⟩, ha, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ j' =>
        have hm : tl[j'] ∈ tl := List.getElem_mem j'.2
        have hp0 := List.countP_eq_zero.mp h0 tl[j'] hm
        exact (hp0 hj).elim
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, add_zero] at h
      obtain ⟨i, hi, huniq⟩ := ih h
      refine ⟨i.succ, hi, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact (ha hj).elim
      | succ j' => exact congrArg Fin.succ (huniq j' hj)

theorem countP_eq_two_unique_idx {α : Type*} (l : List α) (p : α → Bool) (h : l.countP p = 2) :
    ∃ i₁ i₂ : Fin l.length, i₂.1 < i₁.1 ∧ p l[i₁] = true ∧ p l[i₂] = true ∧
      ∀ j : Fin l.length, p l[j] = true → j = i₁ ∨ j = i₂ := by
  induction l with
  | nil => simp at h
  | cons a tl ih =>
    simp only [List.countP_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte] at h
      have h1 : tl.countP p = 1 := by omega
      obtain ⟨i, hi, huniq⟩ := countP_eq_one_unique_idx tl p h1
      refine ⟨i.succ, ⟨0, by simp⟩, Nat.zero_lt_succ i.1, hi, ha, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j' => exact Or.inl (congrArg Fin.succ (huniq j' hj))
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, add_zero] at h
      obtain ⟨i₁, i₂, hlt, h1, h2, huniq⟩ := ih h
      refine ⟨i₁.succ, i₂.succ, Nat.succ_lt_succ hlt, h1, h2, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact (ha hj).elim
      | succ j' =>
        rcases huniq j' hj with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

theorem countP_pos_of_mem {α : Type*} {l : List α} {p : α → Bool} {x : α}
    (hx : x ∈ l) (hp : p x = true) : 1 ≤ l.countP p := by
  have : 0 < l.countP p := List.countP_pos_iff.mpr ⟨x, hx, hp⟩
  omega

def G1 (tr : List Step) (j : Hole) : Finset C :=
  (holeColBank j).filter (fun B => colCount tr B = 1)

def S (tr : List Step) (j : Hole) : Finset Row :=
  Finset.univ.filter (fun k => 1 ≤ nonCount tr (k, j))

def M1 (tr : List Step) (j : Hole) : Finset Row :=
  Finset.univ.filter (fun k => nonCount tr (k, j) = 1)

def colLeaves (tr : List Step) (B : C) (u₀ : V) : Prop :=
  ∃ v R, Step.col B v u₀ R ∈ tr

noncomputable def inEdges (tr : List Step) (j : Hole) (k : Row) : Finset C := by
  classical
  exact (G1 tr j).filter (fun B => colLeaves tr B (k, j))

noncomputable def Z2 (tr : List Step) (j : Hole) : Finset Row :=
  (M1 tr j).filter (fun k => 2 ≤ (inEdges tr j k).card)

theorem colCount_pos {tr : List Step} (h : ValidTrace tr) (he : (∅ : C) ∈ tr.map clauseOf)
    {j : Hole} {B : C} (hB : B ∈ holeColBank j) : 1 ≤ colCount tr B := by
  obtain ⟨i, k, hik, rfl⟩ := mem_holeColBank.mp hB
  obtain ⟨f, hf⟩ := exists_validMatch i k hik j
  by_contra hlt
  have h0 : colCount tr (colAx i k j) = 0 := by omega
  have hsat := masterControl h (colModel i k j f) (colAx i k j) ∅
    (colModel_sat_rows hf) (colModel_sat_cols hf)
    (fun v u R hm => by
      have hp := countP_pos_of_mem hm (by simp [isColOf] : isColOf (colAx i k j) (Step.col (colAx i k j) v u R) = true)
      change 1 ≤ colCount tr (colAx i k j) at hp
      omega)
    (fun v R _ hv => by simp at hv)
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w hw => by simp at hw)
  exact emptyUnsat _ hsat

theorem exists_col_leaving_in_S {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {B : C} (hB : B ∈ holeColBank j) :
    ∃ k ∈ S tr j, colLeaves tr B (k, j) := by
  obtain ⟨i, k, hik, rfl⟩ := mem_holeColBank.mp hB
  obtain ⟨f, hf⟩ := exists_validMatch i k hik j
  let T : Finset V := Finset.univ.filter (fun w => nonCount tr w = 0)
  by_contra hnone
  push Not at hnone
  have h1 : ∀ v u R, Step.col (colAx i k j) v u R ∈ tr → u ∈ T := by
    intro v u R hm
    have hinfo := h.col_mem_info hm
    have hu_hole : u.2 = j := by
      have hu' : (u, false) ∈ colAx i k j := hinfo.2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu'
      rcases hu' with h' | h' <;> exact congrArg Prod.snd h'
    have hu_eq : u = (u.1, j) := Prod.ext rfl hu_hole
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hnz
    have huS : u.1 ∈ S tr j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hu_eq]; omega
    exact hnone u.1 huS ⟨v, R, hu_eq ▸ hm⟩
  have h2 : ∀ v R, Step.non v R ∈ tr → v ∈ T → (∀ w ∈ T, (w, false) ∉ R) →
      ClauseSat (colModel i k j f) R := by
    intro v R hm hv _
    have hv0 : nonCount tr v = 0 := (Finset.mem_filter.mp hv).2
    have hp := countP_pos_of_mem hm (by simp [isNonOf] : isNonOf v (Step.non v R) = true)
    change 1 ≤ nonCount tr v at hp
    omega
  have hsat := masterControl h (colModel i k j f) (colAx i k j) T
    (colModel_sat_rows hf) (colModel_sat_cols hf) h1 h2
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
  exact emptyUnsat _ hsat

theorem four_le_S_card {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) : 4 ≤ (S tr j).card := by
  have hcompl : ((S tr j)ᶜ).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k₁ hk₁ k₂ hk₂
    by_contra hne
    have hB : colAx k₁ k₂ j ∈ holeColBank j := mem_holeColBank.mpr ⟨k₁, k₂, hne, rfl⟩
    obtain ⟨k, hkS, v, R, hm⟩ := exists_col_leaving_in_S h he hB
    have hu : ((k, j), false) ∈ colAx k₁ k₂ j := (h.col_mem_info hm).2.2.1
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
    rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact (Finset.mem_compl.mp hk₁) hkS
    · exact (Finset.mem_compl.mp hk₂) hkS
  have hsum := Finset.card_add_card_compl (S tr j)
  have hR : Fintype.card Row = 5 := by decide +kernel
  omega

theorem g1_unique_step {tr : List Step} {j : Hole} {B : C} (hG : B ∈ G1 tr j) :
    ∀ {v₁ u₁ R₁ v₂ u₂ R₂}, Step.col B v₁ u₁ R₁ ∈ tr → Step.col B v₂ u₂ R₂ ∈ tr →
      v₁ = v₂ ∧ u₁ = u₂ ∧ R₁ = R₂ := by
  have h1 : colCount tr B = 1 := (Finset.mem_filter.mp hG).2
  obtain ⟨i, hi, huniq⟩ := countP_eq_one_unique_idx tr (isColOf B) h1
  intro v₁ u₁ R₁ v₂ u₂ R₂ hm₁ hm₂
  obtain ⟨j₁, hj₁lt, hj₁⟩ := List.getElem_of_mem hm₁
  obtain ⟨j₂, hj₂lt, hj₂⟩ := List.getElem_of_mem hm₂
  have e1 : (⟨j₁, hj₁lt⟩ : Fin tr.length) = i := huniq ⟨j₁, hj₁lt⟩ (by simp [hj₁, isColOf])
  have e2 : (⟨j₂, hj₂lt⟩ : Fin tr.length) = i := huniq ⟨j₂, hj₂lt⟩ (by simp [hj₂, isColOf])
  have heq : Step.col B v₁ u₁ R₁ = Step.col B v₂ u₂ R₂ := by
    rw [← hj₁, ← hj₂, getElem_eq_of_fin_eq e1, getElem_eq_of_fin_eq e2]
  cases heq
  exact ⟨rfl, rfl, rfl⟩

theorem inEdges_mem_iff_unique {tr : List Step} {j : Hole} {k : Row} {B : C}
    (hE : B ∈ inEdges tr j k) :
    B ∈ G1 tr j ∧ ∀ v u R, Step.col B v u R ∈ tr → u = (k, j) := by
  classical
  have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
  obtain ⟨v₀, R₀, hm₀⟩ := (Finset.mem_filter.mp hE).2
  exact ⟨hG, fun v u R hm => (g1_unique_step hG hm hm₀).2.1⟩

theorem inEdges_mem_colAx {tr : List Step} (h : ValidTrace tr) {j : Hole} {k : Row} {B : C}
    (hE : B ∈ inEdges tr j k) :
    ∃ i : Row, i ≠ k ∧ B = colAx i k j := by
  classical
  obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hE).2
  obtain ⟨hne, _, hax⟩ := col_eq_colAx (h.col_mem_info hm).1 (h.col_mem_info hm).2.1
    (h.col_mem_info hm).2.2.1 (h.col_mem_info hm).2.2.2.1
  exact ⟨v.1, hne, hax⟩

theorem inEdges_disjoint {tr : List Step} {j : Hole} {k₁ k₂ : Row} (hne : k₁ ≠ k₂) :
    Disjoint (inEdges tr j k₁) (inEdges tr j k₂) := by
  classical
  rw [Finset.disjoint_left]
  intro B h1 h2
  obtain ⟨hG, _⟩ := inEdges_mem_iff_unique h1
  obtain ⟨v₁, R₁, hm₁⟩ := (Finset.mem_filter.mp h1).2
  obtain ⟨v₂, R₂, hm₂⟩ := (Finset.mem_filter.mp h2).2
  have hu := (g1_unique_step hG hm₁ hm₂).2.1
  exact hne (congrArg Prod.fst hu)

theorem biUnion_inEdges_eq_G1 {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    (S tr j).biUnion (inEdges tr j) = G1 tr j := by
  classical
  ext B
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, _, hE⟩
    exact (Finset.mem_filter.mp hE).1
  · intro hG
    have hB : B ∈ holeColBank j := (Finset.mem_filter.mp hG).1
    obtain ⟨k, hkS, hL⟩ := exists_col_leaving_in_S h he hB
    exact ⟨k, hkS, Finset.mem_filter.mpr ⟨hG, hL⟩⟩

theorem sum_inEdges_card {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    ∑ k ∈ S tr j, (inEdges tr j k).card = (G1 tr j).card := by
  rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne),
    biUnion_inEdges_eq_G1 h he j]

theorem col_hole_lower {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    20 ≤ tr.countP (isColHole j) + (G1 tr j).card := by
  rw [← sum_colCount_hole h j]
  have hcard : (G1 tr j).card = ∑ B ∈ holeColBank j, if colCount tr B = 1 then 1 else 0 := by
    unfold G1
    rw [Finset.card_filter]
  rw [hcard, ← Finset.sum_add_distrib]
  have hle : ∑ B ∈ holeColBank j, 2 ≤
      ∑ B ∈ holeColBank j, (colCount tr B + if colCount tr B = 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro B hB
    have hpos := colCount_pos h he hB
    by_cases h1 : colCount tr B = 1
    · simp [h1]
    · simp [h1]; omega
  rw [Finset.sum_const, holeColBank_card j] at hle
  simpa using hle

theorem non_hole_lower {tr : List Step} (j : Hole) :
    2 * (S tr j).card ≤ tr.countP (isNonHole j) + (M1 tr j).card := by
  rw [← sum_nonCount_hole tr j]
  have hM : (M1 tr j).card = ∑ k : Row, if k ∈ M1 tr j then 1 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    congr 1; ext k; simp
  have hS : 2 * (S tr j).card = ∑ k : Row, if k ∈ S tr j then 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 2; ext k; simp
  rw [hM, hS, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hS' : k ∈ S tr j
  · have hpos : 1 ≤ nonCount tr (k, j) := (Finset.mem_filter.mp hS').2
    by_cases hM' : k ∈ M1 tr j
    · have h1 : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp hM').2
      simp [hS', hM', h1]
    · have hne : nonCount tr (k, j) ≠ 1 := fun he => hM' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      simp [hS', hM']
      omega
  · simp [hS']

theorem non_hole_lower_ge3 {tr : List Step} {j : Hole} {k₀ : Row}
    (hk₀ : 3 ≤ nonCount tr (k₀, j)) :
    2 * (S tr j).card + 1 ≤ tr.countP (isNonHole j) + (M1 tr j).card := by
  rw [← sum_nonCount_hole tr j]
  have hM : (M1 tr j).card = ∑ k : Row, if k ∈ M1 tr j then 1 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    congr 1; ext k; simp
  have hS : 2 * (S tr j).card = ∑ k : Row, if k ∈ S tr j then 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 2; ext k; simp
  have h1 : (1 : ℕ) = ∑ k : Row, if k = k₀ then 1 else 0 := by simp
  rw [hM, hS, h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases heq : k = k₀
  · subst heq
    have hS' : k ∈ S tr j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hM' : k ∉ M1 tr j := fun hm => by
      have := (Finset.mem_filter.mp hm).2; omega
    simp [hS', hM']
    omega
  · simp only [heq, ↓reduceIte, add_zero]
    by_cases hS' : k ∈ S tr j
    · have hpos : 1 ≤ nonCount tr (k, j) := (Finset.mem_filter.mp hS').2
      by_cases hM' : k ∈ M1 tr j
      · have h1' : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp hM').2
        simp [hS', hM', h1']
      · have hne : nonCount tr (k, j) ≠ 1 := fun he => hM' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
        simp [hS', hM']; omega
    · simp [hS']

theorem holeCost_ge_14 {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) : 14 ≤ holeCost tr j := by
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hG : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hM : (M1 tr j).card ≤ (S tr j).card :=
    Finset.card_le_card (fun k hk => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩)
  unfold holeCost
  omega

def edgesIn (A : Finset Row) (j : Hole) : Finset C :=
  ((A ×ˢ A).filter (fun p => p.1 < p.2)).image (fun p => colAx p.1 p.2 j)

theorem edgesIn_subset_holeColBank (A : Finset Row) (j : Hole) :
    edgesIn A j ⊆ holeColBank j := by
  intro B hB
  obtain ⟨⟨i, k⟩, hp, rfl⟩ := Finset.mem_image.mp hB
  exact mem_holeColBank.mpr ⟨i, k, ne_of_lt (Finset.mem_filter.mp hp).2, rfl⟩

theorem edgesIn_card (A : Finset Row) (j : Hole) :
    (edgesIn A j).card = A.card.choose 2 := by
  have hinj : Set.InjOn (fun p : Row × Row => colAx p.1 p.2 j)
      (((A ×ˢ A).filter (fun p => p.1 < p.2)) : Set _) := by
    intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    have m2 : ((k1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold edgesIn
  rw [Finset.card_image_of_injOn hinj]
  have hbij : ((A ×ˢ A).filter (fun p => p.1 < p.2)).card = (A.powersetCard 2).card := by
    refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset Row)) ?_ ?_ ?_
    · intro ⟨i, k⟩ hp
      have hmem := (Finset.mem_filter.mp hp).1
      have hlt : i < k := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (ne_of_lt hlt)⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (Finset.mem_product.mp hmem).1
      · exact (Finset.mem_product.mp hmem).2
    · intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
      have hlt1 : i1 < k1 := (Finset.mem_filter.mp h1).2
      have hlt2 : i2 < k2 := (Finset.mem_filter.mp h2).2
      have m1 : i1 ∈ ({i2, k2} : Finset Row) := heq ▸ by simp
      have m2 : k1 ∈ ({i2, k2} : Finset Row) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
      rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
      · exact (ne_of_lt hlt1 h3.symm).elim
      · rw [h3]
      · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
      · exact (ne_of_lt hlt1 h3.symm).elim
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs.2
      have ha : a ∈ A := hs.1 (by simp)
      have hb : b ∈ A := hs.1 (by simp)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hlt⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hgt⟩,
          Finset.pair_comm b a⟩
  rw [hbij, Finset.card_powersetCard]

theorem inEdges_biUnion_subset_sdiff {tr : List Step} (h : ValidTrace tr)
    (j : Hole) (A : Finset Row) :
    A.biUnion (inEdges tr j) ⊆ holeColBank j \ edgesIn Aᶜ j := by
  classical
  intro B hB
  obtain ⟨k, hkA, hE⟩ := Finset.mem_biUnion.mp hB
  have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
  have hBk : B ∈ holeColBank j := (Finset.mem_filter.mp hG).1
  refine Finset.mem_sdiff.mpr ⟨hBk, ?_⟩
  intro hIn
  obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hIn
  have hr : r ∉ A := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).1
  have hs : s ∉ A := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).2
  obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hE).2
  have hu : ((k, j), false) ∈ colAx r s j := (h.col_mem_info hm).2.2.1
  simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
  rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hr hkA
  · exact hs hkA

theorem sum_inEdges_subset_bound {tr : List Step} (h : ValidTrace tr)
    (j : Hole) (A : Finset Row) :
    ∑ k ∈ A, (inEdges tr j k).card ≤ 10 - (5 - A.card).choose 2 := by
  rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne)]
  have hsub := Finset.card_le_card (inEdges_biUnion_subset_sdiff h j A)
  have hsdiff := Finset.card_sdiff_add_card_eq_card (edgesIn_subset_holeColBank Aᶜ j)
  rw [holeColBank_card j, edgesIn_card] at hsdiff
  have hc : Aᶜ.card = 5 - A.card := by
    have := Finset.card_add_card_compl A
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  rw [hc] at hsdiff
  calc (A.biUnion (inEdges tr j)).card
      ≤ (holeColBank j \ edgesIn Aᶜ j).card := hsub
    _ = 10 - (5 - A.card).choose 2 := by omega

theorem choose2_bound (n : ℕ) (hn : n ≤ 5) :
    n = 0 ∧ n.choose 2 = 0 ∨ n = 1 ∧ n.choose 2 = 0 ∨ n = 2 ∧ n.choose 2 = 1 ∨
    n = 3 ∧ n.choose 2 = 3 ∨ n = 4 ∧ n.choose 2 = 6 ∨ n = 5 ∧ n.choose 2 = 10 := by
  interval_cases n <;> decide +kernel

theorem holeCost_ge_17_of_Z2_empty {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} (hZ : Z2 tr j = ∅) :
    17 ≤ holeCost tr j := by
  classical
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hMsub : M1 tr j ⊆ S tr j := fun k hk =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩
  let F : Finset Row := S tr j \ M1 tr j
  have hcard : F.card + (M1 tr j).card = (S tr j).card := Finset.card_sdiff_add_card_eq_card hMsub
  have hScard5 : (S tr j).card ≤ 5 := by
    have := Finset.card_le_univ (S tr j)
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  have hG10 : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hGsum : (G1 tr j).card = ∑ k ∈ F, (inEdges tr j k).card + ∑ k ∈ M1 tr j, (inEdges tr j k).card := by
    rw [← sum_inEdges_card h he j, ← Finset.sum_union Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset hMsub]
  have hMsum : ∑ k ∈ M1 tr j, (inEdges tr j k).card ≤ (M1 tr j).card := by
    calc ∑ k ∈ M1 tr j, (inEdges tr j k).card
        ≤ ∑ _k ∈ M1 tr j, 1 := by
          apply Finset.sum_le_sum
          intro k hkM
          by_contra hgt
          have h2 : 2 ≤ (inEdges tr j k).card := by omega
          have hmem : k ∈ Z2 tr j := Finset.mem_filter.mpr ⟨hkM, h2⟩
          rw [hZ] at hmem; simp at hmem
      _ = (M1 tr j).card := by simp
  have hFsum := sum_inEdges_subset_bound h j F
  have hFc5 : F.card ≤ 5 := by omega
  have hch := choose2_bound (5 - F.card) (by omega)
  unfold holeCost
  rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega

theorem holeCost_of_Z2_singleton {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k₀ : Row} (hZ : Z2 tr j = {k₀}) :
    16 ≤ holeCost tr j ∧
      (holeCost tr j = 16 →
        ∃ b : Row, b ≠ k₀ ∧ nonCount tr (b, j) = 2 ∧
          ∀ i : Row, i ≠ k₀ → i ≠ b → colAx i b j ∈ inEdges tr j b) := by
  classical
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hMsub : M1 tr j ⊆ S tr j := fun k hk =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩
  have hk₀M : k₀ ∈ M1 tr j := by
    have : k₀ ∈ Z2 tr j := hZ ▸ Finset.mem_singleton_self k₀
    exact (Finset.mem_filter.mp this).1
  let F : Finset Row := S tr j \ M1 tr j
  have hcard : F.card + (M1 tr j).card = (S tr j).card := Finset.card_sdiff_add_card_eq_card hMsub
  have hScard5 : (S tr j).card ≤ 5 := by
    have := Finset.card_le_univ (S tr j)
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  have hMpos : 1 ≤ (M1 tr j).card := Finset.card_pos.mpr ⟨k₀, hk₀M⟩
  have hG10 : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  let F' : Finset Row := insert k₀ F
  let M' : Finset Row := (M1 tr j).erase k₀
  have hk₀F : k₀ ∉ F := fun hm => (Finset.mem_sdiff.mp hm).2 hk₀M
  have hF'card : F'.card = F.card + 1 := Finset.card_insert_of_notMem hk₀F
  have hM'card : M'.card = (M1 tr j).card - 1 := Finset.card_erase_of_mem hk₀M
  have hdisj' : Disjoint F' M' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases Finset.mem_insert.mp hx with rfl | hxF
    · exact (Finset.mem_erase.mp hx').1 rfl
    · exact (Finset.mem_sdiff.mp hxF).2 (Finset.mem_erase.mp hx').2
  have hunion' : F' ∪ M' = S tr j := by
    ext x
    simp only [F', M', F, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ((rfl | ⟨hxS, _⟩) | ⟨_, hxM⟩)
      · exact hMsub hk₀M
      · exact hxS
      · exact hMsub hxM
    · intro hxS
      by_cases hxM : x ∈ M1 tr j
      · by_cases hxk : x = k₀
        · exact Or.inl (Or.inl hxk)
        · exact Or.inr ⟨hxk, hxM⟩
      · exact Or.inl (Or.inr ⟨hxS, hxM⟩)
  have hGsum' : (G1 tr j).card =
      ∑ k ∈ F', (inEdges tr j k).card + ∑ k ∈ M', (inEdges tr j k).card := by
    rw [← sum_inEdges_card h he j, ← hunion', Finset.sum_union hdisj']
  have hM'le1 : ∀ k ∈ M', (inEdges tr j k).card ≤ 1 := by
    intro k hkM'
    have hkne : k ≠ k₀ := (Finset.mem_erase.mp hkM').1
    have hkM : k ∈ M1 tr j := (Finset.mem_erase.mp hkM').2
    by_contra hgt
    have hmem : k ∈ Z2 tr j := Finset.mem_filter.mpr ⟨hkM, by omega⟩
    rw [hZ, Finset.mem_singleton] at hmem
    exact hkne hmem
  have hM'sum : ∑ k ∈ M', (inEdges tr j k).card ≤ M'.card := by
    calc ∑ k ∈ M', (inEdges tr j k).card
        ≤ ∑ _k ∈ M', 1 := Finset.sum_le_sum (fun k hk => hM'le1 k hk)
      _ = M'.card := by simp
  have hF'sum := sum_inEdges_subset_bound h j F'
  have hF'c5 : F'.card ≤ 5 := by omega
  have hch := choose2_bound (5 - F'.card) (by omega)
  have hge16 : 16 ≤ holeCost tr j := by
    unfold holeCost
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  refine ⟨hge16, ?_⟩
  intro heq16
  have hno_ge3 : ∀ k : Row, nonCount tr (k, j) ≤ 2 := by
    intro k
    by_contra hgt
    have hn3 := non_hole_lower_ge3 (tr := tr) (j := j) (k₀ := k) (by omega)
    unfold holeCost at heq16
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  have hF_cases : F.card = 1 ∨ F.card = 2 := by
    unfold holeCost at heq16
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  rcases hF_cases with hF1 | hF2
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hF1
    have hbF : b ∈ F := hb ▸ Finset.mem_singleton_self b
    have hbk : b ≠ k₀ := fun heq => hk₀F (heq ▸ hbF)
    have hb2 : nonCount tr (b, j) = 2 := by
      have hpos : 1 ≤ nonCount tr (b, j) := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hbF).1).2
      have hne1 : nonCount tr (b, j) ≠ 1 := fun h1 =>
        (Finset.mem_sdiff.mp hbF).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      have hle2 := hno_ge3 b
      omega
    have hF'eq : F' = {k₀, b} := by simp [F', hb]
    have hF'sum_eq : ∑ k ∈ F', (inEdges tr j k).card = 7 := by
      have h3 : (5 - F'.card).choose 2 = 3 := by
        rw [hF'card, hF1]; decide +kernel
      rw [h3] at hF'sum
      unfold holeCost at heq16
      omega
    have hbiUnion_eq : F'.biUnion (inEdges tr j) = holeColBank j \ edgesIn F'ᶜ j := by
      apply Finset.eq_of_subset_of_card_le (inEdges_biUnion_subset_sdiff h j F')
      have hsdiff := Finset.card_sdiff_add_card_eq_card (edgesIn_subset_holeColBank F'ᶜ j)
      rw [holeColBank_card j, edgesIn_card] at hsdiff
      have hc' : F'ᶜ.card = 3 := by
        have := Finset.card_add_card_compl F'
        have hR : Fintype.card Row = 5 := by decide +kernel
        omega
      have h3 : (3 : ℕ).choose 2 = 3 := by decide +kernel
      rw [hc', h3] at hsdiff
      rw [Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne), hF'sum_eq]
      omega
    refine ⟨b, hbk, hb2, ?_⟩
    intro i hik hib
    have hBbank : colAx i b j ∈ holeColBank j := mem_holeColBank.mpr ⟨i, b, hib, rfl⟩
    have hBnotIn : colAx i b j ∉ edgesIn F'ᶜ j := by
      intro hIn
      obtain ⟨⟨r, s⟩, hrs, heq⟩ := Finset.mem_image.mp hIn
      have hr : r ∉ F' := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).1
      have hs : s ∉ F' := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).2
      have hm : ((b, j), false) ∈ colAx r s j := heq ▸ by simp [colAx]
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hm
      have hbF' : b ∈ F' := by rw [hF'eq]; simp
      rcases hm with rfl | rfl
      · exact hr hbF'
      · exact hs hbF'
    have hBmem : colAx i b j ∈ F'.biUnion (inEdges tr j) :=
      hbiUnion_eq ▸ Finset.mem_sdiff.mpr ⟨hBbank, hBnotIn⟩
    obtain ⟨k, hkF', hEk⟩ := Finset.mem_biUnion.mp hBmem
    rw [hF'eq, Finset.mem_insert, Finset.mem_singleton] at hkF'
    rcases hkF' with hkk | hkb
    · subst hkk
      exfalso
      obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hEk).2
      have hu : ((k, j), false) ∈ colAx i b j := (h.col_mem_info hm).2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
      rcases hu with h1 | h1
      · exact hik h1.symm
      · exact hbk h1.symm
    · subst hkb; exact hEk
  ·
    have hM2 : (M1 tr j).card = 2 := by unfold holeCost at heq16; omega
    have hS4 : (S tr j).card = 4 := by omega
    have hG10eq : (G1 tr j).card = 10 := by unfold holeCost at heq16; omega
    have hGeq : G1 tr j = holeColBank j :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by rw [hG10eq, holeColBank_card j])
    have hSc1 : ((S tr j)ᶜ).card = 1 := by
      have := Finset.card_add_card_compl (S tr j)
      have hR : Fintype.card Row = 5 := by decide +kernel
      omega
    obtain ⟨u₀, hu₀eq⟩ := Finset.card_eq_one.mp hSc1
    have hu₀notS : u₀ ∉ S tr j := Finset.mem_compl.mp (hu₀eq ▸ Finset.mem_singleton_self u₀)
    have hM'1 : M'.card = 1 := by omega
    obtain ⟨r₁, hr₁eq⟩ := Finset.card_eq_one.mp hM'1
    have hr₁M' : r₁ ∈ M' := hr₁eq ▸ Finset.mem_singleton_self r₁
    have hr₁k₀ : r₁ ≠ k₀ := (Finset.mem_erase.mp hr₁M').1
    have hr₁S : r₁ ∈ S tr j := hMsub (Finset.mem_erase.mp hr₁M').2
    have hu₀r₁ : u₀ ≠ r₁ := fun heq => hu₀notS (heq ▸ hr₁S)

    have edge_owner : ∀ x y : Row, x ≠ y →
        colAx x y j ∈ inEdges tr j x ∨ colAx x y j ∈ inEdges tr j y := by
      intro x y hxy
      have hG : colAx x y j ∈ G1 tr j := hGeq ▸ mem_holeColBank.mpr ⟨x, y, hxy, rfl⟩
      have hmem : colAx x y j ∈ (S tr j).biUnion (inEdges tr j) :=
        (biUnion_inEdges_eq_G1 h he j).symm ▸ hG
      obtain ⟨k, _, hEk⟩ := Finset.mem_biUnion.mp hmem
      obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hEk).2
      have hu : ((k, j), false) ∈ colAx x y j := (h.col_mem_info hm).2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
      rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl hEk
      · exact Or.inr hEk

    have inEdges_u₀_empty : ∀ B, B ∉ inEdges tr j u₀ := by
      intro B hE
      have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
      have hmem : B ∈ (S tr j).biUnion (inEdges tr j) := (biUnion_inEdges_eq_G1 h he j).symm ▸ hG
      obtain ⟨k, hkS, hEk⟩ := Finset.mem_biUnion.mp hmem
      have hne : k ≠ u₀ := fun heq => hu₀notS (heq ▸ hkS)
      exact Finset.disjoint_left.mp (inEdges_disjoint hne) hEk hE

    have hr₁_edge : colAx u₀ r₁ j ∈ inEdges tr j r₁ := by
      rcases edge_owner u₀ r₁ hu₀r₁ with h1 | h2
      · exact (inEdges_u₀_empty _ h1).elim
      · exact h2
    have hr₁_only : ∀ B ∈ inEdges tr j r₁, B = colAx u₀ r₁ j := by
      intro B hB
      have hle1 := hM'le1 r₁ hr₁M'
      exact Finset.card_le_one.mp hle1 B hB (colAx u₀ r₁ j) hr₁_edge
    obtain ⟨b₁, b₂, hbne, hFeq⟩ := Finset.card_eq_two.mp hF2
    have hb₁F : b₁ ∈ F := hFeq ▸ by simp
    have hb₂F : b₂ ∈ F := hFeq ▸ by simp
    have hb_props : ∀ b ∈ F, b ≠ k₀ ∧ b ≠ u₀ ∧ b ≠ r₁ ∧ nonCount tr (b, j) = 2 ∧
        colAx u₀ b j ∈ inEdges tr j b ∧ colAx r₁ b j ∈ inEdges tr j b := by
      intro b hbF
      have hbS : b ∈ S tr j := (Finset.mem_sdiff.mp hbF).1
      have hbnotM : b ∉ M1 tr j := (Finset.mem_sdiff.mp hbF).2
      have hbk : b ≠ k₀ := fun heq => hbnotM (heq ▸ hk₀M)
      have hbu : b ≠ u₀ := fun heq => hu₀notS (heq ▸ hbS)
      have hbr : b ≠ r₁ := fun heq => hbnotM (heq ▸ (Finset.mem_erase.mp hr₁M').2)
      have hb2 : nonCount tr (b, j) = 2 := by
        have hpos : 1 ≤ nonCount tr (b, j) := (Finset.mem_filter.mp hbS).2
        have hne1 : nonCount tr (b, j) ≠ 1 := fun h1 =>
          hbnotM (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        have hle2 := hno_ge3 b
        omega
      have heu : colAx u₀ b j ∈ inEdges tr j b := by
        rcases edge_owner u₀ b hbu.symm with h1 | h2
        · exact (inEdges_u₀_empty _ h1).elim
        · exact h2
      have her : colAx r₁ b j ∈ inEdges tr j b := by
        rcases edge_owner r₁ b hbr.symm with h1 | h2
        · exfalso
          have heq := hr₁_only _ h1
          have hm : ((b, j), false) ∈ colAx u₀ r₁ j := heq ▸ by simp [colAx]
          simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hm
          rcases hm with h1' | h1'
          · exact hbu h1'
          · exact hbr h1'
        · exact h2
      exact ⟨hbk, hbu, hbr, hb2, heu, her⟩
    have row_decomp : ∀ i : Row, i = u₀ ∨ i = k₀ ∨ i = r₁ ∨ i = b₁ ∨ i = b₂ := by
      intro i
      by_cases hiS : i ∈ S tr j
      · by_cases hiM : i ∈ M1 tr j
        · by_cases hik : i = k₀
          · exact Or.inr (Or.inl hik)
          · have hiM' : i ∈ M' := Finset.mem_erase.mpr ⟨hik, hiM⟩
            rw [hr₁eq, Finset.mem_singleton] at hiM'
            exact Or.inr (Or.inr (Or.inl hiM'))
        · have hiF : i ∈ F := Finset.mem_sdiff.mpr ⟨hiS, hiM⟩
          rw [hFeq, Finset.mem_insert, Finset.mem_singleton] at hiF
          rcases hiF with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · have hic : i ∈ (S tr j)ᶜ := Finset.mem_compl.mpr hiS
        rw [hu₀eq, Finset.mem_singleton] at hic
        exact Or.inl hic
    rcases edge_owner b₁ b₂ hbne with hb12 | hb21
    · obtain ⟨hbk, _, _, hb2, heu, her⟩ := hb_props b₁ hb₁F
      refine ⟨b₁, hbk, hb2, ?_⟩
      intro i hik hib
      rcases row_decomp i with rfl | rfl | rfl | rfl | rfl
      · exact heu
      · exact (hik rfl).elim
      · exact her
      · exact (hib rfl).elim
      · rw [colAx_comm]; exact hb12
    · obtain ⟨hbk, _, _, hb2, heu, her⟩ := hb_props b₂ hb₂F
      refine ⟨b₂, hbk, hb2, ?_⟩
      intro i hik hib
      rcases row_decomp i with rfl | rfl | rfl | rfl | rfl
      · exact heu
      · exact (hik rfl).elim
      · exact her
      · exact hb21
      · exact (hib rfl).elim

theorem z2_unique_non {tr : List Step} {j : Hole} {k : Row} (hk : k ∈ Z2 tr j) :
    ∃ (idx : Fin tr.length) (R : C),
      tr[idx] = Step.non (k, j) R ∧
      ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx := by
  have h1 : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  obtain ⟨idx, hi, huniq⟩ := countP_eq_one_unique_idx tr (isNonOf (k, j)) h1
  cases hstep : tr[idx] with
  | ax _ => simp [hstep, isNonOf] at hi
  | col _ _ _ _ => simp [hstep, isNonOf] at hi
  | non v R =>
    simp only [hstep, isNonOf, decide_eq_true_eq] at hi
    subst hi
    exact ⟨idx, R, hstep, huniq⟩

theorem z2_clause_unsat_edge {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k : Row}
    {idx : Fin tr.length} {R : C}
    (hstep : tr[idx] = Step.non (k, j) R)
    (huniq : ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx)
    {i : Row} (hi : colAx i k j ∈ inEdges tr j k)
    {f : Row → Hole} (hf : ValidMatch i k j f) :
    ((k, j), false) ∉ R ∧ ¬ ClauseSat (colModel i k j f) R := by
  by_contra hbad
  have h1 : ∀ v u R', Step.col (colAx i k j) v u R' ∈ tr → u ∈ ({(k, j)} : Finset V) := by
    intro v u R' hm
    rw [Finset.mem_singleton]
    exact (inEdges_mem_iff_unique hi).2 v u R' hm
  have h2 : ∀ v R', Step.non v R' ∈ tr → v ∈ ({(k, j)} : Finset V) →
      (∀ w ∈ ({(k, j)} : Finset V), (w, false) ∉ R') → ClauseSat (colModel i k j f) R' := by
    intro v R' hm hv hnotf
    rw [Finset.mem_singleton] at hv
    subst hv
    obtain ⟨j', hj'lt, hj'⟩ := List.getElem_of_mem hm
    have heq : (⟨j', hj'lt⟩ : Fin tr.length) = idx := huniq ⟨j', hj'lt⟩ (by simp [hj', isNonOf])
    have hj'step : tr[idx] = Step.non (k, j) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
    rw [hstep] at hj'step
    cases hj'step
    have hnot : ((k, j), false) ∉ R := hnotf (k, j) (Finset.mem_singleton_self _)
    by_contra hns
    exact hbad ⟨hnot, hns⟩
  have hsat := masterControl h (colModel i k j f) (colAx i k j) {(k, j)}
    (colModel_sat_rows hf) (colModel_sat_cols hf) h1 h2
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
  exact emptyUnsat _ hsat

theorem z2_clause_shape {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k : Row} (hk : k ∈ Z2 tr j)
    {idx : Fin tr.length} {R : C}
    (hstep : tr[idx] = Step.non (k, j) R)
    (huniq : ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx) :
    (∀ v : V, (v, false) ∉ R) ∧
    (∀ r : Row, ∀ q : Hole, ((r, q), true) ∈ R → (r = k ∨ q = j) ∧ (r, q) ≠ (k, j)) := by
  have h2card : 2 ≤ (inEdges tr j k).card := (Finset.mem_filter.mp hk).2
  obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr j k).card)
  obtain ⟨i₁, hi₁k, rfl⟩ := inEdges_mem_colAx h hB₁
  obtain ⟨i₂, hi₂k, rfl⟩ := inEdges_mem_colAx h hB₂
  have hi₁₂ : i₁ ≠ i₂ := fun heq => hBne (heq ▸ rfl)
  obtain ⟨f₁, hf₁⟩ := exists_validMatch i₁ k hi₁k j
  have hunsat1 := z2_clause_unsat_edge h he hstep huniq hB₁ hf₁
  constructor
  · intro ⟨r, q⟩ hmem
    by_cases hrk : r = k
    · subst hrk
      by_cases hqj : q = j
      · subst hqj; exact hunsat1.1 hmem
      · exact hunsat1.2 ⟨((r, q), false), hmem, by simp [colModel, hqj]⟩
    · have hpick : ∃ i : Row, i ≠ k ∧ i ≠ r ∧ colAx i k j ∈ inEdges tr j k := by
        by_cases h1 : r = i₁
        · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
        · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
      obtain ⟨i, hik, hir, hiE⟩ := hpick
      obtain ⟨f, hf, hfr⟩ := exists_validMatch_avoid i k r hik hir.symm hrk j q
      have huns := (z2_clause_unsat_edge h he hstep huniq hiE hf).2
      exact huns ⟨((r, q), false), hmem, by simp [colModel, hir.symm, hrk, hfr]⟩
  · intro r q hmem
    refine ⟨?_, ?_⟩
    · by_contra hneither
      push Not at hneither
      obtain ⟨hrk, hqj⟩ := hneither
      have hpick : ∃ i : Row, i ≠ k ∧ i ≠ r ∧ colAx i k j ∈ inEdges tr j k := by
        by_cases h1 : r = i₁
        · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
        · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
      obtain ⟨i, hik, hir, hiE⟩ := hpick
      obtain ⟨f, hf, hfr⟩ := exists_validMatch_map i k r hik hir.symm hrk j q hqj
      have huns := (z2_clause_unsat_edge h he hstep huniq hiE hf).2
      exact huns ⟨((r, q), true), hmem, by simp [colModel, hir.symm, hrk, hfr]⟩
    · intro heq
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hunsat1.2 ⟨((r, q), true), hmem, by simp [colModel]⟩

theorem z2_not_coll {R : C} (hnoNeg : ∀ v : V, (v, false) ∉ R) : ¬ Coll R := by
  rintro ⟨i, _, k, _, j, _, _, rfl⟩
  exact hnoNeg (i, j) (by simp [colAx])

theorem z2_unsat_colModel {j : Hole} {k : Row} {R : C}
    (hshape : (∀ v : V, (v, false) ∉ R) ∧
      (∀ r : Row, ∀ q : Hole, ((r, q), true) ∈ R → (r = k ∨ q = j) ∧ (r, q) ≠ (k, j)))
    {i' k' : Row} {j' : Hole} {f : Row → Hole} (hf : ValidMatch i' k' j' f)
    (hjj : j' ≠ j) (hi' : i' ≠ k) (hk' : k' ≠ k) (hfk : f k = j) :
    ¬ ClauseSat (colModel i' k' j' f) R := by
  rintro ⟨⟨⟨r, q⟩, pol⟩, hmem, hsat⟩
  cases pol with
  | false => exact hshape.1 (r, q) hmem
  | true =>
    obtain ⟨hor, hne⟩ := hshape.2 r q hmem
    change colModel i' k' j' f (r, q) = true at hsat
    rcases hor with rfl | rfl
    · have hqj : q ≠ j := fun hq => hne (Prod.ext rfl hq)
      simp only [colModel, hi'.symm, hk'.symm, or_self, ↓reduceIte, decide_eq_true_eq, hfk] at hsat
      exact hqj hsat.symm
    · have hrk : r ≠ k := fun hr => hne (Prod.ext hr rfl)
      by_cases hri : r = i' ∨ r = k'
      · simp only [colModel, hri, ↓reduceIte, decide_eq_true_eq] at hsat
        exact hjj hsat.symm
      · push Not at hri
        simp only [colModel, hri.1, hri.2, or_self, ↓reduceIte, decide_eq_true_eq] at hsat
        exact hrk (hf.2 r k hri.1 hri.2 hi'.symm hk'.symm (hsat.trans hfk.symm))

theorem z2_not_earlier {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf)
    {j₁ j₂ : Hole} {k₁ k₂ : Row} (hk₁ : k₁ ∈ Z2 tr j₁) (hk₂ : k₂ ∈ Z2 tr j₂)
    (hkne : k₁ ≠ k₂) (hjne : j₁ ≠ j₂)
    {idx₁ idx₂ : Fin tr.length} {R₁ R₂ : C}
    (hs₁ : tr[idx₁] = Step.non (k₁, j₁) R₁)
    (hu₁ : ∀ j' : Fin tr.length, isNonOf (k₁, j₁) tr[j'] = true → j' = idx₁)
    (_hs₂ : tr[idx₂] = Step.non (k₂, j₂) R₂)
    (hu₂ : ∀ j' : Fin tr.length, isNonOf (k₂, j₂) tr[j'] = true → j' = idx₂)
    (hlt : idx₂.1 < idx₁.1) : False := by
  have hshape₁ := z2_clause_shape h he hk₁ hs₁ hu₁
  have h2card : 2 ≤ (inEdges tr j₂ k₂).card := (Finset.mem_filter.mp hk₂).2
  obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr j₂ k₂).card)
  obtain ⟨i₁, hi₁k, rfl⟩ := inEdges_mem_colAx h hB₁
  obtain ⟨i₂, hi₂k, rfl⟩ := inEdges_mem_colAx h hB₂
  have hi₁₂ : i₁ ≠ i₂ := fun heq => hBne (heq ▸ rfl)
  have hpick : ∃ i : Row, i ≠ k₂ ∧ i ≠ k₁ ∧ colAx i k₂ j₂ ∈ inEdges tr j₂ k₂ := by
    by_cases h1 : k₁ = i₁
    · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
    · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
  obtain ⟨i, hik₂, hik₁, hiE⟩ := hpick
  obtain ⟨f, hf, hfk₁⟩ := exists_validMatch_map i k₂ k₁ hik₂ hik₁.symm hkne j₂ j₁ hjne
  have hR₁mem : R₁ ∈ (tr.drop idx₁.1).map clauseOf := by
    refine List.mem_map.mpr ⟨Step.non (k₁, j₁) R₁, ?_, rfl⟩
    exact (mem_drop_iff tr idx₁.1 _).mpr ⟨idx₁, le_rfl, hs₁⟩
  have hsat := masterControl (h.drop idx₁.1) (colModel i k₂ j₂ f) (colAx i k₂ j₂) {(k₂, j₂)}
    (colModel_sat_rows hf) (colModel_sat_cols hf)
    (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique hiE).2 v u R' (mem_of_mem_drop hm)))
    (fun v R' hm hv _ => by
      rw [Finset.mem_singleton] at hv
      subst hv
      obtain ⟨m, hmle, hget⟩ := (mem_drop_iff tr idx₁.1 _).mp hm
      have heq := hu₂ m (by rw [hget]; simp [isNonOf])
      omega)
    R₁ hR₁mem (z2_not_coll hshape₁.1) (fun w _ => hshape₁.1 w)
  exact z2_unsat_colModel hshape₁ hf hjne.symm hik₁ hkne.symm hfk₁ hsat

theorem z2_line {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf)
    {j₁ j₂ : Hole} {k₁ k₂ : Row} (hk₁ : k₁ ∈ Z2 tr j₁) (hk₂ : k₂ ∈ Z2 tr j₂) :
    k₁ = k₂ ∨ j₁ = j₂ := by
  by_contra hneither
  push Not at hneither
  obtain ⟨hkne, hjne⟩ := hneither
  obtain ⟨idx₁, R₁, hs₁, hu₁⟩ := z2_unique_non hk₁
  obtain ⟨idx₂, R₂, hs₂, hu₂⟩ := z2_unique_non hk₂
  have hne : idx₁ ≠ idx₂ := by
    intro heq
    subst heq
    rw [hs₁] at hs₂
    cases hs₂
    exact hkne rfl
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact z2_not_earlier h he hk₂ hk₁ hkne.symm hjne.symm hs₂ hu₂ hs₁ hu₁ hlt
  · exact z2_not_earlier h he hk₁ hk₂ hkne hjne hs₁ hu₁ hs₂ hu₂ hgt

def subMask (x y : Nat) : Bool := (x &&& y) == x

theorem subMask_iff_testBit (x y : Nat) :
    subMask x y = true ↔ ∀ i : Nat, x.testBit i = true → y.testBit i = true := by
  simp only [subMask, beq_iff_eq]
  constructor
  · intro h i hxi
    have ht := congrArg (fun n => n.testBit i) h
    rw [Nat.testBit_and, hxi, Bool.true_and] at ht
    exact ht
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

theorem subMask_refl (x : Nat) : subMask x x = true :=
  (subMask_iff_testBit x x).mpr (fun _ h => h)

theorem subMask_trans {x y z : Nat} (h1 : subMask x y = true) (h2 : subMask y z = true) :
    subMask x z = true :=
  (subMask_iff_testBit x z).mpr (fun i hi =>
    (subMask_iff_testBit y z).mp h2 i ((subMask_iff_testBit x y).mp h1 i hi))

theorem subMask_land_mono {a b c d : Nat} (h1 : subMask a c = true) (h2 : subMask b d = true) :
    subMask (a &&& b) (c &&& d) = true := by
  rw [subMask_iff_testBit]
  intro i hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi ⊢
  exact ⟨(subMask_iff_testBit a c).mp h1 i hi.1, (subMask_iff_testBit b d).mp h2 i hi.2⟩

theorem subMask_lor_mono {a b c d : Nat} (h1 : subMask a c = true) (h2 : subMask b d = true) :
    subMask (a ||| b) (c ||| d) = true := by
  rw [subMask_iff_testBit]
  intro i hi
  rw [Nat.testBit_or, Bool.or_eq_true] at hi ⊢
  rcases hi with h | h
  · exact Or.inl ((subMask_iff_testBit a c).mp h1 i h)
  · exact Or.inr ((subMask_iff_testBit b d).mp h2 i h)

def insertMax (x : Nat) (acc : List Nat) : List Nat :=
  if acc.any (fun y => subMask x y) then acc
  else x :: acc.filter (fun y => !(subMask y x))

def pruneMax (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertMax x acc) []

theorem insertMax_covers_old {x : Nat} {acc : List Nat} {z : Nat}
    (hz : ∃ w ∈ acc, subMask z w = true) :
    ∃ w ∈ insertMax x acc, subMask z w = true := by
  unfold insertMax
  split
  · exact hz
  · obtain ⟨w, hw, hzw⟩ := hz
    by_cases hwx : subMask w x = true
    · exact ⟨x, List.mem_cons_self, subMask_trans hzw hwx⟩
    · refine ⟨w, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hw, ?_⟩), hzw⟩
      cases h : subMask w x <;> simp_all

theorem insertMax_covers_new (x : Nat) (acc : List Nat) :
    ∃ w ∈ insertMax x acc, subMask x w = true := by
  unfold insertMax
  split
  · rename_i h
    obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp h
    exact ⟨y, hy, hxy⟩
  · exact ⟨x, List.mem_cons_self, subMask_refl x⟩

theorem foldl_insertMax_covers (xs acc : List Nat) :
    (∀ z ∈ acc, ∃ w ∈ xs.foldl (fun a x => insertMax x a) acc, subMask z w = true) ∧
    (∀ x ∈ xs, ∃ w ∈ xs.foldl (fun a x => insertMax x a) acc, subMask x w = true) := by
  induction xs generalizing acc with
  | nil =>
    exact ⟨fun z hz => ⟨z, hz, subMask_refl z⟩, fun x hx => by cases hx⟩
  | cons a tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨hold, hnew⟩ := ih (insertMax a acc)
    constructor
    · intro z hz
      obtain ⟨w₁, hw₁, hzw₁⟩ := insertMax_covers_old (x := a) ⟨z, hz, subMask_refl z⟩
      obtain ⟨w₂, hw₂, hw₁₂⟩ := hold w₁ hw₁
      exact ⟨w₂, hw₂, subMask_trans hzw₁ hw₁₂⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · obtain ⟨w₁, hw₁, hxw₁⟩ := insertMax_covers_new x acc
        obtain ⟨w₂, hw₂, hw₁₂⟩ := hold w₁ hw₁
        exact ⟨w₂, hw₂, subMask_trans hxw₁ hw₁₂⟩
      · exact hnew x hx'

theorem pruneMax_covers (xs : List Nat) {x : Nat} (hx : x ∈ xs) :
    ∃ y ∈ pruneMax xs, subMask x y = true :=
  (foldl_insertMax_covers xs []).2 x hx

def perm3 (p : Fin 6) (i : Fin 3) : Fin 3 :=
  match p.val, i.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 2
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 1
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

def bHole (c : Fin 3) (p : Fin 6) (r : Fin 5) : Fin 4 :=
  match c.val, r.val with
  | 0, 0 => 0 | 0, 1 => (perm3 p 0).succ | 0, 2 => (perm3 p 1).succ | 0, 3 => 0 | 0, _ => (perm3 p 2).succ
  | 1, 0 => (perm3 p 0).succ | 1, 1 => 0 | 1, 2 => (perm3 p 1).succ | 1, 3 => 0 | 1, _ => (perm3 p 2).succ
  | _, 0 => (perm3 p 0).succ | _, 1 => (perm3 p 1).succ | _, 2 => 0 | _, 3 => 0 | _, _ => (perm3 p 2).succ

def otherHoles (m : Fin 3) : Fin 4 × Fin 4 :=
  match m.val with
  | 0 => (2, 3)
  | 1 => (1, 3)
  | _ => (1, 2)

def oneMustHole (m ic : Fin 3) (r : Fin 5) : Fin 4 :=
  let (h1, h2) := otherHoles m
  match ic.val, r.val with
  | 0, 0 => m.succ | 0, 1 => h1 | 0, 2 => h2 | 0, 3 => 0 | 0, _ => m.succ
  | 1, 0 => h1 | 1, 1 => m.succ | 1, 2 => h2 | 1, 3 => 0 | 1, _ => m.succ
  | _, 0 => h1 | _, 1 => h2 | _, 2 => m.succ | _, 3 => 0 | _, _ => m.succ

def fin3ToRow (c : Fin 3) : Row := ⟨c.val, by omega⟩

theorem bHole_valid : ∀ (c : Fin 3) (p : Fin 6), ValidMatch (fin3ToRow c) 3 0 (bHole c p) := by
  intro c p
  apply validMatch_of_bool
  have h : (List.finRange 3).all (fun c => (List.finRange 6).all (fun p => validMatchB (fin3ToRow c) 3 0 (bHole c p))) = true := by
    decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp h c (List.mem_finRange _)) p (List.mem_finRange _)

theorem bHole_colModel_eq :
    ∀ (c : Fin 3) (p : Fin 6) (r : Row) (q : Hole),
      colModel (fin3ToRow c) 3 0 (bHole c p) (r, q) = decide (bHole c p r = q) := by
  decide +kernel

theorem oneMustHole_valid :
    ∀ (m ic : Fin 3), ValidMatch (fin3ToRow ic) 4 m.succ (oneMustHole m ic) := by
  intro m ic
  apply validMatch_of_bool
  have h : (List.finRange 3).all (fun m => (List.finRange 3).all (fun ic => validMatchB (fin3ToRow ic) 4 m.succ (oneMustHole m ic))) = true := by
    decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp h m (List.mem_finRange _)) ic (List.mem_finRange _)

theorem oneMustHole_colModel_eq :
    ∀ (m ic : Fin 3) (r : Row) (q : Hole),
      colModel (fin3ToRow ic) 4 m.succ (oneMustHole m ic) (r, q) = decide (oneMustHole m ic r = q) := by
  decide +kernel

def idxC (idx : Fin 18) : Fin 3 := ⟨idx.val / 6, by omega⟩
def idxP (idx : Fin 18) : Fin 6 := ⟨idx.val % 6, by omega⟩

def evalLitHole (h : Row → Hole) (l : Literal V) : Bool :=
  if l.2 then decide (h l.1.1 = l.1.2) else !decide (h l.1.1 = l.1.2)

def fmaskList (l : Literal V) : Nat :=
  (List.finRange 18).foldl
    (fun acc idx => if evalLitHole (bHole (idxC idx) (idxP idx)) l then acc else acc ||| (1 <<< idx.val))
    0

def allLits39 : List (Literal V) :=
  ((List.finRange 5).flatMap fun r =>
    (List.finRange 4).flatMap fun q =>
      [((r, q), false), ((r, q), true)]).filter (fun l => l != ((3, 0), false))

def isWitnessLit (m ic : Fin 3) (l : Literal V) : Bool :=
  (l == ((4, m.succ), false)) || evalLitHole (oneMustHole m ic) l

def witsList (m ic : Fin 3) : List Nat :=
  (allLits39.filter (isWitnessLit m ic)).map fmaskList

def req1Mask (pos : Nat) : Nat :=
  (List.finRange 18).foldl
    (fun acc idx =>
      if decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos) then acc ||| (1 <<< idx.val) else acc)
    0

def pairLand (xs ys : List Nat) : List Nat :=
  pruneMax (xs.flatMap (fun a => ys.map (fun b => a &&& b)))

def checkCase (ic0 ic1 ic2 : Fin 3) : Bool :=
  let w0 := pruneMax (witsList 0 ic0)
  let w1 := pruneMax (witsList 1 ic1)
  let w2 := pruneMax (witsList 2 ic2)
  let c01 := pairLand w0 w1
  let c012 := pairLand c01 w2
  let c12 := pairLand w1 w2
  let ok0 := c012.all (fun x => c012.all (fun y => !(subMask 262143 (x ||| y))))
  let ok1 := (c012.filter (fun x => subMask (req1Mask 1) x)).all
    (fun x => c12.all (fun y => !(subMask 262143 (x ||| y))))
  let ok2 := (c012.filter (fun x => subMask (req1Mask 2) x)).all
    (fun x => w2.all (fun y => !(subMask 262143 (x ||| y))))
  let ok3 := c012.all (fun x => !(subMask 262143 x))
  ok0 && ok1 && ok2 && ok3

def checkAll : Bool :=
  (List.finRange 3).all (fun ic0 =>
    (List.finRange 3).all (fun ic1 =>
      (List.finRange 3).all (fun ic2 => checkCase ic0 ic1 ic2)))

theorem checkAll_eq_true : checkAll = true := by decide +kernel

theorem foldl_lor_testBit (p : Fin 18 → Bool) (i : Fin 18) :
    ((List.finRange 18).foldl
      (fun acc idx => if p idx then acc ||| (1 <<< idx.val) else acc) 0).testBit i.val = p i := by
  have hgen : ∀ (l : List (Fin 18)) (acc : Nat),
      (l.foldl (fun a idx => if p idx then a ||| (1 <<< idx.val) else a) acc).testBit i.val =
        (acc.testBit i.val || (i ∈ l && p i)) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a tl ih =>
      intro acc
      simp only [List.foldl_cons, ih]
      by_cases hpa : p a = true
      · simp only [hpa, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
        by_cases hia : i = a
        · subst hia; simp [hpa]
        · have hne : i.val ≠ a.val := Fin.val_ne_of_ne hia
          have hbit : (decide (i.val ≥ a.val) && Nat.testBit 1 (i.val - a.val)) = false := by
            by_cases hle : a.val ≤ i.val
            · have hnz : i.val - a.val ≠ 0 := by omega
              have hnt : Nat.testBit 1 (i.val - a.val) = false :=
                Bool.eq_false_iff.mpr (fun ht => hnz (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht))
              simp [hle, hnt]
            · simp [hle]
          rw [hbit]
          simp [hia]
      · simp only [hpa]
        by_cases hia : i = a
        · subst hia; simp [hpa]
        · simp [hia]
  rw [hgen]
  simp [List.mem_finRange]

theorem fmaskList_testBit (l : Literal V) (idx : Fin 18) :
    (fmaskList l).testBit idx.val = !evalLitHole (bHole (idxC idx) (idxP idx)) l := by
  have h := foldl_lor_testBit (fun idx => !evalLitHole (bHole (idxC idx) (idxP idx)) l) idx
  have heq : fmaskList l = (List.finRange 18).foldl
      (fun acc idx => if !evalLitHole (bHole (idxC idx) (idxP idx)) l then acc ||| (1 <<< idx.val) else acc) 0 := by
    unfold fmaskList
    congr 1
    funext acc i
    cases evalLitHole (bHole (idxC i) (idxP i)) l <;> rfl
  rw [heq, h]

theorem req1Mask_testBit (pos : Nat) (idx : Fin 18) :
    (req1Mask pos).testBit idx.val = decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos) :=
  foldl_lor_testBit (fun idx => decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos)) idx

theorem all18_testBit (i : Nat) : (262143 : Nat).testBit i = decide (i < 18) := by
  by_cases hi : i < 18
  · interval_cases i <;> decide +kernel
  · have hlt : (262143 : Nat) < 2 ^ i := by
      have h1 : (262143 : Nat) < 2 ^ 18 := by decide +kernel
      have h2 : 2 ^ 18 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp [hi, Nat.testBit_lt_two_pow hlt]

theorem mem_allLits39 {l : Literal V} (hne : l ≠ ((3, 0), false)) : l ∈ allLits39 := by
  unfold allLits39
  rw [List.mem_filter]
  refine ⟨?_, by simp [hne]⟩
  rw [List.mem_flatMap]
  refine ⟨l.1.1, List.mem_finRange _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨l.1.2, List.mem_finRange _, ?_⟩
  rcases l with ⟨⟨r, q⟩, pol⟩
  cases pol <;> simp

theorem pairLand_covers {xs ys xs' ys' : List Nat}
    (hx : ∀ x ∈ xs, ∃ x' ∈ xs', subMask x x' = true)
    (hy : ∀ y ∈ ys, ∃ y' ∈ ys', subMask y y' = true)
    {a b : Nat} (ha : a ∈ xs) (hb : b ∈ ys) :
    ∃ z ∈ pairLand xs' ys', subMask (a &&& b) z = true := by
  obtain ⟨a', ha', haa'⟩ := hx a ha
  obtain ⟨b', hb', hbb'⟩ := hy b hb
  have hmem : (a' &&& b') ∈ xs'.flatMap (fun u => ys'.map (fun v => u &&& v)) := by
    rw [List.mem_flatMap]
    exact ⟨a', ha', List.mem_map.mpr ⟨b', hb', rfl⟩⟩
  obtain ⟨z, hz, hsub⟩ := pruneMax_covers _ hmem
  exact ⟨z, hz, subMask_trans (subMask_land_mono haa' hbb') hsub⟩

theorem killer_masks_impossible (ic0 ic1 ic2 : Fin 3) (pos : Fin 4)
    (m1 m2 : Nat)
    (hm1_0 : ∃ x ∈ witsList 0 ic0, subMask m1 x = true)
    (hm1_1 : ∃ x ∈ witsList 1 ic1, subMask m1 x = true)
    (hm1_2 : ∃ x ∈ witsList 2 ic2, subMask m1 x = true)
    (hreq : subMask (req1Mask pos.val) m1 = true)
    (hm2_0 : pos.val = 0 → ∃ x ∈ witsList 0 ic0, subMask m2 x = true)
    (hm2_1 : pos.val ≤ 1 → ∃ x ∈ witsList 1 ic1, subMask m2 x = true)
    (hm2_2 : pos.val ≤ 2 → ∃ x ∈ witsList 2 ic2, subMask m2 x = true)
    (hcov : subMask 262143 (m1 ||| m2) = true) : False := by
  have hcase : checkCase ic0 ic1 ic2 = true := by
    have h0 := List.all_eq_true.mp checkAll_eq_true ic0 (List.mem_finRange _)
    have h1 := List.all_eq_true.mp h0 ic1 (List.mem_finRange _)
    exact List.all_eq_true.mp h1 ic2 (List.mem_finRange _)
  unfold checkCase at hcase
  simp only [Bool.and_eq_true] at hcase
  obtain ⟨⟨⟨hok0, hok1⟩, hok2⟩, hok3⟩ := hcase
  let w0 := pruneMax (witsList 0 ic0)
  let w1 := pruneMax (witsList 1 ic1)
  let w2 := pruneMax (witsList 2 ic2)
  let c01 := pairLand w0 w1
  let c012 := pairLand c01 w2
  let c12 := pairLand w1 w2
  have hw0 : ∀ x ∈ witsList 0 ic0, ∃ y ∈ w0, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hw1 : ∀ x ∈ witsList 1 ic1, ∃ y ∈ w1, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hw2 : ∀ x ∈ witsList 2 ic2, ∃ y ∈ w2, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hcov_m1 : ∃ z1 ∈ c012, subMask m1 z1 = true := by
    obtain ⟨x0, hx0, hmx0⟩ := hm1_0
    obtain ⟨x1, hx1, hmx1⟩ := hm1_1
    obtain ⟨x2, hx2, hmx2⟩ := hm1_2
    obtain ⟨u01, hu01, h01⟩ := pairLand_covers hw0 hw1 hx0 hx1
    obtain ⟨y2, hy2, h2⟩ := hw2 x2 hx2
    have hmem : (u01 &&& y2) ∈ c01.flatMap (fun a => w2.map (fun b => a &&& b)) :=
      List.mem_flatMap.mpr ⟨u01, hu01, List.mem_map.mpr ⟨y2, hy2, rfl⟩⟩
    obtain ⟨z1, hz1, hz1sub⟩ := pruneMax_covers _ hmem
    have hm01 : subMask m1 (x0 &&& x1) = true := by
      have := subMask_land_mono hmx0 hmx1
      simpa [Nat.and_self] using this
    have hm012 : subMask m1 (u01 &&& y2) = true := by
      have := subMask_land_mono (subMask_trans hm01 h01) (subMask_trans hmx2 h2)
      simpa [Nat.and_self] using this
    exact ⟨z1, hz1, subMask_trans hm012 hz1sub⟩
  obtain ⟨z1, hz1, hmz1⟩ := hcov_m1
  fin_cases pos
  ·
    obtain ⟨x0, hx0, hmx0⟩ := hm2_0 rfl
    obtain ⟨x1, hx1, hmx1⟩ := hm2_1 (by decide)
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨u01, hu01, h01⟩ := pairLand_covers hw0 hw1 hx0 hx1
    obtain ⟨y2, hy2, h2⟩ := hw2 x2 hx2
    have hmem : (u01 &&& y2) ∈ c01.flatMap (fun a => w2.map (fun b => a &&& b)) :=
      List.mem_flatMap.mpr ⟨u01, hu01, List.mem_map.mpr ⟨y2, hy2, rfl⟩⟩
    obtain ⟨z2, hz2, hz2sub⟩ := pruneMax_covers _ hmem
    have hm01 : subMask m2 (x0 &&& x1) = true := by
      simpa [Nat.and_self] using subMask_land_mono hmx0 hmx1
    have hmz2 : subMask m2 z2 = true := subMask_trans
      (by simpa [Nat.and_self] using subMask_land_mono (subMask_trans hm01 h01) (subMask_trans hmx2 h2))
      hz2sub
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok0 z1 hz1) z2 hz2
    simp [hfull] at hbad
  ·
    obtain ⟨x1, hx1, hmx1⟩ := hm2_1 (by decide)
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨z2, hz2, h12⟩ := pairLand_covers hw1 hw2 hx1 hx2
    have hmz2 : subMask m2 z2 = true := subMask_trans
      (by simpa [Nat.and_self] using subMask_land_mono hmx1 hmx2) h12
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hz1f : z1 ∈ c012.filter (fun x => subMask (req1Mask 1) x) :=
      List.mem_filter.mpr ⟨hz1, subMask_trans hreq hmz1⟩
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok1 z1 hz1f) z2 hz2
    simp [hfull] at hbad
  ·
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨z2, hz2, h2⟩ := hw2 x2 hx2
    have hmz2 : subMask m2 z2 = true := subMask_trans hmx2 h2
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hz1f : z1 ∈ c012.filter (fun x => subMask (req1Mask 2) x) :=
      List.mem_filter.mpr ⟨hz1, subMask_trans hreq hmz1⟩
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok2 z1 hz1f) z2 hz2
    simp [hfull] at hbad
  ·
    have hreq3 : req1Mask 3 = 262143 := by decide +kernel
    rw [hreq3] at hreq
    have hfull : subMask 262143 z1 = true := subMask_trans hreq hmz1
    have hbad := List.all_eq_true.mp hok3 z1 hz1
    simp [hfull] at hbad

def transportF (er : Row ≃ Row) (eh : Hole ≃ Hole) (g : Row → Hole) : Row → Hole :=
  fun r => eh (g (er.symm r))

theorem transport_validMatch (er : Row ≃ Row) (eh : Hole ≃ Hole)
    {i k : Row} {j : Hole} {g : Row → Hole} (hg : ValidMatch i k j g) :
    ValidMatch (er i) (er k) (eh j) (transportF er eh g) := by
  refine ⟨?_, ?_⟩
  · intro r hri hrk heq
    have h1 : er.symm r ≠ i := fun h => hri (by rw [← h, er.apply_symm_apply])
    have h2 : er.symm r ≠ k := fun h => hrk (by rw [← h, er.apply_symm_apply])
    exact hg.1 (er.symm r) h1 h2 (eh.injective heq)
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    have h1i : er.symm r₁ ≠ i := fun h => hr₁i (by rw [← h, er.apply_symm_apply])
    have h1k : er.symm r₁ ≠ k := fun h => hr₁k (by rw [← h, er.apply_symm_apply])
    have h2i : er.symm r₂ ≠ i := fun h => hr₂i (by rw [← h, er.apply_symm_apply])
    have h2k : er.symm r₂ ≠ k := fun h => hr₂k (by rw [← h, er.apply_symm_apply])
    exact er.symm.injective (hg.2 _ _ h1i h1k h2i h2k (eh.injective heq))

theorem transport_colModel (er : Row ≃ Row) (eh : Hole ≃ Hole)
    {i k : Row} {j : Hole} {g : Row → Hole} (r : Row) (q : Hole) :
    colModel (er i) (er k) (eh j) (transportF er eh g) (er r, eh q) =
      colModel i k j g (r, q) := by
  simp only [colModel, transportF, er.symm_apply_apply, er.injective.eq_iff, eh.injective.eq_iff]

def pullLit (er : Row ≃ Row) (eh : Hole ≃ Hole) (l : Literal V) : Literal V :=
  ((er.symm l.1.1, eh.symm l.1.2), l.2)

theorem literalSat_transport_bHole (er : Row ≃ Row) (eh : Hole ≃ Hole)
    (c : Fin 3) (p : Fin 6) (l : Literal V) :
    LiteralSat (colModel (er (fin3ToRow c)) (er 3) (eh 0) (transportF er eh (bHole c p))) l ↔
      evalLitHole (bHole c p) (pullLit er eh l) = true := by
  rcases l with ⟨⟨r, q⟩, pol⟩
  have hr : r = er (er.symm r) := (er.apply_symm_apply r).symm
  have hq : q = eh (eh.symm q) := (eh.apply_symm_apply q).symm
  conv_lhs => rw [hr, hq]
  simp only [LiteralSat, transport_colModel, bHole_colModel_eq, evalLitHole, pullLit]
  cases pol <;> by_cases h : bHole c p (er.symm r) = eh.symm q <;> simp [h]

theorem literalSat_transport_oneMust (er : Row ≃ Row) (eh : Hole ≃ Hole)
    (m ic : Fin 3) (l : Literal V) :
    LiteralSat (colModel (er (fin3ToRow ic)) (er 4) (eh m.succ) (transportF er eh (oneMustHole m ic))) l ↔
      evalLitHole (oneMustHole m ic) (pullLit er eh l) = true := by
  rcases l with ⟨⟨r, q⟩, pol⟩
  have hr : r = er (er.symm r) := (er.apply_symm_apply r).symm
  have hq : q = eh (eh.symm q) := (eh.apply_symm_apply q).symm
  conv_lhs => rw [hr, hq]
  simp only [LiteralSat, transport_colModel, oneMustHole_colModel_eq, evalLitHole, pullLit]
  cases pol <;> by_cases h : oneMustHole m ic (er.symm r) = eh.symm q <;> simp [h]

theorem exists_row_equiv (k₀ b : Row) (hbk : b ≠ k₀) :
    ∃ er : Row ≃ Row, er 4 = k₀ ∧ er 3 = b := by
  let A : Finset Row := ((Finset.univ : Finset Row).erase k₀).erase b
  have hbm : b ∈ (Finset.univ : Finset Row).erase k₀ :=
    Finset.mem_erase.mpr ⟨hbk, Finset.mem_univ _⟩
  have hAcard : A.card = 3 := by
    dsimp only [A]
    rw [Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem (Finset.mem_univ k₀)]
    decide +kernel
  let e3 : Fin 3 ≃ ↥A :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hAcard])
  let f : Row → Row := fun r =>
    if h0 : r.val < 3 then (e3 ⟨r.val, h0⟩).1
    else if r = 3 then b else k₀
  have hinj : Function.Injective f := by
    intro r₁ r₂ heq
    have hmem : ∀ i : Fin 3, (e3 i).1 ≠ b ∧ (e3 i).1 ≠ k₀ := fun i =>
      ⟨(Finset.mem_erase.mp (e3 i).2).1, (Finset.mem_erase.mp (Finset.mem_erase.mp (e3 i).2).2).1⟩
    by_cases h1 : r₁.val < 3 <;> by_cases h2 : r₂.val < 3
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      have hv : r₁.val = r₂.val := congrArg (fun x : Fin 3 => x.val) (e3.injective (Subtype.ext heq))
      exact Fin.ext hv
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      split_ifs at heq
      · exact ((hmem _).1 heq).elim
      · exact ((hmem _).2 heq).elim
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      split_ifs at heq
      · exact ((hmem _).1 heq.symm).elim
      · exact ((hmem _).2 heq.symm).elim
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      have hr1 : r₁ = 3 ∨ r₁ = 4 := by fin_cases r₁ <;> simp_all
      have hr2 : r₂ = 3 ∨ r₂ = 4 := by fin_cases r₂ <;> simp_all
      rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
      · rfl
      · simp at heq; exact (hbk heq).elim
      · simp at heq; exact (hbk heq.symm).elim
      · rfl
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_, ?_⟩
  · simp [f]
  · simp [f]

theorem exists_hole_equiv_sorted (score : Hole → ℕ)
    (hinj : ∀ j₁ j₂ : Hole, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ → score j₁ ≠ score j₂) :
    ∃ eh : Hole ≃ Hole, eh 0 = 0 ∧
      score (eh 3) < score (eh 2) ∧ score (eh 2) < score (eh 1) := by
  have h12 : score 1 ≠ score 2 := hinj 1 2 (by decide) (by decide) (by decide)
  have h13 : score 1 ≠ score 3 := hinj 1 3 (by decide) (by decide) (by decide)
  have h23 : score 2 ≠ score 3 := hinj 2 3 (by decide) (by decide) (by decide)
  have mkEquiv : ∀ (a b c : Hole), a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
      ∃ eh : Hole ≃ Hole, eh 0 = 0 ∧ eh 1 = a ∧ eh 2 = b ∧ eh 3 = c := by
    intro a b c ha0 hb0 hc0 hab hac hbc
    let f : Hole → Hole := fun q =>
      match q.val with | 0 => 0 | 1 => a | 2 => b | _ => c
    have hfi : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢
      all_goals first | exact ha0 hxy.symm | exact hb0 hxy.symm | exact hc0 hxy.symm |
        exact ha0 hxy | exact hb0 hxy | exact hc0 hxy | exact hab hxy | exact hab hxy.symm |
        exact hac hxy | exact hac hxy.symm | exact hbc hxy | exact hbc hxy.symm
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi), rfl, rfl, rfl, rfl⟩
  rcases lt_or_gt_of_ne h12 with h12' | h21' <;>
    rcases lt_or_gt_of_ne h13 with h13' | h31' <;>
    rcases lt_or_gt_of_ne h23 with h23' | h32'
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 3 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h12', by rw [h2, h1]; exact h23'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h13', by rw [h2, h1]; exact h32'⟩
  · omega
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h31', by rw [h2, h1]; exact h12'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h21', by rw [h2, h1]; exact h13'⟩
  · omega
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h23', by rw [h2, h1]; exact h31'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h32', by rw [h2, h1]; exact h21'⟩

theorem caseA_impossible {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (k₀ : Row)
    (hZ : ∀ j : Hole, Z2 tr j = {k₀})
    (hcost : ∀ j : Hole, holeCost tr j = 16) : False := by
  classical

  obtain ⟨b, hbk, hb2, hbEdges⟩ := (holeCost_of_Z2_singleton h he (hZ 0)).2 (hcost 0)
  obtain ⟨er, her4, her3⟩ := exists_row_equiv k₀ b hbk

  have hzk : ∀ j : Hole, k₀ ∈ Z2 tr j := fun j => (hZ j) ▸ Finset.mem_singleton_self k₀
  choose p Rk hpstep hpuniq using fun j : Hole => z2_unique_non (hzk j)
  have hpinj : ∀ j₁ j₂ : Hole, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ → (p j₁).1 ≠ (p j₂).1 := by
    intro j₁ j₂ _ _ hjne heq
    have hidx : p j₁ = p j₂ := Fin.ext heq
    have hs := (hpstep j₁).symm.trans (hidx ▸ hpstep j₂)
    cases hs
    exact hjne rfl
  obtain ⟨eh, heh0, hord32, hord21⟩ := exists_hole_equiv_sorted (fun j => (p j).1) hpinj

  obtain ⟨i₁, i₂, hi₂₁, hi₁p, hi₂p, hiuniq⟩ := countP_eq_two_unique_idx tr (isNonOf (b, 0)) hb2
  have hextract : ∀ (i : Fin tr.length), isNonOf (b, 0) tr[i] = true → ∃ R, tr[i] = Step.non (b, 0) R := by
    intro i hi
    cases hs : tr[i] with
    | ax _ => simp [hs, isNonOf] at hi
    | col _ _ _ _ => simp [hs, isNonOf] at hi
    | non v R =>
      simp only [hs, isNonOf, decide_eq_true_eq] at hi
      subst hi
      exact ⟨R, rfl⟩
  obtain ⟨R₁, hR₁step⟩ := hextract i₁ hi₁p
  obtain ⟨R₂, hR₂step⟩ := hextract i₂ hi₂p

  let aB : Fin 18 → (V → Bool) := fun idx =>
    colModel (er (fin3ToRow (idxC idx))) b 0 (transportF er eh (bHole (idxC idx) (idxP idx)))
  have haB_valid : ∀ idx : Fin 18,
      ValidMatch (er (fin3ToRow (idxC idx))) b 0 (transportF er eh (bHole (idxC idx) (idxP idx))) := by
    intro idx
    rw [← her3, ← heh0]
    exact transport_validMatch er eh (bHole_valid (idxC idx) (idxP idx))
  have haB_edge : ∀ idx : Fin 18, colAx (er (fin3ToRow (idxC idx))) b 0 ∈ inEdges tr 0 b := by
    intro idx
    apply hbEdges
    · rw [← her4]; exact fun heq => by
        have := er.injective heq
        have : (idxC idx).val = 4 := congrArg Fin.val this
        omega
    · rw [← her3]; exact fun heq => by
        have := er.injective heq
        have : (idxC idx).val = 3 := congrArg Fin.val this
        omega

  have hp1_lt_i₁ : (p (eh 1)).1 < i₁.1 := by
    by_contra hge
    have hne : p (eh 1) ≠ i₁ := by
      intro heq
      have hs := (hpstep (eh 1)).symm.trans (heq ▸ hR₁step)
      have hv : (k₀, eh 1) = (b, 0) := by injection hs
      exact hbk (congrArg Prod.fst hv).symm
    have hlt : i₁.1 < (p (eh 1)).1 := by
      have := Fin.val_ne_of_ne hne
      omega
    have hslot : bHole (idxC 3) (idxP 3) 4 = 1 := by decide +kernel
    have hshape := z2_clause_shape h he (hzk (eh 1)) (hpstep (eh 1)) (hpuniq (eh 1))
    have hRkmem : Rk (eh 1) ∈ (tr.drop (p (eh 1)).1).map clauseOf := by
      refine List.mem_map.mpr ⟨Step.non (k₀, eh 1) (Rk (eh 1)), ?_, rfl⟩
      exact (mem_drop_iff tr (p (eh 1)).1 _).mpr ⟨p (eh 1), le_rfl, hpstep (eh 1)⟩
    have hsat := masterControl (h.drop (p (eh 1)).1) (aB 3) (colAx (er (fin3ToRow (idxC 3))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid 3)) (colModel_sat_cols (haB_valid 3))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge 3)).2 v u R' (mem_of_mem_drop hm)))
      (fun v R' hm hv _ => by
        rw [Finset.mem_singleton] at hv; subst hv
        obtain ⟨m, hmle, hget⟩ := (mem_drop_iff tr (p (eh 1)).1 _).mp hm
        rcases hiuniq m (by rw [hget]; simp [isNonOf]) with rfl | rfl <;> omega)
      (Rk (eh 1)) hRkmem (z2_not_coll hshape.1) (fun w _ => hshape.1 w)
    have hfk : transportF er eh (bHole (idxC 3) (idxP 3)) k₀ = eh 1 := by
      simp [transportF, ← her4, hslot]
    have hne01 : (0 : Hole) ≠ eh 1 := by
      rw [← heh0]; exact fun heq => by have := eh.injective heq; cases this
    have hicne : er (fin3ToRow (idxC 3)) ≠ k₀ := by
      rw [← her4]; exact fun heq => by have : (idxC 3).val = 4 := congrArg Fin.val (er.injective heq); omega
    exact z2_unsat_colModel hshape (haB_valid 3) hne01 hicne hbk hfk hsat

  have hex_ic : ∀ m : Fin 3, ∃ ic : Fin 3,
      colAx (er (fin3ToRow ic)) k₀ (eh m.succ) ∈ inEdges tr (eh m.succ) k₀ := by
    intro m
    have h2card : 2 ≤ (inEdges tr (eh m.succ) k₀).card := (Finset.mem_filter.mp (hzk (eh m.succ))).2
    obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr (eh m.succ) k₀).card)
    obtain ⟨x₁, hx₁k, rfl⟩ := inEdges_mem_colAx h hB₁
    obtain ⟨x₂, hx₂k, rfl⟩ := inEdges_mem_colAx h hB₂
    have hx₁₂ : x₁ ≠ x₂ := fun heq => hBne (heq ▸ rfl)
    have hpick : ∃ x : Row, x ≠ k₀ ∧ x ≠ b ∧ colAx x k₀ (eh m.succ) ∈ inEdges tr (eh m.succ) k₀ := by
      by_cases hb1 : x₁ = b
      · exact ⟨x₂, hx₂k, hb1 ▸ hx₁₂.symm, hB₂⟩
      · exact ⟨x₁, hx₁k, hb1, hB₁⟩
    obtain ⟨x, hxk, hxb, hxE⟩ := hpick
    let y : Row := er.symm x
    have hyx : er y = x := er.apply_symm_apply x
    have hy4 : y ≠ 4 := fun h => hxk (by rw [← hyx, h, her4])
    have hy3 : y ≠ 3 := fun h => hxb (by rw [← hyx, h, her3])
    have hylt : y.val < 3 := by
      have hy5 := y.2
      have h3 : y.val ≠ 3 := fun h => hy3 (Fin.ext h)
      have h4 : y.val ≠ 4 := fun h => hy4 (Fin.ext h)
      omega
    refine ⟨⟨y.val, hylt⟩, ?_⟩
    have hy_eq : er (fin3ToRow ⟨y.val, hylt⟩) = x := by
      have : fin3ToRow ⟨y.val, hylt⟩ = y := Fin.ext rfl
      rw [this, hyx]
    rwa [hy_eq]
  choose ic hicE using hex_ic

  have hi₂_ne_p : ∀ m : Fin 3, i₂.1 ≠ (p (eh m.succ)).1 := by
    intro m heq
    have hidx : i₂ = p (eh m.succ) := Fin.ext heq
    have hs := hR₂step.symm.trans (hidx ▸ hpstep (eh m.succ))
    have hv : (b, 0) = (k₀, eh m.succ) := by injection hs
    exact hbk (congrArg Prod.fst hv)
  let pos : Fin 4 :=
    if (p (eh 1)).1 < i₂.1 then 0
    else if (p (eh 2)).1 < i₂.1 then 1
    else if (p (eh 3)).1 < i₂.1 then 2
    else 3
  have hpos_lt : ∀ m : Fin 3, m.val < pos.val → i₂.1 < (p (eh m.succ)).1 := by
    intro m hm
    have h1 := hi₂_ne_p 0
    have h2 := hi₂_ne_p 1
    have h3 := hi₂_ne_p 2
    dsimp only [pos] at hm
    split_ifs at hm with c1 c2 c3
    · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exfalso; simp at hm
      · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c2) h2
      · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c2) h2
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c3) h3
  have hpos_ge : ∀ m : Fin 3, pos.val ≤ m.val → (p (eh m.succ)).1 < i₂.1 := by
    intro m hm
    dsimp only [pos] at hm
    split_ifs at hm with c1 c2 c3
    · fin_cases m
      · exact c1
      · exact lt_trans hord21 c1
      · exact lt_trans hord32 (lt_trans hord21 c1)
    · fin_cases m
      · exfalso; simp at hm
      · exact c2
      · exact lt_trans hord32 c2
    · fin_cases m
      · exfalso; simp at hm
      · exfalso; simp at hm
      · exact c3
    · exfalso; fin_cases m <;> simp at hm

  let okR : C → Prop := fun R => ((b, 0), false) ∉ R ∧ ¬ Coll R
  let p1 : Fin 18 → Bool := fun idx => decide (okR R₁ ∧ ¬ ClauseSat (aB idx) R₁)
  let p2 : Fin 18 → Bool := fun idx => decide (okR R₂ ∧ ¬ ClauseSat (aB idx) R₂)
  let m1 : Nat := (List.finRange 18).foldl (fun acc idx => if p1 idx then acc ||| (1 <<< idx.val) else acc) 0
  let m2 : Nat := (List.finRange 18).foldl (fun acc idx => if p2 idx then acc ||| (1 <<< idx.val) else acc) 0
  have hm1_bit : ∀ idx : Fin 18, m1.testBit idx.val = p1 idx := foldl_lor_testBit p1
  have hm2_bit : ∀ idx : Fin 18, m2.testBit idx.val = p2 idx := foldl_lor_testBit p2

  have auto_not_coll : ∀ (R : C) (idx : Fin 18), ((b, 0), false) ∉ R → ¬ ClauseSat (aB idx) R → ¬ Coll R := by
    intro R idx hnotf hns hcol
    apply hns
    apply colModel_sat_cols (haB_valid idx) R hcol
    intro heq
    exact hnotf (heq ▸ by simp [colAx])

  have hcov : subMask 262143 (m1 ||| m2) = true := by
    rw [subMask_iff_testBit]
    intro i hi
    rw [all18_testBit, decide_eq_true_eq] at hi
    let idx : Fin 18 := ⟨i, hi⟩
    rw [Nat.testBit_or, Bool.or_eq_true, hm1_bit idx, hm2_bit idx]
    by_contra hneither
    push Not at hneither
    have hsat := masterControl h (aB idx) (colAx (er (fin3ToRow (idxC idx))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid idx)) (colModel_sat_cols (haB_valid idx))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge idx)).2 v u R' hm))
      (fun v R' hm hv hnotf => by
        rw [Finset.mem_singleton] at hv; subst hv
        have hnf : ((b, 0), false) ∉ R' := hnotf (b, 0) (Finset.mem_singleton_self _)
        obtain ⟨j', hj'lt, hj'⟩ := List.getElem_of_mem hm
        rcases hiuniq ⟨j', hj'lt⟩ (by simp [hj', isNonOf]) with heq | heq
        · have hj'step : tr[i₁] = Step.non (b, 0) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
          rw [hR₁step] at hj'step; cases hj'step
          by_contra hns
          have htrue : p1 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₁ idx hnf hns⟩, hns⟩
          exact hneither.1 htrue
        · have hj'step : tr[i₂] = Step.non (b, 0) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
          rw [hR₂step] at hj'step; cases hj'step
          by_contra hns
          have htrue : p2 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₂ idx hnf hns⟩, hns⟩
          exact hneither.2 htrue)
      ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
    exact emptyUnsat _ hsat

  have foldl_lt18 : ∀ (q : Fin 18 → Bool) (k : Nat),
      ((List.finRange 18).foldl (fun acc idx => if q idx then acc ||| (1 <<< idx.val) else acc) 0).testBit k = true →
      k < 18 := by
    intro q k hk
    by_contra hge
    have hgen : ∀ (l : List (Fin 18)) (acc : Nat),
        (∀ j, acc.testBit j = true → j < 18) →
        (l.foldl (fun a idx => if q idx then a ||| (1 <<< idx.val) else a) acc).testBit k = false := by
      intro l
      induction l with
      | nil =>
        intro acc hacc
        simp only [List.foldl_nil]
        cases htk : acc.testBit k
        · rfl
        · exact (hge (hacc k htk)).elim
      | cons a tl ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        intro j hj
        split_ifs at hj
        · rw [Nat.testBit_or, Bool.or_eq_true] at hj
          rcases hj with hj1 | hj2
          · exact hacc j hj1
          · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
              Nat.testBit_one_eq_true_iff_self_eq_zero] at hj2
            omega
        · exact hacc j hj
    rw [hgen (List.finRange 18) 0 (by simp)] at hk
    cases hk

  have hreq : subMask (req1Mask pos.val) m1 = true := by
    rw [subMask_iff_testBit]
    intro i hi
    have hilt : i < 18 := foldl_lt18 (fun idx => decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos.val)) i hi
    let idx : Fin 18 := ⟨i, hilt⟩
    rw [req1Mask_testBit pos.val idx, decide_eq_true_eq] at hi
    rw [hm1_bit idx]
    have h4pos : 0 < (bHole (idxC idx) (idxP idx) 4).val := by
      have : ∀ (c : Fin 3) (p : Fin 6), 0 < (bHole c p 4).val := by decide +kernel
      exact this (idxC idx) (idxP idx)
    let m : Fin 3 := ⟨(bHole (idxC idx) (idxP idx) 4).val - 1, by omega⟩
    have hm_succ : m.succ = bHole (idxC idx) (idxP idx) 4 := Fin.ext (by dsimp [m]; omega)
    have hmlt : m.val < pos.val := hi
    have hi₂_lt_pm : i₂.1 < (p (eh m.succ)).1 := hpos_lt m hmlt
    have hshape := z2_clause_shape h he (hzk (eh m.succ)) (hpstep (eh m.succ)) (hpuniq (eh m.succ))
    have hRkmem : Rk (eh m.succ) ∈ (tr.drop (p (eh m.succ)).1).map clauseOf := by
      refine List.mem_map.mpr ⟨Step.non (k₀, eh m.succ) (Rk (eh m.succ)), ?_, rfl⟩
      exact (mem_drop_iff tr (p (eh m.succ)).1 _).mpr ⟨p (eh m.succ), le_rfl, hpstep (eh m.succ)⟩
    by_contra hp1f
    have hsat := masterControl (h.drop (p (eh m.succ)).1) (aB idx)
      (colAx (er (fin3ToRow (idxC idx))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid idx)) (colModel_sat_cols (haB_valid idx))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge idx)).2 v u R' (mem_of_mem_drop hm)))
      (fun v R' hm hv hnotf => by
        rw [Finset.mem_singleton] at hv; subst hv
        have hnf : ((b, 0), false) ∉ R' := hnotf (b, 0) (Finset.mem_singleton_self _)
        obtain ⟨j', hj'le, hj'⟩ := (mem_drop_iff tr (p (eh m.succ)).1 _).mp hm
        rcases hiuniq j' (by rw [hj']; simp [isNonOf]) with rfl | rfl
        · rw [hR₁step] at hj'; cases hj'
          by_contra hns
          have htrue : p1 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₁ idx hnf hns⟩, hns⟩
          exact hp1f htrue
        · omega)
      (Rk (eh m.succ)) hRkmem (z2_not_coll hshape.1) (fun w _ => hshape.1 w)
    have hfk : transportF er eh (bHole (idxC idx) (idxP idx)) k₀ = eh m.succ := by
      simp [transportF, ← her4, hm_succ]
    have hne0m : (0 : Hole) ≠ eh m.succ := by
      rw [← heh0]; exact fun heq => by have := eh.injective heq; exact Fin.succ_ne_zero m this.symm
    have hicne : er (fin3ToRow (idxC idx)) ≠ k₀ := by
      rw [← her4]; exact fun heq => by have : (idxC idx).val = 4 := congrArg Fin.val (er.injective heq); omega
    exact z2_unsat_colModel hshape (haB_valid idx) hne0m hicne hbk hfk hsat

  have cor3_witness : ∀ (i : Fin tr.length) (R : C) (m : Fin 3) (mask : Nat),
      clauseOf tr[i] = R →
      (p (eh m.succ)).1 < i.1 →
      (∀ idx : Fin 18, mask.testBit idx.val = true → okR R ∧ ¬ ClauseSat (aB idx) R) →
      (∀ k, mask.testBit k = true → k < 18) →
      ∃ x ∈ witsList m (ic m), subMask mask x = true := by
    intro i R m mask hcl hlt hmask hmask18
    by_cases hok : okR R
    · let aM := colModel (er (fin3ToRow (ic m))) k₀ (eh m.succ)
        (transportF er eh (oneMustHole m (ic m)))
      have haM_valid : ValidMatch (er (fin3ToRow (ic m))) k₀ (eh m.succ)
          (transportF er eh (oneMustHole m (ic m))) := by
        rw [← her4]
        exact transport_validMatch er eh (oneMustHole_valid m (ic m))
      have hRmem : R ∈ (tr.drop i.1).map clauseOf := by
        refine List.mem_map.mpr ⟨tr[i], ?_, hcl⟩
        exact (mem_drop_iff tr i.1 _).mpr ⟨i, le_rfl, rfl⟩
      have hex_lit : ∃ l ∈ R, isWitnessLit m (ic m) (pullLit er eh l) = true := by
        by_cases hneg : ((k₀, eh m.succ), false) ∈ R
        · refine ⟨((k₀, eh m.succ), false), hneg, ?_⟩
          simp [isWitnessLit, pullLit, ← her4]
        · have hsat := masterControl (h.drop i.1) aM
            (colAx (er (fin3ToRow (ic m))) k₀ (eh m.succ)) {(k₀, eh m.succ)}
            (colModel_sat_rows haM_valid) (colModel_sat_cols haM_valid)
            (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (hicE m)).2 v u R' (mem_of_mem_drop hm)))
            (fun v R' hm hv _ => by
              rw [Finset.mem_singleton] at hv; subst hv
              obtain ⟨j', hj'le, hj'⟩ := (mem_drop_iff tr i.1 _).mp hm
              have heq := hpuniq (eh m.succ) j' (by rw [hj']; simp [isNonOf])
              omega)
            R hRmem hok.2 (fun w hw => by rw [Finset.mem_singleton] at hw; subst hw; exact hneg)
          obtain ⟨l, hlR, hlsat⟩ := hsat
          have heval : evalLitHole (oneMustHole m (ic m)) (pullLit er eh l) = true := by
            have h' : LiteralSat (colModel (er (fin3ToRow (ic m))) (er 4) (eh m.succ)
                (transportF er eh (oneMustHole m (ic m)))) l := by
              simpa [aM, her4] using hlsat
            exact (literalSat_transport_oneMust er eh m (ic m) l).mp h'
          exact ⟨l, hlR, by simp [isWitnessLit, heval]⟩
      obtain ⟨l, hlR, hlwit⟩ := hex_lit
      have hlne : pullLit er eh l ≠ ((3, 0), false) := by
        intro heq
        have h1 : l = ((b, 0), false) := by
          rcases l with ⟨⟨r, q⟩, pol⟩
          simp only [pullLit, Prod.mk.injEq] at heq
          obtain ⟨⟨hr, hq⟩, rfl⟩ := heq
          have hr' : r = b := by rw [← er.apply_symm_apply r, hr, her3]
          have hq' : q = 0 := by rw [← eh.apply_symm_apply q, hq, heh0]
          rw [hr', hq']
        exact hok.1 (h1 ▸ hlR)
      refine ⟨fmaskList (pullLit er eh l),
        List.mem_map.mpr ⟨pullLit er eh l, List.mem_filter.mpr ⟨mem_allLits39 hlne, hlwit⟩, rfl⟩, ?_⟩
      rw [subMask_iff_testBit]
      intro k hk
      have hk18 := hmask18 k hk
      let idx : Fin 18 := ⟨k, hk18⟩
      rw [fmaskList_testBit (pullLit er eh l) idx]
      have hns := (hmask idx hk).2
      have hnl : ¬ LiteralSat (aB idx) l := fun hs => hns ⟨l, hlR, hs⟩
      have hneval : evalLitHole (bHole (idxC idx) (idxP idx)) (pullLit er eh l) ≠ true := by
        intro hev
        apply hnl
        have h' := (literalSat_transport_bHole er eh (idxC idx) (idxP idx) l).mpr hev
        simpa [aB, her3, heh0] using h'
      cases hev : evalLitHole (bHole (idxC idx) (idxP idx)) (pullLit er eh l)
      · rfl
      · exact (hneval hev).elim
    ·
      have h0 : ∀ k, mask.testBit k = false := by
        intro k
        cases hk : mask.testBit k
        · rfl
        · exfalso
          exact hok (hmask ⟨k, hmask18 k hk⟩ hk).1
      let l₀ : Literal V := ((4, m.succ), false)
      have hl₀ne : l₀ ≠ ((3, 0), false) := by intro h; dsimp only [l₀] at h; cases h
      have hl₀wit : isWitnessLit m (ic m) l₀ = true := by simp [isWitnessLit, l₀]
      refine ⟨fmaskList l₀,
        List.mem_map.mpr ⟨l₀, List.mem_filter.mpr ⟨mem_allLits39 hl₀ne, hl₀wit⟩, rfl⟩, ?_⟩
      rw [subMask_iff_testBit]
      intro k hk
      rw [h0 k] at hk; cases hk

  have hm1_prop : ∀ idx : Fin 18, m1.testBit idx.val = true → okR R₁ ∧ ¬ ClauseSat (aB idx) R₁ := by
    intro idx hbit
    rw [hm1_bit idx] at hbit
    exact of_decide_eq_true hbit
  have hm2_prop : ∀ idx : Fin 18, m2.testBit idx.val = true → okR R₂ ∧ ¬ ClauseSat (aB idx) R₂ := by
    intro idx hbit
    rw [hm2_bit idx] at hbit
    exact of_decide_eq_true hbit
  have hcl1 : clauseOf tr[i₁] = R₁ := by rw [hR₁step]; rfl
  have hcl2 : clauseOf tr[i₂] = R₂ := by rw [hR₂step]; rfl
  exact killer_masks_impossible (ic 0) (ic 1) (ic 2) pos m1 m2
    (cor3_witness i₁ R₁ 0 m1 hcl1 hp1_lt_i₁ hm1_prop (foldl_lt18 p1))
    (cor3_witness i₁ R₁ 1 m1 hcl1 (lt_trans hord21 hp1_lt_i₁) hm1_prop (foldl_lt18 p1))
    (cor3_witness i₁ R₁ 2 m1 hcl1 (lt_trans hord32 (lt_trans hord21 hp1_lt_i₁)) hm1_prop (foldl_lt18 p1))
    hreq
    (fun h0 => cor3_witness i₂ R₂ 0 m2 hcl2 (hpos_ge 0 (by omega)) hm2_prop (foldl_lt18 p2))
    (fun h1 => cor3_witness i₂ R₂ 1 m2 hcl2 (hpos_ge 1 (by omega)) hm2_prop (foldl_lt18 p2))
    (fun h2 => cor3_witness i₂ R₂ 2 m2 hcl2 (hpos_ge 2 (by omega)) hm2_prop (foldl_lt18 p2))
    hcov

theorem refutationLower {π : List C} (hπ : IsRefutation (PHP 5 4) π) :
    110 ≤ π.length := by
  classical
  obtain ⟨tr, hmap, htr⟩ := of_isDerivation hπ.1
  have hlen : tr.length = π.length := by rw [← hmap, List.length_map]
  have he : (∅ : C) ∈ tr.map clauseOf := hmap ▸ hπ.2
  have hax := ax_lower htr he
  have hdec := length_decomp tr
  rw [← hlen, hdec]
  by_cases hex : ∃ j : Hole, ∃ k : Row, k ∈ Z2 tr j
  · obtain ⟨j₀, k₀, hk₀⟩ := hex
    by_cases htwo : ∃ k₁ : Row, k₁ ∈ Z2 tr j₀ ∧ k₁ ≠ k₀
    ·
      obtain ⟨k₁, hk₁, hne10⟩ := htwo
      have hother : ∀ j : Hole, j ≠ j₀ → 17 ≤ holeCost tr j := by
        intro j hne
        apply holeCost_ge_17_of_Z2_empty htr he
        ext k
        simp only [Finset.notMem_empty, iff_false]
        intro hk
        have e0 := z2_line htr he hk hk₀
        have e1 := z2_line htr he hk hk₁
        rcases e0 with rfl | h0
        · rcases e1 with h1 | h1
          · exact hne10 h1.symm
          · exact hne h1
        · exact hne h0
      have hsum : 65 ≤ ∑ j : Hole, holeCost tr j := by
        have hsplit := Finset.add_sum_erase Finset.univ (holeCost tr) (Finset.mem_univ j₀)
        have h14 := holeCost_ge_14 htr he j₀
        have hrest : 51 ≤ ∑ j ∈ Finset.univ.erase j₀, holeCost tr j := by
          calc 51 = ∑ _j ∈ (Finset.univ : Finset Hole).erase j₀, 17 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₀)]
                have h4 : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
                rw [h4]; decide +kernel
            _ ≤ ∑ j ∈ Finset.univ.erase j₀, holeCost tr j :=
                Finset.sum_le_sum (fun j hj => hother j (Finset.mem_erase.mp hj).1)
        omega
      omega
    ·
      push Not at htwo
      have hsub : ∀ j : Hole, Z2 tr j = ∅ ∨ Z2 tr j = {k₀} := by
        intro j
        by_cases hemp : Z2 tr j = ∅
        · exact Or.inl hemp
        · right
          obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          have hkeq : k = k₀ := by
            by_cases hjj : j = j₀
            · subst hjj; exact htwo k hk
            · rcases z2_line htr he hk hk₀ with h1 | h2
              · exact h1
              · exact (hjj h2).elim
          ext x
          simp only [Finset.mem_singleton]
          constructor
          · intro hx
            by_cases hjj : j = j₀
            · subst hjj; exact htwo x hx
            · rcases z2_line htr he hx hk₀ with h1 | h2
              · exact h1
              · exact (hjj h2).elim
          · rintro rfl; exact hkeq ▸ hk
      have hall16 : ∀ j : Hole, 16 ≤ holeCost tr j := by
        intro j
        rcases hsub j with h0 | h1
        · have := holeCost_ge_17_of_Z2_empty htr he h0; omega
        · exact (holeCost_of_Z2_singleton htr he h1).1
      by_cases hex17 : ∃ j₁ : Hole, 17 ≤ holeCost tr j₁
      · obtain ⟨j₁, hj₁⟩ := hex17
        have hsum : 65 ≤ ∑ j : Hole, holeCost tr j := by
          have hsplit := Finset.add_sum_erase Finset.univ (holeCost tr) (Finset.mem_univ j₁)
          have hrest : 48 ≤ ∑ j ∈ Finset.univ.erase j₁, holeCost tr j := by
            calc 48 = ∑ _j ∈ (Finset.univ : Finset Hole).erase j₁, 16 := by
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₁)]
                  have h4 : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
                  rw [h4]; decide +kernel
              _ ≤ ∑ j ∈ Finset.univ.erase j₁, holeCost tr j :=
                  Finset.sum_le_sum (fun j _ => hall16 j)
          omega
        omega
      · push Not at hex17
        have hall_eq16 : ∀ j : Hole, holeCost tr j = 16 := fun j => by
          have h1 := hall16 j; have h2 := hex17 j; omega
        have hall_Z : ∀ j : Hole, Z2 tr j = {k₀} := by
          intro j
          rcases hsub j with h0 | h1
          · exfalso
            have := holeCost_ge_17_of_Z2_empty htr he h0
            have := hall_eq16 j
            omega
          · exact h1
        exact (caseA_impossible htr he k₀ hall_Z hall_eq16).elim
  ·
    push Not at hex
    have hsum : 68 ≤ ∑ j : Hole, holeCost tr j := by
      calc 68 = ∑ _j : Hole, 17 := by decide +kernel
        _ ≤ ∑ j : Hole, holeCost tr j := by
          apply Finset.sum_le_sum
          intro j _
          apply holeCost_ge_17_of_Z2_empty htr he
          ext k
          simp [hex j k]
    omega

end Pcx180Ord

theorem Pcx180Ord : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 109) := by
  rintro ⟨π, hπ, hlen⟩
  have := Pcx180Ord.refutationLower hπ
  omega



namespace PEqualNP.Outside.L_pcx_118.Bridge

open Relation Classical

abbrev Walk (E : ℕ → ℕ → Prop) := Relation.ReflTransGen E

theorem walk_le {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {i j : ℕ} (w : Walk E i j) : j ≤ i := by
  induction w with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (Nat.le_of_lt (dec e)).trans ih

theorem walk_sub {E E' : ℕ → ℕ → Prop} (sub : ∀ {i j}, E i j → E' i j)
    {i j : ℕ} (w : Walk E i j) : Walk E' i j := by
  induction w with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (sub e)

theorem clash {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ A m ∧ Walk E c m ∧ Walk E d m := by
  induction wc with
  | refl =>
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · exact False.elim (ne e)
    · have lt : q < r := (walk_le dec wq).trans_lt (dec rd)
      exact ⟨r, q, c, Or.inl rfl, Or.inr wq, rc, eq, (Ne.symm (ne_of_lt lt)),
        ac, .refl, wd⟩
  | @tail u v wu he ih =>
    have wcu : Walk E c u := walk_sub (fun h => h.1) wu
    have lu : u < r := (walk_le dec wcu).trans_lt (dec rc)
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · subst v
      exact ⟨u, r, d, Or.inr wcu, Or.inl rfl, he.1, rd, ne_of_lt lu, he.2,
        .tail wcu he.1, .refl⟩
    · by_cases hp : u = q
      · subst q
        exact ih wq
      · exact ⟨u, q, v, Or.inr wcu, Or.inr wq, he.1, eq, hp, he.2,
          .tail wcu he.1, wd⟩

theorem same_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) : A z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, am, _, _⟩ := clash dec rc rd ne ac wc wd
  exact unique p q m hp hq ep eq neq ▸ am

theorem swap_entry {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d z : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)
    {A : ℕ → Prop} (ad : A d) {x : ℕ}
    (wd : Walk (fun i j => E i j ∧ A j) d x) (wc : Walk E c x) : A z :=
  same_entry dec rd rc ne.symm
    (fun p q m hp hq ep eq hne => unique q p m hq hp eq ep hne.symm) ad wd wc

section semantic

variable {α κ : Type}
variable {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
variable {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
variable (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
variable (B : α → ℕ → Prop) (side : α → Bool)
variable (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
variable (branch : ∀ a, B a (if side a then c else d))
variable (route : ∀ a i, B a i →
  ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
variable (points : ∀ k, ∃ a, point k a)

def Common (E : ℕ → ℕ → Prop) (c d : ℕ) (u : ℕ) : Prop :=
  Walk E c u ∧ Walk E d u

def Forced (bad : α → κ → Prop) (point : κ → α → Prop) (side : α → Bool) (a : α) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ side b ≠ side a) ∨
  (∀ k, bad a k → ∀ b, point k b → side b ≠ side a)

include branch route one in
theorem criticalSide {a k} (ha : point k a) :
    Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  obtain ⟨j, hj, w⟩ := route a _ (branch a)
  have eq := (one ha j).1 hj
  simpa [eq] using w

include branch route one points in
theorem forced_common {a} (ha : Forced bad point side a) :
    ∃ k, bad a k ∧ Common E c d (leaf k) ∧
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  have mk : ∀ {k b}, bad a k →
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) →
      point k b → side b ≠ side a →
      ∃ k, bad a k ∧ Common E c d (leaf k) ∧
        Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
    intro k b bk wa pb hn
    have wb := criticalSide bad point leaf B side one branch route pb
    refine ⟨k, bk, ?_, wa⟩
    have ua := walk_sub (fun h => h.1) wa
    have ub := walk_sub (fun h => h.1) wb
    cases ea : side a <;> cases eb : side b <;> simp_all [Common]
  rcases ha with ⟨k, ka, b, kb, hn⟩ | ha
  · exact mk ((one ka k).2 rfl) (criticalSide bad point leaf B side one branch route ka) kb hn
  · obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    obtain ⟨b, kb⟩ := points k
    exact mk bk wa kb (ha k bk b kb)

include dec rc rd ne branch route one points in
theorem entry_exists {a} (ha : Forced bad point side a) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ B a m ∧ Common E c d m := by
  obtain ⟨k, _, ⟨wc, wd⟩, w⟩ := forced_common bad point leaf B side one branch route points ha
  cases h : side a
  · simp [h] at w
    obtain ⟨q, p, m, hq, hp, eq, ep, neq, b, rd', rc'⟩ :=
      clash dec rd rc ne.symm (by simpa [h] using branch a) w wc
    exact ⟨p, q, m, hp, hq, ep, eq, neq.symm, b, rc', rd'⟩
  · simp [h] at w
    exact clash dec rc rd ne (by simpa [h] using branch a) w wd

variable {z : ℕ}
variable (unique : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z)

include dec rc rd ne unique branch route one in
theorem false_on_common {k a}
    (hc : Common E c d (leaf k)) (ha : point k a) : B a z := by
  have w := criticalSide bad point leaf B side one branch route ha
  cases h : side a
  · simp [h] at w
    exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.1
  · simp [h] at w
    exact same_entry dec rc rd ne unique (by simpa [h] using branch a) w hc.2

include dec rc rd ne unique branch route one points in
theorem false_on_forced {a}
    (ha : Forced bad point side a) : B a z := by
  obtain ⟨p, q, m, hp, hq, ep, eq, neq, hm, _⟩ :=
    entry_exists dec rc rd ne bad point leaf B side one branch route points ha
  exact unique p q m hp hq ep eq neq ▸ hm

include dec rc rd ne unique branch route one points in
theorem one_entry_characterization (fz : Common E c d z) :
    (∀ a, Forced bad point side a → B a z) ∧
    (∀ a, B a z → ∃ k, bad a k ∧ ∀ b, point k b → B b z) ∧
    (∀ a, ¬ B a z → ∃ k, bad a k ∧ ∃ b, point k b ∧ ¬ B b z) := by
  refine ⟨fun a ha => false_on_forced dec rc rd ne bad point leaf B side one branch route points unique ha, ?_, ?_⟩
  · intro a ba
    obtain ⟨k, bk, w⟩ := route a z ba
    have w' := walk_sub (fun h => h.1) w
    have common : Common E c d (leaf k) := ⟨fz.1.trans w', fz.2.trans w'⟩
    exact ⟨k, bk, fun b hb => false_on_common dec rc rd ne bad point leaf B side one branch route unique common hb⟩
  · intro a ba
    obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    by_contra! hall
    have hpk := hall k bk
    -- If every critical point of the routed leaf lies below z, following any such
    -- point from z proves z reaches that leaf. Then both root sides can reach it.
    obtain ⟨b, hb⟩ := points k
    obtain ⟨j, bj, w⟩ := route b z (hpk b hb)
    rcases (one hb j).1 bj with rfl
    have w' := walk_sub (fun h => h.1) w
    have cl : Common E c d (leaf j) := ⟨fz.1.trans w', fz.2.trans w'⟩
    apply ba
    cases h : side a
    · simp [h] at wa
      exact swap_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.1
    · simp [h] at wa
      exact same_entry dec rc rd ne unique (by simpa [h] using branch a) wa cl.2

end semantic

end PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_118.Graph

abbrev ClauseMap (V : Type) := Nat → LinClause V
abbrev Parents := Nat → List Nat

def Rule {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (i : Nat) : Prop :=
    (P i = [] ∧ C i ∈ F) ∨
    (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
    (∃ j < i, ∃ k < i, P i = [j, k] ∧ IsLinResolvent (C j) (C k) (C i))

def Encoded {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (lines : List (LinClause V)) : Prop :=
  (∀ i < lines.length, Rule F C P i) ∧
  (∀ D, D ∈ lines ↔ ∃ i < lines.length, C i = D)

theorem rule_congr {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C D : ClauseMap V} {P Q : Parents} {i : Nat}
    (same : ∀ j ≤ i, D j = C j) (parents : Q i = P i)
    (h : Rule F C P i) : Rule F D Q i := by
  rw [Rule, parents, same i le_rfl]
  rcases h with h | ⟨j, ji, e, weak⟩ | ⟨j, ji, k, ki, e, res⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, ji, e, by simpa only [same _ ji.le] using weak⟩)
  · exact Or.inr (Or.inr ⟨j, ji, k, ki, e, by simpa only [same _ ji.le, same _ ki.le] using res⟩)

theorem extend {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents} (enc : Encoded F C P π)
    (D : LinClause V) (q : List Nat)
    (hr : Rule F (Function.update C π.length D) (Function.update P π.length q) π.length) :
    Encoded F (Function.update C π.length D) (Function.update P π.length q) (D :: π) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have ib : i ≤ π.length := Nat.lt_succ_iff.1 (by simpa only [List.length_cons] using hi)
    rcases eq_or_lt_of_le ib with rfl | lt
    · exact hr
    · refine rule_congr (fun j ji => Function.update_of_ne (ne_of_lt (ji.trans_lt lt)) _ _) ?_ (enc.1 i lt)
      exact Function.update_of_ne (ne_of_lt lt) _ _
  · intro A
    simp only [List.mem_cons, List.length_cons]
    constructor
    · intro h
      rcases h with rfl | h
      · exact ⟨π.length, Nat.lt_succ_self _, by simp⟩
      · obtain ⟨i, hi, eq⟩ := (enc.2 _).1 h
        exact ⟨i, by omega, by simpa [Function.update_of_ne (ne_of_lt hi)] using eq⟩
    · rintro ⟨i, hi, eq⟩
      have ib : i ≤ π.length := by omega
      rcases eq_or_lt_of_le ib with rfl | lt
      · exact Or.inl (by simpa using eq.symm)
      · exact Or.inr ((enc.2 _).2 ⟨i, lt, by simpa [Function.update_of_ne (ne_of_lt lt)] using eq⟩)

theorem build_graph {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) : ∃ C P, Encoded F C P π := by
  induction der with
  | nil => exact ⟨fun _ => ∅, fun _ => [], by simp [Encoded]⟩
  | @ax π D _ hD ih =>
    obtain ⟨C, P, enc⟩ := ih
    refine ⟨_, _, extend enc D [] ?_⟩
    exact Or.inl (by simpa using hD)
  | @res π D H R _ d h res ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, di⟩ := (enc.2 _).1 d
    obtain ⟨j, hj, ej⟩ := (enc.2 _).1 h
    refine ⟨_, _, extend enc R [i, j] (Or.inr (Or.inr ⟨i, hi, j, hj, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), Function.update_of_ne (ne_of_lt hj), di, ej] using res
  | @weak π D R _ hD hw ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, eq⟩ := (enc.2 _).1 hD
    refine ⟨_, _, extend enc R [i] (Or.inr (Or.inl ⟨i, hi, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), eq] using hw

def Edge (P : Parents) (i j : Nat) : Prop := j ∈ P i

theorem edge_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i j : Nat} (h : Rule F C P i)
    (e : Edge P i j) : j < i := by
  rcases h with ⟨r, _⟩ | ⟨k, ki, r, _⟩ | ⟨k, ki, m, mi, r, _⟩
  · simp [Edge, r] at e
  · have eq : j = k := by simpa [Edge, r] using e
    simpa [eq] using ki
  · simp only [Edge, r, List.mem_cons, List.mem_nil_iff, or_false] at e
    rcases e with rfl | rfl <;> assumption

def FalseAt {V : Type} (C : ClauseMap V) (a : V → Bool) (i : Nat) : Prop :=
  ¬ LinClauseSat a (C i)

theorem resolve_branch {V : Type} [DecidableEq V] {D H R : LinClause V}
    (a : V → Bool) {f : Finset V}
    (rr : R = D.erase (f, false) ∪ H.erase (f, true))
    (fr : ¬ LinClauseSat a R) :
    if Odd (f.filter (fun x => a x = true)).card
    then ¬ LinClauseSat a D else ¬ LinClauseSat a H := by
  subst R
  by_cases h : Odd (f.filter (fun x => a x = true)).card
  · rw [ite_eq_left h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat
  · rw [ite_eq_right h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat

theorem follow {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {n : Nat} (rule : ∀ i < n, Rule F C P i) (a : V → Bool)
    {i : Nat} (hi : i < n) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have visit : ∀ j < i, Edge P i j → FalseAt C a j →
        ∃ k, P k = [] ∧ C k ∈ F ∧ FalseAt C a k ∧
          Walk (fun u v => Edge P u v ∧ FalseAt C a v) i k := by
      intro j lt ej fj
      obtain ⟨k, p0, fm, fk, w⟩ := ih j lt (lt.trans hi) fj
      exact ⟨k, p0, fm, fk, Relation.ReflTransGen.head ⟨ej, fj⟩ w⟩
    rcases rule i hi with ⟨p0, hF⟩ | ⟨j, ji, pp, hw⟩ | ⟨j, ji, k, ki, pp, f, h1, h2, rr⟩
    · exact ⟨i, p0, hF, fi, .refl⟩
    · exact visit j ji (by simp [Edge, pp]) (fun h => fi (hw a h))
    · have br := resolve_branch a rr fi
      split at br
      · exact visit j ji (by simp [Edge, pp]) br
      · exact visit k ki (by simp [Edge, pp]) br

theorem first_false {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {π : List (LinClause V)}
    (graph : Encoded F C P π) (empty : ∅ ∈ π)
    (axsat : ∀ D ∈ F, ∃ a, LinClauseSat a D) :
    ∃ r < π.length, (∀ a, FalseAt C a r) ∧
      (∀ j < r, ∃ a, LinClauseSat a (C j)) ∧
      ∃ j < r, ∃ k < r, j ≠ k ∧ P r = [j, k] ∧ ∃ f : Finset V,
          f ≠ ∅ ∧ ∀ a, if Odd (f.filter (fun x => a x = true)).card
            then FalseAt C a j else FalseAt C a k := by
  classical
  have existsFalse : ∃ j, j < π.length ∧ ∀ a, FalseAt C a j := by
    obtain ⟨j, hj, he⟩ := (graph.2 _).1 empty
    exact ⟨j, hj, by simp [FalseAt, he, LinClauseSat]⟩
  let r := Nat.find existsFalse
  obtain ⟨ri, fr⟩ := Nat.find_spec existsFalse
  have prev : ∀ j < r, ∃ a, LinClauseSat a (C j) := by
    intro j hj
    by_contra! h
    exact Nat.find_min existsFalse hj ⟨hj.trans ri, h⟩
  refine ⟨r, ri, fr, prev, ?_⟩
  rcases graph.1 r ri with ⟨_, hF⟩ | ⟨j, jr, _, hw⟩ | ⟨j, jr, k, kr, p, f, df, dk, rr⟩
  · obtain ⟨a, ha⟩ := axsat _ hF
    exact (fr a ha).elim
  · obtain ⟨a, ha⟩ := prev j jr
    exact (fr a (hw a ha)).elim
  · have br : ∀ a, if Odd (f.filter (fun x => a x = true)).card
      then FalseAt C a j else FalseAt C a k := fun a => resolve_branch a rr (fr a)
    have ne : j ≠ k := by
      intro eq
      obtain ⟨a, sat⟩ := prev j jr
      have no := br a
      rw [eq] at no sat
      split at no <;> exact no sat
    have nz : f ≠ ∅ := by
      intro eq
      obtain ⟨a, sat⟩ := prev k kr
      exact (by simpa [eq] using br a : FalseAt C a k) sat
    exact ⟨j, jr, k, kr, ne, p, f, nz, br⟩

open scoped BigOperators

def LocalEdge (P : Parents) (r i j : Nat) : Prop := i ≤ r ∧ Edge P i j

noncomputable def Live (P : Parents) (r : Nat) : Finset Nat := by
  classical
  exact (Finset.range (r+1)).filter (fun v => Walk (LocalEdge P r) r v)

theorem bounded_edge {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {i j : Nat} (e : LocalEdge P r i j) : j < i := edge_desc (rules i e.1) e.2

theorem live_iff {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    i ∈ Live P r ↔ Walk (LocalEdge P r) r i := by
  classical
  simp only [Live, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun w => ⟨walk_le (bounded_edge rules) w, w⟩⟩

theorem live_closed {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hi : i ∈ Live P r) (e : Edge P i j) :
    j ∈ Live P r := by
  have w := (live_iff rules).1 hi
  exact (live_iff rules).2 (.tail w ⟨walk_le (bounded_edge rules) w, e⟩)

def InDegree (P : Parents) (s : Finset Nat) (j : Nat) : Nat :=
  ∑ i ∈ s, (P i).count j

theorem count_edges {P : Parents} {s : Finset Nat}
    (hs : ∀ i ∈ s, ∀ j ∈ P i, j ∈ s) :
    ∑ j ∈ s, InDegree P s j = ∑ i ∈ s, (P i).length := by
  unfold InDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j ∈ s, List.count j (P i)) = ∑ j ∈ (P i).toFinset, List.count j (P i) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact hs i hi j (List.mem_toFinset.1 hj)
      · intro j hj hnot
        exact List.count_eq_zero_of_not_mem (fun h => hnot (List.mem_toFinset.2 h))
    _ = (P i).length := by
      simpa only [List.toFinset_coe, Multiset.coe_count, Multiset.coe_card] using
        Multiset.toFinset_sum_count_eq ((P i : List Nat) : Multiset Nat)

theorem inDegree_root {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    InDegree P (Live P r) r = 0 := by
  unfold InDegree
  apply Finset.sum_eq_zero
  intro i hi
  have il := walk_le (bounded_edge rules) ((live_iff rules).1 hi)
  apply List.count_eq_zero_of_not_mem
  intro ei
  exact (Nat.not_lt_of_le il) (edge_desc (rules i il) ei)

theorem inDegree_pos {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (hj : j ∈ Live P r) (ne : j ≠ r) : 1 ≤ InDegree P (Live P r) j := by
  obtain ⟨i, wi, ei⟩ := ((live_iff rules).1 hj).cases_tail.resolve_left ne
  have im : i ∈ Live P r := (live_iff rules).2 wi
  have h := Finset.single_le_sum (f := fun u => (P u).count j) (fun _ _ => Nat.zero_le _) im
  exact (Nat.succ_le_of_lt (List.count_pos_iff.2 ei.2)).trans h

noncomputable def Surplus (P : Parents) (r : Nat) : Nat :=
  ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1)

theorem surplus_identity {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (∑ i ∈ Live P r, (P i).length) + 1 = (Live P r).card + Surplus P r := by
  have h1 := count_edges (fun i hi j hj => live_closed rules hi hj)
  have root : r ∈ Live P r := (live_iff rules).2 .refl
  have hsum := Finset.sum_erase_add (Live P r) (InDegree P (Live P r)) root
  rw [inDegree_root rules, Nat.add_zero, h1] at hsum
  have hc := Finset.card_erase_of_mem root
  have hp := Finset.card_pos.2 ⟨_, root⟩
  have eq : ∑ j ∈ (Live P r).erase r, InDegree P (Live P r) j =
      ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1 + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨ne, hm⟩ := Finset.mem_erase.1 hj
    have lb := inDegree_pos rules hm ne
    omega
  have hone : (∑ _ ∈ (Live P r).erase r, (1 : Nat)) = ((Live P r).erase r).card := by simp
  rw [Finset.sum_add_distrib, hone] at eq
  unfold Surplus
  omega

noncomputable def WithArity (P : Parents) (r n : Nat) : Finset Nat :=
  (Live P r).filter (fun j => (P j).length = n)

theorem length_le_two {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i : Nat} (h : Rule F C P i) :
    (P i).length ≤ 2 := by
  rcases h with ⟨r, _⟩ | ⟨j, _, r, _⟩ | ⟨j, _, k, _, r, _⟩ <;> simp [r]

theorem arity_sum (P : Parents) (r n k : Nat) :
    (∑ i ∈ Live P r, if (P i).length = n then k else 0) = k * (WithArity P r n).card := by
  rw [← Finset.sum_filter]
  simp [WithArity, Nat.mul_comm]
theorem arity_count {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (Live P r).card + 1 =
      2 * (WithArity P r 0).card + (WithArity P r 1).card + Surplus P r := by
  have hk : ∀ i ∈ Live P r, (P i).length ≤ 2 := by
    intro i hi
    exact length_le_two (rules i (walk_le (bounded_edge rules) ((live_iff rules).1 hi)))
  have decomp :
      (Live P r).card = (WithArity P r 0).card + (WithArity P r 1).card + (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (1 : Nat) = ∑ i ∈ Live P r,
        ((if (P i).length = 0 then 1 else 0) + (if (P i).length = 1 then 1 else 0) +
          (if (P i).length = 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    have countOnes : (∑ _ ∈ Live P r, (1 : Nat)) = (Live P r).card := by simp
    rw [countOnes] at h
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have edges :
      (∑ i ∈ Live P r, (P i).length) = (WithArity P r 1).card + 2 * (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (P i).length = ∑ i ∈ Live P r,
        ((if (P i).length = 1 then 1 else 0) + (if (P i).length = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have hs := surplus_identity rules
  omega

theorem shared_degree {P : Parents} {s : Finset Nat} {p q m : Nat}
    (hp : p ∈ s) (hq : q ∈ s) (ep : Edge P p m) (eq : Edge P q m) (ne : p ≠ q) :
    2 ≤ InDegree P s m := by
  have tm : ({p, q} : Finset Nat) ⊆ s := by
    intro i hi
    rcases (by simpa using hi : i = p ∨ i = q) with rfl | rfl <;> assumption
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (P u).count m) tm
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 ne), Finset.sum_singleton] at hs
  have lp := List.count_pos_iff.2 ep
  have lq := List.count_pos_iff.2 eq
  unfold InDegree
  omega

theorem only_one_share {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r m z : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (budget : Surplus P r ≤ 1)
    (hm : m ∈ Live P r) (hz : z ∈ Live P r)
    (sm : 2 ≤ InDegree P (Live P r) m) (sz : 2 ≤ InDegree P (Live P r) z) :
    m = z := by
  by_contra hne
  have nr := inDegree_root rules
  have mn : m ≠ r := by
    rintro rfl
    omega
  have zn : z ≠ r := by
    rintro rfl
    omega
  have both : ({m,z} : Finset Nat) ⊆ (Live P r).erase r := by
    intro j hj
    rcases (by simpa using hj : j = m ∨ j = z) with rfl | rfl
    · exact Finset.mem_erase.2 ⟨mn,hm⟩
    · exact Finset.mem_erase.2 ⟨zn,hz⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => InDegree P (Live P r) j - 1) both (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 hne), Finset.sum_singleton] at hh
  unfold Surplus at budget
  omega

theorem walk_localize {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ≤ r)
    (w : Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j ∧ j ≤ r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have next := (edge_desc (rules _ ih.2) e.1).le.trans ih.2
    exact ⟨.tail ih.1 ⟨⟨ih.2, e.1⟩, next, e.2⟩, next⟩

theorem localized_route {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) {i : Nat} (hi : i ≤ r) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j := by
  obtain ⟨j, h0, ha, ff, w⟩ := follow (n := r+1)
    (fun i hi => rules i (Nat.lt_succ_iff.1 hi)) a (Nat.lt_succ_iff.2 hi) fi
  exact ⟨j, h0, ha, ff, (walk_localize rules hi w).1⟩

theorem live_card_le (P : Parents) (r : Nat) : (Live P r).card ≤ r + 1 := by
  classical
  unfold Live
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem unique_leaves {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (ax : κ → LinClause V) (exh : F = Set.range ax)
    (critical : ∀ k, ∃ a : V → Bool, ∀ j, ¬ LinClauseSat a (ax j) ↔ j = k) :
    ∃ leaf : κ → Nat, Function.Injective leaf ∧
      (∀ k, leaf k ∈ WithArity P r 0 ∧ C (leaf k) = ax k) ∧
      Fintype.card κ ≤ (WithArity P r 0).card ∧
      ((WithArity P r 0).card = Fintype.card κ →
        ∀ j ∈ WithArity P r 0, ∃ k, leaf k = j) := by
  classical
  have located : ∀ k, ∃ j, j ∈ WithArity P r 0 ∧ C j = ax k := by
    intro k
    obtain ⟨a, cert⟩ := critical k
    obtain ⟨j, hj, hc, ff, w⟩ := localized_route rules a le_rfl (fr a)
    rw [exh] at hc
    obtain ⟨k', hk'⟩ := hc
    have h : ¬ LinClauseSat a (ax k') := by simpa [FalseAt, hk'] using ff
    have eq := (cert k').1 h
    subst k'
    refine ⟨j, ?_, hk'.symm⟩
    simp only [WithArity, Finset.mem_filter, hj, List.length_nil, and_true]
    exact (live_iff rules).2 (walk_sub (fun e => e.1) w)
  choose leaf spec using located
  have inj : Function.Injective leaf := by
    intro u v h
    obtain ⟨a, cert⟩ := critical u
    have hEq := (spec u).2.symm.trans ((congrArg C h).trans (spec v).2)
    have no := (cert u).2 rfl
    rw [hEq] at no
    exact ((cert v).1 no).symm
  have ss : Finset.univ.image leaf ⊆ WithArity P r 0 := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hj
    exact (spec k).1
  have card : (Finset.univ.image leaf).card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
  refine ⟨leaf, inj, spec, by simpa [card] using Finset.card_le_card ss, ?_⟩
  intro eq j hj
  have e : Finset.univ.image leaf = WithArity P r 0 :=
    Finset.eq_of_subset_of_card_le ss (by rw [eq, card])
  rw [← e] at hj
  obtain ⟨k, _, e⟩ := Finset.mem_image.1 hj
  exact ⟨k, e⟩

noncomputable def useful {V : Type} (R : LinClause V) : Bool := by
  classical
  exact decide (∃ a, ¬ LinClauseSat a R)

theorem useful_spec {V : Type} (R : LinClause V) :
    useful R = true ↔ ∃ a, ¬ LinClauseSat a R := by
  classical
  simp [useful]

theorem prune_taut {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) :
    IsLinDerivation F (π.filter useful) := by
  induction der with
  | nil => exact .nil
  | @ax π D _ hD ih =>
    simp only [List.filter_cons]
    split
    · exact .ax ih hD
    · exact ih
  | @res π D H R _ d h resolvent ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨f, df, hf, rr⟩ := resolvent
      by_cases ud : useful D = true
      · have md := List.mem_filter.2 ⟨d, ud⟩
        by_cases uh : useful H = true
        · exact .res ih md (List.mem_filter.2 ⟨h, uh⟩) ⟨f, df, hf, rr⟩
        · exact .weak ih md (by
            intro a sat
            by_contra no
            have b := resolve_branch a rr no
            split at b
            · exact b sat
            · exact uh ((useful_spec _).2 ⟨a, b⟩))
      · have weak : ∀ a, LinClauseSat a H → LinClauseSat a R := by
          intro a sat
          by_contra no
          have b := resolve_branch a rr no
          split at b
          · exact ud ((useful_spec _).2 ⟨a, b⟩)
          · exact b sat
        obtain ⟨a, ff⟩ := (useful_spec _).1 ur
        have hu : useful H = true := (useful_spec _).2 ⟨a, fun s => ff (weak a s)⟩
        exact .weak ih (List.mem_filter.2 ⟨h, hu⟩) weak
    · rw [ite_eq_right ur]
      exact ih
  | @weak π D R _ hD hw ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨a, no⟩ := (useful_spec _).1 ur
      exact .weak ih (List.mem_filter.2 ⟨hD, (useful_spec _).2 ⟨a, fun h => no (hw a h)⟩⟩) hw
    · rw [ite_eq_right ur]
      exact ih

theorem encoded_useful {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents}
    (h : Encoded F C P (π.filter useful)) {i : Nat} (hi : i < (π.filter useful).length) :
    ∃ a, FalseAt C a i := by
  have mm := (h.2 _).2 ⟨i, hi, rfl⟩
  exact (useful_spec _).1 (List.mem_filter.1 mm).2

theorem walk_keep_live {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ∈ Live P r)
    (w : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ∈ Live P r ∧ FalseAt C a v)) i j ∧ j ∈ Live P r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have hm := live_closed rules ih.2 e.1.2
    exact ⟨.tail ih.1 ⟨e.1, hm, e.2.2⟩, hm⟩

theorem high_weak_shared {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (rc : LocalEdge P r r c) (rd : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 47) (wcount : 3 ≤ (WithArity P r 1).card)
    (labels : Fintype.card κ = 22)
    (ax : κ → LinClause V) (exh : F = Set.range ax) (point : κ → (V → Bool) → Prop)
    (point_exists : ∀ k, ∃ a, point k a)
    (one : ∀ {a k}, point k a → ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k)
    (side : (V → Bool) → Bool)
    (side_choose : ∀ a, FalseAt C a (if side a then c else d))
    (force_exists : ∃ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a) :
    ∃ z < r,
      (∀ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a → FalseAt C a z) ∧
      (∀ a, FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∀ b, point k b → FalseAt C b z) ∧
      (∀ a, ¬ FalseAt C a z → ∃ k, (¬ LinClauseSat a (ax k)) ∧ ∃ b, point k b ∧ ¬ FalseAt C b z) := by
  have crit : ∀ k, ∃ a : V → Bool, ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := point_exists k
    exact ⟨a, one ha⟩
  obtain ⟨leaf, _, atLeaf, lb, covers⟩ := unique_leaves rules fr ax exh crit
  have card := arity_count rules
  have ex : (WithArity P r 0).card = Fintype.card κ := by omega
  have su : Surplus P r ≤ 1 := by omega
  let E := LocalEdge P r
  let B := fun a i => i ∈ Live P r ∧ FalseAt C a i
  let bad := fun a k => ¬ LinClauseSat a (ax k)
  have branch : ∀ a, B a (if side a then c else d) := by
    intro a
    refine ⟨?_, side_choose a⟩
    cases h : side a
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rd))
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rc))
  have route : ∀ a i, B a i →
      ∃ k, bad a k ∧ Walk (fun u v => E u v ∧ B a v) i (leaf k) := by
    intro a i bi
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 bi.1)
    obtain ⟨j, j0, _, jf, w⟩ := localized_route rules a ir bi.2
    obtain ⟨wm, jm⟩ := walk_keep_live rules bi.1 w
    have jax : j ∈ WithArity P r 0 := by simpa [WithArity, j0] using jm
    obtain ⟨k, hk⟩ := covers ex j jax
    have ceq : C j = ax k := hk ▸ (atLeaf k).2
    exact ⟨k, by simpa [bad, FalseAt, ceq] using jf, hk ▸ wm⟩
  have desc : ∀ {i j}, E i j → j < i := bounded_edge rules
  obtain ⟨a, ha⟩ := force_exists
  obtain ⟨p, q, z, hp, hq, ep, eq, pq, _, common⟩ :=
    entry_exists desc rc rd ne bad point leaf B side one branch route point_exists ha
  have from_left : ∀ {p}, p = r ∨ Walk E c p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rc hp)
  have from_right : ∀ {p}, p = r ∨ Walk E d p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rd hp)
  have zl : z ∈ Live P r := live_closed rules (from_left hp) ep.2
  have zd : 2 ≤ InDegree P (Live P r) z := shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq
  have one_merge : ∀ p q m, (p = r ∨ Walk E c p) → (q = r ∨ Walk E d q) →
      E p m → E q m → p ≠ q → m = z := by
    intro p q m hp hq ep eq pq
    have ml := live_closed rules (from_left hp) ep.2
    exact only_one_share rules su ml zl
      (shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq) zd
  have lem := one_entry_characterization desc rc rd ne bad point leaf B side one branch route
    point_exists one_merge common
  have zr : z < r := (desc ep).trans_le ep.1
  exact ⟨z, zr, by simpa [B, zl] using lem⟩

end PEqualNP.Outside.L_pcx_118.Graph
namespace PEqualNP.Outside.L_pcx_178.Split
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Bridge PEqualNP.Outside.L_pcx_118.Graph

def Used (P : Parents) (r i j : Nat) : Prop := i ∈ Live P r ∧ Edge P i j
def Stop (P : Parents) (r i : Nat) : Prop := i = r ∨ Edge P r i ∨ 2 ≤ InDegree P (Live P r) i
def Private (P : Parents) (r p i : Nat) : Prop :=
  Used P r p i ∧ ¬ Stop P r i ∧ ∀ q, Used P r q i → q=p

theorem ownerExists {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {k : Nat} (hk : k ∈ Live P r) :
    ∃ u ∈ Live P r, Stop P r u ∧ Walk (Private P r) u k := by
  classical
  suffices aux : ∀ d i, r-i=d → i ∈ Live P r →
      ∃ u ∈ Live P r, Stop P r u ∧ Walk (Private P r) u i from aux _ k rfl hk
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i eq live
    by_cases stop : Stop P r i
    · exact ⟨i,live,stop,.refl⟩
    have ne : i ≠ r := fun e => stop (Or.inl e)
    obtain ⟨p,wp,ep⟩ := ((live_iff rules).1 live).cases_tail.resolve_left ne
    have lp := (live_iff rules).2 wp
    have ip := bounded_edge rules ep
    have pr := walk_le (bounded_edge rules) wp
    obtain ⟨u,lu,su,path⟩ := ih (r-p) (by omega) p rfl lp
    refine ⟨u,lu,su,.tail path ⟨⟨lp,ep.2⟩,stop,?_⟩⟩
    intro q hq
    by_contra distinct
    exact stop (Or.inr (Or.inr (shared_degree hq.1 lp hq.2 ep.2 distinct)))

theorem retreat {P : Parents} {r u k t : Nat} {B : Nat → Prop}
    (suffix : Walk (Private P r) u k) (st : Stop P r t)
    (path : Walk (fun i j => Used P r i j ∧ B j) t k) :
    Walk (fun i j => Used P r i j ∧ B j) t u := by
  induction suffix with
  | refl => exact path
  | @tail p j _ hp ih =>
    rcases path.cases_tail with eq | ⟨q,w,hq⟩
    · exact False.elim (hp.2.1 (eq.symm ▸ st))
    · have same : q=p := hp.2.2 q hq.1
      subst q
      exact ih w

theorem markEnd {E : Nat → Nat → Prop} {B : Nat → Prop} {i j : Nat} (bi : B i)
    (w : Walk (fun p q => E p q ∧ B q) i j) : B j := by
  induction w with
  | refl => exact bi
  | tail _ last _ => exact last.2

theorem used_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (e : Used P r i j) : j < i :=
  bounded_edge rules ⟨walk_le (bounded_edge rules) ((live_iff rules).1 e.1),e.2⟩

theorem usedPath {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) (li : i ∈ Live P r)
    (path : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => Used P r u v ∧ FalseAt C a v) i j ∧ j ∈ Live P r := by
  induction path with
  | refl => exact ⟨.refl,li⟩
  | tail _ last ih =>
    exact ⟨.tail ih.1 ⟨⟨ih.2,last.1.2⟩,last.2.2⟩,live_closed rules ih.2 last.1.2⟩

abbrev Leaf (P : Parents) (r : Nat) := {i : Nat // i ∈ WithArity P r 0}

theorem owners {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (empty : ∀ a, FalseAt C a r) (head : P r ≠ []) :
    ∃ own : Leaf P r → Nat,
      (∀ k, own k ∈ Live P r ∧ Stop P r (own k) ∧ Walk (Private P r) (own k) k.val ∧ own k < r) ∧
      (∀ a u, (∀ k : Leaf P r, FalseAt C a k.val → own k = u) → FalseAt C a u) ∧
      (∀ a u, u ∈ Live P r → Stop P r u → FalseAt C a u →
        ∃ k : Leaf P r, FalseAt C a k.val ∧
          (own k = u ∨ own k < u ∧ FalseAt C a (own k))) := by
  classical
  have pick (k : Leaf P r) := ownerExists rules (Finset.mem_filter.1 k.property).1
  choose own spec using pick
  have route (a : V → Bool) (u : Nat) (lu : u ∈ Live P r) (fu : FalseAt C a u) :
      ∃ k : Leaf P r, FalseAt C a k.val ∧ Walk (fun i j => Used P r i j ∧ FalseAt C a j) u k.val := by
    have ur := walk_le (bounded_edge rules) ((live_iff rules).1 lu)
    obtain ⟨j,hj,_,fj,w⟩ := localized_route rules a ur fu
    obtain ⟨w',lj⟩ := usedPath rules a lu w
    exact ⟨⟨j,Finset.mem_filter.2 ⟨lj,by simp [hj]⟩⟩,fj,w'⟩
  have small (k : Leaf P r) : own k < r := by
    have le := walk_le (bounded_edge rules) ((live_iff rules).1 (spec k).1)
    by_contra! h
    have eq : own k = r := by omega
    have ww := (spec k).2.2
    rw [eq] at ww
    rcases ww.cases_head with e | ⟨v,edge,_⟩
    · have nil := (Finset.mem_filter.1 k.property).2
      have same : k.val = r := by omega
      rw [same] at nil
      exact head (List.length_eq_zero_iff.mp nil)
    · exact edge.2.1 (Or.inr (Or.inl edge.1.2))
  refine ⟨own,fun k => ⟨(spec k).1,(spec k).2.1,(spec k).2.2,small k⟩,?_,?_⟩
  · intro a u covered
    have lr : r ∈ Live P r := (live_iff rules).2 .refl
    obtain ⟨k,bad,path⟩ := route a r lr (empty a)
    have w := retreat (spec k).2.2 (Or.inl rfl : Stop P r r) path
    exact covered k bad ▸ markEnd (empty a) w
  · intro a u lu su fu
    obtain ⟨k,bad,path⟩ := route a u lu fu
    have w := retreat (spec k).2.2 su path
    have le := walk_le (fun {i j} (h : Used P r i j ∧ FalseAt C a j) => used_desc rules h.1) w
    exact ⟨k,bad,le.eq_or_lt.imp_right (fun lt => ⟨lt,markEnd fu w⟩)⟩

end PEqualNP.Outside.L_pcx_178.Split

namespace Lpcx178ThreeDemands
open PEqualNP.ProofComplexity
section
variable {V : Type} [DecidableEq V]
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


end
abbrev Cell := Fin 5 × Fin 4
def board (x : Cell → Bool) : Prop :=
  ∀ i j : Cell, i.2 = j.2 → x i = true → x j = true → i = j
def served (x : Cell → Bool) (p : Fin 5) := ∃ h, x (p,h) = true
def seed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (v : Cell) : Bool :=
  decide (∃ n : Fin 3, v = (r n, k n))

theorem freshHoles : ∀ h : Fin 4, ∃ k : Fin 3 → Fin 4,
    Function.Injective k ∧ ∀ n, k n ≠ h := by decide +kernel

theorem seedBoard (r : Fin 3 → Fin 5) {k : Fin 3 → Fin 4} (inj : Function.Injective k) :
    board (seed r k) := by
  intro i j eq hi hj
  obtain ⟨m,ei⟩ := of_decide_eq_true hi
  obtain ⟨n,ej⟩ := of_decide_eq_true hj
  subst i
  subst j
  obtain rfl := inj eq
  rfl

theorem seedServed (r : Fin 3 → Fin 5) (k : Fin 3 → Fin 4) (n : Fin 3) :
    served (seed r k) (r n) :=
  ⟨k n,decide_eq_true ⟨n,rfl⟩⟩

theorem freshFlip (x : Cell → Bool) (i : Cell) (hx : board x)
    (clear : ∀ u : Cell, u.2 = i.2 → x u = false) : board (flip x i) := by
  intro u v eq hu hv
  by_cases ui : u = i
  · by_cases vi : v = i
    · exact ui.trans vi.symm
    · have z := clear v (eq.symm.trans (congrArg Prod.snd ui))
      simp [flip,vi,z] at hv
  · by_cases vi : v = i
    · have z := clear u (eq.trans (congrArg Prod.snd vi))
      simp [flip,ui,z] at hu
    · exact hx u v eq (by simpa [flip,ui] using hu) (by simpa [flip,vi] using hv)

theorem threeDemandFiber {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinEqSat x (f,b) := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨k,inj,avoid⟩ := freshHoles i.2
  let x := seed r k
  have bx : board x := seedBoard r inj
  have clear (u : Cell) (hu : u.2 = i.2) : x u = false := by
    change decide (∃ n : Fin 3, u = (r n,k n)) = false
    apply decide_eq_false
    rintro ⟨n,e⟩
    exact avoid n ((congrArg Prod.snd e).symm.trans hu)
  by_cases hit : LinEqSat x (f,b)
  · exact ⟨x,bx,seedServed r k,hit⟩
  · refine ⟨flip x i,freshFlip x i bx clear,?_,(opposite hi b).mpr hit⟩
    intro n
    have ne : (r n,k n) ≠ i := fun e => avoid n (congrArg Prod.snd e)
    refine ⟨k n,?_⟩
    have yes : x (r n,k n) = true := decide_eq_true ⟨n,rfl⟩
    simpa [flip,ne] using yes

theorem noThreeDemandFiberClause {f : Finset Cell} (h : f.Nonempty) (b : Bool)
    (r : Fin 3 → Fin 5) (K : LinClause Cell)
    (valid : ∀ x, board x → (∀ n, served x (r n)) → LinClauseSat x K) :
    ¬ (∀ x, LinEqSat x (f,b) → ¬ LinClauseSat x K) := by
  obtain ⟨x,bx,rows,hf⟩ := threeDemandFiber h b r
  exact fun bad => bad x hf (valid x bx rows)


theorem threeRowsSpan (K : LinClause Cell) (r : Fin 3 → Fin 5)
    {z : Cell → Bool} (hz : LinClauseSat z K) :
    ∃ x : Cell → Bool, board x ∧ (∀ n, served x (r n)) ∧ LinClauseSat x K := by
  obtain ⟨⟨f,b⟩,mem,eq⟩ := hz
  by_cases nonempty : f.Nonempty
  · obtain ⟨x,bx,rows,hit⟩ := threeDemandFiber nonempty b r
    exact ⟨x,bx,rows,(f,b),mem,hit⟩
  · have fe : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst f
    obtain ⟨x,bx,rows,_⟩ := threeDemandFiber
      (f := {((0 : Fin 5),(0 : Fin 4))}) (by simp) false r
    refine ⟨x,bx,rows,(∅,b),mem,?_⟩
    unfold LinEqSat at eq ⊢
    simpa only [Finset.filter_empty] using eq

theorem noProperDominator (K : LinClause Cell) (r : Fin 3 → Fin 5)
    (onlyPaths : ∀ x, board x → (∀ n, served x (r n)) → ¬ LinClauseSat x K) :
    ∀ z, ¬ LinClauseSat z K := by
  intro z hit
  obtain ⟨x,bx,rows,sat⟩ := threeRowsSpan K r hit
  exact onlyPaths x bx rows sat

theorem resolutionSound {x : Cell → Bool} {C D R : LinClause Cell}
    (p : IsLinResolvent C D R) (c : LinClauseSat x C) (d : LinClauseSat x D) :
    LinClauseSat x R := by
  obtain ⟨f,_,_,rfl⟩ := p
  obtain ⟨u,hu,su⟩ := c
  obtain ⟨v,hv,sv⟩ := d
  by_cases e : u = (f,false)
  · by_cases e' : v = (f,true)
    · subst u
      subst v
      have impossible : false = true := su.mp (sv.mpr rfl)
      contradiction
    · exact ⟨v,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e',hv⟩),sv⟩
  · exact ⟨u,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hu⟩),su⟩

theorem derivationSound {F : Set (LinClause Cell)} {π} {x : Cell → Bool}
    (d : IsLinDerivation F π) (init : ∀ C ∈ F, LinClauseSat x C) :
    ∀ C ∈ π, LinClauseSat x C := by
  induction d with
  | nil => simp
  | ax _ ax ih =>
    intro C hc
    rcases List.mem_cons.mp hc with rfl|old
    · exact init _ ax
    · exact ih _ old
  | res _ hC hD step ih =>
    intro R hr
    rcases List.mem_cons.mp hr with rfl|old
    · exact resolutionSound step (ih _ hC) (ih _ hD)
    · exact ih _ old
  | weak _ hc w ih =>
    intro D hd
    rcases List.mem_cons.mp hd with rfl|old
    · exact w _ (ih _ hc)
    · exact ih _ old

def row (p : Fin 5) : Clause Cell :=
  Finset.univ.image (fun h : Fin 4 => ((p,h),true))
def coll (p q : Fin 5) (h : Fin 4) : Clause Cell :=
  {((p,h),false),((q,h),false)}
def threeAxioms (r : Fin 3 → Fin 5) : Set (LinClause Cell) :=
  {K | (∃ n, K = linOfClause (row (r n))) ∨
       ∃ p q h, p ≠ q ∧ K = linOfClause (coll p q h)}

theorem litEq {x : Cell → Bool} (v : Cell) (b : Bool) (h : x v = b) :
    LinEqSat x ({v},b) := by
  have e : ({v} : Finset Cell).filter (fun u => x u = true) = (if b then {v} else ∅) := by
    ext u
    by_cases eq : u = v
    · subst u
      cases b <;> simp [h]
    · cases b <;> simp [eq]
  unfold LinEqSat
  change (Odd (({v} : Finset Cell).filter (fun u => x u = true)).card ↔ b = true)
  rw [e]
  cases b <;> simp

theorem axiomsTrue {x : Cell → Bool} (r : Fin 3 → Fin 5) (xb : board x)
    (rows : ∀ n, served x (r n)) : ∀ A ∈ threeAxioms r, LinClauseSat x A := by
  intro A ha
  rcases ha with ⟨n,rfl⟩|⟨p,q,h,pq,rfl⟩
  · obtain ⟨h,yes⟩ := rows n
    refine ⟨_,Finset.mem_image.mpr ⟨((r n,h),true),?_,rfl⟩,litEq _ true yes⟩
    exact Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩
  · have no : x (p,h) = false ∨ x (q,h) = false := by
      by_cases hp : x (p,h) = true
      · right
        cases hq : x (q,h) with
        | false => rfl
        | true => exact (pq (congrArg Prod.fst (xb (p,h) (q,h) rfl hp hq))).elim
      · left
        cases h : x (p,h) <;> simp_all
    rcases no with no|no
    · exact ⟨_,Finset.mem_image.mpr ⟨((p,h),false),by simp [coll],rfl⟩,litEq _ false no⟩
    · exact ⟨_,Finset.mem_image.mpr ⟨((q,h),false),by simp [coll],rfl⟩,litEq _ false no⟩


end Lpcx178ThreeDemands

namespace PEqualNP.Outside.L_pcx_178.Five
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_178.Split Lpcx178ThreeDemands
abbrev F := (linOfClause '' PHP 5 4 : Set (LinClause Cell))
theorem otherThree : ∀ p q : Fin 5, p ≠ q → ∃ a b c : Fin 5,
  ∀ i : Fin 5, i = p ∨ i = q ∨ i = a ∨ i = b ∨ i = c := by decide +kernel

theorem onlyTwo {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i)
    {p q : Fin 5} {a b c : Fin 5} (cover : ∀ i : Fin 5, i=p ∨ i=q ∨ i=a ∨ i=b ∨ i=c)
    (x : Cell → Bool) (xb : board x) (serv : ∀ t : Fin 3, served x (![a,b,c] t))
    {k : Leaf P r} (ff : FalseAt C x k.val) :
    C k.val = linOfClause (row p) ∨ C k.val = linOfClause (row q) := by
  have live := (Finset.mem_filter.mp k.property).1
  have m := walk_le (bounded_edge rules) ((live_iff rules).1 live)
  have pn : P k.val = [] := List.length_eq_zero_iff.mp (Finset.mem_filter.mp k.property).2
  have ax : C k.val ∈ F := by
    rcases rules k.val m with ⟨_,hm⟩ | ⟨u,_,e,_⟩ | ⟨u,_,v,_,e,_⟩
    · exact hm
    · rw [pn] at e; contradiction
    · rw [pn] at e; contradiction
  obtain ⟨D,hd,eq⟩ := ax
  rcases hd with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · rcases cover i with e|e|e|e|e
    · exact Or.inl (by simpa [row,e] using eq.symm)
    · exact Or.inr (by simpa [row,e] using eq.symm)
    all_goals
      exfalso
      apply ff
      rw [←eq]
      apply axiomsTrue _ xb serv
      left
    · exact ⟨0,by simp [row,e]⟩
    · exact ⟨1,by simp [row,e]⟩
    · exact ⟨2,by simp [row,e]⟩
  · exfalso
    apply ff
    rw [←eq]
    exact axiomsTrue _ xb serv _ (Or.inr ⟨i,j,h,ne,rfl⟩)

theorem rowInj {C : ClauseMap Cell} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r ≠ [])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i)) :
    ∃ f : Fin 5 → Nat, Function.Injective f ∧ ∀ i,
      f i ∈ Live P r ∧ f i < r ∧ (Edge P r (f i) ∨ 2 ≤ InDegree P (Live P r) (f i)) := by
  classical
  obtain ⟨own,whereAt,must,_⟩ := owners rules empty head
  refine ⟨fun i => own (atRow i),?_,?_⟩
  · intro p q eq
    by_contra ne
    obtain ⟨a,b,c,cover⟩ := otherThree p q ne
    let u := own (atRow p)
    obtain ⟨z,hit⟩ := prev u (whereAt (atRow p)).2.2.2
    obtain ⟨x,xb,sv,yes⟩ := threeRowsSpan (C u) (![a,b,c]) hit
    apply (must x u ?_) yes
    intro k bad
    have L (j : Leaf P r) : j.val ∈ Live P r := (Finset.mem_filter.mp j.property).1
    rcases onlyTwo rules cover x xb sv bad with hp|hq
    · have id : k = atRow p := Subtype.ext (inj (L k) (L _) (hp.trans (rows p).symm))
      exact congrArg own id
    · have id : k = atRow q := Subtype.ext (inj (L k) (L _) (hq.trans (rows q).symm))
      exact (congrArg own id).trans eq.symm
  · intro i
    obtain ⟨l,st,_,lt⟩ := whereAt (atRow i)
    exact ⟨l,lt,st.resolve_left (Nat.ne_of_lt lt)⟩

theorem sharedThree {C : ClauseMap Cell} {P : Parents} {r u v : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (empty : ∀ x, FalseAt C x r)
    (prev : ∀ i<r, ∃ a, LinClauseSat a (C i)) (head : P r = [u,v])
    (inj : Set.InjOn C (↑(Live P r) : Set Nat))
    (atRow : Fin 5 → Leaf P r) (rows : ∀ i, C (atRow i).val = linOfClause (row i)) :
    3 ≤ Surplus P r := by
  classical
  obtain ⟨f,inject,sp⟩ := rowInj rules empty prev (by simp [head]) inj atRow rows
  let T := (Live P r).erase r
  let S := T.filter fun j => 2 ≤ InDegree P (Live P r) j
  have cap : S.card ≤ Surplus P r := by
    have low : (∑ j ∈ S, 1) ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      omega
    have incl : S ⊆ T := Finset.filter_subset _ _
    have a : S.card ≤ ∑ j ∈ S, (InDegree P (Live P r) j - 1) := by simpa using low
    exact a.trans (Finset.sum_le_sum_of_subset_of_nonneg incl (by intros; omega))
  have inc : Finset.univ.image f ⊆ ({u,v} : Finset Nat) ∪ S := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨live,lt,e|h⟩ := sp i
    · apply Finset.mem_union_left
      simpa [Edge,head] using e
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Nat.ne_of_lt lt,live⟩,h⟩)
  have lo := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ inject,Finset.card_univ,Fintype.card_fin] at lo
  have hi := Finset.card_union_le ({u,v} : Finset Nat) S
  have uv : ({u,v} : Finset Nat).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega
end PEqualNP.Outside.L_pcx_178.Five

namespace PEqualNP.Outside.L_pcx_178.Five
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_178.Split Lpcx178ThreeDemands
open PEqualNP.Outside.L_pcx_119_compile PEqualNP.Outside.L_pcx_119_image
abbrev V := Cell
theorem derivation_dedup {F : Set (LinClause V)} {pi : List (LinClause V)}
    (deriv : IsLinDerivation F pi) :
    ∃ rho, IsLinDerivation F rho ∧ rho.Nodup ∧ rho.Sublist pi ∧
      ∀ c, c ∈ pi ↔ c ∈ rho := by
  classical
  induction deriv with
  | nil =>
    exact ⟨[], .nil, List.nodup_nil, .slnil, fun _ => Iff.rfl⟩
  | @ax pi C deriv hC ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : C ∈ rho
    · refine ⟨rho, hd, nd, sub.cons C, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨C :: rho, .ax hd hC, List.nodup_cons.mpr ⟨h, nd⟩,
        sub.cons_cons C, fun c => by simp [eq]⟩
  | @res pi C D R deriv hC hD hr ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : R ∈ rho
    · refine ⟨rho, hd, nd, sub.cons R, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨R :: rho, .res hd ((eq C).mp hC) ((eq D).mp hD) hr,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons R, fun c => by simp [eq]⟩
  | @weak pi C D deriv hC hw ih =>
    obtain ⟨rho, hd, nd, sub, eq⟩ := ih
    by_cases h : D ∈ rho
    · refine ⟨rho, hd, nd, sub.cons D, fun c => ?_⟩
      simp only [List.mem_cons, eq]
      exact ⟨fun H => H.elim (fun e => e.symm ▸ h) id, Or.inr⟩
    · exact ⟨D :: rho, .weak hd ((eq C).mp hC) hw,
        List.nodup_cons.mpr ⟨h, nd⟩, sub.cons_cons D, fun c => by simp [eq]⟩
theorem encoded_injective {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {xs : List (LinClause V)}
    (graph : Encoded F C P xs) (nd : xs.Nodup) :
    Set.InjOn C (↑(Finset.range xs.length) : Set Nat) := by
  classical
  have im : (Finset.range xs.length).image C = xs.toFinset := by
    ext D
    simpa only [Finset.mem_image,Finset.mem_range,List.mem_toFinset] using (graph.2 D).symm
  apply Finset.card_image_iff.mp
  rw [im,List.toFinset_card_of_nodup nd,Finset.card_range]

def axisBank : List (LinClause V) := [linOfClause (Finset.univ.image (fun j : Fin 4 => ((0,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((1,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((2,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((3,j),true))), linOfClause (Finset.univ.image (fun j : Fin 4 => ((4,j),true))), linOfClause {((0,0), false), ((1,0), false)}, linOfClause {((0,0), false), ((2,0), false)}, linOfClause {((0,0), false), ((3,0), false)}, linOfClause {((0,0), false), ((4,0), false)}, linOfClause {((1,0), false), ((2,0), false)}, linOfClause {((1,0), false), ((3,0), false)}, linOfClause {((1,0), false), ((4,0), false)}, linOfClause {((2,0), false), ((3,0), false)}, linOfClause {((2,0), false), ((4,0), false)}, linOfClause {((3,0), false), ((4,0), false)}, linOfClause {((0,1), false), ((1,1), false)}, linOfClause {((0,1), false), ((2,1), false)}, linOfClause {((0,1), false), ((3,1), false)}, linOfClause {((0,1), false), ((4,1), false)}, linOfClause {((1,1), false), ((2,1), false)}, linOfClause {((1,1), false), ((3,1), false)}, linOfClause {((1,1), false), ((4,1), false)}, linOfClause {((2,1), false), ((3,1), false)}, linOfClause {((2,1), false), ((4,1), false)}, linOfClause {((3,1), false), ((4,1), false)}, linOfClause {((0,2), false), ((1,2), false)}, linOfClause {((0,2), false), ((2,2), false)}, linOfClause {((0,2), false), ((3,2), false)}, linOfClause {((0,2), false), ((4,2), false)}, linOfClause {((1,2), false), ((2,2), false)}, linOfClause {((1,2), false), ((3,2), false)}, linOfClause {((1,2), false), ((4,2), false)}, linOfClause {((2,2), false), ((3,2), false)}, linOfClause {((2,2), false), ((4,2), false)}, linOfClause {((3,2), false), ((4,2), false)}, linOfClause {((0,3), false), ((1,3), false)}, linOfClause {((0,3), false), ((2,3), false)}, linOfClause {((0,3), false), ((3,3), false)}, linOfClause {((0,3), false), ((4,3), false)}, linOfClause {((1,3), false), ((2,3), false)}, linOfClause {((1,3), false), ((3,3), false)}, linOfClause {((1,3), false), ((4,3), false)}, linOfClause {((2,3), false), ((3,3), false)}, linOfClause {((2,3), false), ((4,3), false)}, linOfClause {((3,3), false), ((4,3), false)}]
def axis (i : Fin 45) : LinClause V := axisBank.getD i.val ∅
def sat (a : V → Bool) (C : LinClause V) : Bool :=
  decide (∃ q ∈ C, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))
theorem sat_true {a : V→Bool} {C : LinClause V} : sat a C = true ↔ LinClauseSat a C := by
  unfold sat LinClauseSat LinEqSat
  rw [decide_eq_true_eq]

def tag (p : Fin 5) : Fin 45 := ⟨p.val,by omega⟩
theorem axisRow : ∀ p, axis (tag p)=linOfClause (row p) := by decide +kernel
theorem allCol : ∀ (p q : Fin 5) (h : Fin 4), p≠q → ∃ j, axis j=linOfClause (coll p q h) := by decide +kernel
theorem isAx : ∀ j : Fin 45, (∃ p, axis j=linOfClause (row p)) ∨
    ∃ p q h, p≠q ∧ axis j=linOfClause (coll p q h) := by decide +kernel
theorem rangeAx : F = Set.range axis := by
  ext K
  constructor
  · rintro ⟨D,d,rfl⟩
    rcases d with ⟨i,rfl⟩ | ⟨p,q,h,ne,rfl⟩
    · exact ⟨tag i,axisRow i⟩
    · exact allCol p q h ne
  · rintro ⟨j,rfl⟩
    rcases isAx j with ⟨p,eq⟩|⟨p,q,h,ne,eq⟩
    · exact ⟨row p,Or.inl ⟨p,rfl⟩,eq.symm⟩
    · exact ⟨coll p q h,Or.inr ⟨p,q,h,ne,rfl⟩,eq.symm⟩

def privateAsg (i : Fin 45) := Pcx180Price.asg ((Pcx180Price.pts i).headD 0)
theorem checks : ∀ i j : Fin 45, sat (privateAsg i) (axis j) = decide (i ≠ j) := by decide +kernel
theorem priv (i : Fin 45) : ∃ x, ∀ j, ¬ LinClauseSat x (axis j) ↔ j=i := by
  refine ⟨privateAsg i,fun j => ?_⟩
  rw [←sat_true,checks]
  constructor
  · intro h
    by_contra ne
    exact h (decide_eq_true (Ne.symm ne))
  · intro eq y
    exact (of_decide_eq_true y) eq.symm
theorem axSat (K : LinClause Cell) (hm : K∈F) : ∃ x,LinClauseSat x K := by
  obtain ⟨j,rfl⟩ := rangeAx ▸ hm
  by_cases e : j=0
  · exact ⟨privateAsg 1,sat_true.mp (by rw [checks,e];decide)⟩
  · exact ⟨privateAsg 0,sat_true.mp (by simpa [checks] using Ne.symm e)⟩

def ledger (C : ClauseMap Cell) : Nat → List (LinClause Cell)
  | 0 => []
  | i+1 => C i :: ledger C i
theorem lenLedger (C : ClauseMap Cell) (n : Nat) : (ledger C n).length=n := by induction n <;> simp_all [ledger]
theorem inLedger {C : ClauseMap Cell} {i n} (h : i<n) : C i ∈ ledger C n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : i=n
    · simp [ledger,e]
    · exact List.mem_cons_of_mem _ (ih (by omega))
theorem recorded {C : ClauseMap Cell} {P : Parents} {n}
    (valid : ∀ i<n,Rule F C P i) :
    ∃ X, Log F X (ledger C n) ∧ X.length=((Finset.range n).filter fun i => (P i).length = 1).card := by
  induction n with
  | zero => exact ⟨[],.nil,by simp⟩
  | succ n ih =>
    obtain ⟨X,w,size⟩ := ih (fun i hi => valid i (by omega))
    rcases valid n (by omega) with ⟨pn,axiomLine⟩|⟨j,lt,pn,weak⟩|⟨j,lt,k,lt',pn,res⟩
    · exact ⟨X,.ax w axiomLine,by simpa [Finset.range_add_one,Finset.filter_insert,pn] using size⟩
    · refine ⟨_,.weak w (inLedger lt) weak,?_⟩
      simp [Finset.range_add_one,Finset.filter_insert,pn,size]
    · exact ⟨X,.res w (inLedger lt) (inLedger lt') res,by simpa [Finset.range_add_one,Finset.filter_insert,pn] using size⟩

theorem posted95 {pi : List (LinClause Cell)} (proof : IsLinRefutation (PHP 5 4) pi) :
    95 ≤ pi.length := by
  classical
  by_contra! short
  obtain ⟨xs,der,nd,sub,mem⟩ := derivation_dedup proof.1
  have emp := (mem _).1 proof.2
  obtain ⟨C,P,gr⟩ := build_graph der
  obtain ⟨r,hr,bottom,prev,u,hu,v,hv,_,head,_⟩ := first_false gr emp axSat
  have rules : ∀ i≤r,Rule F C P i := fun i hi => gr.1 i (hi.trans_lt hr)
  obtain ⟨leaf,_,spec,sz,_⟩ := unique_leaves rules bottom axis rangeAx priv
  let rowNode (i : Fin 5) : Leaf P r := ⟨leaf (tag i),(spec _).1⟩
  have lsub : Live P r ⊆ Finset.range xs.length := by
    intro i hi
    exact Finset.mem_range.mpr ((walk_le (bounded_edge rules) ((live_iff rules).1 hi)).trans_lt hr)
  have su := sharedThree rules bottom prev head ((encoded_injective gr nd).mono lsub)
    rowNode (fun i => (spec (tag i)).2.trans (axisRow i))
  have graphCount := arity_count rules
  simp only [Fintype.card_fin] at sz
  obtain ⟨X,w,wn⟩ := recorded gr.1
  have x3 : 3 ≤ X.length := by
    by_contra! few
    obtain ⟨j,hj,hc⟩ := (gr.2 _).1 emp
    have le : (∅ : LinClause Cell)∈ledger C xs.length := hc ▸ inLedger hj
    obtain ⟨rho,ref,num⟩ := twoWeakRefutation ((0,0) : Cell) w (by omega) le
    rw [lenLedger] at num
    have sl := sub.length_le
    exact Pcx180Ord ⟨rho,ref,by omega⟩
  let whole := Finset.range xs.length
  let live := Live P r
  let weak (i : Nat) := (P i).length=1
  have eq := Finset.card_sdiff_add_card_eq_card lsub
  have ub : (whole.filter weak).card ≤ (WithArity P r 1).card + (whole \ live).card := by
    have incl : whole.filter weak ⊆ WithArity P r 1 ∪ (whole \ live) := by
      intro i hi
      obtain ⟨inw,un⟩ := Finset.mem_filter.mp hi
      by_cases il : i∈live
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨il,un⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨inw,il⟩)
    exact (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  change X.length=(whole.filter weak).card at wn
  change (whole \ live).card + (Live P r).card = (Finset.range xs.length).card at eq
  rw [Finset.card_range] at eq
  have sl := sub.length_le
  omega
end PEqualNP.Outside.L_pcx_178.Five
namespace PEqualNP.Outside.L_pcx_178.Five
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph PEqualNP.Outside.L_pcx_118.Bridge
open PEqualNP.Outside.L_pcx_178.Split Lpcx178ThreeDemands
open PEqualNP.Outside.L_pcx_119_compile PEqualNP.Outside.L_pcx_119_image
theorem counted96 (impossible : ∀ (C : ClauseMap Cell) (P : Parents) (r u v : Nat),
    (∀ i ≤ r, Rule F C P i) → (∀ x, FalseAt C x r) →
    (∀ i<r, ∃ a, LinClauseSat a (C i)) → u≠v → P r=[u,v] →
    Set.InjOn C (↑(Live P r) : Set Nat) →
    (∀ A∈F, ∃ k : Leaf P r, C k.val=A) →
    (∀ S : Finset Cell, (∀ a, if Odd (S.filter (fun x => a x = true)).card then FalseAt C a u else FalseAt C a v) →
      Surplus P r ≤ 3 → False)) {pi : List (LinClause Cell)} (proof : IsLinRefutation (PHP 5 4) pi) :
    96 ≤ pi.length := by
  classical
  by_contra! short
  obtain ⟨xs,der,nd,sub,mem⟩ := derivation_dedup proof.1
  have emp := (mem _).1 proof.2
  obtain ⟨C,P,gr⟩ := build_graph der
  obtain ⟨r,hr,bottom,prev,u,hu,v,hv,uv,head,S,nz,pivot⟩ := first_false gr emp axSat
  have rules : ∀ i≤r,Rule F C P i := fun i hi => gr.1 i (hi.trans_lt hr)
  obtain ⟨leaf,_,spec,sz,_⟩ := unique_leaves rules bottom axis rangeAx priv
  let rowNode (i : Fin 5) : Leaf P r := ⟨leaf (tag i),(spec _).1⟩
  have lsub : Live P r ⊆ Finset.range xs.length := by
    intro i hi
    exact Finset.mem_range.mpr ((walk_le (bounded_edge rules) ((live_iff rules).1 hi)).trans_lt hr)
  have su := sharedThree rules bottom prev head ((encoded_injective gr nd).mono lsub)
    rowNode (fun i => (spec (tag i)).2.trans (axisRow i))
  have graphCount := arity_count rules
  simp only [Fintype.card_fin] at sz
  obtain ⟨X,w,wn⟩ := recorded gr.1
  have x3 : 3 ≤ X.length := by
    by_contra! few
    obtain ⟨j,hj,hc⟩ := (gr.2 _).1 emp
    have le : (∅ : LinClause Cell)∈ledger C xs.length := hc ▸ inLedger hj
    obtain ⟨rho,ref,num⟩ := twoWeakRefutation ((0,0) : Cell) w (by omega) le
    rw [lenLedger] at num
    have sl := sub.length_le
    exact Pcx180Ord ⟨rho,ref,by omega⟩
  let whole := Finset.range xs.length
  let live := Live P r
  let weak (i : Nat) := (P i).length=1
  have eq := Finset.card_sdiff_add_card_eq_card lsub
  have ub : (whole.filter weak).card ≤ (WithArity P r 1).card + (whole \ live).card := by
    have incl : whole.filter weak ⊆ WithArity P r 1 ∪ (whole \ live) := by
      intro i hi
      obtain ⟨inw,un⟩ := Finset.mem_filter.mp hi
      by_cases il : i∈live
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨il,un⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨inw,il⟩)
    exact (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  change X.length=(whole.filter weak).card at wn
  change (whole \ live).card + (Live P r).card = (Finset.range xs.length).card at eq
  rw [Finset.card_range] at eq
  have sl := sub.length_le
  have bud : Surplus P r ≤3 := by omega
  have leavesHere (A) (a : A∈F) : ∃ k : Leaf P r, C k.val=A := by
    obtain ⟨j,rfl⟩ := rangeAx ▸ a
    exact ⟨⟨leaf j,(spec _).1⟩,(spec _).2⟩
  exact impossible C P r u v rules bottom prev uv head ((encoded_injective gr nd).mono lsub) leavesHere S pivot bud
end PEqualNP.Outside.L_pcx_178.Five

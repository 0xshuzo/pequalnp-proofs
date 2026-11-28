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
namespace PEqualNP.Outside.L_pcx_119_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_119_compile
variable {V : Type} [DecidableEq V]

/-- A simultaneous choice of signed non-coordinate equations makes every paid line free
in ordinary resolution, independently of where its ancestors and readers occur. -/
theorem coveredLog (v : V) {F : Set (Clause V)} {W π}
    (h : Log (linOfClause '' F) W π) (emp : (∅ : LinClause V) ∈ π)
    (orient : Finset V → Bool)
    (covered : ∀ p ∈ W, ∃ q ∈ extras p.2, orient q.1 = q.2) :
    ∃ ρ, IsRefutation F ρ ∧ ρ.length + W.length ≤ π.length := by
  classical
  let M (q : LinEq V) : Clause V := if orient q.1 = q.2 then yesC v else ∅
  have disj : DisjointSigns M := by
    intro f x h₀ h₁
    cases e : orient f
    · exact noEmpty x (by simpa [M,e] using h₁)
    · exact noEmpty x (by simpa [M,e] using h₀)
  have weakens : ∀ p ∈ W, ImageWeak M p.1 p.2 := by
    intro p hp x _
    obtain ⟨q,hq,eq⟩ := covered p hp
    exact (imageParts _ _ _).2 (Or.inr ⟨q,hq,by simpa [M,eq] using topYes v x⟩)
  obtain ⟨ρ,der,len,track⟩ := compile h (imageC M) (fun A _ => plainLift A M)
    (validRes M disj) weakens
  refine ⟨ρ,⟨der,?_⟩,len⟩
  have tr := track ∅ emp
  rw [imageEmpty] at tr
  rcases tr with tt|⟨D,hd,sub⟩
  · exact False.elim (by simpa [ClauseSat] using tt (fun _ => false))
  · have eq : D = ∅ := Finset.Subset.antisymm sub (Finset.empty_subset _)
    exact eq ▸ hd

end PEqualNP.Outside.L_pcx_119_image
namespace PEqualNP.Outside.L_pcx_119_image
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_119_compile
variable {V : Type} [DecidableEq V]

private def Agree {α : Type} (a b : α × Bool) : Prop := a.1=b.1 → a.2=b.2

private theorem orientThree {α : Type} [DecidableEq α] {a b c : α × Bool}
    (ab : Agree a b) (ac : Agree a c) (bc : Agree b c) :
    ∃ t : α → Bool, t a.1 = a.2 ∧ t b.1 = b.2 ∧ t c.1 = c.2 := by
  let t (f : α) := if f=a.1 then a.2 else if f=b.1 then b.2 else c.2
  refine ⟨t,by simp [t],?_,?_⟩
  · by_cases eq : b.1=a.1
    · simpa [t,eq] using ab eq.symm
    · simp [t,eq]
  · by_cases eq : c.1=a.1
    · simpa [t,eq] using ac eq.symm
    · by_cases eq' : c.1=b.1
      · have ba : b.1 ≠ a.1 := fun h => eq (eq'.trans h)
        simpa [t,eq',ba] using bc eq'.symm
      · simp [t,eq,eq']

private theorem notAgree {α : Type} {a b : α × Bool} (h : ¬Agree a b) :
    a.1=b.1 ∧ a.2≠b.2 := by
  unfold Agree at h
  by_contra! hh
  exact h (fun e => hh e)

def TwoForms (C : LinClause V) : Prop :=
  ∀ f : Finset V, ∃ q ∈ extras C, q.1 ≠ f

private theorem sameOther (i j k : Bool) (hj : i ≠ j) (hk : i ≠ k) : j = k := by
  cases i <;> cases j <;> cases k <;> simp_all

private theorem orientWide {A B C : LinClause V}
    (ha : TwoForms A) (hb : TwoForms B) (hc : TwoForms C) :
    ∃ t : Finset V → Bool,
      (∃ a ∈ extras A,t a.1=a.2) ∧ (∃ b ∈ extras B,t b.1=b.2) ∧
      (∃ c ∈ extras C,t c.1=c.2) := by
  classical
  have finish {a b c : LinEq V} (aA : a ∈ extras A) (bB : b ∈ extras B) (cC : c ∈ extras C)
      (ab : Agree a b) (ac : Agree a c) (bc : Agree b c) :
      ∃ t : Finset V → Bool,
        (∃ a ∈ extras A,t a.1=a.2) ∧ (∃ b ∈ extras B,t b.1=b.2) ∧
        (∃ c ∈ extras C,t c.1=c.2) := by
    obtain ⟨t,at',bt,ct⟩ := orientThree ab ac bc
    exact ⟨t,⟨a,aA,at'⟩,⟨b,bB,bt⟩,⟨c,cC,ct⟩⟩
  obtain ⟨a,ha₁,_⟩ := ha ∅
  obtain ⟨b,hb₁,ba⟩ := hb a.1
  obtain ⟨c,hc₁,ca⟩ := hc a.1
  have ab : Agree a b := fun e => (ba e.symm).elim
  have ac : Agree a c := fun e => (ca e.symm).elim
  by_cases bc : Agree b c
  · exact finish ha₁ hb₁ hc₁ ab ac bc
  have bc₀ := (notAgree bc).1
  obtain ⟨b',hb₂,bb⟩ := hb b.1
  obtain ⟨c',hc₂,cc⟩ := hc c.1
  by_cases ab' : Agree a b'
  · exact finish ha₁ hb₂ hc₁ ab' ac (fun e => (bb (e.trans bc₀.symm)).elim)
  by_cases ac' : Agree a c'
  · exact finish ha₁ hb₁ hc₂ ab ac' (fun e => (cc (e.symm.trans bc₀)).elim)
  obtain ⟨fb,sb⟩ := notAgree ab'
  obtain ⟨fc,sc⟩ := notAgree ac'
  obtain ⟨a',ha₂,aa⟩ := ha a.1
  have eq : b'.2=c'.2 := sameOther _ _ _ sb sc
  exact finish ha₂ hb₂ hc₂ (fun e => (aa (e.trans fb.symm)).elim)
    (fun e => (aa (e.trans fc.symm)).elim) (fun _ => eq)

/-- At exactly three paid weakenings, a parity speedup needs a conclusion
whose non-coordinate equations have at most one distinct left side. -/
theorem threeWideCompile (v : V) {F : Set (Clause V)} {π} {a b c : LinClause V × LinClause V}
    (h : Log (linOfClause '' F) [a,b,c] π) (emp : (∅ : LinClause V) ∈ π)
    (ha : TwoForms a.2) (hb : TwoForms b.2) (hc : TwoForms c.2) :
    ∃ ρ, IsRefutation F ρ ∧ ρ.length+3 ≤ π.length := by
  obtain ⟨t,ht₁,ht₂,ht₃⟩ := orientWide ha hb hc
  apply coveredLog v h emp t
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact ht₁
  · exact ht₂
  · exact ht₃

end PEqualNP.Outside.L_pcx_119_image

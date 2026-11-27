import PEqualNP.Outside.L_pcx_162

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


end PEqualNP.Outside.L_pcx_119_image

namespace PEqualNP.Outside.L_pcx_178_select
open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_119_compile PEqualNP.Outside.L_pcx_119_image
variable {V : Type} [DecidableEq V]

def active (t : Finset V → Bool) (C : LinClause V) : Prop :=
  ∃ q ∈ extras C, t q.1 = q.2

def mapped (v : V) (t : Finset V → Bool) (q : LinEq V) : Clause V :=
  if t q.1 = q.2 then {(v,true),(v,false)} else ∅

theorem atomSat (v : V) (t : Finset V → Bool) (q : LinEq V) (x : V → Bool) :
    ClauseSat x (mapped v t q) ↔ t q.1=q.2 := by
  by_cases yes : t q.1=q.2
  · constructor
    · exact fun _ => yes
    · intro _
      cases h : x v
      · exact ⟨(v,false), by simp [mapped,yes], h⟩
      · exact ⟨(v,true), by simp [mapped,yes], h⟩
  · simp [mapped,yes,ClauseSat]

theorem mapSat (v : V) (t : Finset V → Bool) (C : LinClause V) (x : V → Bool) :
    ClauseSat x (imageC (mapped v t) C) ↔ ClauseSat x (plainPart C) ∨ active t C := by
  rw [imageParts]
  simp only [atomSat,active]

theorem signOK (v : V) (t : Finset V → Bool) : DisjointSigns (mapped v t) := by
  intro f x a b
  have h₁ := (atomSat v t (f,false) x).1 a
  have h₂ := (atomSat v t (f,true) x).1 b
  exact Bool.noConfusion (h₁.symm.trans h₂)

def passes (t : Finset V → Bool) (P D : LinClause V) : Prop :=
  active t D ∨ (∀ x, ClauseSat x (plainPart D)) ∨
    (¬ active t P) ∧ (∀ x, ClauseSat x (plainPart P) → ClauseSat x (plainPart D))

theorem exactTest (v : V) (t : Finset V → Bool) (P D : LinClause V) :
    passes t P D ↔
      ∀ x, ClauseSat x (imageC (mapped v t) P) → ClauseSat x (imageC (mapped v t) D) := by
  classical
  simp only [mapSat,passes]
  constructor
  · rintro (hd|ht|⟨no,plain⟩) x sat
    · exact Or.inr hd
    · exact Or.inl (ht x)
    · exact Or.inl (plain x (sat.resolve_right no))
  · intro h
    by_cases hd : active t D
    · exact Or.inl hd
    · by_cases hp : active t P
      · exact Or.inr (Or.inl (fun x => (h x (Or.inr hp)).resolve_right hd))
      · exact Or.inr (Or.inr ⟨hp,fun x hx => (h x (Or.inl hx)).resolve_right hd⟩)

theorem simulate (v : V) (t : Finset V → Bool) {F : Set (Clause V)} {W π}
    (h : Log (linOfClause '' F) W π) (emp : (∅ : LinClause V)∈π)
    (wins : ∀ p ∈ W, passes t p.1 p.2) :
    ∃ ρ, IsRefutation F ρ ∧ ρ.length+W.length ≤ π.length := by
  classical
  let M := mapped v t
  obtain ⟨ρ,der,len,track⟩ := compile h (imageC M) (fun A _ => plainLift A M)
    (validRes M (signOK v t)) (fun p hp => (exactTest v t p.1 p.2).1 (wins p hp))
  refine ⟨ρ,⟨der,?_⟩,len⟩
  have hit := track ∅ emp
  rw [imageEmpty] at hit
  rcases hit with imp|⟨A,ha,sub⟩
  · exact False.elim (by simpa [ClauseSat] using imp (fun _ => false))
  · have e : A=∅ := Finset.Subset.antisymm sub (Finset.empty_subset _)
    exact e ▸ ha

abbrev Cell := Fin 5 × Fin 4

theorem obstruction {π : List (LinClause Cell)} (h : IsLinRefutation (PHP 5 4) π)
    (small : π.length ≤ 106) :
    ∀ W, Log (linOfClause '' PHP 5 4) W π → ∀ t : Finset Cell → Bool,
      ∃ p∈W, ¬ passes t p.1 p.2 := by
  classical
  intro W hw t
  by_contra! all
  obtain ⟨ρ,hr,size⟩ := simulate ((0,0) : Cell) t hw h.2 all
  exact PEqualNP.Outside.L_pcx_162 ⟨ρ,hr,by omega⟩

theorem affineCover {π : List (LinClause Cell)} (h : IsLinRefutation (PHP 5 4) π)
    (small : π.length ≤ 106) {W} (hw : Log (linOfClause '' PHP 5 4) W π)
    (x : Cell → Bool) :
    ∃ p∈W, (∀ q∈extras p.2, ¬ LinEqSat x q) ∧ ¬ (∀ a, ClauseSat a (plainPart p.2)) := by
  classical
  let u : Finset Cell → Bool := fun S => decide (Odd (S.filter (fun i => x i=true)).card)
  obtain ⟨p,hp,fail⟩ := obstruction h small W hw u
  refine ⟨p,hp,?_,fun plain => fail (Or.inr (Or.inl plain))⟩
  intro q hq hsat
  apply fail
  left
  refine ⟨q,hq,?_⟩
  rcases q with ⟨S,b⟩
  cases b <;> simp_all [u,LinEqSat]

end PEqualNP.Outside.L_pcx_178_select

namespace PEqualNP.Outside.L_pcx_178_select
open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_119_compile PEqualNP.Outside.L_pcx_119_image

noncomputable section
open Classical
set_option maxRecDepth 8000

abbrev Tests := Finset Cell → Bool
abbrev Entry := LinClause Cell × LinClause Cell

def fails (p : Entry) : Finset Tests :=
  Finset.univ.filter (fun t => ¬ passes t p.1 p.2)

def unionFails : List Entry → Finset Tests
  | [] => ∅
  | p::ps => fails p ∪ unionFails ps

theorem memFails (p : Entry) (t : Tests) : t∈fails p ↔ ¬passes t p.1 p.2 := by
  simp only [fails,Finset.mem_filter,Finset.mem_univ,true_and]

theorem inside {p : Entry} {t : Tests} (hp : t∈fails p) : ¬ active t p.2 := by
  intro h
  exact (memFails p t).mp hp (Or.inl h)

theorem member {p : Entry} {t : Tests} {W : List Entry} (hp : p∈W) (ht : t∈fails p) : t∈unionFails W := by
  induction W with
  | nil => simp at hp
  | cons w ws ih =>
    change t∈fails w ∪ unionFails ws
    rcases List.mem_cons.mp hp with eq|hr
    · exact Finset.mem_union_left _ (eq ▸ ht)
    · exact Finset.mem_union_right _ (ih hr)

theorem budget (a B : Nat) (W : List Entry) (bounded : ∀ p∈W, a*(fails p).card≤B) :
    a*(unionFails W).card ≤ W.length*B := by
  induction W with
  | nil => simp [unionFails]
  | cons w ws ih =>
    have lo := ih (fun p hp => bounded p (List.mem_cons_of_mem _ hp))
    have first := bounded w (by simp)
    have hu := Nat.mul_le_mul_left a (Finset.card_union_le (fails w) (unionFails ws))
    rw [Nat.mul_add] at hu
    change a*(fails w ∪ unionFails ws).card ≤ (ws.length+1)*B
    rw [Nat.add_mul,one_mul]
    omega

def pencil (q : Fin 5 → Finset Cell) (r : Fin 5 → Bool) (t : Tests) : Tests :=
  fun k => if h : ∃i, q i=k then r (Classical.choose h) else t k

theorem pencilAt (q : Fin 5 → Finset Cell) (inj : Function.Injective q)
    (r : Fin 5 → Bool) (t : Tests) (i : Fin 5) : pencil q r t (q i)=r i := by
  let h : ∃j, q j=q i := ⟨i,rfl⟩
  have eq := inj (Classical.choose_spec h)
  simp [pencil,h,eq]

def five (p : Entry) : Prop :=
  ∃ (q : Fin 5 → Finset Cell) (b : Fin 5 → Bool),
    Function.Injective q ∧ ∀ i, (q i,b i)∈extras p.2

theorem multiplicity (p : Entry) (h : five p) : 32*(fails p).card ≤ Fintype.card Tests := by
  obtain ⟨q,b,inj,eqs⟩ := h
  let paint : (Fin 5 → Bool) × ↥(fails p) → Tests := fun v => pencil q v.1 v.2.val
  have inject : Function.Injective paint := by
    rintro ⟨a,x⟩ ⟨c,y⟩ eq
    have left : a=c := by
      funext i
      have e := congrFun eq (q i)
      simpa only [paint,pencilAt q inj] using e
    have right : x=y := by
      apply Subtype.ext
      funext k
      by_cases hk : ∃i, q i=k
      · obtain ⟨i,rfl⟩ := hk
        have nx : x.val (q i) ≠ b i := fun h => inside (p:=p) (t:=x.val) x.property ⟨(q i,b i),eqs i,h⟩
        have ny : y.val (q i) ≠ b i := fun h => inside (p:=p) (t:=y.val) y.property ⟨(q i,b i),eqs i,h⟩
        cases ea : x.val (q i) <;> cases ec : y.val (q i) <;> cases eb : b i <;> simp_all
      · have e := congrFun eq k
        simpa only [paint,pencil,dif_neg hk] using e
    exact Prod.ext left right
  have le := Fintype.card_le_of_injective paint inject
  calc
    32*(fails p).card = Fintype.card ((Fin 5 → Bool) × ↥(fails p)) := by
      simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
        Fintype.card_coe, (show (2:Nat)^5 = 32 by decide)]
    _ ≤ Fintype.card Tests := le

theorem narrow {π : List (LinClause Cell)} (h : IsLinRefutation (PHP 5 4) π)
    (small : π.length≤106) {W : List Entry} (hist : Log (linOfClause '' PHP 5 4) W π)
    (short : W.length<32) : ∃ p∈W, ¬ five p ∧ (fails p).Nonempty := by
  classical
  by_contra none
  have wide : ∀ p∈W,32*(fails p).card≤Fintype.card Tests := by
    intro p hp
    by_cases nonempty : (fails p).Nonempty
    · apply multiplicity p
      by_contra bad
      exact none ⟨p,hp,bad,nonempty⟩
    · have e := Finset.not_nonempty_iff_eq_empty.mp nonempty
      simp [e]
  have covers : unionFails W=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    obtain ⟨p,hp,ht⟩ := obstruction h small W hist t
    exact member (p:=p) (t:=t) hp ((memFails p t).mpr ht)
  have total := budget 32 (Fintype.card Tests) W wide
  rw [covers,Finset.card_univ] at total
  have pos : 0 < Fintype.card Tests := Fintype.card_pos
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_right short pos)) total

end
end PEqualNP.Outside.L_pcx_178_select

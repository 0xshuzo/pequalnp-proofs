import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_121_phantom
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
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


abbrev Model (V : Type) := Finset V → Bool
def abstractSat (z : Model V) (C : LinClause V) := ∃ q∈C,z q.1=q.2

theorem abstractRes {z : Model V} {C D R : LinClause V} (r : IsLinResolvent C D R)
    (left : abstractSat z C) (right : abstractSat z D) : abstractSat z R := by
  obtain ⟨f,_,_,rfl⟩ := r
  cases val : z f with
  | false =>
    obtain ⟨e,mem,v⟩ := right
    have ne : e ≠ (f,true) := by intro eq; subst e; simp [val] at v
    exact ⟨e,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,mem⟩),v⟩
  | true =>
    obtain ⟨e,mem,v⟩ := left
    have ne : e ≠ (f,false) := by intro eq; subst e; simp [val] at v
    exact ⟨e,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,mem⟩),v⟩

theorem allGood {F : Set (LinClause V)} {W π} (d : Log F W π) (z : Model V)
    (raw : ∀C∈F,abstractSat z C)
    (ok : ∀p∈W,abstractSat z p.1 → abstractSat z p.2) : ∀C∈π,abstractSat z C := by
  induction d with
  | nil => simp
  | @ax W π C _ member ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl|old
    · exact raw _ member
    · exact ih ok D old
  | @res W π C D R _ hc hd hr ih =>
    intro T ht
    rcases List.mem_cons.mp ht with rfl|old
    · exact abstractRes hr (ih ok _ hc) (ih ok _ hd)
    · exact ih ok T old
  | @weak W π C D _ hc _ ih =>
    have prior := ih (fun p hp => ok p (List.mem_cons_of_mem _ hp))
    intro T ht
    rcases List.mem_cons.mp ht with rfl|old
    · exact ok _ List.mem_cons_self (prior _ hc)
    · exact prior T old

theorem breakNeeded {F : Set (LinClause V)} {W π} (d : Log F W π)
    (empty : (∅ : LinClause V)∈π) (z : Model V) (raw : ∀C∈F,abstractSat z C) :
    ∃p∈W, abstractSat z p.1 ∧ ¬abstractSat z p.2 := by
  classical
  by_contra! none
  have no := allGood d z raw (fun p hp h => none p hp h) ∅ empty
  simpa [abstractSat] using no

theorem actualWeak {F : Set (LinClause V)} {W π} (h : Log F W π) :
    ∀p∈W, ∀x,LinClauseSat x p.1 → LinClauseSat x p.2 := by
  induction h with
  | nil => simp
  | ax _ _ ih => exact ih
  | res _ _ _ _ ih => exact ih
  | @weak W π C D _ _ step ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl|old
    · exact step
    · exact ih _ old

theorem oneFault {F : Set (LinClause V)} {W π} (d : Log F W π) (empty : (∅ : LinClause V)∈π)
    (one : W.length≤1) {z₀ : Model V} (sat₀ : ∀C∈F,abstractSat z₀ C) :
    ∃ C D : LinClause V, (C,D)∈W ∧ (∀x,LinClauseSat x C → LinClauseSat x D) ∧
      ∀ z : Model V, (∀c∈F,abstractSat z c) → abstractSat z C ∧ ¬abstractSat z D := by
  obtain ⟨p,mem,_,_⟩ := breakNeeded d empty z₀ sat₀
  have list : W=[p] := by
    cases W with
    | nil => cases mem
    | cons a t =>
      have len : t.length=0 := by
        change t.length+1≤1 at one
        omega
      have nil : t=[] := List.length_eq_zero_iff.mp len
      subst t
      have eq : p=a := by simpa using mem
      subst a
      rfl
  refine ⟨p.1,p.2,mem,actualWeak d p mem,?_⟩
  intro z sat
  obtain ⟨q,hq,a,b⟩ := breakNeeded d empty z sat
  have eq : q=p := by simpa [list] using hq
  subst q
  exact ⟨a,b⟩

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


theorem realizeAtom (z : Model V) (zero : z ∅=false) (q : LinEq V)
    (on : z q.1=q.2) : ∃x : V→Bool, LinEqSat x q := by
  classical
  by_cases sat : LinEqSat (fun _=>false) q
  · exact ⟨_,sat⟩
  · by_cases h : q.1.Nonempty
    · obtain ⟨v,hv⟩ := h
      exact ⟨_,(opposite hv q.2).2 sat⟩
    · have nil : q.1=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have off : q.2=false := by simpa [nil,zero] using on.symm
      exfalso
      apply sat
      simp [LinEqSat,nil,off,Nat.odd_iff]

theorem twoFaults {F : Set (LinClause V)} {W π} (d : Log F W π) (empty : (∅ : LinClause V)∈π)
    {z₀ : Model V} (zero : z₀ ∅=false) (sat₀ : ∀C∈F,abstractSat z₀ C)
    (spread : ∀q : LinEq V,∃z : Model V,(∀C∈F,abstractSat z C) ∧ z q.1=q.2) : 2≤W.length := by
  by_contra! small
  obtain ⟨C,D,_,rule,breaks⟩ := oneFault d empty (by omega) sat₀
  have none : ∀q∈D,False := by
    intro q hq
    obtain ⟨z,bank,on⟩ := spread q
    exact (breaks z bank).2 ⟨q,hq,on⟩
  obtain ⟨q,mem,on⟩ := (breaks z₀ sat₀).1
  obtain ⟨x,hx⟩ := realizeAtom z₀ zero q on
  obtain ⟨e,he,_⟩ := rule x ⟨q,mem,hx⟩
  exact none e he

def mentioned (F : Set (LinClause V)) (f : Finset V) :=
  ∃c∈F,∃q∈c,q.1=f
theorem modelsSpread {F : Set (LinClause V)} {z₀ : Model V} (sat₀ : ∀C∈F,abstractSat z₀ C)
    (two : ∀f,mentioned F f → ∀ b : Bool,∃z : Model V,(∀C∈F,abstractSat z C) ∧ z f=b) :
    ∀q : LinEq V,∃z : Model V,(∀C∈F,abstractSat z C) ∧ z q.1=q.2 := by
  classical
  intro q
  by_cases present : mentioned F q.1
  · exact two q.1 present q.2
  · let z : Model V := fun f => if f=q.1 then q.2 else z₀ f
    refine ⟨z,?_,by simp [z]⟩
    intro c hc
    obtain ⟨e,he,val⟩ := sat₀ c hc
    have ne : e.1≠q.1 := fun eq => present ⟨c,hc,e,he,eq⟩
    exact ⟨e,he,by simpa [z,ne] using val⟩


def everyBit (F : Set (LinClause V)) :=
  ∀q : LinEq V,∃z : Model V,(∀C∈F,abstractSat z C) ∧ z q.1=q.2

theorem adjust {F : Set (LinClause V)} {f : Finset V} (fresh : ¬mentioned F f)
    {z : Model V} (sat : ∀C∈F,abstractSat z C) (b : Bool) :
    ∀C∈F,abstractSat (fun t => if t=f then b else z t) C := by
  intro C hC
  obtain ⟨e,he,v⟩ := sat C hC
  have ne : e.1≠f := fun h=>fresh ⟨C,hC,e,he,h⟩
  exact ⟨e,he,by simpa [ne] using v⟩

theorem freshOr {F : Set (LinClause V)} (free : everyBit F)
    {D : LinClause V} {p r : LinEq V} (present : p∈D) (other : r∈D) (ne : r≠p)
    (fresh : ¬mentioned F p.1) : everyBit (insert D F) := by
  classical
  intro q
  by_cases same : q.1=p.1
  · obtain ⟨z,sat,hit⟩ := free r
    let z' : Model V := fun f => if f=p.1 then q.2 else z f
    refine ⟨z',?_,by simp [z',same]⟩
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl|before
    · by_cases bits : q.2=p.2
      · exact ⟨p,present,by simp [z',bits]⟩
      · by_cases eq : r.1=p.1
        · have nt : r.2≠p.2 := fun h=>ne (Prod.ext eq h)
          have v : q.2=r.2 := by cases a:q.2 <;> cases b:r.2 <;> cases c:p.2 <;> simp_all
          exact ⟨r,other,by simp [z',eq,v]⟩
        · exact ⟨r,other,by simpa [z',eq] using hit⟩
    · exact adjust fresh sat _ c before
  · obtain ⟨z,sat,hit⟩ := free q
    let z' : Model V := fun f => if f=p.1 then p.2 else z f
    refine ⟨z',?_,by simpa [z',same] using hit⟩
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl|before
    · exact ⟨p,present,by simp [z']⟩
    · exact adjust fresh sat _ c before

def keep (D : LinClause V) (q : LinClause V × LinClause V) : Bool := decide (q.2≠D)
theorem promote {F : Set (LinClause V)} {W π} (d : Log F W π) (A : LinClause V) :
    Log (insert A F) (W.filter (keep A)) π := by
  classical
  induction d with
  | nil => exact .nil
  | ax _ h ih => exact .ax ih (Set.mem_insert_of_mem _ h)
  | res _ a b r ih => exact .res ih a b r
  | @weak W π C D _ cm w ih =>
    by_cases eq : D=A
    · subst D
      simpa [keep] using (Log.ax ih (Set.mem_insert A F))
    · simpa [keep,eq] using (Log.weak ih cm w)

theorem filterDrops (D : LinClause V) (W : List (LinClause V × LinClause V))
    {C : LinClause V} (site : (C,D)∈W) : (W.filter (keep D)).length<W.length := by
  induction W with
  | nil => simp at site
  | cons a l ih =>
    by_cases take : keep D a=true
    · have tail : (C,D)∈l := by
        rcases List.mem_cons.mp site with eq|old
        · subst a; simp [keep] at take
        · exact old
      simpa [take] using ih tail
    · have small := List.length_filter_le (keep D) l
      simp only [List.filter_cons,take,ite_false,List.length_cons]
      omega

theorem freshCanOnlyBeUnit {F : Set (LinClause V)} (free : everyBit F)
    {W π} (d : Log F W π) (empty : (∅ : LinClause V)∈π) (few : W.length≤2)
    {C D : LinClause V} (site : (C,D)∈W) {p : LinEq V} (hd : p∈D)
    (fresh : ¬mentioned F p.1) : D={p} := by
  classical
  apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hd)
  intro r hr
  by_contra nmem
  have ne : r≠p := fun eq=>nmem (by simp [eq])
  have full := freshOr free hd hr ne fresh
  obtain ⟨z,satz,off⟩ := full (∅,false)
  have two := twoFaults (promote d D) empty off satz full
  have less := filterDrops D W site
  omega

end PEqualNP.Outside.L_pcx_121_phantom

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

abbrev Cell := Fin 4 × Fin 3
def form9 (i : Fin 9) : Finset Cell := #[({(0,0)} : Finset Cell),({(0,1)} : Finset Cell),({(1,0)} : Finset Cell),({(0,0),(1,0)} : Finset Cell),({(1,1)} : Finset Cell),({(1,2)} : Finset Cell),({(2,1)} : Finset Cell),({(3,0)} : Finset Cell),({(3,1)} : Finset Cell)][i.val]!
def lineList (i : Fin 10) : List (LinEq Cell) := (#[[(form9 2,true),(form9 4,true),(form9 5,true)],[(form9 0,false),(form9 2,false)],[(form9 0,false),(form9 7,false)],[(form9 2,false),(form9 7,false)],[(form9 1,false),(form9 4,false)],[(form9 1,false),(form9 6,false)],[(form9 1,false),(form9 8,false)],[(form9 7,true),(form9 3,false)],[(form9 5,false),(form9 6,true),(form9 8,true)],[(form9 0,true),(form9 1,true),(form9 3,true)]] : Array (List (LinEq Cell)))[i.val]!
def row10 (i : Fin 10) : LinClause Cell := (lineList i).toFinset
def code5 (k : Fin 5) : Nat := #[6,17,152,97,273][k.val]!

def model5 (k : Fin 5) (f : Finset Cell) : Bool :=
  (List.ofFn (fun i : Fin 9 => (form9 i,(code5 k).testBit i.val))).any
    (fun e => decide (e.1=f) && e.2)
def listed (i : Fin 10) : Bool :=
  (lineList i).all (fun q=>(List.ofFn form9).contains q.1)
def accepts (k : Fin 5) (i : Fin 10) := (lineList i).any (fun q=>decide (model5 k q.1=q.2))

set_option maxHeartbeats 3000000 in
theorem listedAll : ∀i,listed i=true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem modelBank : ∀k i,accepts k i=true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem modelVaries : ∀i : Fin 9,∀b : Bool, ∃k : Fin 5, model5 k (form9 i)=b := by decide +kernel

theorem bankSat (k : Fin 5) : ∀c∈Set.range row10, abstractSat (model5 k) c := by
  rintro c ⟨i,rfl⟩
  obtain ⟨q,hq,on⟩ := List.any_eq_true.mp (modelBank k i)
  exact ⟨q,by simpa [row10] using hq,of_decide_eq_true on⟩

theorem tenNeedsTwo {W π} (d : Log (Set.range row10) W π) (empty : (∅ : LinClause Cell)∈π) :
    2≤W.length := by
  apply twoFaults d empty (z₀:=model5 0) (by decide +kernel) (bankSat 0)
  apply modelsSpread (bankSat 0)
  intro f present b
  obtain ⟨c,⟨i,rfl⟩,q,hq,rfl⟩ := present
  have hl := List.all_eq_true.mp (listedAll i) q (by simpa [row10] using hq)
  have member : q.1 ∈ List.ofFn form9 := by simpa using hl
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp member
  obtain ⟨k,v⟩ := modelVaries j b
  exact ⟨model5 k,bankSat k,hj ▸ v⟩
end PEqualNP.Outside.L_pcx_121_phantom

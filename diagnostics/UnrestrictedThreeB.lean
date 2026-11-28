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
      have off : keep D a=false := by cases v:keep D a <;> simp_all
      simpa [off] using (Nat.lt_succ_of_le small)

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


theorem unread {a : V→Bool} {f : Finset V} {v : V} (hv : v∉f) (b : Bool) :
    LinEqSat (flip a v) (f,b) ↔ LinEqSat a (f,b) := by
  have eq : f.filter (fun w=>flip a v w=true)=f.filter (fun w=>a w=true) := by
    ext w
    by_cases e:w=v
    · subst w; simp [hv]
    · simp [flip,e]
  unfold LinEqSat
  change (Odd (f.filter _).card ↔ b=true) ↔ _
  rw [eq]

theorem forceValue (x : V→Bool) {f : Finset V} {v : V} (inside : v∈f) (b : Bool) :
    LinEqSat x (f,b) ∨ LinEqSat (flip x v) (f,b) := by
  classical
  by_cases h:LinEqSat x (f,b)
  · exact Or.inl h
  · exact Or.inr ((opposite inside b).2 h)

theorem falseValue {f : Finset V} (non : f.Nonempty) (b : Bool) : ∃x,¬LinEqSat x (f,b) := by
  classical
  obtain ⟨v,hv⟩ := non
  let x : V→Bool := fun _=>false
  by_cases h:LinEqSat x (f,b)
  · exact ⟨flip x v,fun bad=>(opposite hv b).1 bad h⟩
  · exact ⟨x,h⟩

theorem atomIndependent (z : Model V) (zero : z ∅=false)
    (e p : LinEq V) (yes : z e.1=e.2) (no : z p.1≠p.2) :
    ∃x,LinEqSat x e ∧ ¬LinEqSat x p := by
  classical
  obtain ⟨f,s⟩ := e
  obtain ⟨g,t⟩ := p
  change z f=s at yes
  change z g≠t at no
  obtain ⟨x,hx⟩ := realizeAtom z zero (f,s) yes
  by_cases left : g⊆f
  · by_cases right : f⊆g
    · have eq := Finset.Subset.antisymm right left
      subst g
      refine ⟨x,hx,?_⟩
      intro hp
      have signs : (s=true ↔ t=true) := hx.symm.trans hp
      cases hs:s <;> cases ht:t <;> simp_all
    · obtain ⟨v,vf,vg⟩ := Finset.not_subset.mp right
      by_cases gn:g.Nonempty
      · obtain ⟨y,ny⟩ := falseValue gn t
        rcases forceValue y vf s with h|h
        · exact ⟨y,h,ny⟩
        · exact ⟨_,h,fun a=>ny ((unread vg _).1 a)⟩
      · have eg : g=∅ := Finset.not_nonempty_iff_eq_empty.mp gn
        subst g
        refine ⟨x,hx,?_⟩
        cases t <;> simp_all [LinEqSat,Nat.odd_iff]
  · obtain ⟨v,vg,vf⟩ := Finset.not_subset.mp left
    by_cases h:LinEqSat x (g,t)
    · exact ⟨flip x v,(unread vf s).2 hx,fun bad=>(opposite vg t).1 bad h⟩
    · exact ⟨x,hx,h⟩

theorem unitInert {C : LinClause V} (p : LinEq V) (w : ∀x,LinClauseSat x C → LinClauseSat x {p})
    {z : Model V} (zero : z ∅=false) (yes : abstractSat z C) : abstractSat z {p} := by
  classical
  by_cases good:z p.1=p.2
  · exact ⟨p,by simp,good⟩
  obtain ⟨e,hm,on⟩:=yes
  obtain ⟨x,hs,fail⟩:=atomIndependent z zero e p on good
  obtain ⟨q,hq,s⟩:=w x ⟨e,hm,hs⟩
  have eq : q=p := Finset.mem_singleton.mp hq
  exact (fail (eq ▸ s)).elim

def regularSpread (F : Set (LinClause V)) := ∀p : LinEq V,p.1≠∅ →
    ∃z : Model V,z ∅=false ∧ (∀c∈F,abstractSat z c) ∧ z p.1=p.2

theorem chooseOne {F : Set (LinClause V)} (rich : regularSpread F) {z₀ : Model V} (zero : z₀ ∅=false)
    (bank : ∀c∈F,abstractSat z₀ c) {C D : LinClause V} (w : ∀x,LinClauseSat x C → LinClauseSat x D) :
    ∃z : Model V,z ∅=false ∧ (∀c∈F,abstractSat z c) ∧ (abstractSat z C → abstractSat z D) := by
  classical
  by_cases live:∃q∈D,q.1≠∅
  · obtain ⟨q,hq,non⟩:=live
    obtain ⟨z,h,model,on⟩:=rich q non
    exact ⟨z,h,model,fun _=>⟨q,hq,on⟩⟩
  · refine ⟨z₀,zero,bank,?_⟩
    rintro ⟨p,hp,on⟩
    obtain ⟨x,yes⟩ := realizeAtom z₀ zero p on
    obtain ⟨q,hq,hit⟩ := w x ⟨p,hp,yes⟩
    have eq : q.1=∅ := by by_contra ne; exact live ⟨q,hq,ne⟩
    exact ⟨q,hq,by cases h:q.2 <;> simp_all [LinEqSat,Nat.odd_iff]⟩

theorem regularOfFree {F : Set (LinClause V)} (free : everyBit F) (nz : ¬mentioned F ∅) :
    regularSpread F := by
  intro q non
  obtain ⟨z,bank,ok⟩:=free q
  refine ⟨fun f=>if f=∅ then false else z f,by simp,adjust nz bank false,by simpa [non] using ok⟩

theorem noPaidUnit {F : Set (LinClause V)} {W π} (d : Log F W π)
    (empty : (∅ : LinClause V)∈π) (few : W.length≤2) (free : everyBit F)
    (nz : ¬mentioned F ∅) {C : LinClause V} {p : LinEq V} (paid : (C,{p})∈W) : False := by
  classical
  obtain ⟨base,bGood,zero⟩ := free (∅,false)
  have h0 : base ∅=false := zero
  have rich := regularOfFree free nz
  
  let rest := W.erase (C,{p})
  have small : rest.length≤1 := by
    have drop := List.length_erase_of_mem paid
    dsimp [rest]; omega
  have single : ∃A B : LinClause V, (∀x,LinClauseSat x A→LinClauseSat x B) ∧
      ∀q∈rest,q=(A,B) := by
    cases e:rest with
    | nil => exact ⟨∅,∅,fun _ h=>h,by simp [e]⟩
    | cons q l =>
      have tail : l=[] := by
        apply List.length_eq_zero_iff.mp
        rw [e] at small
        change l.length+1≤1 at small
        omega
      subst l
      have mem : q∈rest := by simp [e]
      exact ⟨q.1,q.2,actualWeak d q (List.mem_of_mem_erase mem),by simp [e]⟩
  obtain ⟨A,B,rule,restEq⟩:=single
  obtain ⟨z,hz,bz,good⟩:=chooseOne rich h0 bGood rule
  have all := allGood d z bz (by
    intro q hq
    by_cases eq:q=(C,{p})
    · subst q;exact unitInert p (actualWeak d _ paid) hz
    · have inR : q∈rest := (List.mem_erase_of_ne eq).2 hq
      have e := restEq q inR
      subst q;exact good)
  simpa [abstractSat] using all ∅ empty

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
def probes (i : Fin 3) : Nat := #[6,17,152][i.val]!
def repairRow (a b : Fin 3) (i : Fin 9) : Nat := #[0,0,0,0,0,0,0,0,0,0,2,9,0,0,0,0,0,0,0,2,8,0,0,0,0,0,0,9,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,17,16,16,16,16,16,16,16,16,0,0,0,8,16,0,0,512,0,16,16,16,17,16,16,16,528,16,0,0,0,0,0,0,0,0,0][((a.val*3+b.val)*9+i.val)]!

def digital (n : Nat) (v : Cell) := n.testBit (3*v.1.val+v.2.val)
def old (C : LinClause Cell) := ∀q∈C,∃i : Fin 9,form9 i=q.1
def test3 (a : Fin 3) (f : Finset Cell) : Bool :=
  (List.ofFn (fun i : Fin 9 => (form9 i,(probes a).testBit i.val))).any
    (fun e => decide (e.1=f) && e.2)
def testOK (k : Fin 3) (i : Fin 10) := (lineList i).any (fun q=>decide (test3 k q.1=q.2))
theorem testRows : ∀k i,testOK k i=true := by decide +kernel
theorem testBank (k : Fin 3) : ∀c∈Set.range row10, abstractSat (test3 k) c := by
  rintro c ⟨i,rfl⟩
  obtain ⟨q,hq,on⟩ := List.any_eq_true.mp (testRows k i)
  exact ⟨q,by simpa [row10] using hq,of_decide_eq_true on⟩
def testReal (a b : Fin 3) (i j : Fin 9) : Bool :=
  decide (Odd (((form9 j).filter (fun v=>digital (repairRow a b i) v=true)).card))
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem repairs : ∀ a b : Fin 3, a≠b → ∀ i j : Fin 9,
    (j=i ∨ test3 a (form9 j)=test3 b (form9 j)) →
        testReal a b i j=test3 a (form9 j) := by decide +kernel

theorem incompat {C D : LinClause Cell} (cOld : old C) (dOld : old D)
    (w : ∀x,LinClauseSat x C → LinClauseSat x D) {a b : Fin 3} (ne : a≠b)
    (one : abstractSat (test3 a) C ∧ ¬abstractSat (test3 a) D)
    (two : abstractSat (test3 b) C ∧ ¬abstractSat (test3 b) D) : False := by
  obtain ⟨q,qc,hit⟩ := one.1
  obtain ⟨i,e⟩ := cOld q qc
  have ri := repairs a b ne i i (Or.inl rfl)
  have yes : LinEqSat (digital (repairRow a b i)) q := by
    have v : testReal a b i i=q.2 := ri.trans (by simpa only [e] using hit)
    unfold LinEqSat
    rw [←e]
    simpa [testReal] using (show (testReal a b i i=true ↔ q.2=true) by rw [v])
  obtain ⟨r,rd,sat⟩ := w _ ⟨q,qc,yes⟩
  obtain ⟨j,er⟩ := dOld r rd
  have na : test3 a r.1≠r.2 := fun h=>one.2 ⟨r,rd,h⟩
  have nb : test3 b r.1≠r.2 := fun h=>two.2 ⟨r,rd,h⟩
  have same : test3 a r.1=test3 b r.1 := by
    cases h:test3 a r.1 <;> cases k:test3 b r.1 <;> cases l:r.2 <;> simp_all
  have rr := repairs a b ne i j (Or.inr (by simpa only [er] using same))
  have real : testReal a b i j=r.2 := by
    unfold LinEqSat at sat
    rw [←er] at sat
    cases h:r.2 <;> simp_all [testReal]
  exact na (by rw [←er,←rr,real])

theorem threeInBank {W π} (d : Log (Set.range row10) W π)
    (empty : (∅ : LinClause Cell)∈π) (locality : ∀p∈W,old p.1 ∧ old p.2) : 3≤W.length := by
  classical
  have pick (k : Fin 3) := breakNeeded d empty (test3 k) (testBank k)
  choose step member first last using pick
  have inj : Function.Injective step := by
    intro a b eq
    by_contra ne
    have p:=member a
    have h:=actualWeak d (step a) p
    exact incompat (locality _ p).1 (locality _ p).2 h ne ⟨first a,last a⟩
      (eq ▸ And.intro (first b) (last b))
  let into (k : Fin 3) : W.toFinset := ⟨step k,List.mem_toFinset.mpr (member k)⟩
  have embed : Function.Injective into := fun _ _ e=>inj (congrArg Subtype.val e)
  have card := Fintype.card_le_of_injective into embed
  have small := List.toFinset_card_le W
  simp only [Fintype.card_fin,Fintype.card_coe] at card
  omega

theorem bankFree : everyBit (Set.range row10) := by
  apply modelsSpread (bankSat 0)
  intro f present b
  obtain ⟨c,⟨i,rfl⟩,q,hq,rfl⟩ := present
  have hl := List.all_eq_true.mp (listedAll i) q (by simpa [row10] using hq)
  have member : q.1 ∈ List.ofFn form9 := by simpa using hl
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp member
  obtain ⟨k,v⟩ := modelVaries j b
  exact ⟨model5 k,bankSat k,hj ▸ v⟩

theorem baseOld {c : LinClause Cell} (hc : c∈Set.range row10) : old c := by
  obtain ⟨i,rfl⟩:=hc
  intro q hq
  have hl:=List.all_eq_true.mp (listedAll i) q (by simpa [row10] using hq)
  exact List.mem_ofFn.mp (by simpa using hl)

theorem knownEquations {f : Finset Cell} (src : mentioned (Set.range row10) f) : ∃i,form9 i=f := by
  obtain ⟨c,hc,q,hq,rfl⟩:=src
  exact baseOld hc _ hq

theorem nonzero9 : ∀i : Fin 9,form9 i≠∅ := by decide +kernel

theorem closedForms {F : Set (LinClause Cell)} {W π} (d : Log F W π)
    (base : ∀c∈F,old c) (out : ∀p∈W, old p.2) : (∀c∈π,old c) ∧ (∀p∈W,old p.1) := by
  induction d with
  | nil => simp
  | @ax W π C _ h ih =>
    obtain ⟨prior,sources⟩:=ih out
    exact ⟨by
      intro c hc
      rcases List.mem_cons.mp hc with eq|mem
      · subst c;exact base _ h
      · exact prior _ mem,sources⟩
  | @res W π C D R _ hc hd hr ih =>
    obtain ⟨prior,sources⟩:=ih out
    refine ⟨?_,sources⟩
    intro c mem
    rcases List.mem_cons.mp mem with eq|past
    · subst c
      obtain ⟨pivot,_,_,rfl⟩:=hr
      intro q hq
      rcases Finset.mem_union.mp hq with m|m
      · exact prior _ hc _ (Finset.mem_of_mem_erase m)
      · exact prior _ hd _ (Finset.mem_of_mem_erase m)
    · exact prior _ past
  | @weak W π C D _ hc _ ih =>
    obtain ⟨prior,sources⟩:=ih (fun q h=>out q (List.mem_cons_of_mem _ h))
    constructor
    · intro c h
      rcases List.mem_cons.mp h with eq|mem
      · subst c;exact out (C,D) List.mem_cons_self
      · exact prior _ mem
    · intro p h
      rcases List.mem_cons.mp h with eq|mem
      · subst p;exact prior _ hc
      · exact sources _ mem

theorem unrestrictedThree {W π} (d : Log (Set.range row10) W π)
    (empty : (∅ : LinClause Cell)∈π) : 3≤W.length := by
  classical
  by_contra! small
  have few : W.length≤2 := by omega
  have nz : ¬mentioned (Set.range row10) ∅ := by
    intro old
    obtain ⟨i,h⟩:=knownEquations old
    exact nonzero9 i h
  have outs : ∀v∈W,old v.2 := by
    rintro ⟨C,D⟩ paid p hp
    by_contra unknown
    have fresh : ¬mentioned (Set.range row10) p.1 := fun hm=>unknown (knownEquations hm)
    have eq := freshCanOnlyBeUnit bankFree d empty few paid hp fresh
    subst D
    exact noPaidUnit d empty few bankFree nz paid
  have localities := closedForms d (fun _ h=>baseOld h) outs
  exact (Nat.not_lt_of_ge (threeInBank d empty (fun p hp=>⟨localities.2 p hp,outs p hp⟩))) small

end PEqualNP.Outside.L_pcx_121_phantom

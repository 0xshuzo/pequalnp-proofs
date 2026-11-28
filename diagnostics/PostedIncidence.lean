import PEqualNP.Defs
open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_178.SampleLedger

variable {V : Type} [DecidableEq V]
abbrev Bank (V : Type) := Set (LinClause V)
def Hits (T : Finset (LinClause V)) (a : V → Bool) := ∃ c ∈ T, ¬ LinClauseSat a c

variable {I : Type}

def Certified (pts : I→V→Bool) (F : Bank V) (b : Nat) (G : Bank V) : Prop :=
  ∀ T : Finset (LinClause V), (∀ c ∈ T, c ∈ G) →
    ∃ U : Finset (LinClause V), (∀ c ∈ U, c ∈ F) ∧
      U.card ≤ T.card+b ∧ ∀ i, Hits T (pts i) → Hits U (pts i)

theorem starting (pts : I→V→Bool) (F : Bank V) : Certified pts F 0 F := by
  intro T inc
  exact ⟨T,inc,by omega,fun _ x => x⟩

theorem add {pts : I→V→Bool} {F G : Bank V} {b k : Nat} {R : LinClause V}
    (old : Certified pts F b G) (parents : Finset (LinClause V))
    (known : ∀ c ∈ parents, c ∈ G) (fee : parents.card ≤ k+1)
    (sound : ∀ i, ¬ LinClauseSat (pts i) R → Hits parents (pts i)) :
    Certified pts F (b+k) (insert R G) := by
  classical
  intro T inc
  by_cases hr : R ∈ T
  · let S := (T.erase R) ∪ parents
    have sub : ∀ c ∈ S, c ∈ G := by
      intro c hc
      rcases Finset.mem_union.mp hc with h | h
      · have e := Finset.mem_erase.mp h
        exact (Set.mem_insert_iff.mp (inc c e.2)).resolve_left e.1
      · exact known c h
    obtain ⟨U,uf,sz,covers⟩ := old S sub
    refine ⟨U,uf,?_,?_⟩
    · have ub := Finset.card_union_le (T.erase R) parents
      have er := Finset.card_erase_of_mem hr
      change U.card ≤ ((T.erase R) ∪ parents).card+b at sz
      have pos := Finset.card_pos.mpr ⟨R,hr⟩
      omega
    · intro a h
      apply covers a
      obtain ⟨c,ct,bad⟩ := h
      by_cases eq : c=R
      · subst c
        obtain ⟨d,dp,df⟩ := sound a bad
        exact ⟨d,Finset.mem_union_right _ dp,df⟩
      · exact ⟨c,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ct⟩),bad⟩
  · have sub : ∀ c ∈ T, c ∈ G := by
      intro c ct
      rcases Set.mem_insert_iff.mp (inc c ct) with rfl | h
      · contradiction
      · exact h
    obtain ⟨U,uf,sz,cover⟩ := old T sub
    exact ⟨U,uf,by omega,cover⟩

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

theorem resStep {pts : I→V→Bool} {F G : Bank V} {b : Nat} {C D R : LinClause V}
    (old : Certified pts F b G) (c : C ∈ G) (d : D ∈ G)
    (res : IsLinResolvent C D R) : Certified pts F (b+1) (insert R G) := by
  classical
  apply add old ({C,D} : Finset (LinClause V))
  · intro e h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> assumption
  · have h := Finset.card_insert_le C ({D} : Finset (LinClause V))
    simpa using h
  · intro a hr
    obtain ⟨f,_,_,eq⟩ := res
    have h := resolve_branch (pts a) eq hr
    split at h
    · exact ⟨C,by simp,h⟩
    · exact ⟨D,by simp,h⟩

theorem weakStep {pts : I→V→Bool} {F G : Bank V} {b : Nat} {C D : LinClause V}
    (old : Certified pts F b G) (c : C ∈ G)
    (w : ∀ i, LinClauseSat (pts i) C → LinClauseSat (pts i) D) : Certified pts F b (insert D G) := by
  apply add (k:=0) old ({C} : Finset (LinClause V))
  · intro e h
    simpa [Finset.mem_singleton.mp h] using c
  · simp
  · intro a h
    exact ⟨C,by simp,fun s => h (w a s)⟩

def available (F : Bank V) (π : List (LinClause V)) : Bank V := {c | c∈F ∨ c∈π}
theorem availCons (F : Bank V) (C : LinClause V) (π : List (LinClause V)) :
    available F (C::π) = insert C (available F π) := by
  ext d
  simp [available,or_left_comm,or_assoc]


def Con {I : Type} (pts : I→V→Bool) (C R : LinClause V) : Prop :=
  ∀ i, LinClauseSat (pts i) C → LinClauseSat (pts i) R

inductive Ledger {I : Type} (pts : I→V→Bool) (F : Bank V) :
    Nat → List (LinClause V) → Prop
  | nil : Ledger pts F 0 []
  | ax {b π C} : Ledger pts F b π → C∈F → Ledger pts F b (C::π)
  | weak {b π C R} : Ledger pts F b π → C∈π → (∀a,LinClauseSat a C → LinClauseSat a R) →
      Ledger pts F b (R::π)
  | contract {b π C D R} : Ledger pts F b π → C∈π → D∈π → IsLinResolvent C D R →
      (Con pts C R ∨ Con pts D R) → Ledger pts F b (R::π)
  | charged {b π C D R} : Ledger pts F b π → C∈π → D∈π → IsLinResolvent C D R →
      ¬ (Con pts C R ∨ Con pts D R) → Ledger pts F (b+1) (R::π)

theorem ofDer {I : Type} (pts : I→V→Bool) {F : Bank V} {π} (h : IsLinDerivation F π) :
    ∃ b,Ledger pts F b π := by
  classical
  induction h with
  | nil => exact ⟨0,.nil⟩
  | ax _ mem ih =>
    obtain ⟨b,h⟩:=ih
    exact ⟨b,.ax h mem⟩
  | weak _ c w ih =>
    obtain ⟨b,h⟩:=ih
    exact ⟨b,.weak h c w⟩
  | @res π C D R _ c d rr ih =>
    obtain ⟨b,h⟩:=ih
    by_cases e : Con pts C R ∨ Con pts D R
    · exact ⟨b,.contract h c d rr e⟩
    · exact ⟨b+1,.charged h c d rr e⟩

theorem accounting {pts : I→V→Bool} {F : Bank V} {π b} (h : Ledger pts F b π) :
    Certified pts F b (available F π) := by
  induction h with
  | nil =>
    have e : available F [] = F := by ext c; simp [available]
    rw [e]
    exact starting pts F
  | @ax b π C _ mem ih =>
    rw [availCons,Set.insert_eq_of_mem (show C∈available F π from Or.inl mem)]
    exact ih
  | weak _ c w ih =>
    rw [availCons]
    exact weakStep ih (Or.inr c) (fun i => w (pts i))
  | contract _ c d _ tr ih =>
    rw [availCons]
    rcases tr with tr|tr
    · exact weakStep ih (Or.inr c) tr
    · exact weakStep ih (Or.inr d) tr
  | charged _ c d rr _ ih =>
    rw [availCons]
    exact resStep ih (Or.inr c) (Or.inr d) rr

theorem separated {n : Nat} {pts : Fin n→V→Bool} {F : Bank V} {π b}
    (h : Ledger pts F b π) (empty : (∅ : LinClause V) ∈ π)
    (unique : ∀ c∈F,∀ i j, ¬LinClauseSat (pts i) c → ¬LinClauseSat (pts j) c → i=j) :
    n ≤ b+1 := by
  classical
  have e : (∅ : LinClause V) ∈ available F π := Or.inr empty
  obtain ⟨U,ok,sz,cov⟩:=(accounting h) ({∅} : Finset (LinClause V)) (by simpa using e)
  have finds (i : Fin n) : ∃ c∈U, ¬LinClauseSat (pts i) c :=
    cov i ⟨∅,by simp,by simp [LinClauseSat]⟩
  choose c inc bad using finds
  let f (i : Fin n) : U := ⟨c i,inc i⟩
  have fi : Function.Injective f := by
    intro i j eq
    have same : c i=c j := congrArg Subtype.val eq
    exact unique _ (ok _ (inc i)) i j (bad i) (same.symm ▸ bad j)
  have count := Fintype.card_le_of_injective f fi
  simp at count sz
  omega
end PEqualNP.Outside.L_pcx_178.SampleLedger

namespace PEqualNP.Outside.L_pcx_178.PostedIncidence
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_178.SampleLedger
abbrev V := Fin 5 × Fin 4
def samples : Array Nat := #[541200,295440,533520,164880,272400,149520,540960,295200,529440,99360,268320,84000,532800,164160,528960,98880,137280,75840,270720,147840,266880,82560,136320,74880,541185,295425,533505,164865,272385,149505,540930,295170,529410,99330,268290,83970,532740,164100,528900,98820,137220,75780,270600,147720,266760,82440,136200,74760,540705,294945,532545,163905,270465,147585,540690,294930,528450,98370,266370,82050,532500,163860,528420,98340,135300,73860,270360,147480,266280,81960,135240,73800,525345,264225,524865,133185,262785,132225,525330,264210,524610,67650,262530,66690,524820,133140,524580,67620,131460,66180,262680,132120,262440,66600,131400,66120,33825,18465,33345,10305,17025,9345,33810,18450,33090,6210,16770,5250,33300,10260,33060,6180,8580,4740,16920,9240,16680,5160,8520,4680,541201,295441,533521,164881,272401,149521,540962,295202,529442,99362,268322,84002,532804,164164,528964,98884,137284,75844,270728,147848,266888,82568,136328,74888,540961,295201,532801,164161,270721,147841,541202,295442,528962,98882,266882,82562,533524,164884,529444,99364,136324,74884,272408,149528,268328,84008,137288,75848,529441,268321,528961,137281,266881,136321,533522,272402,532802,75842,270722,74882,541204,149524,540964,84004,147844,82564,295448,164888,295208,99368,164168,98888,99361,84001,98881,75841,82561,74881,164882,149522,164162,137282,147842,136322,295444,272404,295204,268324,270724,266884,541208,533528,540968,529448,532808,528968,540946,295186,532756,164116,270616,147736,541217,295457,528932,98852,266792,82472,533569,164929,529474,99394,136264,74824,272513,149633,268418,84098,137348,75908,529426,268306,528916,137236,266776,136216,533537,272417,532772,75812,270632,74792,541249,149569,540994,84034,147784,82504,295553,164993,295298,99458,164228,98948,99346,83986,98836,75796,82456,74776,164897,149537,164132,137252,147752,136232,295489,272449,295234,268354,270664,266824,541313,533633,541058,529538,532868,529028,528706,266626,528676,135556,266536,135496,533057,270977,533012,74372,270872,74312,541729,148609,541714,83074,148504,82984,296993,165953,296978,100418,165908,100388,98626,82306,98596,74116,82216,74056,164417,148097,164372,135812,147992,135752,295969,271489,295954,267394,271384,267304,542753,534593,542738,530498,534548,530468,71746,70786,71716,70276,70696,70216,141377,140417,141332,139652,140312,139592,280609,279169,280594,278914,279064,278824,558113,557633,558098,557378,557588,557348]
def pairs : Array Nat := #[0,5,9,13,17,5,0,21,25,29,9,21,0,33,37,13,25,33,0,41,17,29,37,41,0]

def point (u : Fin 360) (v : V) := (samples[u.val]!).testBit (4*v.1.val+v.2.val)
def label (u : Fin 360) := if u.val<120 then u.val/24 else 5+(u.val-120)/6
def cp (i j : Fin 5) (h : Fin 4) := pairs[5*i.val+j.val]!+h.val
def Audit (u : Fin 360) : Prop :=
  (∀ i : Fin 5, label u=i.val ∨ ∃ h : Fin 4,point u (i,h)=true) ∧
  (∀ (i j : Fin 5) (h : Fin 4), i=j ∨ label u=cp i j h ∨
    point u (i,h)=false ∨ point u (j,h)=false)
instance (u : Fin 360) : Decidable (Audit u) := by unfold Audit; infer_instance
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab0 : ∀ z : Fin 30, Audit ⟨0+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab1 : ∀ z : Fin 30, Audit ⟨30+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab2 : ∀ z : Fin 30, Audit ⟨60+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab3 : ∀ z : Fin 30, Audit ⟨90+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab4 : ∀ z : Fin 30, Audit ⟨120+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab5 : ∀ z : Fin 30, Audit ⟨150+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab6 : ∀ z : Fin 30, Audit ⟨180+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab7 : ∀ z : Fin 30, Audit ⟨210+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab8 : ∀ z : Fin 30, Audit ⟨240+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab9 : ∀ z : Fin 30, Audit ⟨270+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab10 : ∀ z : Fin 30, Audit ⟨300+z.val,by omega⟩ := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem slab11 : ∀ z : Fin 30, Audit ⟨330+z.val,by omega⟩ := by decide +kernel
theorem audited (u : Fin 360) : Audit u := by
  by_cases t0 : u.val < 30
  · have h:=slab0 ⟨u.val-0,by omega⟩
    have e : (⟨0+(u.val-0),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t1 : u.val < 60
  · have h:=slab1 ⟨u.val-30,by omega⟩
    have e : (⟨30+(u.val-30),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t2 : u.val < 90
  · have h:=slab2 ⟨u.val-60,by omega⟩
    have e : (⟨60+(u.val-60),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t3 : u.val < 120
  · have h:=slab3 ⟨u.val-90,by omega⟩
    have e : (⟨90+(u.val-90),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t4 : u.val < 150
  · have h:=slab4 ⟨u.val-120,by omega⟩
    have e : (⟨120+(u.val-120),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t5 : u.val < 180
  · have h:=slab5 ⟨u.val-150,by omega⟩
    have e : (⟨150+(u.val-150),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t6 : u.val < 210
  · have h:=slab6 ⟨u.val-180,by omega⟩
    have e : (⟨180+(u.val-180),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t7 : u.val < 240
  · have h:=slab7 ⟨u.val-210,by omega⟩
    have e : (⟨210+(u.val-210),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t8 : u.val < 270
  · have h:=slab8 ⟨u.val-240,by omega⟩
    have e : (⟨240+(u.val-240),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t9 : u.val < 300
  · have h:=slab9 ⟨u.val-270,by omega⟩
    have e : (⟨270+(u.val-270),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  by_cases t10 : u.val < 330
  · have h:=slab10 ⟨u.val-300,by omega⟩
    have e : (⟨300+(u.val-300),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
    exact e ▸ h
  have h:=slab11 ⟨u.val-330,by omega⟩
  have e : (⟨330+(u.val-330),by omega⟩ : Fin 360)=u := Fin.ext (by dsimp; omega)
  exact e ▸ h

def select (i : Fin 45) (v : Fin 24) : Fin 360 :=
  if hr : i.val<5 then ⟨24*i.val+v.val,by omega⟩ else
    ⟨120+6*(i.val-5)+(v.val%6),by omega⟩
theorem tagSelect : ∀ (i : Fin 45) (v : Fin 24),label (select i v)=i.val := by decide +kernel

theorem useLiteral {C : Clause V} {a : V→Bool} {v : V} {b : Bool}
    (lit : (v,b)∈C) (m : a v=b) : LinClauseSat a (linOfClause C) := by
  refine ⟨({v},b),Finset.mem_image.mpr ⟨(v,b),lit,rfl⟩,?_⟩
  cases b <;> simp [LinEqSat,Finset.filter_singleton,m]

theorem uniquePrivate (choosePoint : Fin 45→Fin 24)
    (C : LinClause V) (raw : C∈linOfClause '' PHP 5 4) :
    ∀ i j, ¬LinClauseSat (point (select i (choosePoint i))) C →
      ¬LinClauseSat (point (select j (choosePoint j))) C → i=j := by
  have oneTag : ∃ t : Nat,∀ i,¬LinClauseSat (point (select i (choosePoint i))) C → i.val=t := by
    rcases raw with ⟨raw,(⟨p,rfl⟩|⟨p,q,h,pq,rfl⟩),rfl⟩
    · refine ⟨p.val,?_⟩
      intro i fail
      rcases (audited (select i (choosePoint i))).1 p with l|⟨k,hk⟩
      · simpa [tagSelect] using l
      · exact False.elim (fail (useLiteral (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩) hk))
    · refine ⟨cp p q h,?_⟩
      intro i fail
      rcases (audited (select i (choosePoint i))).2 p q h with eq|l|off|off
      · exact False.elim (pq eq)
      · simpa [tagSelect] using l
      · exact False.elim (fail (useLiteral (v:=(p,h)) (b:=false) (by simp) off))
      · exact False.elim (fail (useLiteral (v:=(q,h)) (b:=false) (by simp) off))
  obtain ⟨t,h⟩:=oneTag
  intro i j fi fj
  exact Fin.ext ((h _ fi).trans (h _ fj).symm)

theorem posted (π : List (LinClause V)) (h : IsLinRefutation (PHP 5 4) π)
    (choosePoint : Fin 45→Fin 24) :
    ∃ b,Ledger (fun i => point (select i (choosePoint i))) (linOfClause '' PHP 5 4) b π ∧ 44≤b := by
  obtain ⟨b,log⟩:=ofDer (fun i => point (select i (choosePoint i))) h.1
  refine ⟨b,log,?_⟩
  have le:=separated log h.2 (uniquePrivate choosePoint)
  omega
end PEqualNP.Outside.L_pcx_178.PostedIncidence

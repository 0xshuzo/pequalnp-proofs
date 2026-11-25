import PEqualNP.Defs

namespace Guarded3457
variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

def incidence (R : P→L→Prop) (X : Finset P) (Y : Finset L) := ∃p∈X,∃l∈Y,R p l

def block (K : Finset (Finset P)) (B : Finset L) (X : Finset P) (Y : Finset L) :=
  (∃l∈B,l∈Y) ∧ ∀A∈K,∃p∈A,p∈X

def common (K : Finset (Finset P)) : Finset P := Finset.univ.filter fun p=>∀A∈K,p∈A

inductive Choice (P L : Type*) where
  | zero
  | point (p : P)
  | line (A : Finset P) (l : L)

def available (K : Finset (Finset P)) (B : Finset L) : Choice P L→Prop
  | .zero => True
  | .point p => p∈common K
  | .line A l => A∈K ∧ l∈B

def chosen (B : Finset L) (X : Finset P) (Y : Finset L) : Choice P L→Prop
  | .zero => False
  | .point p => p∈X ∧ ∃l∈B,l∈Y
  | .line A l => (∃p∈A,p∈X) ∧ l∈Y

theorem paired (K : Finset (Finset P)) (B : Finset L) (p : P) (l : L) :
    block K B {p} {l} ↔ p∈common K ∧ l∈B := by
  simp [block,common,Finset.mem_filter,and_comm]

theorem edge (R : P→L→Prop) (p : P) (l : L) : incidence R {p} {l} ↔ R p l := by simp [incidence]

theorem shrink (R : P→L→Prop) (square : ∀p q l k,p≠q→l≠k→¬(R p l ∧ R p k ∧ R q l ∧ R q k))
    (K : Finset (Finset P)) (B : Finset L)
    (safe : ∀X Y,block K B X Y→incidence R X Y) :
    ∃a : Choice P L,available K B a ∧
      (∀X Y,chosen B X Y a→incidence R X Y) ∧
      (∀p l,block K B {p} {l}→chosen B {p} {l} a) := by
  classical
  have rectangle (p : P) (l : L) (hp : p∈common K) (hl : l∈B) : R p l :=
    (edge R p l).mp (safe _ _ ((paired K B p l).mpr ⟨hp,hl⟩))
  by_cases cb : B.Nonempty
  · obtain ⟨l,lb⟩ := cb
    by_cases cp : (common K).Nonempty
    · obtain ⟨p,ps⟩ := cp
      by_cases small : (common K).card≤1
      · refine ⟨.point p,ps,?_,?_⟩
        · rintro X Y ⟨px,b,bb,by'⟩
          exact ⟨p,px,b,by',rectangle p b ps bb⟩
        · intro q b hit
          obtain ⟨qs,bb⟩ := (paired K B q b).mp hit
          have same := Finset.card_le_one.mp small p ps q qs
          exact ⟨by simpa using same,b,bb,by simp⟩
      · obtain ⟨u,us,v,vs,uv⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
        have only (b : L) (bb : b∈B) : b=l := by
          by_contra ne
          exact square u v b l uv ne ⟨rectangle u b us bb,rectangle u l us lb,rectangle v b vs bb,rectangle v l vs lb⟩
        have port : ∃A∈K,∀q∈A,R q l := by
          by_contra! no
          let X := Finset.univ.filter (fun q=>¬R q l)
          have hit : block K B X {l} := by
            refine ⟨⟨l,lb,by simp⟩,?_⟩
            intro A mem
            obtain ⟨q,qa,noq⟩ := no A mem
            exact ⟨q,qa,by simp [X,noq]⟩
          obtain ⟨q,qx,b,bl,inc⟩ := safe _ _ hit
          have eql : b=l := by simpa using bl
          exact (Finset.mem_filter.mp qx).2 (eql ▸ inc)
        obtain ⟨A,ak,all⟩ := port
        refine ⟨.line A l,⟨ak,lb⟩,?_,?_⟩
        · rintro X Y ⟨⟨q,qa,qx⟩,ly⟩
          exact ⟨q,qx,l,ly,all q qa⟩
        · intro q b hit
          obtain ⟨qs,bb⟩ := (paired K B q b).mp hit
          have qa := (Finset.mem_filter.mp qs).2 A ak
          exact ⟨⟨q,qa,by simp⟩,by simp [only b bb]⟩
    · refine ⟨.zero,trivial,fun _ _ h=>h.elim,?_⟩
      exact fun p l hit=>cp ⟨p,((paired K B p l).mp hit).1⟩
  · refine ⟨.zero,trivial,fun _ _ h=>h.elim,?_⟩
    exact fun p l hit=>cb ⟨l,((paired K B p l).mp hit).2⟩

theorem covers {J : Type*} [Fintype J] (R : P→L→Prop)
    (square : ∀p q l k,p≠q→l≠k→¬(R p l ∧ R p k ∧ R q l ∧ R q k))
    (K : J→Finset (Finset P)) (B : J→Finset L)
    (exactly : ∀X Y,incidence R X Y ↔ ∃j,block (K j) (B j) X Y) :
    ∃a : J→Choice P L,(∀j,available (K j) (B j) (a j)) ∧
      (∀j X Y,chosen (B j) X Y (a j)→incidence R X Y) ∧
      (∀X Y,incidence R X Y ↔ ∃j,chosen (B j) X Y (a j)) := by
  classical
  choose a avail safe save using fun j=>shrink R square (K j) (B j) (fun X Y h=>(exactly X Y).mpr ⟨j,h⟩)
  refine ⟨a,avail,safe,?_⟩
  intro X Y
  constructor
  · rintro ⟨p,px,l,ly,pl⟩
    obtain ⟨j,old⟩ := (exactly {p} {l}).mp ((edge R p l).mpr pl)
    refine ⟨j,?_⟩
    have keep := save j p l old
    cases e : a j with
    | zero => rw [e] at keep;exact keep.elim
    | point q =>
      rw [e] at keep
      obtain ⟨qp,b,bb,bl⟩ := keep
      have u : q=p := by simpa using qp
      have v : b=l := by simpa using bl
      exact ⟨u.symm ▸ px,b,bb,v.symm ▸ ly⟩
    | line A b =>
      rw [e] at keep
      obtain ⟨⟨q,qa,qp⟩,bl⟩ := keep
      have u : q=p := by simpa using qp
      have v : b=l := by simpa using bl
      exact ⟨⟨q,qa,u.symm ▸ px⟩,v.symm ▸ ly⟩
  · rintro ⟨j,h⟩
    exact safe j X Y h

end Guarded3457

namespace Clean3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.BicliqueBlockCost

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun s g => s ++ [val g s]) w
def valid : ℕ → List Gate → Prop
  | _, [] => True
  | m, g::gs => ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < m) ∧ valid (m+1) gs
def safe (F : Bool) : List Gate → List Bool → Prop
  | [], _ => True
  | g::gs, w => (g.op=.and → val g w=true → F=true) ∧ safe F gs (w++[val g w])

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs++hs) w=run hs (run gs w) := by simp [run,List.foldl_append]

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => change (run gs (w++[val g w])).length = _; rw [ih]; simp; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false = _
    rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]

theorem valid_app (m : ℕ) (a b : List Gate) (ha : valid m a) (hb : valid (m+a.length) b) : valid m (a++b) := by
  induction a generalizing m with
  | nil => simpa using hb
  | cons g a ih =>
    exact ⟨ha.1,ih _ ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem safe_app (F : Bool) (a b : List Gate) (w : List Bool) (ha : safe F a w) (hb : safe F b (run a w)) :
    safe F (a++b) w := by
  induction a generalizing w with
  | nil => exact hb
  | cons g a ih => exact ⟨ha.1,ih _ ha.2 hb⟩

theorem valid_spec (m : ℕ) (gs : List Gate) (hg : valid m gs) :
    (∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) ∧
    ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < m+j := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨fan,back⟩ := ih (m+1) hg.2
    constructor
    · intro h hh
      rcases List.mem_cons.mp hh with rfl|hh
      · exact ⟨hg.1.1,hg.1.2.1⟩
      · exact fan _ hh
    · intro j hj i hi
      cases j with
      | zero => exact hg.1.2.2 i hi
      | succ j =>
        have h := back j (by simpa using hj) i hi
        omega

theorem safe_spec (F : Bool) (gs : List Gate) (w : List Bool) (hg : safe F gs w) :
    ∀ j (hj : j < gs.length), gs[j].op=.and → (run gs w).getD (w.length+j) false=true → F=true := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    intro j hj op value
    change (run gs (w++[val g w])).getD _ false=true at value
    cases j with
    | zero =>
      rw [Nat.add_zero,run_keep _ _ _ (by simp)] at value
      exact hg.1 op (by simpa using value)
    | succ j =>
      apply ih _ hg.2 j (by simpa using hj) op
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using value

def Bld (n : ℕ) (F f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (o : ℕ), valid m gs ∧ gs.length ≤ s ∧ o < m+gs.length ∧
    ∀ w : List Bool, w.length=m → (run gs w).getD o false = f (fun i => w.getD i.val false) ∧
      safe (F (fun i => w.getD i.val false)) gs w

theorem bld_congr {n s t : ℕ} {F f h : (Fin n → Bool) → Bool} (hf : Bld n F f s) (st : s ≤ t)
    (eq : ∀ x, f x=h x) : Bld n F h t := by
  intro m hm
  obtain ⟨gs,o,v,b,r,e⟩ := hf m hm
  exact ⟨gs,o,v,b.trans st,r,fun w hw => ⟨(e w hw).1.trans (eq _),(e w hw).2⟩⟩

theorem bld_var {n : ℕ} (F : (Fin n → Bool) → Bool) (i : Fin n) : Bld n F (fun x => x i) 0 := by
  intro m hm
  exact ⟨[],i.val,True.intro,le_rfl,by simp; omega,fun w _ => ⟨rfl,True.intro⟩⟩

theorem bld_bin {n s t : ℕ} {F f h : (Fin n → Bool) → Bool}
    (lf : Bld n F f s) (rt : Bld n F h t) (op : GateOp) (allowed : op=.and ∨ op=.or)
    (legal : op=.and → ∀ x, op.eval [f x,h x]=true → F x=true) :
    Bld n F (fun x => op.eval [f x,h x]) (s+t+1) := by
  intro m hm
  obtain ⟨a,u,va,ca,ru,ea⟩ := lf m hm
  obtain ⟨b,v,vb,cb,rv,eb⟩ := rt (m+a.length) (by omega)
  let last : Gate := ⟨op,[u,v]⟩
  let o := m+a.length+b.length
  have fin : valid o [last] := by
    refine ⟨⟨allowed,by change [u,v].length ≤ 2; exact le_rfl,?_⟩,True.intro⟩
    intro i hi
    change i∈[u,v] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl <;> dsimp [o] <;> omega
  refine ⟨a++b++[last],o,valid_app _ _ _ (valid_app _ _ _ va vb) (by simpa [o,Nat.add_assoc] using fin),
    by simp;omega,by simp [o];omega,?_⟩
  intro w hw
  let x : Fin n → Bool := fun i => w.getD i.val false
  let p := run a w
  let q := run b p
  have pl : p.length=m+a.length := by simp [p,run_len,hw]
  have ql : q.length=o := by simp [q,o,run_len,pl]
  have pRaw : (fun i : Fin n => p.getD i.val false) = x := by
    funext i
    exact run_keep _ _ _ (by have := i.isLt; omega)
  have v1 : q.getD u false=f x := by
    rw [show q.getD u false=p.getD u false by exact run_keep _ _ _ (by omega)]
    exact (ea w hw).1
  have v2 : q.getD v false=h x := by rw [←pRaw]; exact (eb p pl).1
  have vLast : val last q=op.eval [f x,h x] := by
    change op.eval [q.getD u false,q.getD v false]=op.eval [f x,h x]
    rw [v1,v2]
  have sA : safe (F x) a w := (ea w hw).2
  have sB : safe (F x) b p := by rw [←pRaw]; exact (eb p pl).2
  have sLast : safe (F x) [last] q := ⟨fun hop val => legal hop x (vLast ▸ val),True.intro⟩
  constructor
  · rw [run_append,run_append]
    change (q++[val last q]).getD o false=op.eval [f x,h x]
    rw [←ql]
    simpa using vLast
  · apply safe_app _ _ _ _ (safe_app _ _ _ _ sA sB)
    rw [run_append]
    exact sLast

theorem bld_or {n s t : ℕ} {F f h : (Fin n → Bool) → Bool} (lf : Bld n F f s) (rt : Bld n F h t) :
    Bld n F (fun x => f x || h x) (s+t+1) :=
  bld_congr (bld_bin lf rt .or (Or.inr rfl) (by intro bad; contradiction)) le_rfl
    (fun x => by simp [GateOp.eval])

theorem bld_any {n : ℕ} (F : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (ne : S.Nonempty) :
    Bld n F (fun x => decide (∃ i∈S, x i=true)) (S.card-1) := by
  have build (vs : List (Fin n)) : ∀ v : Fin n, Bld n F (fun x => (v::vs).any fun i => x i) vs.length := by
    induction vs with
    | nil => intro v; exact bld_congr (bld_var F v) le_rfl (by simp)
    | cons h t ih =>
      intro v
      exact bld_congr (bld_or (bld_var F v) (ih h)) (by simp) (by simp)
  obtain ⟨v,vs,eq⟩ : ∃ v vs, S.toList = v::vs := by
    cases h : S.toList with
    | nil => simp at h; exact False.elim (ne.ne_empty h)
    | cons v vs => exact ⟨v,vs,rfl⟩
  have sz : S.card=vs.length+1 := by rw [←Finset.length_toList,eq];rfl
  apply bld_congr (build vs v) (by omega)
  intro x
  rw [Bool.eq_iff_iff,decide_eq_true_iff,←eq,List.any_eq_true]
  simp

end Clean3451

namespace Hardware3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Clean3451

abbrev Port (n : Nat) := Fin n×Fin n

def anyPair {n : Nat} (E : Finset (Port n)) (x : Fin n→Bool) := decide (∃e∈E,x e.1=true ∧ x e.2=true)

theorem portFamily {n : Nat} (E : Finset (Port n)) (S : Finset (Port n)) (incl : S⊆E) (non : S.Nonempty) :
    Bld n (anyPair E) (anyPair S) (2*S.card-1) := by
  classical
  have one (p : Port n) (hp : p∈E) : Bld n (anyPair E) (fun x=>x p.1 && x p.2) 1 := by
    have legal : GateOp.and=GateOp.and → ∀x : Fin n→Bool,GateOp.and.eval [x p.1,x p.2]=true→anyPair E x=true := by
      intro _ x on
      apply decide_eq_true
      exact ⟨p,hp,by simpa [GateOp.eval] using on⟩
    exact bld_congr (bld_bin (bld_var (anyPair E) p.1) (bld_var (anyPair E) p.2) .and (Or.inl rfl) legal) le_rfl
      (fun x=>by simp [GateOp.eval])
  induction S using Finset.induction_on with
  | empty => simp at non
  | @insert p S fresh ih =>
    have hp := incl (Finset.mem_insert_self p S)
    have ss : S⊆E := fun v hv=>incl (Finset.mem_insert_of_mem hv)
    by_cases more : S.Nonempty
    · apply bld_congr (bld_or (one p hp) (ih ss more))
      · rw [Finset.card_insert_of_notMem fresh]
        have h := Finset.card_pos.mpr more
        omega
      · intro x
        apply Bool.eq_iff_iff.mpr
        simp [anyPair,or_and_right,exists_or]
    · have z := Finset.not_nonempty_iff_eq_empty.mp more
      subst S
      apply bld_congr (one p hp)
      · simp
      · intro x
        apply Bool.eq_iff_iff.mpr
        simp [anyPair]

theorem purePrefix (gs : List Gate) (h : ∀g∈gs,g.op=GateOp.or) (w : List Bool) (f : Bool) : safe f gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    exact ⟨fun op=>by rw [h _ List.mem_cons_self] at op;contradiction,ih (fun c m=>h c (List.mem_cons_of_mem _ m)) _⟩

def seen (n : Nat) (pre : List Gate) (x : Fin n→Bool) (i : Fin (n+pre.length)) :=
  (run pre (List.ofFn x)).getD i.val false

theorem attach (n : Nat) (pre : List Gate) (validPre : valid n pre) (pure : ∀g∈pre,g.op=GateOp.or)
    (E : Finset (Port (n+pre.length))) :
    ∃D : Circuit,Monotone2 D ∧ ReadsBack n D ∧ D.size≤pre.length+(2*E.card-1) ∧
      (∀x,circuitFun n D x=anyPair E (seen n pre x)) ∧
      (∀j<D.gates.length,(gateAt D j).op=.and→∀x : Fin n→Bool,(D.wires (List.ofFn x)).getD (n+j) false=true→anyPair E (seen n pre x)=true) := by
  classical
  by_cases non : E.Nonempty
  · obtain ⟨gs,o,vg,cg,_,ev⟩ := portFamily E E (Finset.Subset.refl _) non (n+pre.length) le_rfl
    let D : Circuit := ⟨pre++gs,o⟩
    have good : valid n D.gates := valid_app n pre gs validPre vg
    have gate (j : Nat) (hj : j<D.gates.length) : gateAt D j=D.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
    have total (x : Fin n→Bool) := ev (run pre (List.ofFn x)) (by simp [run_len])
    refine ⟨D,?_,?_,?_,?_,?_⟩
    · intro g hg
      obtain ⟨op,ar⟩ := (valid_spec _ _ good).1 g hg
      exact ⟨by simpa using op,ar⟩
    · intro j hj;rw [gate j hj];exact (valid_spec _ _ good).2 j hj
    · change (pre++gs).length≤_
      simp only [List.length_append];omega
    · intro x
      change (run (pre++gs) (List.ofFn x)).getD o false=_
      rw [run_append]
      exact (total x).1
    · intro j hj op x high
      have safeAll := safe_app (anyPair E (seen n pre x)) pre gs (List.ofFn x) (purePrefix pre pure _ _) (total x).2
      rw [gate j hj] at op
      change (run (pre++gs) (List.ofFn x)).getD (n+j) false=true at high
      exact safe_spec _ _ _ safeAll j hj op (by simpa only [List.length_ofFn] using high)
  · have empty := Finset.not_nonempty_iff_eq_empty.mp non
    subst E
    let D : Circuit := ⟨[],n⟩
    refine ⟨D,by simp [D,Monotone2],by simp [D,ReadsBack],Nat.zero_le _,?_,by simp [D]⟩
    intro x
    change (List.ofFn x).getD n false=_
    rw [List.getD_eq_default _ _ (by simp)]
    simp [anyPair]

end Hardware3457

namespace Global3457
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Clean3451 Guarded3457 Hardware3457
variable {N : Nat}
abbrev pt (p : Fin N) := Fin.castAdd N p
abbrev ln (l : Fin N) := Fin.natAdd N l
def PX (x : Fin (N+N)→Bool) := Finset.univ.filter fun p : Fin N=>x (pt p)=true
def LY (x : Fin (N+N)→Bool) := Finset.univ.filter fun l : Fin N=>x (ln l)=true

abbrev Correct (I : Fin N→Fin N→Prop) (D : Circuit) := ∀x,circuitFun (N+N) D x=true ↔∃p l,I p l ∧ x (pt p)=true ∧ x (ln l)=true

theorem normalize {J : Type*} [Fintype J] (I : Fin N→Fin N→Prop) (C : Circuit)
    (free : ∀p q l k,p≠q→l≠k→¬(I p l ∧ I p k ∧ I q l ∧ I q k))
    (K : J→Finset (Finset (Fin N))) (B : J→Finset (Fin N))
    (exactly : ∀X Y,incidence I X Y ↔ ∃j,block (K j) (B j) X Y)
    (pre : List Gate) (good : valid (N+N) pre) (pure : ∀g∈pre,g.op=GateOp.or)
    (Pport : J→Finset (Fin N)→Fin ((N+N)+pre.length)) (Lport : J→Fin ((N+N)+pre.length))
    (psem : ∀j A,A∈K j→∀x,seen (N+N) pre x (Pport j A)=true ↔ ∃p∈A,p∈PX x)
    (lsem : ∀j x,seen (N+N) pre x (Lport j)=true ↔ ∃l∈B j,l∈LY x)
    (paid : pre.length + (2*Fintype.card J-1)≤C.size) :
    ∃D : Circuit,Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size≤C.size ∧ Correct I D ∧
      ∀j<D.gates.length,(gateAt D j).op=.and→∀x : Fin (N+N)→Bool,
       (D.wires (List.ofFn x)).getD (N+N+j) false=true→circuitFun (N+N) D x=true := by
  classical
  obtain ⟨a,available',safe,match'⟩ := covers I free K B exactly
  let index (i : Fin (N+N)) : Fin ((N+N)+pre.length) := ⟨i.val,by have := i.isLt;omega⟩
  have raw (x : Fin (N+N)→Bool) (i : Fin (N+N)) : seen (N+N) pre x (index i)=x i := by
    change (run pre (List.ofFn x)).getD i.val false=_
    rw [run_keep _ _ _ (by simp)]
    simp
  let portOf (j : J) (t : Choice (Fin N) (Fin N)) : Option (Port ((N+N)+pre.length)) := match t with
    | .zero => none
    | .point p => some (index (pt p),Lport j)
    | .line A l => some (Pport j A,index (ln l))
  let select (j : J) := portOf j (a j)
  let E := Finset.univ.biUnion fun j=>(select j).toFinset
  have cost : E.card≤Fintype.card J := by
    apply (Finset.card_biUnion_le).trans
    calc
      ∑j : J,(select j).toFinset.card ≤ ∑ _ : J,1 := Finset.sum_le_sum (fun j _=>by cases h : select j <;> simp)
      _ = _ := by simp
  have term (j : J) (x : Fin (N+N)→Bool) :
      (∃e∈(select j).toFinset,seen (N+N) pre x e.1=true ∧ seen (N+N) pre x e.2=true) ↔ chosen (B j) (PX x) (LY x) (a j) := by
    have avail := available' j
    cases h : a j with
    | zero => simp [select,portOf,h,chosen]
    | point p => simp [select,portOf,h,chosen,raw,lsem,PX]
    | line A l =>
      rw [h] at avail
      simp [select,portOf,h,chosen,raw,psem j A avail.1 x,LY]
  have equality (x : Fin (N+N)→Bool) : anyPair E (seen (N+N) pre x)=true ↔ incidence I (PX x) (LY x) := by
    rw [match' (PX x) (LY x)]
    change decide (∃e∈E,_) =true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨e,he,on⟩
      obtain ⟨j,_,mem⟩ := Finset.mem_biUnion.mp he
      exact ⟨j,(term j x).mp ⟨e,mem,on⟩⟩
    · rintro ⟨j,hit⟩
      obtain ⟨e,mem,on⟩ := (term j x).mpr hit
      exact ⟨e,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,mem⟩,on⟩
  obtain ⟨D,mo,bk,sz,out,clean⟩ := attach (N+N) pre good pure E
  refine ⟨D,mo,bk,by omega,?_,?_⟩
  · intro x
    rw [out,equality]
    simp only [incidence,PX,LY,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨p,px,l,ly,inc⟩;exact ⟨p,l,inc,px,ly⟩
    · rintro ⟨p,l,inc,px,ly⟩;exact ⟨p,px,l,ly,inc⟩
  · intro j hj op x hi
    rw [out]
    exact clean j hj op x hi

end Global3457

import Mathlib
import PEqualNP.Defs

namespace Clean3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.BicliqueBlockCost

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun s g => s ++ [val g s]) w
def valid : ℕ → List Gate → Prop
  | _, [] => True
  | m, g::gs => ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i<m) ∧ valid (m+1) gs
def safe (F : Bool) : List Gate → List Bool → Prop
  | [], _ => True
  | g::gs, w => (g.op=.and → val g w=true → F=true) ∧ safe F gs (w++[val g w])

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs++hs) w=run hs (run gs w) := by simp [run,List.foldl_append]

theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => change (run gs (w++[val g w])).length = _; rw [ih]; simp; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
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
    (∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧
    ∀ j (hj : j<gs.length), ∀ i ∈ gs[j].inputs, i<m+j := by
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
    ∀ j (hj : j<gs.length), gs[j].op=.and → (run gs w).getD (w.length+j) false=true → F=true := by
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
  ∀ m, n≤m → ∃ (gs : List Gate) (o : ℕ), valid m gs ∧ gs.length ≤ s ∧ o<m+gs.length ∧
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
  have vLast : val last q=op.eval [f x,h x] := by simp [val,last,v1,v2]
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

namespace Clean3451
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.BicliqueBlockCost

def edgeFn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :=
  decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
def blockFn {n : ℕ} (B : Block n) (x : Fin n → Bool) :=
  decide (∃ a ∈ B.1, x a=true) && decide (∃ b ∈ B.2, x b=true)
def unionFn {n : ℕ} (F : Finset (Block n)) (x : Fin n → Bool) := decide (∃ B ∈ F, blockFn B x=true)

theorem oneBlock {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B : Block n) (hb : IsBlock G B) :
    Bld n (edgeFn G) (blockFn B) (blockCost B) := by
  have s := bld_bin (bld_any (edgeFn G) B.1 hb.2.1) (bld_any (edgeFn G) B.2 hb.2.2.1) .and (Or.inl rfl) (by
    intro _ x on
    simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq] at on
    obtain ⟨⟨a,ha,xa⟩,b,hb',xb⟩ := on
    exact decide_eq_true ⟨a,b,hb.2.2.2 a ha b hb',xa,xb⟩)
  have la := Finset.card_pos.mpr hb.2.1
  have lb := Finset.card_pos.mpr hb.2.2.1
  exact bld_congr s (by unfold blockCost;omega) (by intro x;simp [blockFn,GateOp.eval])

theorem family {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : Finset (Block n))
    (good : ∀ B ∈ F, IsBlock G B) (ne : F.Nonempty) : Bld n (edgeFn G) (unionFn F) (familyCost F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp at ne
  | @insert B F hb ih =>
    have val := oneBlock G B (good _ (Finset.mem_insert_self ..))
    by_cases has : F.Nonempty
    · have more := ih (fun p hp => good _ (Finset.mem_insert_of_mem hp)) has
      apply bld_congr (bld_or val more)
      · have pos := Finset.card_pos.mpr has
        simp only [familyCost,Finset.sum_insert hb,Finset.card_insert_of_notMem hb]
        omega
      · intro x
        apply Bool.eq_iff_iff.mpr
        simp [unionFn]
    · have empty := Finset.not_nonempty_iff_eq_empty.mp has
      subst F
      apply bld_congr val
      · simp [familyCost]
      · intro x
        apply Bool.eq_iff_iff.mpr
        simp [unionFn]

theorem canonical {n s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (cost : HasBlockCost G s) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ s ∧ circuitFun n D=edgeFn G ∧
      ∀ j < D.gates.length, (gateAt D j).op=.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n+j) false=true → edgeFn G x=true := by
  classical
  obtain ⟨F,⟨all,cover⟩,budget⟩ := cost
  by_cases existsF : F.Nonempty
  · have formulas := family G F all existsF
    have agrees (x : Fin n → Bool) : unionFn F x = edgeFn G x := by
      apply Bool.eq_iff_iff.mpr
      simp only [unionFn,edgeFn,decide_eq_true_eq,blockFn,Bool.and_eq_true]
      constructor
      · rintro ⟨B,bf,⟨a,ha,xa⟩,b,hb,xb⟩
        exact ⟨a,b,(all _ bf).2.2.2 a ha b hb,xa,xb⟩
      · rintro ⟨a,b,ab,xa,xb⟩
        obtain ⟨B,bf,h⟩ := cover a b ab
        rcases h with ⟨ha,hb⟩|⟨hb,ha⟩
        · exact ⟨B,bf,⟨a,ha,xa⟩,b,hb,xb⟩
        · exact ⟨B,bf,⟨b,hb,xb⟩,a,ha,xa⟩
    obtain ⟨gs,o,v,b,_,h⟩ := (bld_congr formulas budget agrees) n le_rfl
    let D : Circuit := ⟨gs,o⟩
    have idx (j : ℕ) (hj : j<gs.length) : gateAt D j=gs[j] := by simp [D,gateAt,List.getD_eq_getElem?_getD,hj]
    have raw (x : Fin n → Bool) : (fun i : Fin n => (List.ofFn x).getD i.val false)=x := by funext i;simp
    refine ⟨D,?_,?_,b,?_,?_⟩
    · intro g hg
      obtain ⟨ops,arity⟩ := (valid_spec _ gs v).1 g hg
      exact ⟨by simpa using ops,arity⟩
    · intro j hj;rw [idx j hj];exact (valid_spec _ gs v).2 j hj
    · funext x
      exact (h (List.ofFn x) (by simp)).1.trans (congrArg (edgeFn G) (raw x))
    · intro j hj op x on
      rw [idx _ hj] at op
      have val := safe_spec _ _ _ (h (List.ofFn x) (by simp)).2 j hj op (by simpa only [List.length_ofFn] using on)
      simpa only [raw] using val
  · have zero (x : Fin n → Bool) : edgeFn G x=false := by
      cases h : edgeFn G x with
      | false => rfl
      | true =>
        obtain ⟨a,b,ab,_,_⟩ := of_decide_eq_true h
        obtain ⟨B,hB,_⟩ := cover a b ab
        exact False.elim (existsF ⟨B,hB⟩)
    let D : Circuit := ⟨[],n⟩
    refine ⟨D,by simp [D,Monotone2],by simp [D,ReadsBack],Nat.zero_le _,?_,by simp [D]⟩
    funext x
    rw [zero]
    change (List.ofFn x).getD n false=false
    exact List.getD_eq_default _ _ (by simp)

end Clean3451

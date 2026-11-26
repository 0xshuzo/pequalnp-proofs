import PEqualNP.Defs

namespace Builder3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.BicliqueBlockCost

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun s g => s ++ [val g s]) w
def valid : ℕ → List Gate → Prop
  | _, [] => True
  | m, g::gs => ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m) ∧ valid (m+1) gs
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
    (∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length = 2) ∧
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
    refine ⟨⟨allowed,by change [u,v].length = 2; rfl,?_⟩,True.intro⟩
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

end Builder3566

namespace Builder3566
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
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ s ∧ circuitFun n D=edgeFn G := by
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
    have idx (j : ℕ) (hj : j < gs.length) : gateAt D j=gs[j] := by simp [D,gateAt,List.getD_eq_getElem?_getD,hj]
    have raw (x : Fin n → Bool) : (fun i : Fin n => (List.ofFn x).getD i.val false)=x := by funext i;simp
    refine ⟨D, ⟨?_,?_,?_⟩, b, ?_⟩
    · intro g hg
      exact ((valid_spec _ gs v).1 g hg).1
    · intro j hj
      rw [idx j hj]
      exact (valid_spec _ gs v).2 j hj
    · intro g hg
      exact ((valid_spec _ gs v).1 g hg).2
    · funext x
      exact (h (List.ofFn x) (by simp)).1.trans (congrArg (edgeFn G) (raw x))
  · have zero (x : Fin n → Bool) : edgeFn G x=false := by
      cases h : edgeFn G x with
      | false => rfl
      | true =>
        obtain ⟨a,b,ab,_,_⟩ := of_decide_eq_true h
        obtain ⟨B,hB,_⟩ := cover a b ab
        exact False.elim (existsF ⟨B,hB⟩)
    let D : Circuit := ⟨[],n⟩
    refine ⟨D,⟨by simp [D,PEqualNP.EdgeOwnership.AndOrOnly],by simp [D,ReadsBack],by simp [D]⟩,Nat.zero_le _,?_⟩
    funext x
    rw [zero]
    change (List.ofFn x).getD n false=false
    exact List.getD_eq_default _ _ (by simp)

end Builder3566

namespace Stars3566

open PEqualNP.BicliqueBlockCost PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem starBridge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) (e : ∃ u v, G.Adj u v) :
    HasBlockCost G (G.edgeFinset.card + T.card - 1) := by
  classical
  let leaves (u : Fin n) := Finset.univ.filter (fun v => G.Adj u v ∧ (v ∉ T ∨ u < v))
  have leaf (u v) : v ∈ leaves u ↔ G.Adj u v ∧ (v ∉ T ∨ u < v) := by simp [leaves]
  let centres := T.filter (fun u => (leaves u).Nonempty)
  let star (u : Fin n) : Block n := ({u}, leaves u)
  have inj : Function.Injective star := by
    intro u v h
    have eq : ({u} : Finset (Fin n)) = {v} := congrArg Prod.fst h
    simpa using eq
  have covers (u v : Fin n) (h : G.Adj u v) :
      (u ∈ T ∧ v ∈ leaves u) ∨ (v ∈ T ∧ u ∈ leaves v) := by
    by_cases hu : u ∈ T
    · by_cases hv : v ∈ T
      · rcases lt_or_gt_of_ne h.ne with hlt | hgt
        · exact Or.inl ⟨hu, (leaf _ _).2 ⟨h, Or.inr hlt⟩⟩
        · exact Or.inr ⟨hv, (leaf _ _).2 ⟨h.symm, Or.inr hgt⟩⟩
      · exact Or.inl ⟨hu, (leaf _ _).2 ⟨h, Or.inl hv⟩⟩
    · exact Or.inr ⟨(hc u v h).resolve_left hu, (leaf _ _).2 ⟨h.symm, Or.inl hu⟩⟩
  have centre {u v} (hu : u ∈ T) (hv : v ∈ leaves u) : u ∈ centres :=
    Finset.mem_filter.mpr ⟨hu, v, hv⟩
  refine ⟨centres.image star, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨Finset.disjoint_singleton_left.mpr (fun h => G.irrefl ((leaf u u).1 h).1),
      Finset.singleton_nonempty u, (Finset.mem_filter.mp hu).2, ?_⟩
    intro a ha b hb
    have ea : a = u := Finset.mem_singleton.mp ha
    exact ea ▸ ((leaf u b).1 hb).1
  · intro u v h
    rcases covers u v h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨star u, Finset.mem_image_of_mem _ (centre hu hv), Or.inl ⟨Finset.mem_singleton_self _, hv⟩⟩
    · exact ⟨star v, Finset.mem_image_of_mem _ (centre hv hu), Or.inr ⟨Finset.mem_singleton_self _, hu⟩⟩
  · have bound : (centres.sigma leaves).card ≤ G.edgeFinset.card := by
      apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
      · intro p hp
        exact SimpleGraph.mem_edgeFinset.mpr ((leaf _ _).1 (Finset.mem_sigma.mp hp).2).1
      · rintro ⟨u,v⟩ h₁ ⟨w,z⟩ h₂ heq
        obtain ⟨hu, hv⟩ := Finset.mem_sigma.mp h₁
        obtain ⟨hw, hz⟩ := Finset.mem_sigma.mp h₂
        rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · have lt₁ := ((leaf _ _).1 hv).2.resolve_left (not_not_intro (Finset.mem_filter.mp hw).1)
          have lt₂ := ((leaf _ _).1 hz).2.resolve_left (not_not_intro (Finset.mem_filter.mp hu).1)
          exact False.elim ((not_lt_of_gt lt₁) lt₂)
    rw [Finset.card_sigma] at bound
    have cardLe : centres.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have pos : 0 < T.card := by
      obtain ⟨u, v, h⟩ := e
      rcases hc u v h with hu | hv
      · exact Finset.card_pos.mpr ⟨u, hu⟩
      · exact Finset.card_pos.mpr ⟨v, hv⟩
    unfold familyCost
    rw [Finset.sum_image inj.injOn, Finset.card_image_of_injective _ inj]
    have cost (u) : blockCost (star u) = (leaves u).card := by simp [blockCost, star]
    simp_rw [cost]
    omega



end Stars3566

namespace Peel3566
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.BicliqueBlockCost PEqualNP.MetaComplexity.CoverPromise

def MeetsLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ T : Finset (Fin n), IsVertexCover G T →
    (∀ S : Finset (Fin n), IsVertexCover G S → T.card ≤ S.card) →
    G.edgeFinset.card + T.card ≤ C.size+1

theorem minCover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ ∀ S : Finset (Fin n), IsVertexCover G S → T.card ≤ S.card := by
  classical
  let covers := Finset.univ.filter (fun S : Finset (Fin n) => IsVertexCover G S)
  have occurs (S : Finset (Fin n)) : S ∈ covers ↔ IsVertexCover G S := by simp [covers]
  have yes : covers.Nonempty := ⟨Finset.univ, (occurs _).2 (fun a _ _ => Or.inl (Finset.mem_univ a))⟩
  obtain ⟨T,hT,ht⟩ := Finset.exists_min_image covers Finset.card yes
  exact ⟨T,(occurs _).1 hT,fun S hS => ht S ((occurs _).2 hS)⟩

def Drop {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ S : Finset (Fin n), IsVertexCover H S ∧ ∀ T : Finset (Fin n), IsVertexCover G T → S.card<T.card

theorem atVertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n)
    (hedge : ∃ u v, (G.deleteIncidenceSet z).Adj u v) (C : Circuit) (low : MeetsLower G C) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun x : Fin n → Bool => @decide (∃ u v, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧
        x u=true ∧ x v=true) (Classical.propDecidable _)) ∧
      D.size + G.degree z ≤ C.size ∧ (Drop G (G.deleteEdges (G.incidenceSet z)) →
        D.size + G.degree z + 1 ≤ C.size) := by
  classical
  let H := G.deleteIncidenceSet z
  obtain ⟨T,hT,mT⟩ := minCover G
  obtain ⟨S,hS,mS⟩ := minCover H
  obtain ⟨D,ao,sz,eq⟩ := Builder3566.canonical H (Stars3566.starBridge H S hS hedge)
  have lower := low T hT mT
  have contain : IsVertexCover H T := fun u v h => hT u v ((G.deleteIncidenceSet_le z) h)
  have le := mS T contain
  have split : H.edgeFinset.card = G.edgeFinset.card-G.degree z :=
    G.card_edgeFinset_deleteIncidenceSet z
  have degreeLe : G.degree z ≤ G.edgeFinset.card := by
    rw [← G.card_incidenceFinset_eq_degree z]
    exact Finset.card_le_card (G.incidenceFinset_subset z)
  have positive : 0 < H.edgeFinset.card := by
    obtain ⟨u,v,uv⟩ := hedge
    exact Finset.card_pos.mpr ⟨s(u,v),SimpleGraph.mem_edgeFinset.mpr uv⟩
  refine ⟨D,ao,?_,by omega,?_⟩
  · rw [eq]
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Builder3566.edgeFn,decide_eq_true_eq]
    constructor <;> rintro ⟨a,b,ab,xa,xb⟩ <;> exact ⟨a,b,ab,xa,xb⟩
  · rintro ⟨X,hX,strict⟩
    have leX := mS X hX
    have less := strict T hT
    omega

theorem select {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (many : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∃ u v, (G.deleteIncidenceSet z).Adj u v := by
  classical
  obtain ⟨e,he,f,hf,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < G.edgeFinset.card)
  revert he hf ne
  refine e.ind ?_
  intro a b
  refine f.ind ?_
  intro c d he hf ne
  have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp he
  have hcd : G.Adj c d := SimpleGraph.mem_edgeFinset.mp hf
  have pos (k j : Fin n) (h : G.Adj k j) : 0 < G.degree k := by
    exact Finset.card_pos.mpr ⟨j, (G.mem_neighborFinset k j).2 h⟩
  by_cases ha : c ≠ a ∧ d ≠ a
  · exact ⟨a,pos a b hab,c,d,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hcd,ha.1,ha.2⟩⟩
  have hb : c ≠ b ∧ d ≠ b := by
    by_contra h
    push Not at ha h
    apply ne
    simp only [Sym2.eq_iff]
    have h₁ := hab.ne
    have h₂ := hcd.ne
    grind
  exact ⟨b,pos b a hab.symm,c,d,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hcd,hb.1,hb.2⟩⟩

end Peel3566

namespace Peel3566
open PEqualNP.MetaComplexity.CoverPromise

theorem cover_insert {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) (S : Finset (Fin n))
    (cover : IsVertexCover (G.deleteIncidenceSet z) S) : IsVertexCover G (insert z S) := by
  intro u v uv
  by_cases uz : u=z
  · exact Or.inl (by simp [uz])
  by_cases vz : v=z
  · exact Or.inr (by simp [vz])
  rcases cover u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,uz,vz⟩) with us|vs
  · exact Or.inl (Finset.mem_insert_of_mem us)
  · exact Or.inr (Finset.mem_insert_of_mem vs)

theorem drop_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) :
    Drop G (G.deleteIncidenceSet z) ↔
      ∃ T : Finset (Fin n), z∈T ∧ IsVertexCover G T ∧
        ∀ X : Finset (Fin n), IsVertexCover G X → T.card≤X.card := by
  classical
  constructor
  · rintro ⟨S,cov,strict⟩
    refine ⟨insert z S,by simp,cover_insert G z S cov,?_⟩
    intro X hx
    have h := strict X hx
    exact (Finset.card_insert_le z S).trans (by omega)
  · rintro ⟨T,zt,hT,mT⟩
    refine ⟨T.erase z,?_,?_⟩
    · intro u v uv
      obtain ⟨hg,hu,hv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp uv
      rcases hT u v hg with uT|vT
      · exact Or.inl (Finset.mem_erase.mpr ⟨hu,uT⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hv,vT⟩)
    · intro X hX
      have lt := Finset.card_erase_lt_of_mem zt
      exact lt_of_lt_of_le lt (mT X hX)

theorem no_drop_twins {n : ℕ} (G : SimpleGraph (Fin n)) (u v p : Fin n) (uv : u≠v)
    (ua : G.Adj u p) (va : G.Adj v p) (du : ∀ w, G.Adj u w → w=p) (dv : ∀ w, G.Adj v w → w=p) :
    ¬ Drop G (G.deleteIncidenceSet u) := by
  classical
  intro drop
  obtain ⟨T,uT,cov,minT⟩ := (drop_iff G u).1 drop
  have pc : p∉T := by
    intro tp
    have suf : IsVertexCover G (T.erase u) := by
      intro a b ab
      by_cases au : a=u
      · subst a
        exact Or.inr (Finset.mem_erase.mpr ⟨ab.ne.symm,(du b ab) ▸ tp⟩)
      by_cases bu : b=u
      · subst b
        exact Or.inl (Finset.mem_erase.mpr ⟨ab.ne,(du a ab.symm) ▸ tp⟩)
      rcases cov a b ab with ha|hb
      · exact Or.inl (Finset.mem_erase.mpr ⟨au,ha⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨bu,hb⟩)
    exact (Nat.not_lt_of_ge (minT _ suf)) (Finset.card_erase_lt_of_mem uT)
  have vT := (cov v p va).resolve_right pc
  let X := insert p ((T.erase u).erase v)
  have bigger := minT X (by
    intro a b ab
    by_cases au : a=u
    · subst a;exact Or.inr (by simp [X,du b ab])
    by_cases av : a=v
    · subst a;exact Or.inr (by simp [X,dv b ab])
    by_cases bu : b=u
    · subst b;exact Or.inl (by simp [X,du a ab.symm])
    by_cases bv : b=v
    · subst b;exact Or.inl (by simp [X,dv a ab.symm])
    rcases cov a b ab with ha|hb
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨av,Finset.mem_erase.mpr ⟨au,ha⟩⟩))
    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨bv,Finset.mem_erase.mpr ⟨bu,hb⟩⟩)))
  have h1 := Finset.card_erase_lt_of_mem uT
  have h2 := Finset.card_erase_lt_of_mem (Finset.mem_erase.mpr ⟨uv.symm,vT⟩ : v∈T.erase u)
  have h3 : X.card≤((T.erase u).erase v).card+1 := Finset.card_insert_le _ _
  omega
end Peel3566

namespace Peel3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.MetaComplexity.CoverPromise

def Computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  IsAO2 n C ∧ circuitFun n C=graphFun G ∅

def Saves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) (s : Nat) :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D=(fun x : Fin n → Bool => @decide
      (∃ u v, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧ x u=true ∧ x v=true) (Classical.propDecidable _)) ∧
    D.size+G.degree z ≤ s ∧ (Drop G (G.deleteEdges (G.incidenceSet z)) → D.size+G.degree z+1 ≤ s)

theorem saves_mono {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (z : Fin n)
    {s t : ℕ} (hs : Saves G z s) (h : s ≤ t) : Saves G z t := by
  obtain ⟨D,ao,correct,base,bonus⟩ := hs
  exact ⟨D,ao,correct,base.trans h,fun drop => (bonus drop).trans h⟩

theorem chooseLeast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (many : 2 ≤ G.edgeFinset.card)
    (byCircuit : ∀ C : Circuit, Computes G C → ∃ z, 0<G.degree z ∧ Saves G z C.size) :
    ∃ z, 0<G.degree z ∧ ∀ C : Circuit, Computes G C → Saves G z C.size := by
  classical
  by_cases hex : ∃ C : Circuit, Computes G C
  · let P := fun s : ℕ => ∃ C : Circuit, Computes G C ∧ C.size=s
    have hp : ∃ s, P s := by obtain ⟨C,hC⟩ := hex;exact ⟨_,C,hC,rfl⟩
    obtain ⟨C,hC,budget⟩ := Nat.find_spec hp
    obtain ⟨z,hz,win⟩ := byCircuit C hC
    refine ⟨z,hz,fun D hD => saves_mono z win ?_⟩
    rw [budget]
    exact Nat.find_min' hp ⟨D,hD,rfl⟩
  · obtain ⟨z,hz,_⟩ := select G many
    exact ⟨z,hz,fun C hC => False.elim (hex ⟨C,hC⟩)⟩

theorem fixed_from_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (many : 2 ≤ G.edgeFinset.card) (low : ∀ C, Computes G C → MeetsLower G C) :
    ∃ z, 0<G.degree z ∧ ∀ C : Circuit, Computes G C → Saves G z C.size := by
  obtain ⟨z,hz,keep⟩ := select G many
  exact ⟨z,hz,fun C hC => atVertex G z keep C (low C hC)⟩

theorem eval_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (he : circuitFun n C=graphFun G ∅) (x : Fin n → Bool) :
    C.eval (List.ofFn x)=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
  change circuitFun n C x=true ↔ _
  rw [he]
  simp [graphFun]

theorem ao_mono {n : ℕ} (C : Circuit) (ha : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using ha.1 g hg, le_of_eq (ha.2.2 g hg)⟩

end Peel3566


namespace Pin3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def good (m : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
    gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < m+j

def rawReads (z : Nat) (gs : List Gate) := gs.countP (fun g => g.inputs.contains z)

def atWire (w : List Bool) (o : Option Nat) := o.elim false (fun i => w.getD i false)

theorem atWire_append (w : List Bool) (b : Bool) (o : Option Nat) (h : ∀ i ∈ o, i < w.length) :
    atWire (w++[b]) o = atWire w o := by
  cases o with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (h i (by simp))

theorem getD_snoc (xs : List Bool) (b : Bool) (i : Nat) :
    (xs ++ [b]).getD i false = if i=xs.length then b else xs.getD i false := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
  · by_cases eq : i=xs.length
    · subst i; simp
    · rw [List.getD_eq_default _ _ (by simp; omega), ite_eq_right eq, List.getD_eq_default _ _ (by omega)]

theorem run_len (gs : List Gate) (xs : List Bool) : (run gs xs).length=xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (xs++[_])).length=_
    rw [ih];simp;omega

theorem good_snoc {m : Nat} {gs : List Gate} (h : good m gs) (g : Gate)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length=2) (back : ∀ i ∈ g.inputs, i < m + gs.length) :
    good m (gs++[g]) := by
  intro j hj
  by_cases lt : j < gs.length
  · rw [List.getElem_append_left lt]
    exact h j lt
  · have eq : j=gs.length := by simp at hj; omega
    subst j
    simpa using And.intro op (And.intro arity back)

theorem good_left {m : Nat} {gs : List Gate} {g : Gate} (h : good m (gs++[g])) : good m gs := by
  intro j hj
  have v := h j (by simp;omega)
  simpa only [List.getElem_append_left hj] using v

theorem good_last {m : Nat} {gs : List Gate} {g : Gate} (h : good m (gs++[g])) :
    (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ ∀ i ∈ g.inputs, i < m + gs.length := by
  simpa using h gs.length (by simp)

theorem binary {g : Gate} (h : g.inputs.length=2) : ∃ a b, g.inputs=[a,b] := by
  exact List.length_eq_two.mp h

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w = run gs w ++ [g.op.eval (g.inputs.map fun j => (run gs w).getD j false)] := by
  simp [run,List.foldl_append]

theorem translate {n : Nat} (z : Fin n) (gs : List Gate) (hg : good n gs) :
    ∃ (ds : List Gate) (tab : Nat → Option Nat), good n ds ∧
      ds.length + rawReads z.val gs ≤ gs.length ∧ tab z.val = none ∧
      (∀ i, ∀ j ∈ tab i, j < n + ds.length) ∧
      ∀ (x : Fin n → Bool) (i : Nat),
        (run gs (List.ofFn (Function.update x z false))).getD i false =
          atWire (run ds (List.ofFn x)) (tab i) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    let tab : Nat → Option Nat := fun i => if i<n ∧ i≠z.val then some i else none
    refine ⟨[], tab, by simp [good], by simp [rawReads], by simp [tab], ?_, ?_⟩
    · intro i j hj
      by_cases hi : i<n ∧ i≠z.val <;> simp [tab,hi] at hj
      subst j
      simpa using hi.1
    · intro x i
      by_cases hi : i<n
      · let k : Fin n := ⟨i,hi⟩
        by_cases eq : i=z.val
        · have ke : k=z := Fin.ext eq
          subst i
          simp [run,tab,atWire]
        · have kdiff : k ≠ z := fun e => eq (congrArg Fin.val e)
          have on : i<n ∧ i≠z.val := ⟨hi,eq⟩
          change (List.ofFn (Function.update x z false)).getD k.val false = atWire (List.ofFn x) (tab i)
          simp [tab,on,atWire,List.getD_eq_getElem?_getD,hi,k,Function.update_of_ne kdiff]
      · have stop : ¬(i<n ∧ i≠z.val) := fun h => hi h.1
        change (List.ofFn (Function.update x z false)).getD i false = atWire (List.ofFn x) (tab i)
        rw [List.getD_eq_default _ _ (by simp;omega)]
        simp [tab,stop,atWire]
  | append_singleton gs g ih =>
    obtain ⟨ds,tab,gd,sz,tz,live,sim⟩ := ih (good_left hg)
    obtain ⟨op,arity,back⟩ := good_last hg
    obtain ⟨a,b,ab⟩ := binary arity
    let old := n+gs.length
    let new := n+ds.length
    have adjust (added : List Gate) (o : Option Nat)
        (valid : good n (ds++added))
        (cost : (ds++added).length + rawReads z.val (gs++[g]) ≤ (gs++[g]).length)
        (ob : ∀ j ∈ o, j < n + (ds++added).length)
        (carry : ∀ (x : Fin n → Bool) i, atWire (run (ds++added) (List.ofFn x)) (tab i)=atWire (run ds (List.ofFn x)) (tab i))
        (eval : ∀ (x : Fin n → Bool), g.op.eval [atWire (run ds (List.ofFn x)) (tab a),atWire (run ds (List.ofFn x)) (tab b)] =
            atWire (run (ds++added) (List.ofFn x)) o) :
        ∃ (ds : List Gate) (tab : Nat → Option Nat), good n ds ∧
          ds.length + rawReads z.val (gs++[g]) ≤ (gs++[g]).length ∧ tab z.val = none ∧
          (∀ i, ∀ j ∈ tab i, j < n + ds.length) ∧
          ∀ (x : Fin n → Bool) i, (run (gs++[g]) (List.ofFn (Function.update x z false))).getD i false =
            atWire (run ds (List.ofFn x)) (tab i) := by
      let nxt i := if i=old then o else tab i
      have zlt : z.val<old := by dsimp [old];omega
      refine ⟨ds++added,nxt,valid,cost,by simpa [nxt,Nat.ne_of_lt zlt] using tz,?_,?_⟩
      · intro i j h
        by_cases eq : i=old
        · exact ob j (by simpa [nxt,eq] using h)
        · have := live i j (by simpa [nxt,eq] using h)
          simp;omega
      · intro x i
        let xs := List.ofFn (Function.update x z false)
        have len : (run gs xs).length=old := by simp [xs,run_len,old]
        change (run (gs++[g]) xs).getD i false=_
        rw [run_snoc,getD_snoc,len]
        by_cases eq : i=old
        · simp only [ite_eq_left eq,nxt,ab,List.map_cons,List.map_nil]
          rw [show (run gs xs).getD a false=_ from sim x a,
              show (run gs xs).getD b false=_ from sim x b]
          exact eval x
        · simp only [ite_eq_right eq,nxt]
          exact (sim x i).trans (carry x i).symm
    have one : rawReads z.val (gs++[g]) ≤ rawReads z.val gs + 1 := by
      simp [rawReads,List.countP_append];split <;> omega
    have keep (o : Option Nat) (ob : ∀ j ∈ o,j < new)
        (eval : ∀ x : Fin n → Bool, g.op.eval [atWire (run ds (List.ofFn x)) (tab a),atWire (run ds (List.ofFn x)) (tab b)]
          = atWire (run ds (List.ofFn x)) o) := adjust [] o (by simpa using gd)
      (by simp; omega) (by simpa [new] using ob) (by simp) (by simpa using eval)
    cases ea : tab a with
    | none =>
      rcases op with op|op
      · apply keep none (by simp)
        intro x; simp [ea,op,atWire,GateOp.eval]
      · apply keep (tab b) (live b)
        intro x; simp [ea,op,atWire,GateOp.eval]
    | some a' =>
      cases eb : tab b with
      | none =>
        rcases op with op|op
        · apply keep none (by simp)
          intro x; simp [eb,op,atWire,GateOp.eval]
        · apply keep (tab a) (live a)
          intro x; simp [eb,op,atWire,GateOp.eval]
      | some b' =>
        let g' : Gate := ⟨g.op,[a',b']⟩
        have ha : a'<new := live a a' (by simp [ea])
        have hb : b'<new := live b b' (by simp [eb])
        have az : a≠z.val := by rintro rfl; rw [tz] at ea; contradiction
        have bz : b≠z.val := by rintro rfl; rw [tz] at eb; contradiction
        have no : g.inputs.contains z.val=false := by simp [ab,az,bz,Ne.symm az,Ne.symm bz]
        apply adjust [g'] (some new)
        · apply good_snoc gd g' op rfl
          intro i hi
          rcases (by simpa [g'] using hi : i=a' ∨ i=b') with rfl|rfl
          · exact ha
          · exact hb
        · have miss : z.val ∉ g.inputs := by simpa using no
          have eq : rawReads z.val (gs++[g]) = rawReads z.val gs := by
            simp [rawReads,List.countP_append,miss]
          rw [eq]
          simp only [List.length_append,List.length_cons,List.length_nil] 
          omega
        · intro j hj; have eq : new=j := by simpa using hj
          subst j; simp [new]
        · intro x i
          rw [run_snoc]
          apply atWire_append
          intro j hj;simpa [run_len] using live i j hj
        · intro x
          rw [run_snoc]
          have len : (run ds (List.ofFn x)).length=new := by simp [run_len,new]
          simp [g',atWire,getD_snoc,len,ea,eb]
end Pin3566

namespace Pin3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]

theorem good_iff (n : ℕ) (C : Circuit) : IsAO2 n C ↔ good n C.gates := by
  constructor
  · intro h j hj
    have mem := List.getElem_mem hj (l := C.gates)
    exact ⟨h.1 _ mem,h.2.2 _ mem,by simpa [gateAt_eq C j hj] using h.2.1 j hj⟩
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      exact (h j hj).1
    · intro j hj
      simpa [gateAt_eq C j hj] using (h j hj).2.2
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      exact (h j hj).2.1

theorem pinFalse {n : ℕ} (C : Circuit) (z : Fin n) (ao : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (Function.update x z false)) ∧
      D.size + rawReads z.val C.gates ≤ C.size := by
  obtain ⟨ds,tab,gd,sz,_,_,sim⟩ := translate z C.gates ((good_iff n C).1 ao)
  let out := (tab C.output).getD (n+ds.length)
  let D : Circuit := ⟨ds,out⟩
  refine ⟨D,(good_iff n D).2 gd,?_,sz⟩
  intro x
  change (run ds (List.ofFn x)).getD out false = (run C.gates (List.ofFn (Function.update x z false))).getD C.output false
  rw [sim]
  cases e : tab C.output with
  | none =>
    change (run ds (List.ofFn x)).getD out false=false
    have hk : out=n+ds.length := by simp [out,e]
    rw [hk,List.getD_eq_default _ _ (by simp [run_len])]
  | some k => simp [out,e,atWire]

theorem cofactor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) (x : Fin n → Bool) :
    graphFun G ∅ (Function.update x z false) =
      @decide (∃ u v, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧ x u=true ∧ x v=true) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    have uz : u≠z := by rintro rfl; simp at hu
    have vz : v≠z := by rintro rfl; simp at hv
    exact ⟨u,v,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uv,uz,vz⟩,by simpa [Function.update_of_ne uz] using hu,by simpa [Function.update_of_ne vz] using hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    obtain ⟨edge,uz,vz⟩ := SimpleGraph.deleteIncidenceSet_adj.mp uv
    exact ⟨u,v,edge,by simpa [Function.update_of_ne uz] using hu,by simpa [Function.update_of_ne vz] using hv⟩

theorem pinGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (z : Fin n)
    (ao : IsAO2 n C) (he : circuitFun n C=graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D=(fun x : Fin n → Bool =>
      @decide (∃ u v, (G.deleteEdges (G.incidenceSet z)).Adj u v ∧ x u=true ∧ x v=true) (Classical.propDecidable _)) ∧
      D.size+rawReads z.val C.gates ≤ C.size := by
  obtain ⟨D,good,sim,cost⟩ := pinFalse C z ao
  exact ⟨D,good,funext fun x => (sim x).trans ((congrFun he _).trans (cofactor G z x)),cost⟩

end Pin3566


namespace Circuit2636
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma gate_eval_eq_of_not_contains {h : Gate} {i : ℕ}
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not)
    (hlen : h.inputs.length ≤ 2)
    (hnot : (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i = false)
    {w1 w2 : List Bool} (hagree : ∀ k : ℕ, k ≠ i → w1.getD k false = w2.getD k false) :
    h.op.eval (h.inputs.map (fun k => w1.getD k false)) =
      h.op.eval (h.inputs.map (fun k => w2.getD k false)) := by
  rcases hop with hop | hop | hop
  · rw [hop] at hnot ⊢
    have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hlen
    have hfalse : GateOp.and.eval [false] = false := rfl
    rw [hfalse, Bool.cond_false, htake] at hnot
    congr 1
    apply List.map_congr_left
    intro k hk
    apply hagree k
    intro heq
    subst heq
    have hmem : h.inputs.contains k = true := List.contains_iff_mem.mpr hk
    rw [hmem] at hnot
    exact Bool.noConfusion hnot
  · rw [hop] at hnot ⊢
    have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hlen
    have hfalse : GateOp.or.eval [false] = false := rfl
    rw [hfalse, Bool.cond_false, htake] at hnot
    congr 1
    apply List.map_congr_left
    intro k hk
    apply hagree k
    intro heq
    subst heq
    have hmem : h.inputs.contains k = true := List.contains_iff_mem.mpr hk
    rw [hmem] at hnot
    exact Bool.noConfusion hnot
  · rw [hop] at hnot ⊢
    have htrue : GateOp.not.eval [false] = true := rfl
    rw [htrue, Bool.cond_true] at hnot
    cases hinp : h.inputs with
    | nil => rfl
    | cons a rest =>
      rw [hinp] at hnot
      have hne : a ≠ i := by
        intro heq
        subst heq
        simp at hnot
      simp only [GateOp.eval, List.map_cons, List.headD]
      rw [hagree a hne]

private lemma append_getD_agree {w1 w2 : List Bool} {b : Bool} {i : ℕ}
    (hlen : w1.length = w2.length)
    (hagree : ∀ k : ℕ, k ≠ i → w1.getD k false = w2.getD k false) :
    ∀ k : ℕ, k ≠ i → (w1 ++ [b]).getD k false = (w2 ++ [b]).getD k false := by
  intro k hki
  by_cases hk : k < w1.length
  · have hk2 : k < w2.length := hlen ▸ hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hk, List.getElem?_append_left hk2]
    have h := hagree k hki
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at h
    exact h
  · by_cases hkeq : k = w1.length
    · subst hkeq
      have a1 : (w1 ++ [b]).getD w1.length false = b := by simp [List.getD_eq_getElem?_getD]
      have a2 : (w2 ++ [b]).getD w1.length false = b := by
        rw [hlen]; simp [List.getD_eq_getElem?_getD]
      rw [a1, a2]
    · have hge1 : (w1 ++ [b]).length ≤ k := by simp; omega
      have hge2 : (w2 ++ [b]).length ≤ k := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

theorem escape (n : ℕ) (C : Circuit) (v : Fin n) (P Z : Finset (Fin n)) :
    FanInTwo C → C.output ≠ v.val → v ∉ P → v ∉ Z →
    (∃ x : Fin n → Bool, (∀ p ∈ P, x p=true) ∧ (∀ z ∈ Z, x z=false) ∧
      circuitFun n C x ≠ circuitFun n C (Function.update x v true)) →
    ∃ g ∈ C.gates, v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) ∧
      (g.op=.or → ∀ p ∈ P, p.val ∉ g.inputs) ∧ (g.op=.and → ∀ z ∈ Z, z.val ∉ g.inputs) := by
  intro fan notOut vp vz ⟨x,xp,xz,diff⟩
  by_contra none
  let step (s : List Bool) (g : Gate) := s ++ [g.op.eval (g.inputs.map fun k => s.getD k false)]
  have block (g : Gate) (hg : g ∈ C.gates)
      (read : v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2)) :
      (g.op=.or ∧ ∃ p ∈ P, p.val∈g.inputs) ∨ (g.op=.and ∧ ∃ z ∈ Z, z.val∈g.inputs) := by
    by_contra no
    apply none
    refine ⟨g,hg,read,fun op p hp h => no (Or.inl ⟨op,p,hp,h⟩),fun op z hz h => no (Or.inr ⟨op,z,hz,h⟩)⟩
  have iterate (gs : List Gate) (within : ∀ g ∈ gs, g∈C.gates)
      (s t : List Bool) (len : s.length=t.length) (large : n ≤ s.length)
      (agree : ∀ k, k ≠ v.val → s.getD k false = t.getD k false)
      (pos : ∀ p ∈ P, s.getD p.val false=true) (neg : ∀ z ∈ Z, s.getD z.val false=false) :
      ∀ k, k ≠ v.val → (gs.foldl step s).getD k false = (gs.foldl step t).getD k false := by
    induction gs generalizing s t with
    | nil => exact agree
    | cons g gs ih =>
      have cg := within g (by simp)
      have value : g.op.eval (g.inputs.map fun k => s.getD k false) =
          g.op.eval (g.inputs.map fun k => t.getD k false) := by
        by_cases h : v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2)
        · rcases block g cg h with ⟨op,p,hp,ip⟩|⟨op,z,hz,iz⟩
          · have ne : p.val ≠ v.val := fun eq => vp ((Fin.ext eq) ▸ hp)
            have use (w : List Bool) (on : w.getD p.val false=true) :
                g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
              rw [op]
              simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
              exact ⟨p.val,ip,on⟩
            exact (use s (pos p hp)).trans (use t ((agree p.val ne).symm.trans (pos p hp))).symm
          · have ne : z.val ≠ v.val := fun eq => vz ((Fin.ext eq) ▸ hz)
            have use (w : List Bool) (off : w.getD z.val false=false) :
                g.op.eval (g.inputs.map fun k => w.getD k false) = false := by
              rw [op]
              cases eq : GateOp.and.eval (g.inputs.map fun k => w.getD k false) with
              | false => rfl
              | true =>
                simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at eq
                have no := eq z.val iz
                rw [off] at no
                contradiction
            exact (use s (neg z hz)).trans (use t ((agree z.val ne).symm.trans (neg z hz))).symm
        · have hf := fan g cg
          apply gate_eval_eq_of_not_contains (by simpa using hf.1) hf.2 _ agree
          simpa [List.contains_iff_mem] using h
      change ∀ k, k≠v.val → (gs.foldl step (step s g)).getD k false = (gs.foldl step (step t g)).getD k false
      apply ih (fun h hh => within h (by simp [hh])) (step s g) (step t g) (by simp [step,len]) (by simp [step]; omega)
      · simpa only [step,value] using (append_getD_agree (b := g.op.eval (g.inputs.map fun k => t.getD k false)) len agree)
      · intro p hp
        change (s ++ [_]).getD p.val false = true
        rw [List.getD_append _ _ _ _ (by have := p.isLt; omega)]
        exact pos p hp
      · intro z hz
        change (s ++ [_]).getD z.val false = false
        rw [List.getD_append _ _ _ _ (by have := z.isLt; omega)]
        exact neg z hz
  let y := Function.update x v true
  have agree (k : ℕ) (hk : k ≠ v.val) :
      (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
    by_cases h : k<n
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,dite_true,Option.getD_some]
      exact (Function.update_of_ne (show (⟨k,h⟩ : Fin n) ≠ v from fun e => hk (congrArg Fin.val e)) true x).symm
    · simp [List.getD_eq_getElem?_getD,h]
  apply diff
  apply iterate C.gates (fun _ h => h) (List.ofFn x) (List.ofFn y) (by simp) (by simp) agree
    (fun p hp => by simpa [List.getD_eq_getElem?_getD] using xp p hp)
    (fun z hz => by simpa [List.getD_eq_getElem?_getD] using xz z hz) C.output notOut

end Circuit2636

namespace Peel3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm Pin3566

theorem singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) :
    graphFun G ∅ (fun w => decide (w=z)) = false := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_false_iff_not,decide_eq_true_eq]
  rintro ⟨u,v,uv,rfl,rfl⟩
  exact uv.ne rfl

theorem incident_reads {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : Computes G C) (z p : Fin n) (zp : G.Adj z p) :
    0 < rawReads z.val C.gates := by
  classical
  have fan : FanInTwo C := by
    intro g hg
    refine ⟨?_, le_of_eq (hc.1.2.2 g hg)⟩
    rcases hc.1.1 g hg with op|op <;> simp [op]
  have out : C.output ≠ z.val := by
    intro eq
    let x : Fin n → Bool := fun w => decide (w=z)
    have bad : circuitFun n C x = false :=
      (congrFun hc.2 x).trans (singleton_false G z)
    change (Builder3566.run C.gates (List.ofFn x)).getD C.output false = false at bad
    rw [eq,Builder3566.run_keep _ _ _ (by simp)] at bad
    simpa [x,List.getD_eq_getElem?_getD] using bad
  let x : Fin n → Bool := fun w => decide (w=p)
  have off : circuitFun n C x=false := (congrFun hc.2 x).trans (singleton_false G p)
  have on : circuitFun n C (Function.update x z true)=true := by
    apply (eval_graph G C hc.2 _).2
    exact ⟨z,p,zp,by simp,by simp [Function.update_of_ne zp.ne.symm,x]⟩
  obtain ⟨g,hg,read,_,_⟩ := Circuit2636.escape n C z ∅ ∅ fan out (by simp) (by simp)
    ⟨x,by simp,by simp,by rw [on,off];decide⟩
  exact List.countP_pos_iff.mpr ⟨g,hg,List.contains_iff_mem.mpr (List.mem_of_mem_take read)⟩

theorem counted {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (hc : Computes G C)
    (z : Fin n) (base : G.degree z ≤ rawReads z.val C.gates)
    (bonus : Drop G (G.deleteEdges (G.incidenceSet z)) → G.degree z+1 ≤ rawReads z.val C.gates) :
    Saves G z C.size := by
  obtain ⟨D,ao,correct,cost⟩ := pinGraph G C z hc.1 hc.2
  exact ⟨D,ao,correct,by omega,fun drop => by have := bonus drop;omega⟩

theorem leaf_no_drop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z p : Fin n)
    (zp : G.Adj z p) (deg : G.degree z=1) (nd : ¬Drop G (G.deleteIncidenceSet z)) :
    ∃ k, 0<G.degree k ∧ ∀ C : Circuit, Computes G C → Saves G k C.size := by
  refine ⟨z,by omega,fun C hc => counted G C hc z ?_ (fun h => (nd h).elim)⟩
  have := incident_reads G C hc z p zp
  omega

theorem twins {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v p : Fin n) (uv : u≠v)
    (ua : G.Adj u p) (va : G.Adj v p) (du : ∀ w, G.Adj u w → w=p) (dv : ∀ w, G.Adj v w → w=p) :
    ∃ k, 0<G.degree k ∧ ∀ C : Circuit, Computes G C → Saves G k C.size := by
  apply leaf_no_drop G u p ua _ (no_drop_twins G u v p uv ua va du dv)
  have h : G.neighborFinset u = {p} := by
    ext w
    rw [G.mem_neighborFinset,Finset.mem_singleton]
    exact ⟨du w,fun e => e ▸ ua⟩
  show (G.neighborFinset u).card = 1
  simp [h]

end Peel3566


namespace PEqualNP.Outside.L_meta_720

-- Adapted from Mads Anker Nielsen’s subdivided K4 proof and the project circuit lemmas.
open PEqualNP.MetaComplexity

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

end

end PEqualNP.MetaComplexity.Helpers

end

section


namespace PEqualNP.MetaComplexity.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.MetaComplexity.Helpers.PermInputs

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.MetaComplexity.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers

end

section


namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not

def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ NotFree C.gates ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem HasMonoSize.has {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ} (h : HasMonoSize n f s) :
    HasCircuitSize n f s := by
  obtain ⟨C, h1, _, h3, h4⟩ := h
  exact ⟨C, h1, h3, h4⟩

theorem HasMonoSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ} (h : HasMonoSize n f s)
    (hs : s ≤ s') : HasMonoSize n f s' := by
  obtain ⟨C, h1, h2, h3, h4⟩ := h
  exact ⟨C, h1, h2, le_trans h3 hs, h4⟩

def MClean (m : ℕ) (gs : List Gate) : Prop := CleanL m gs ∧ NotFree gs

def Computes (m : ℕ) (gs : List Gate) (o : ℕ) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ x : Fin m → Bool, vl gs x o = f x

def LeastIn (Q : List Gate → Prop) (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate)
    (o : ℕ) : Prop :=
  CleanL m gs ∧ Q gs ∧ Computes m gs o f ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → Q gs' → Computes m gs' o' f →
      gs.length ≤ gs'.length

def MLeast (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  LeastIn NotFree m f gs o

theorem MLeast.clean {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (h : MLeast m f gs o) : MClean m gs := ⟨h.1, h.2.1⟩

noncomputable def RdSet (gs : List Gate) (w : ℕ) : Finset ℕ := by
  classical exact (Finset.range gs.length).filter (fun q => Reads gs q w)

theorem mem_rdSet {gs : List Gate} {w q : ℕ} : q ∈ RdSet gs w ↔ Reads gs q w := by
  classical
  unfold RdSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨reads_len h, h⟩⟩

def pt {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun i => decide (i ∈ S)

def Removable (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ) : Prop :=
  ∀ p ∈ S, p < gs.length ∧
    ((∃ j, tgt p = some j ∧ j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j) ∨
      (tgt p = none ∧ o ≠ m + p ∧ (∀ q, Reads gs q (m + p) → q ∈ S) ∧
        ∀ q ∈ S, tgt q ≠ some (m + p)))

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open SimpleGraph

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs
open SimpleGraph

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

end PEqualNP.MetaComplexity.Helpers.Forest

end

section


namespace PEqualNP.MetaComplexity.Loc

open SimpleGraph
open PEqualNP.MetaComplexity.Helpers.Forest

noncomputable def tau {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k}

noncomputable def Phi1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  A.card + G.edgeSet.ncard + tau G

def AFree {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∉ A

structure Run {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop where
  nd : [a', a, s, t, b, b'].Nodup
  ha : ∀ w, G.Adj a w ↔ w = a' ∨ w = s
  hs : ∀ w, G.Adj s w ↔ w = a ∨ w = t
  ht : ∀ w, G.Adj t w ↔ w = s ∨ w = b
  hb : ∀ w, G.Adj b w ↔ w = t ∨ w = b'
  ha' : ∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c
  hb' : ∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c

theorem Run.symm {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Run G b' b t s a a' where
  nd := by
    have := List.nodup_reverse.2 h.nd
    simpa using this
  ha := fun w => (h.hb w).trans Or.comm
  hs := fun w => (h.ht w).trans Or.comm
  ht := fun w => (h.hs w).trans Or.comm
  hb := fun w => (h.ha w).trans Or.comm
  ha' := h.hb'
  hb' := h.ha'

def BoundOf {n : ℕ} (Sz : ((Fin n → Bool) → Bool) → ℕ → Prop) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Prop :=
  ∀ s : ℕ, Sz (F G A) s → Phi1 G A ≤ s + 1

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open SimpleGraph

abbrev Bound {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  BoundOf (HasMonoSize n) G A

def IH {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)), G' ≤ G → AFree G' A' →
    (G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) → Bound G' A'

structure Cex {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) :
    Prop where
  inv : AFree G A
  ih : IH G A
  least : MLeast n (F G A) gs o
  small : gs.length + 2 ≤ Phi1 G A

structure Ctx {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) : Prop where
  cex : Cex G A gs o
  run : Run G a' a s t b b'
  hA : A = ∅

theorem Ctx.symm {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    {a' a s t b b' : Fin n} (h : Ctx G A gs o a' a s t b b') : Ctx G A gs o b' b t s a a' :=
  ⟨h.cex, h.run.symm, h.hA⟩

structure Fan {n : ℕ} (gs : List Gate) (a s t b : Fin n) (qa qs qt qb : ℕ) : Prop where
  fa : RdSet gs a = {qa}
  fs : RdSet gs s = {qs}
  ft : RdSet gs t = {qt}
  fb : RdSet gs b = {qb}

theorem Fan.symm {n : ℕ} {gs : List Gate} {a s t b : Fin n} {qa qs qt qb : ℕ}
    (h : Fan gs a s t b qa qs qt qb) : Fan gs b t s a qb qt qs qa :=
  ⟨h.fb, h.ft, h.fs, h.fa⟩

def ToolLeast : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), (∃ x y : Fin n → Bool, f x ≠ f y) →
    HasMonoSize n f s → ∃ (gs : List Gate) (o : ℕ), MLeast n f gs o ∧ gs.length ≤ s

def ToolOfClean : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ), MClean m gs →
    HasMonoSize m (fun x => vl gs x o) gs.length

def ToolRemoval : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ), CleanL m gs → Removable m gs o P S tgt →
    ∃ (gs' : List Gate) (r : ℕ → ℕ), CleanL m gs' ∧ (NotFree gs → NotFree gs') ∧
      gs'.length + S.card ≤ gs.length ∧ (∀ j, j < m → r j = j) ∧
      ∀ j, j < m + gs.length → (∀ p ∈ S, tgt p = none → j ≠ m + p) →
        r j < m + gs'.length ∧ ∀ x ∈ P, vl gs' x (r j) = vl gs x j

def ToolNoAlias : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) → ∀ p, p < gs.length → ∀ j, j < m + p →
      ¬ ∀ x : Fin m → Bool, vl gs x (m + p) = vl gs x j

def ToolLive : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) →
      o < m + gs.length ∧ ∀ p, p < gs.length → o ≠ m + p → (RdSet gs (m + p)).Nonempty

def ToolProp : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (x x' : Fin m → Bool) (D : Set ℕ) (K : ℕ), CleanL m gs →
    (∀ i : Fin m, (i : ℕ) ∉ D → x i = x' i) →
    (∀ p g, gs[p]? = some g → m + p < K → m + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ vl gs x (m + p) = vl gs x' (m + p)) →
    ∀ j, j < K → j ∉ D → vl gs x j = vl gs x' j

end PEqualNP.MetaComplexity.Loc

end

section


namespace PEqualNP.MetaComplexity.Loc.Clean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Loc

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    NotFree gs → NotFree acc.2 → NotFree (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

theorem ToolOfClean_proof : ToolOfClean := by
  intro m gs o h
  refine ⟨⟨gs, o⟩, ?_, h.2, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok m gs h.1 g hg).1

def HasMClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ NotFree gs ∧ gs.length ≤ s ∧ Computes n gs o f

theorem mclean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasMonoSize n f s) : HasMClean n f s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · exact elim_mono n C.gates _ hnf (by intro g hg; simp at hg)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem ToolLeast_proof : ToolLeast := by
  classical
  intro n f s hnc h
  have hc := mclean_of n f s hnc h
  have hex : ∃ t, HasMClean n f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hnf, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hnf, hev, ?_⟩, by omega⟩
  intro gs' o' hc' hn' he'
  have := Nat.find_min' hex ⟨gs', o', hc', hn', le_refl _, he'⟩
  omega

theorem relabel_mono {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasMonoSize n h s) : HasMonoSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact hnf g0 hg0
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end PEqualNP.MetaComplexity.Loc.Clean
end
namespace Pendant3566
open _root_.PEqualNP.CircuitLowerBounds _root_.PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Loc

theorem mono_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, nf, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have gfree : NotFree gs := by
    intro g hg
    obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg
    have no := nf g0 h0
    cases op : g0.op <;> simp_all [normGate]
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), Clean.elim_mono n gs _ gfree (by intro _ h; simp at h), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

theorem mono_two_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasMonoSize (n + 1) (fun x => f (x ∘ σ)) s := Clean.relabel_mono (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := mono_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := Clean.relabel_mono (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end Pendant3566
end PEqualNP.Outside.L_meta_720


namespace PEqualNP.Outside.L_meta_720.Marked3566
open _root_.PEqualNP.CircuitLowerBounds _root_.PEqualNP.MetaComplexity _root_.PEqualNP.MetaComplexity.NestedCover
open _root_.PEqualNP.TopForm _root_.Peel3566
open PEqualNP.MetaComplexity.Loc

theorem exactModel {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (hnc : ∃ x y, f x ≠ f y) (hs : HasMonoSize n f s) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ D.size ≤ s := by
  obtain ⟨gs,o,clean,nf,bound,he⟩ := Clean.mclean_of n f s hnc hs
  let D : Circuit := ⟨gs,o⟩
  refine ⟨D,(_root_.Pin3566.good_iff n D).2 ?_,funext he,bound⟩
  change _root_.Pin3566.good n gs
  intro j hj
  have hit : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  rcases clean j _ hit with ⟨op,_⟩|⟨op,a,b,ha,hb,ab⟩
  · exact (nf _ (List.getElem_mem hj) op).elim
  · refine ⟨op,by simp [ab],?_⟩
    intro i hi
    rcases (by simpa [ab] using hi : i=a ∨ i=b) with rfl|rfl
    · exact ha
    · exact hb

end PEqualNP.Outside.L_meta_720.Marked3566


namespace Peel3566
open PEqualNP.MetaComplexity.NestedCover

theorem leaf_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z p : Fin n)
    (zp : G.Adj z p) (uniq : ∀ w, G.Adj z w → w=p)
    (x : Fin n → Bool) :
    graphFun G ∅ (Function.update x z true) =
      (x p || @decide (∃ a b, (G.deleteIncidenceSet p).Adj a b ∧ x a=true ∧ x b=true) (Classical.propDecidable _)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    by_cases az : a=z
    · subst a
      have bp := uniq b ab
      subst b
      exact Or.inl (by simpa [Function.update_of_ne zp.ne.symm] using hb)
    by_cases bz : b=z
    · subst b
      have ap := uniq a ab.symm
      subst a
      exact Or.inl (by simpa [Function.update_of_ne zp.ne.symm] using ha)
    rw [Function.update_of_ne az] at ha
    rw [Function.update_of_ne bz] at hb
    by_cases ap : a=p
    · exact Or.inl (ap ▸ ha)
    by_cases bp : b=p
    · exact Or.inl (bp ▸ hb)
    exact Or.inr ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,ap,bp⟩,ha,hb⟩
  · rintro (hp|⟨a,b,ab,ha,hb⟩)
    · exact ⟨z,p,zp,by simp,by simpa [Function.update_of_ne zp.ne.symm] using hp⟩
    · obtain ⟨edge,ap,bp⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
      have az : a≠z := by rintro rfl;exact bp (uniq b edge)
      have bz : b≠z := by rintro rfl;exact ap (uniq a edge.symm)
      exact ⟨a,b,edge,by simpa [Function.update_of_ne az] using ha,by simpa [Function.update_of_ne bz] using hb⟩
end Peel3566

namespace Peel3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm Pin3566

noncomputable def resid {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) (x : Fin n→Bool) : Bool :=
  @decide (∃ a b, (G.deleteEdges (G.incidenceSet p)).Adj a b ∧ x a=true ∧ x b=true) (Classical.propDecidable _)

theorem resid_zero {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    resid G p (fun _ => false)=false := by simp [resid]

theorem resid_pin {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) (x : Fin n→Bool) :
    resid G p (Function.update x p false)=resid G p x := by
  apply Bool.eq_iff_iff.mpr
  simp only [resid,decide_eq_true_eq]
  constructor <;> rintro ⟨a,b,ab,ha,hb⟩ <;> refine ⟨a,b,ab,?_,?_⟩
  · simpa only [Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.1] using ha
  · simpa only [Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.2] using hb
  · simpa only [Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.1] using ha
  · simpa only [Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.2] using hb

theorem read_because {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (p : Fin n)
    (w x : Fin n→Bool) (wp : w p=false) (hw : circuitFun n C w=true)
    (off : circuitFun n C x=false) (on : circuitFun n C (Function.update x p true)=true) :
    0 < rawReads p.val C.gates := by
  have fan : FanInTwo C := by
    intro g hg
    rcases ao.1 g hg with h|h <;> exact ⟨by simp [h],le_of_eq (ao.2.2 g hg)⟩
  have out : C.output ≠ p.val := by
    intro eq
    change (Builder3566.run C.gates (List.ofFn w)).getD C.output false = true at hw
    rw [eq,Builder3566.run_keep _ _ _ (by simp)] at hw
    simpa [List.getD_eq_getElem?_getD,wp] using hw
  obtain ⟨g,hg,reads,_,_⟩ := Circuit2636.escape n C p ∅ ∅ fan out (by simp) (by simp)
    ⟨x,by simp,by simp,by rw [on,off]; decide⟩
  exact List.countP_pos_iff.mpr ⟨g,hg,List.contains_iff_mem.mpr (List.mem_of_mem_take reads)⟩

theorem clear_split {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) (A : Circuit)
    (ao : IsAO2 n A) (remote : ∃ a b, (G.deleteIncidenceSet p).Adj a b)
    (value : ∀ x, circuitFun n A x=(x p || resid G p x)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D=resid G p ∧ D.size+1≤A.size := by
  classical
  obtain ⟨a,b,ab⟩ := remote
  let w := Function.update (fun _ : Fin n => true) p false
  have wa : w a=true := by simp [w,Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.1]
  have wb : w b=true := by simp [w,Function.update_of_ne (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.2]
  have rwit : resid G p w=true := by
    simp only [resid,decide_eq_true_eq]
    exact ⟨a,b,ab,wa,wb⟩
  let zero : Fin n→Bool := fun _ => false
  have reads := read_because A ao p w zero (by simp [w]) (by simp [value,rwit])
    (by simp [value,zero,resid_zero]) (by simp [value])
  obtain ⟨D,da,de,ds⟩ := pinFalse A p ao
  exact ⟨D,da,funext fun t => by rw [de,value,resid_pin]; simp,by omega⟩

end Peel3566

namespace PEqualNP.Outside.L_meta_720.Pendant3566
open _root_.PEqualNP.CircuitLowerBounds _root_.PEqualNP.TopForm _root_.PEqualNP.MetaComplexity
open _root_.PEqualNP.MetaComplexity.NestedCover _root_.Peel3566 PEqualNP.MetaComplexity.Loc

theorem residual_after_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (l z : Fin n)
    (leaf : ∀ w, G.Adj l w → w=z) :
    (G.deleteIncidenceSet l).deleteIncidenceSet z = G.deleteIncidenceSet z := by
  ext a b
  simp only [SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · rintro ⟨⟨ab,_,_⟩,az,bz⟩
    exact ⟨ab,az,bz⟩
  · rintro ⟨ab,az,bz⟩
    refine ⟨⟨ab,?_,?_⟩,az,bz⟩
    · rintro rfl
      exact bz (leaf _ ab)
    · rintro rfl
      exact az (leaf _ ab.symm)

theorem graph_resid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) :
    graphFun (G.deleteIncidenceSet z) ∅ = resid G z := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [graphFun,resid]

theorem clear_vertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : _root_.Peel3566.Computes G C) (z u : Fin n) (zu : G.Adj z u) :
    ∃ D : Circuit, _root_.Peel3566.Computes (G.deleteIncidenceSet z) D ∧ D.size+1≤C.size := by
  have r := incident_reads G C hc z u zu
  obtain ⟨D,ao,eq,cost⟩ := _root_.Pin3566.pinGraph G C z hc.1 hc.2
  have eq' : circuitFun n D = resid G z := eq
  exact ⟨D,⟨ao,eq'.trans (graph_resid G z).symm⟩,by omega⟩

theorem residual_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (l z : Fin n)
    (leaf : ∀ w,G.Adj l w → w=z) :
    resid (G.deleteIncidenceSet l) z = resid G z := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [resid,decide_eq_true_eq,residual_after_leaf G l z leaf]

theorem pay_last_leaf {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj]
    (C : Circuit) (hc : _root_.Peel3566.Computes G C) (z p u : Fin (n+1))
    (zp : G.Adj z p) (uniq : ∀ w, G.Adj z w → w=p) (pu : G.Adj p u) (uz : u≠z)
    (remote : ∃ a b, (G.deleteIncidenceSet p).Adj a b) :
    ∃ D : Circuit, IsAO2 (n+1) D ∧ circuitFun (n+1) D=resid G p ∧ D.size+3≤C.size := by
  classical
  let f := graphFun G ∅
  let zero : Fin (n+1)→Bool := fun _ => false
  let oneP : Fin (n+1)→Bool := fun t => decide (t=p)
  have f0 : f oneP=false := singleton_false G p
  have f1 : f (Function.update oneP z true)=true := by
    change graphFun G ∅ _=true
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    exact ⟨z,p,zp,by simp,by simp [oneP,Function.update_of_ne zp.ne.symm]⟩
  have flip : (!oneP z)=true := by simp [oneP,zp.ne]
  have dep : ∃ x, f (Function.update x z (!x z)) ≠ f x :=
    ⟨oneP,by rw [flip,f1,f0]; decide⟩
  have low (b : Bool) : f (Function.update zero z b)=false := by
    cases b
    · have eq : Function.update zero z false=zero := by
        funext i; by_cases h : i=z <;> simp [zero,h,Function.update_of_ne]
      rw [eq]; simp [f,zero,graphFun]
    · have eq : Function.update zero z true=(fun w => decide (w=z)) := by
        funext i
        by_cases h : i=z <;> simp [zero,h,Function.update_of_ne]
      rw [eq]; exact singleton_false G z
  obtain ⟨a,b,ab⟩ := remote
  have az : a≠z := by rintro rfl; exact (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.2 (uniq b (SimpleGraph.deleteIncidenceSet_adj.mp ab).1)
  have bz : b≠z := by rintro rfl; exact (SimpleGraph.deleteIncidenceSet_adj.mp ab).2.1 (uniq a (SimpleGraph.deleteIncidenceSet_adj.mp ab).1.symm)
  let ones : Fin (n+1)→Bool := fun _ => true
  have upper (k : Bool) : f (Function.update ones z k)=true := by
    change graphFun G ∅ _ = true
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    exact ⟨a,b,(SimpleGraph.deleteIncidenceSet_adj.mp ab).1,by simp [ones,Function.update_of_ne az],
      by simp [ones,Function.update_of_ne bz]⟩
  have nc (k : Bool) : ∃ x y, f (Function.update x z k) ≠ f (Function.update y z k) :=
    ⟨ones,zero,by rw [upper,low]; decide⟩
  have has : HasMonoSize _ f C.size := by
    refine ⟨C,?_,?_,le_rfl,congrFun hc.2⟩
    · intro g hg
      rcases hc.1.1 g hg with op|op <;> exact ⟨by simp [op],le_of_eq (hc.1.2.2 g hg)⟩
    · intro g hg
      rcases hc.1.1 g hg with op|op <;> simp [op]
  obtain ⟨k,s,sz,hs⟩ := mono_two_at n f z C.size dep nc has
  obtain ⟨A,aa,af,asize⟩ := Marked3566.exactModel (nc k) hs
  cases k with
  | false =>
    have eq : circuitFun (n+1) A = resid G z :=
      funext fun x => (congrFun af x).trans (_root_.Pin3566.cofactor G z x)
    have ac : _root_.Peel3566.Computes (G.deleteIncidenceSet z) A :=
      ⟨aa,eq.trans (graph_resid G z).symm⟩
    have pu' : (G.deleteIncidenceSet z).Adj p u :=
      SimpleGraph.deleteIncidenceSet_adj.mpr ⟨pu,zp.ne.symm,uz⟩
    obtain ⟨D,dc,cost⟩ := clear_vertex _ A ac p u pu'
    have de := dc.2.trans (graph_resid (G.deleteIncidenceSet z) p)
    exact ⟨D,dc.1,de.trans (residual_eq G z p uniq),by omega⟩
  | true =>
    have value (x) : circuitFun (n+1) A x=(x p || resid G p x) :=
      (congrFun af x).trans (leaf_true G z p zp uniq x)
    obtain ⟨D,da,de,cost⟩ := clear_split G p A aa ⟨a,b,ab⟩ value
    exact ⟨D,da,de,by omega⟩

end PEqualNP.Outside.L_meta_720.Pendant3566

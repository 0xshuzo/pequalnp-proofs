import Mathlib
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

end Peel3566

namespace Peel3566
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.MetaComplexity.CoverPromise

theorem positive_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (he : Computes G C) (u v : Fin n) (uv : G.Adj u v) : 0<C.size := by
  by_contra! zero
  have gs : C.gates=[] := List.length_eq_zero_iff.mp (by change C.gates.length≤0 at zero;omega)
  by_cases h : C.output<n
  · let k : Fin n := ⟨C.output,h⟩
    let x : Fin n → Bool := fun i => decide (i=k)
    have yes : C.eval (List.ofFn x)=true := by
      simp [Circuit.eval,Circuit.wires,gs,x,k,List.getD_eq_getElem?_getD,h]
    obtain ⟨a,b,ab,ha,hb⟩ := (eval_graph G C he.2 x).1 yes
    have ak : a=k := of_decide_eq_true ha
    have bk : b=k := of_decide_eq_true hb
    exact ab.ne (ak.trans bk.symm)
  · let x : Fin n → Bool := fun _ => true
    have yes := (eval_graph G C he.2 x).2 ⟨u,v,uv,rfl,rfl⟩
    simpa [Circuit.eval,Circuit.wires,gs,List.getD_eq_getElem?_getD,h] using yes

theorem base_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (he : Computes G C) (small : G.edgeFinset.card≤1) : MeetsLower G C := by
  classical
  intro T _ ht
  by_cases ep : G.edgeFinset.Nonempty
  · have one : G.edgeFinset.card=1 := by have := Finset.card_pos.mpr ep;omega
    obtain ⟨e,eq⟩ := Finset.card_eq_one.mp one
    revert eq
    refine e.ind ?_
    intro u v eq
    have uv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (by rw [eq];simp)
    have pos := positive_cost G C he u v uv
    have ct := ht {u} (by
      intro a b ab
      have mem := SimpleGraph.mem_edgeFinset.mpr ab
      rw [eq,Finset.mem_singleton] at mem
      rcases Sym2.eq_iff.mp mem with ⟨au,_⟩|⟨_,bu⟩
      · exact Or.inl (Finset.mem_singleton.mpr au)
      · exact Or.inr (Finset.mem_singleton.mpr bu))
    simp only [Finset.card_singleton] at ct
    omega
  · have e := Finset.not_nonempty_iff_eq_empty.mp ep
    have ct := ht ∅ (by
      intro a b ab
      have mem := SimpleGraph.mem_edgeFinset.mpr ab
      rw [e] at mem
      exact (Finset.notMem_empty _ mem).elim)
    have z : T.card≤0 := by simpa only [Finset.card_empty] using ct
    have card : T.card=0 := by omega
    simp [e,card]

theorem hereditary_converse {n : ℕ} (K : SimpleGraph (Fin n))
    (peel : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G≤K → 2≤G.edgeFinset.card →
      ∃ z, 0<G.degree z ∧ ∀ C : Circuit, Computes G C → Saves G z C.size) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G≤K → ∀ C : Circuit, Computes G C → MeetsLower G C := by
  classical
  intro G inst le C hc
  generalize e : G.edgeFinset.card = m
  induction m using Nat.strong_induction_on generalizing G C with
  | _ m ih =>
    by_cases small : G.edgeFinset.card≤1
    · exact base_lower G C hc small
    obtain ⟨z,hz,good⟩ := peel G le (by omega)
    obtain ⟨D,ao,correct,base,bonus⟩ := good C hc
    let H := G.deleteIncidenceSet z
    have split : H.edgeFinset.card=G.edgeFinset.card-G.degree z :=
      G.card_edgeFinset_deleteIncidenceSet z
    have degLe : G.degree z ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree z]
      exact Finset.card_le_card (G.incidenceFinset_subset z)
    have hH : H≤K := (G.deleteIncidenceSet_le z).trans le
    have ch : Computes H D := by
      refine ⟨ao,?_⟩
      rw [correct]
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
      constructor <;> rintro ⟨a,b,ab,xa,xb⟩ <;> exact ⟨a,b,ab,xa,xb⟩
    have low : MeetsLower H D := by
      apply ih H.edgeFinset.card (by omega) H hH D ch rfl
    intro T cov minT
    obtain ⟨S,cvS,minS⟩ := minCover H
    have lc := low S cvS minS
    have extend := minT (insert z S) (cover_insert G z S cvS)
    have lim := Finset.card_insert_le z S
    by_cases less : S.card<T.card
    · have drop : Drop G (G.deleteEdges (G.incidenceSet z)) :=
        ⟨S,cvS,fun X hX => lt_of_lt_of_le less (minT X hX)⟩
      have := bonus drop
      omega
    · omega

end Peel3566

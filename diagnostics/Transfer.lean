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


namespace Transfer2585
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm Peel3566

/-- For an arbitrary AO2 DAG, removing any finite family of vertices of degree at
    most one saves at least the number of removed edges, including shared readers. -/
theorem leaves {n : ℕ} (S : Finset (Fin n)) :
    ∀ (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Circuit),
      Computes G C → (∀ v∈S,G.degree v ≤ 1) →
      (∀ a b, H.Adj a b ↔ G.Adj a b ∧ a∉S ∧ b∉S) →
      ∃ D : Circuit, Computes H D ∧ D.size+G.edgeFinset.card ≤ C.size+H.edgeFinset.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro G H iG iH C hc _ relation
    have eq : H=G := by ext a b; simpa using relation a b
    subst H
    exact ⟨C,hc,le_rfl⟩
  | @insert v S fresh ih =>
    intro G H iG iH C hc deg relation
    let K := G.deleteIncidenceSet v
    have size := G.card_edgeFinset_deleteIncidenceSet v
    change K.edgeFinset.card=G.edgeFinset.card-G.degree v at size
    have dg : G.degree v ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree v]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
    have ds := deg v (Finset.mem_insert_self ..)
    have budget : G.degree v ≤ Pin3566.rawReads v.val C.gates := by
      by_cases nz : (G.neighborFinset v).Nonempty
      · obtain ⟨w,hw⟩ := nz
        have := Peel3566.incident_reads G C hc v w ((G.mem_neighborFinset v w).mp hw)
        omega
      · have e := Finset.not_nonempty_iff_eq_empty.mp nz
        have z : G.degree v=0 := Finset.card_eq_zero.mpr e
        omega
    obtain ⟨B,ao,correct,elim⟩ := Pin3566.pinGraph G C v hc.1 hc.2
    have cb : Computes K B := by
      refine ⟨ao,?_⟩
      rw [correct]
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
      constructor <;> rintro ⟨a,b,ab,xa,xb⟩ <;> exact ⟨a,b,ab,xa,xb⟩
    have kd (x : Fin n) (hx : x∈S) : K.degree x ≤ 1 := by
      have sub : K.neighborFinset x ⊆ G.neighborFinset x := by
        intro y hy
        exact (G.mem_neighborFinset x y).2 ((G.deleteIncidenceSet_le v) ((K.mem_neighborFinset x y).1 hy))
      exact (Finset.card_le_card sub).trans (deg x (Finset.mem_insert_of_mem hx))
    have hk (a b) : H.Adj a b ↔ K.Adj a b ∧ a∉S ∧ b∉S := by
      rw [relation]
      simp only [K,SimpleGraph.deleteIncidenceSet_adj,Finset.mem_insert,not_or]
      tauto
    obtain ⟨D,cD,rest⟩ := ih K H B cb kd hk
    exact ⟨D,cD,by omega⟩

end Transfer2585

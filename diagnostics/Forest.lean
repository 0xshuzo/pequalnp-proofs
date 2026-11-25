import Mathlib
import PEqualNP.Outside.L_meta_1003
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_237
import PEqualNP.Outside.L_meta_243

namespace Forest3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1003_aux.H926
open PEqualNP.Outside.L_meta_1485 (gateAt_eq)

abbrev V (n : Nat) := Fin n → Bool

def raw (n : Nat) (w : List Bool) : V n := fun i => w.getD i.val false

def bit (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def Safe (F : Prop) (w : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2 ∧ (∀ u∈g.inputs, u<w.length) ∧
      (g.op=.and → bit g w=true → F)) ∧ Safe F (w++[bit g w]) gs

theorem append_safe (F : Prop) (w : List Bool) (s t : List Gate) (hs : Safe F w s)
    (ht : Safe F (wiresFrom s w) t) : Safe F w (s++t) := by
  induction s generalizing w with
  | nil => exact ht
  | cons g gs ih => exact ⟨hs.1, ih _ hs.2 ht⟩

theorem spec (F : Prop) (w : List Bool) (gs : List Gate) (safe : Safe F w gs)
    (j : Nat) (hj : j<gs.length) :
    (gs[j].op=.and ∨ gs[j].op=.or) ∧ gs[j].inputs.length≤2 ∧
    (∀ u∈gs[j].inputs, u<w.length+j) ∧
    (gs[j].op=.and → (wiresFrom gs w).getD (w.length+j) false=true → F) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have ⟨⟨op,len,back,hit⟩,_⟩ := safe
      refine ⟨op,len,by simpa using back,?_⟩
      intro hand h
      apply hit hand
      change (wiresFrom gs (w++[bit g w])).getD (w.length+0) false = true at h
      rw [Nat.add_zero,getD_wiresFrom _ _ _ (by simp),getD_snoc_eq] at h
      exact h
    | succ j =>
      have h := ih (w++[bit g w]) safe.2 j (by simpa using hj)
      have idx : (w++[bit g w]).length+j=w.length+(j+1) := by simp; omega
      rw [idx] at h
      exact h

def Build {n : Nat} (target : V n → Prop) (f : V n → Bool) (s : Nat) : Prop :=
  ∀ m, n≤m → ∃ (gs : List Gate) (o : Nat), gs.length ≤ s ∧ o<m+gs.length ∧
    ∀ w : List Bool, w.length=m →
      (wiresFrom gs w).getD o false=f (raw n w) ∧ Safe (target (raw n w)) w gs

variable {n : Nat} {T : V n → Prop}

theorem bld_mono {F : V n → Bool} {s t} (h : Build T F s) (leq : s≤t) : Build T F t := by
  intro m hm
  obtain ⟨gs,o,len,lt,ok⟩ := h m hm
  exact ⟨gs,o,len.trans leq,lt,ok⟩

theorem bld_congr {F H : V n → Bool} {s} (h : Build T F s) (eq : ∀ x, F x=H x) :
    Build T H s := by
  have : F=H := funext eq
  rwa [← this]

theorem bld_var (i : Fin n) : Build T (fun x => x i) 0 := by
  intro m hm
  exact ⟨[],i.val,le_rfl,by simp; omega,fun _ _ => ⟨rfl,True.intro⟩⟩

theorem bld_bin (op : GateOp) (hop : op=.and ∨ op=.or) (c : Bool → Bool → Bool)
    (hc : ∀ a b, op.eval [a,b]=c a b)
    {F H : V n → Bool} {s1 s2 : Nat} (h1 : Build T F s1) (h2 : Build T H s2)
    (safe : op=.and → ∀ x, c (F x) (H x)=true → T x) :
    Build T (fun x => c (F x) (H x)) (s1+s2+1) := by
  intro m hm
  obtain ⟨gs1,o1,len1,ho1,ev1⟩ := h1 m hm
  obtain ⟨gs2,o2,len2,ho2,ev2⟩ := h2 (m+gs1.length) (by omega)
  let g : Gate := ⟨op,[o1,o2]⟩
  refine ⟨gs1++gs2++[g],m+gs1.length+gs2.length,by simp; omega,by simp; omega,?_⟩
  intro w hw
  let v := wiresFrom gs1 w
  let u := wiresFrom gs2 v
  have lv : v.length=m+gs1.length := by simp [v,length_wiresFrom,hw]
  have lu : u.length=m+gs1.length+gs2.length := by simp [u,length_wiresFrom,lv]
  have rv : raw n v=raw n w := by
    funext i
    exact getD_wiresFrom _ _ _ (by omega)
  have e1 : u.getD o1 false=F (raw n w) :=
    (getD_wiresFrom _ _ _ (by omega)).trans (ev1 w hw).1
  have e2 : u.getD o2 false=H (raw n w) := (ev2 v lv).1.trans (congrArg H rv)
  have output : bit g u=c (F (raw n w)) (H (raw n w)) := by
    change op.eval [u.getD o1 false,u.getD o2 false]=_
    rw [hc,e1,e2]
  constructor
  · rw [wiresFrom_append,wiresFrom_append]
    change (u++[bit g u]).getD (m+gs1.length+gs2.length) false=_
    rw [←lu,getD_snoc_eq,output]
  · apply append_safe
    · exact append_safe _ _ _ _ (ev1 w hw).2 (rv ▸ (ev2 v lv).2)
    · rw [wiresFrom_append]
      change Safe (T (raw n w)) u [g]
      refine ⟨⟨hop,by decide,?_,?_⟩,True.intro⟩
      · intro y hy
        rcases (show y=o1 ∨ y=o2 by simpa [g] using hy) with rfl | rfl <;> omega
      · intro hand up
        exact safe hand _ (output ▸ up)

theorem bld_or {F H : V n → Bool} {s1 s2} (a : Build T F s1) (b : Build T H s2) :
    Build T (fun x => F x || H x) (s1+s2+1) :=
  bld_bin .or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) a b (by intro h; cases h)

theorem bld_and {F H : V n → Bool} {s1 s2} (a : Build T F s1) (b : Build T H s2)
    (safe : ∀ x, F x=true → H x=true → T x) : Build T (fun x => F x && H x) (s1+s2+1) :=
  bld_bin .and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) a b
    (fun _ x h => safe x (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2)

theorem realize {F : V n → Bool} {k : Nat} (h : Build T F k) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size≤k ∧ (∀ x, circuitFun n D x=F x) ∧
      ∀ j<D.gates.length, (gateAt D j).op=.and → ∀ x : V n,
        (D.wires (List.ofFn x)).getD (n+j) false=true → T x := by
  obtain ⟨gs,o,len,_,ok⟩ := h n le_rfl
  let D : Circuit := ⟨gs,o⟩
  have rr (x : V n) : raw n (List.ofFn x)=x := by
    funext i
    exact getD_ofFn x i
  have ss (x : V n) (j) (hj : j<gs.length) := spec _ _ _ (ok (List.ofFn x) (by simp)).2 j hj
  refine ⟨D,?_,?_,len,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    have p := ss (fun _ => false) j hj
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using p.1,p.2.1⟩
  · intro j hj u hu
    rw [gateAt_eq hj] at hu
    simpa using (ss (fun _ => false) j hj).2.2.1 u hu
  · intro x
    exact (ok (List.ofFn x) (by simp)).1.trans (congrArg F (rr x))
  · intro j hj hand x up
    rw [gateAt_eq hj] at hand
    have hh := (ss x j hj).2.2.2 hand (by simpa only [List.length_ofFn] using up)
    rwa [rr x] at hh

theorem bld_anyList (vs : List (Fin n)) : ∀ v : Fin n,
    Build T (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset (S : Finset (Fin n)) (hS : S.Nonempty) :
    Build T (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (ambient : Finset (Sym2 (Fin n))) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty → E ⊆ ambient →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Build (fun x => ∃ e ∈ ambient, ∀ v ∈ e, x v = true) (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE subset hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE subset hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Build (fun x => ∃ e ∈ ambient, ∀ v ∈ e, x v = true) (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (T := fun x => ∃ e ∈ ambient, ∀ v ∈ e, x v = true)
        (bld_var t) (bld_anyFinset S hSne) (by
          intro x xt xv
          obtain ⟨v,hv,hot⟩ := of_decide_eq_true xv
          refine ⟨s(t,v),subset (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).1,?_⟩
          intro i hi
          rcases Sym2.mem_iff.mp hi with rfl | rfl <;> assumption)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 (fun v hv => subset (Finset.mem_filter.mp hv).1) c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 (fun v hv => subset (Finset.mem_filter.mp hv).1) c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hE : ∃ i j, G.Adj i j) (hc : ∀ i j, G.Adj i j → i∈T ∨ j∈T) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ G.edgeFinset.card+T.card-1 ∧
      (∀ x, circuitFun n D x=decide (∃ i j, G.Adj i j ∧ x i=true ∧ x j=true)) ∧
      ∀ j<D.gates.length, (gateAt D j).op=.and → ∀ x : V n,
        (D.wires (List.ofFn x)).getD (n+j) false=true → ∃ i k, G.Adj i k ∧ x i=true ∧ x k=true := by
  classical
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  have equiv (x : V n) : (∃ e∈G.edgeFinset, ∀ v∈e, x v=true) ↔
      ∃ i j, G.Adj i j ∧ x i=true ∧ x j=true := by
    constructor
    · rintro ⟨e, he, h⟩
      revert he h
      refine Sym2.ind (fun a b => ?_) e
      intro he h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨s(i, j), by simpa using hij, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
  obtain ⟨D,hm,back,size,ev,hands⟩ := realize (bld_edges n G.edgeFinset T G.edgeFinset hne (fun _ h => h) cov)
  refine ⟨D,hm,back,size,?_,?_⟩
  · intro x
    rw [ev,decide_eq_decide]
    exact equiv x
  · intro j hj hand x on
    exact (equiv x).mp (hands j hj hand x on)

theorem forest (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (acyclic : G.IsAcyclic) (has : ∃ u v, G.Adj u v) (C : Circuit) (hm : Monotone2 C)
    (eval : ∀ x : V n, circuitFun n C x = decide (∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size≤C.size ∧
      (∀ x, circuitFun n D x = decide (∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)) ∧
      (∀ j<D.gates.length, (gateAt D j).op=.and → ∀ x : V n,
        (D.wires (List.ofFn x)).getD (n+j) false=true → ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      (∀ j<D.gates.length, (gateAt D j).op=.and → ∀ i : Fin n,
        (D.wires (List.ofFn (fun w : Fin n => decide (w=i)))).getD (n+j) false=false) := by
  classical
  let f := fun x : V n => decide (∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
  have all : ∃ t, ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧ T.card=t :=
    ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  let t := Nat.find all
  obtain ⟨T,cover,card⟩ := Nat.find_spec all
  have min (U : Finset (Fin n)) (hU : CoverPromise.IsVertexCover G U) : t≤U.card :=
    Nat.find_min' all ⟨U,hU,rfl⟩
  have repr : HasCircuitSize n f C.size := by
    refine ⟨C,?_,le_rfl,eval⟩
    intro g hg
    obtain ⟨op,count⟩ := hm g hg
    exact ⟨by simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢; tauto,count⟩
  have price := (PEqualNP.Outside.L_meta_243 n t C.size G acyclic has ⟨T,cover,card⟩ min).mp
    (PEqualNP.Outside.L_meta_237 n f C.size repr)
  obtain ⟨D,md,back,size,ev,strong⟩ := edge_upper n G T has cover
  refine ⟨D,md,back,by omega,ev,strong,?_⟩
  intro j hj hand i
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u,v,adj,hu,hv⟩ := strong j hj hand _ h
  have eu : u=i := of_decide_eq_true hu
  have ev' : v=i := of_decide_eq_true hv
  exact adj.ne (eu.trans ev'.symm)

end Forest3321

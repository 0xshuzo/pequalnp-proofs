import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2069
import PEqualNP.Outside.L_meta_2067

namespace Rail2071
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2069

-- The counting argument below is from L2069. Its soundness hypothesis is
-- only used at gates structurally reachable from the output.
set_option maxHeartbeats 2000000 in
lemma assembleLive {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (hsz : m ≤ 64) (hout : o < 26+m)
    (inp : ∀ t : Vtx, S t.val = {t}) (out0 : S o = ∅)
    (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (Q : Vtx → Vtx → ℕ → Prop)
    (qIn : ∀ x y t : Vtx, Q x y t.val → t = x ∨ t = y)
    (qOut : ∀ x y, adjb x y = true → Q x y o)
    (qStep : ∀ x y j, Q x y (W j) →
      (A j → Q x y (a j) ∧ Q x y (b j)) ∧ (¬ A j → Q x y (a j) ∨ Q x y (b j)))
    (sound : ∀ j, Needed a b o (W j) → A j → ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true)
    (x y : Vtx) (edge : adjb x y = true) (D : ℕ → Prop) (dy : D y.val)
    (dAnd : ∀ j, A j → ((x ∈ S (a j) ∧ D (b j)) ∨ (D (a j) ∧ x ∈ S (b j))) → D (W j))
    (dOr : ∀ j, ¬ A j → D (a j) ∨ D (b j) → D (W j)) : D o := by
  classical
  let U := roots a b S o
  have rootAnd (j : Fin m) (hj : j ∈ U) : A j := by
    by_contra no
    obtain ⟨_,h0,f⟩ := (Finset.mem_filter.mp hj).2
    rw [(ops j).2 no,Finset.union_eq_empty] at h0
    exact f.1.ne_empty h0.1
  have sov (j : Fin m) (hj : j ∈ U) := sound j (Finset.mem_filter.mp hj).2.1 (rootAnd j hj)
  obtain ⟨z,leaf,hside,hstar⟩ := starChoice a b S o sov
  have wlt (j : Fin m) : W j < 26+m := Nat.add_lt_add_left j.isLt _
  have seek (s t : Vtx) (h : adjb s t = true) : ∃ j ∈ U, Cross a b S j s t := by
    suffices run : ∀ w < 26+m, Needed a b o w → Q s t w →
        (s ∈ S w ∨ t ∈ S w) ∨ ∃ j ∈ U, Cross a b S j s t by
      simpa [out0] using run o hout (fun _ ho _ => ho) (qOut s t h)
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw qw
      rcases decomp hw with lo | ⟨j,rfl⟩
      · let v : Vtx := ⟨w,lo⟩
        have eq : S w = {v} := inp v
        rcases qIn s t v qw with e | e
        · exact .inl (.inl (by rw [eq,Finset.mem_singleton]; exact e.symm))
        · exact .inl (.inr (by rw [eq,Finset.mem_singleton]; exact e.symm))
      obtain ⟨na,nb⟩ := children nw
      by_cases aj : A j
      · obtain ⟨qa,qb⟩ := (qStep s t j qw).1 aj
        rcases ih _ (ha j) ((ha j).trans hw) na qa with hitsA | got
        · rcases ih _ (hb j) ((hb j).trans hw) nb qb with hitsB | got
          · right
            have single (v) (h1 : v ∈ S (a j)) (h2 : v ∈ S (b j)) : False := by
              have e := sound j nw aj v h1 v h2
              rw [adj_irr] at e
              contradiction
            rcases hitsA with aa | aa <;> rcases hitsB with bb | bb
            · exact (single s aa bb).elim
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨s,aa⟩,⟨t,bb⟩⟩,.inl ⟨aa,bb⟩⟩
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨t,aa⟩,⟨s,bb⟩⟩,.inr ⟨aa,bb⟩⟩
            · exact (single t aa bb).elim
          · exact .inr got
        · exact .inr got
      · rcases (qStep s t j qw).2 aj with qa | qb
        · have hh := ih _ (ha j) ((ha j).trans hw) na qa
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
        · have hh := ih _ (hb j) ((hb j).trans hw) nb qb
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
  have st (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases aj : A j
    · exact .inl ((ops j).1 aj)
    · exact .inr ((ops j).2 aj)
  have low (w : ℕ) (hw : w < 26) : (S w).card ≤ 1 := by
    rw [inp (⟨w,hw⟩ : Vtx)]
    simp
  have bound (j) : leaf j < 26+m := (hside j).elim (fun e => e.symm ▸ (ha j).trans (wlt j))
    (fun e => e.symm ▸ (hb j).trans (wlt j))
  obtain ⟨tight,full,apart⟩ := tallyRoots a b S o z leaf low ha hb st bound hsz
    (fun j hj => (hstar j hj).1) (by
      rintro ⟨s,t⟩ he
      obtain ⟨_,hst,adj⟩ := Finset.mem_filter.mp he
      obtain ⟨j,hj,hcr⟩ := seek s t adj
      obtain ⟨u,hu,eq⟩ := (hstar j hj).2 s t hcr
      exact ⟨j,hj,u,hu,by simpa [tag,min_eq_left hst.le,max_eq_right hst.le] using eq⟩)
  obtain ⟨r,hr,cr⟩ := seek x y edge
  have ys : ∀ w < 26+m, y ∈ S w → D w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hy
      rcases decomp hw with lo | ⟨k,rfl⟩
      · have ht : y = (⟨w,lo⟩ : Vtx) := Finset.mem_singleton.mp ((inp ⟨w,lo⟩) ▸ hy)
        have e : y.val = w := congrArg Fin.val ht
        exact e ▸ dy
      by_cases ak : A k
      · simp [(ops k).1 ak] at hy
      · rw [(ops k).2 ak,Finset.mem_union] at hy
        exact dOr k ak (hy.imp (ih _ (ha k) ((ha k).trans hw)) (ih _ (hb k) ((hb k).trans hw)))
  apply route a b S A o ha hb neab (fun t => by rw [inp]; simp) out0 ops z leaf full
      (fun j hj s t hc => ⟨by
        rcases hc with ⟨aa,bb⟩ | ⟨aa,bb⟩
        · exact sov j hj s aa t bb
        · exact (adj_symm s t).trans (sov j hj t aa s bb),(hstar j hj).2 s t hc⟩)
      apart tight r hr ?_ D ?_ dOr
  · intro l hl H hp hl' hc hroot
    suffices hh : ∀ w < 26+m, Needed a b o w → Q (z r) l w → H w from
      hh o hout (fun _ ho _ => ho) (qOut _ _ ((mem_N _ _).mp hl))
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw hq
      rcases decomp hw with lo | ⟨j,rfl⟩
      · rcases qIn _ _ ⟨w,lo⟩ hq with eq | eq
        · have e : w = (z r).val := congrArg Fin.val eq
          exact e.symm ▸ hp
        · have e : w = l.val := congrArg Fin.val eq
          exact e.symm ▸ hl'
      by_cases e : j = r
      · exact e.symm ▸ hroot
      obtain ⟨na,nb⟩ := children nw
      have ia := ih _ (ha j) ((ha j).trans hw) na
      have ib := ih _ (hb j) ((hb j).trans hw) nb
      by_cases aj : A j
      · obtain ⟨q1,q2⟩ := (qStep _ _ _ hq).1 aj
        exact (hc j nw e).1 aj (ia q1) (ib q2)
      · exact (hc j nw e).2 aj (((qStep _ _ _ hq).2 aj).imp ia ib)
  · apply dAnd r (rootAnd r hr)
    rcases cr with ⟨aa,bb⟩ | ⟨aa,bb⟩
    · exact .inl ⟨aa,ys _ ((hb r).trans (wlt r)) bb⟩
    · exact .inr ⟨ys _ ((ha r).trans (wlt r)) aa,bb⟩


inductive Rail (C : Circuit) (v : Vtx) : ℕ → Prop
  | input : Rail C v v.val
  | next (j : Fin C.gates.length) {w : ℕ} (hop : C.gates[j.val].op=.or)
      (hw : w ∈ C.gates[j.val].inputs) (h : Rail C v w) : Rail C v (26+j.val)

lemma rail_raw (C : Circuit) (v t : Vtx) : Rail C v t.val ↔ t=v := by
  constructor
  · intro h
    generalize eq : t.val=z at h
    cases h with
    | input => exact Fin.ext eq
    | next j op hw hr => have := t.isLt; omega
  · rintro rfl
    exact .input

lemma rail_gate (C : Circuit) (v : Vtx) (j : Fin C.gates.length) :
    Rail C v (26+j.val) ↔ C.gates[j.val].op=.or ∧
      ∃ w∈C.gates[j.val].inputs, Rail C v w := by
  constructor
  · intro h
    generalize eq : 26+j.val=z at h
    cases h with
    | input => have := v.isLt; omega
    | next k op hw hr =>
      have e : j=k := Fin.ext (by omega)
      subst k
      exact ⟨op,_,hw,hr⟩
  · rintro ⟨op,w,hw,hr⟩
    exact .next j op hw hr

def Live (C : Circuit) (w : ℕ) : Prop :=
  ∀ H : ℕ → Prop, H C.output →
    (∀ j : Fin C.gates.length, H (26+j.val) → ∀ i∈C.gates[j.val].inputs, H i) → H w

def SoundCross (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length, Live C (26+j.val) → C.gates[j.val].op=.and →
    ∀ a b : ℕ, C.gates[j.val].inputs=[a,b] → ∀ u v : Vtx,
      Rail C u a → Rail C v b → adjb u v=true

theorem flags : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → SoundCross x4 → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l dP dL size gates correct _ sound incidence traceP traceL
  classical
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  let S (w : ℕ) : Sup := Finset.univ.filter fun v => Rail C v w
  have mem (w : ℕ) (u : Vtx) : u ∈ S w ↔ Rail C u w := by simp [S]
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have same (s t : Vtx) : V (pr s t) C.output ↔ adjb s t = true :=
    (correct (pr s t)).trans (pairSpec s t).symm
  have off (s : Vtx) : ¬V (one s) C.output := by
    intro h
    have eq : one s = pr s s := by funext v; simp [one,pr]
    rw [eq] at h
    have h1 := (same s s).1 h
    simp [adj_irr] at h1
  have railOne (v : Vtx) (w : ℕ) (h : Rail C v w) : V (one v) w := by
    induction h with
    | input =>
      change val C.gates v.val (one v) =true
      rw [val_input _ _ _ v.isLt]
      simp [one]
    | @next j i ho hi hr ih =>
      have no : ¬ A j := by change (g j).op ≠ .and; rw [show (g j).op=.or from ho]; intro eq; cases eq
      apply (orEv _ j no).mpr
      change i∈(g j).inputs at hi
      rw [pins j] at hi
      rcases List.mem_cons.mp hi with ha | hb
      · exact Or.inl (ha ▸ ih)
      · obtain e : i=b j := List.mem_singleton.mp hb
        exact Or.inr (e ▸ ih)
  let X : Vtx := Fin.castAdd 13 p
  let Y : Vtx := Fin.natAdd 13 l
  have edge : adjb X Y = true := (adjSide p l).2 incidence
  have hout : C.output < 26+m := by
    by_contra! h
    have yes := (same X Y).2 edge
    change val C.gates C.output (pr X Y) = true at yes
    rw [val_big _ _ _ h] at yes
    contradiction
  left
  apply assembleLive a b S A C.output ha hb ne size hout ?_ ?_ ?_
    (fun s t w => V (pr s t) w) ?_ (fun s t => (same s t).2) ?_ ?_
    X Y edge (fun w => dP w = true) ?_ ?_ ?_
  · intro t
    ext s
    rw [mem,rail_raw,Finset.mem_singleton]
    exact eq_comm
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    exact fun v hv => off v (railOne v _ ((mem _ _).mp hv))
  · intro j
    constructor
    · intro aj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have ho := ((rail_gate C v j).mp ((mem _ _).mp hv)).1
      change (g j).op=.or at ho
      rw [show (g j).op=.and from aj] at ho
      contradiction
    · intro no
      ext v
      simp only [Finset.mem_union,mem]
      change Rail C v (26+j.val) ↔ _
      rw [rail_gate]
      change (g j).op=.or ∧ (∃ i∈(g j).inputs, Rail C v i) ↔ _
      simp [orOp j no,pins j]
  · intro s t v h
    change val C.gates v.val (pr s t) = true at h
    rw [val_input _ _ _ v.isLt] at h
    exact of_decide_eq_true h
  · intro s t j h
    exact ⟨fun op => (andEv _ j op).1 h,fun op => (orEv _ j op).1 h⟩
  · intro j needed op s hs t ht
    apply sound j _ op _ _ (pins j) s t ((mem _ _).mp hs) ((mem _ _).mp ht)
    intro H hOut hstep
    apply needed H hOut
    intro k hk
    have both := hstep k hk
    change ∀ i∈(g k).inputs, H i at both
    rw [pins k] at both
    exact ⟨both _ (by simp),both _ (by simp)⟩
  · rw [traceP.1 _ Y.isLt]
    simp [Y,Nat.add_comm]
  · intro j op h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).1 op]
    simp only [Bool.or_eq_true,Bool.and_eq_true]
    exact h.imp (fun hh => ⟨railOne _ _ ((mem _ _).mp hh.1),hh.2⟩) (fun hh => ⟨hh.1,railOne _ _ ((mem _ _).mp hh.2)⟩)
  · intro j no h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).2 (orOp _ no),Bool.or_eq_true]
    exact h

end Rail2071
namespace Source2071

abbrev Gate (m : ℕ) := Fin m
def w {m : ℕ} (j : Gate m) := 26+j.val

inductive Feed {m : ℕ} (a b : Gate m → ℕ) (k : Gate m) : ℕ → Prop
  | here : Feed a b k (w k)
  | left (j : Gate m) (h : Feed a b k (a j)) : Feed a b k (w j)
  | right (j : Gate m) (h : Feed a b k (b j)) : Feed a b k (w j)

def SourceOnly {m : ℕ} (a b : Gate m → ℕ) (A : Gate m → Prop) (d : Gate m) :=
  ∀ k j, A k → A j → (Feed a b k (a j) ∨ Feed a b k (b j)) → k=d

def Live {m : ℕ} (a b : Gate m → ℕ) (o i : ℕ) :=
  ∀ H : ℕ → Prop, H o → (∀ j, H (w j) → H (a j) ∧ H (b j)) → H i

lemma reaches {m} {a b : Gate m → ℕ} {k : Gate m} {o : ℕ} (h : Live a b o (w k)) :
    Feed a b k o := by
  by_contra absent
  have h' := h (fun i => ¬Feed a b k i) absent (fun j hj =>
    ⟨fun ha => hj (.left j ha),fun hb => hj (.right j hb)⟩)
  exact h' .here

def Values {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (D : ℕ → Bool) :=
  ∀ j, (A j → D (w j) = (D (a j) && D (b j))) ∧
    (¬A j → D (w j) = (D (a j) || D (b j)))

lemma source_dirty {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o}
    (one : SourceOnly a b A d) (ak : A k) (hk : Live a b o (w k)) (Y : ℕ → Bool)
    (value : Values a b A Y) (yk : Y (w k)=true) (yo : Y o=false) : Y (w d)=true := by
  by_cases same : k=d
  · rwa [←same]
  have forward (i : ℕ) (h : Feed a b k i) : Y i=true := by
    induction h with
    | here => exact yk
    | left j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inl hj))
      simp [(value j).2 nj,ih]
    | right j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inr hj))
      simp [(value j).2 nj,ih]
  exact Bool.noConfusion ((forward o (reaches hk)).symm.trans yo)

inductive Parse {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (x y : ℕ) :
    ℕ → ℕ → ℕ → Prop
  | xleaf : Parse a b A x y x 1 0
  | yleaf : Parse a b A x y y 0 1
  | join (j : Gate m) (op : A j) {u v s t : ℕ}
      (ha : Parse a b A x y (a j) u v) (hb : Parse a b A x y (b j) s t) :
      Parse a b A x y (w j) (u+s) (v+t)
  | left (j : Gate m) (op : ¬A j) {u v : ℕ} (ha : Parse a b A x y (a j) u v) :
      Parse a b A x y (w j) u v
  | right (j : Gate m) (op : ¬A j) {u v : ℕ} (hb : Parse a b A x y (b j) u v) :
      Parse a b A x y (w j) u v

lemma feed_le {m} {a b : Gate m → ℕ} (ha : ∀ j,a j < w j) (hb : ∀ j,b j < w j)
    {k : Gate m} {i : ℕ} (f : Feed a b k i) : w k ≤ i := by
  induction f with
  | here => exact le_rfl
  | left j _ h => exact h.trans (ha j).le
  | right j _ h => exact h.trans (hb j).le

def Above {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (w0 : ℕ) (S : Gate m → Prop) :=
  ∀ k, A k → Feed a b k w0 → S k

-- For any chosen proof, a wire with no AND ancestors contributes one leaf.
-- If its only possible AND ancestor is d, it contributes at most two;
-- if d is true on Y and the wire is false, it contributes just one.
lemma bound {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d : Gate m} {x y i u v}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    {Y : ℕ → Bool} (yd : Y (w d)=true) (val : Values a b A Y)
    (proof : Parse a b A x y i u v) :
    (Above a b A i (fun _ => False) → u+v=1) ∧
    (Above a b A i (fun k => k=d) → u+v ≤ 2 ∧ (Y i=false → u+v=1)) ∧
    (Y i=false → u+v ≤ 3) := by
  induction proof with
  | xleaf => simp
  | yleaf => simp
  | @join j op u v s t pr1 pr2 ih1 ih2 =>
    have oa : Above a b A (a j) (fun k => k=d) := fun k ak f => one k j ak op (.inl f)
    have ob : Above a b A (b j) (fun k => k=d) := fun k ak f => one k j ak op (.inr f)
    obtain ⟨small1,short1⟩ := ih1.2.1 oa
    obtain ⟨small2,short2⟩ := ih2.2.1 ob
    refine ⟨fun empty => (empty j op .here).elim,?_,?_⟩
    · intro only
      have eq : j=d := only j op .here
      have e1 : u+v=1 := ih1.1 (fun k ak f => by
        have same := (oa k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (ha j)) le)
      have e2 : s+t=1 := ih2.1 (fun k ak f => by
        have same := (ob k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (hb j)) le)
      refine ⟨by omega,?_⟩
      intro h
      rw [eq,yd] at h
      contradiction
    · intro no
      rw [(val j).1 op,Bool.and_eq_false_iff] at no
      rcases no with h | h
      · have := short1 h; omega
      · have := short2 h; omega
  | left j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (a j) S :=
      fun k ak f => all k ak (.left j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).1
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩
  | right j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (b j) S :=
      fun k ak f => all k ak (.right j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).2
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩

lemma parse_of_value {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j)
    (D : ℕ → Bool) (ops : Values a b A D)
    (raw : ∀ i<26,D i=true → i=x ∨ i=y) :
    ∀ i, i<26+m → D i=true → ∃ u v, Parse a b A x y i u v := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi on
    by_cases small : i<26
    · rcases raw i small on with rfl | rfl
      · exact ⟨1,0,.xleaf⟩
      · exact ⟨0,1,.yleaf⟩
    let j : Gate m := ⟨i-26,by omega⟩
    have eq : i=w j := by dsimp [w,j]; omega
    have pa := ih (a j) ((ha j).trans_le eq.symm.le) (by have := ha j; omega)
    have pb := ih (b j) ((hb j).trans_le eq.symm.le) (by have := hb j; omega)
    rw [eq] at on ⊢
    by_cases op : A j
    · obtain ⟨va,vb⟩ := Bool.and_eq_true_iff.mp (((ops j).1 op).symm.trans on)
      obtain ⟨u,v,pu⟩ := pa va
      obtain ⟨s,t,pv⟩ := pb vb
      exact ⟨_,_,.join j op pu pv⟩
    · rcases Bool.or_eq_true_iff.mp (((ops j).2 op).symm.trans on) with va | vb
      · obtain ⟨u,v,pu⟩ := pa va
        exact ⟨_,_,.left j op pu⟩
      · obtain ⟨s,t,pv⟩ := pb vb
        exact ⟨_,_,.right j op pv⟩

def Trace {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (X M : ℕ → Bool) :=
  ∀ j, (A j → M (w j) = (X (a j) && M (b j) || M (a j) && X (b j))) ∧
       (¬A j → M (w j) = (M (a j) || M (b j)))

lemma counts {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y i u v}
    {X Y L P : ℕ → Bool} (vx : Values a b A X) (vy : Values a b A Y)
    (tl : Trace a b A X L) (tp : Trace a b A Y P)
    (xx : X x=true) (yy : Y y=true) (lx : P x=true) (ly : L y=true)
    (proof : Parse a b A x y i u v) :
    (u=0 → Y i=true) ∧ (u=1 → P i=true) ∧ (v=0 → X i=true) ∧ (v=1 → L i=true) := by
  induction proof with
  | xleaf => simp [xx,lx]
  | yleaf => simp [yy,ly]
  | @join j op u v s t _ _ qa qb =>
    obtain ⟨py,pm,px,pn⟩ := qa
    obtain ⟨qy,qm,qx,qn⟩ := qb
    refine ⟨?_,?_,?_,?_⟩
    · intro e
      simp [(vy j).1 op,py (by omega),qy (by omega)]
    · intro e
      rw [(tp j).1 op]
      have alt : (u=0 ∧ s=1) ∨ (u=1 ∧ s=0) := by omega
      rcases alt with ⟨aa,bb⟩ | ⟨aa,bb⟩ <;> simp_all
    · intro e
      simp [(vx j).1 op,px (by omega),qx (by omega)]
    · intro e
      rw [(tl j).1 op]
      have alt : (v=0 ∧ t=1) ∨ (v=1 ∧ t=0) := by omega
      rcases alt with ⟨aa,bb⟩ | ⟨aa,bb⟩ <;> simp_all
  | left j op _ ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    exact ⟨fun e => by simp [(vy j).2 op,h0 e], fun e => by simp [(tp j).2 op,h1 e],
      fun e => by simp [(vx j).2 op,h2 e], fun e => by simp [(tl j).2 op,h3 e]⟩
  | right j op _ ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    exact ⟨fun e => by simp [(vy j).2 op,h0 e], fun e => by simp [(tp j).2 op,h1 e],
      fun e => by simp [(vx j).2 op,h2 e], fun e => by simp [(tl j).2 op,h3 e]⟩

theorem single_source {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o x y : ℕ}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    (ak : A k) (live : Live a b o (w k)) {B X Y Z L P : ℕ → Bool}
    (vb : Values a b A B) (vx : Values a b A X) (vy : Values a b A Y)
    (vz : Values a b A Z) (tl : Trace a b A X L) (tp : Trace a b A Y P)
    (hout : o<26+m) (raw : ∀ i<26,B i=true → i=x ∨ i=y)
    (bp : B o=true) (nx : X o=false) (ny : Y o=false)
    (xx : X x=true) (yy : Y y=true) (lx : P x=true) (ly : L y=true)
    (zk : Z (w k)=true) (zo : Z o=false) : L o=true ∨ P o=true := by
  obtain ⟨u,v,pt⟩ := parse_of_value ha hb B vb raw o hout bp
  have small := (bound ha hb one (source_dirty one ak live Z vz zk zo) vz pt).2.2 zo
  obtain ⟨u0,u1,v0,v1⟩ := counts vx vy tl tp xx yy lx ly pt
  have hu : u≠0 := by intro h; have := u0 h; simp_all
  have hv : v≠0 := by intro h; have := v0 h; simp_all
  by_cases e : u=1
  · exact Or.inr (u1 e)
  · exact Or.inl (v1 (by omega))

end Source2071

namespace OneSource2071
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2069
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def UniqueLower (C : Circuit) :=
  ∃ d : Fin C.gates.length, ∀ k j : Fin C.gates.length,
    C.gates[k.val].op = .and → C.gates[j.val].op = .and →
    InCone 26 C k.val j.val → k=d

theorem solution : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   UniqueLower x4 → x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l dP dL uniq size gates correct nested dirty incidence traceP traceL
  classical
  by_cases sound : Rail2071.SoundCross C
  · exact Rail2071.flags C p l dP dL size gates correct nested sound incidence traceP traceL
  unfold Rail2071.SoundCross at sound
  push_neg at sound
  obtain ⟨k,live,ak,u,v,hins,s,t,railS,railT,miss⟩ := sound
  obtain ⟨d,hd⟩ := uniq
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have same (s t : Vtx) : V (pr s t) C.output ↔ adjb s t = true :=
    (correct (pr s t)).trans (pairSpec s t).symm
  have off (s : Vtx) : ¬V (one s) C.output := by
    intro h
    have eq : one s = pr s s := by funext v; simp [one,pr]
    rw [eq] at h
    have h1 := (same s s).1 h
    simp [adj_irr] at h1

  let E (x : Vtx → Bool) (i : ℕ) := val C.gates i x
  have vals (x : Vtx → Bool) : Source2071.Values a b A (E x) := by
    intro j
    constructor
    · intro op
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.and_eq_true] using andEv x j op
    · intro no
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.or_eq_true] using orEv x j no
  have reach (t : Vtx) (i : ℕ) (rail : Rail2071.Rail C t i) (f : Vtx → Bool) (hf : f t=true) :
      V f i := by
    induction rail with
    | input =>
      change val C.gates t.val f=true
      rwa [val_input _ _ _ t.isLt]
    | @next j z op inz _ ih =>
      have no : ¬ A j := by change (g j).op≠.and; rw [show (g j).op=.or from op]; intro e; cases e
      apply (orEv _ j no).2
      change z∈(g j).inputs at inz
      rw [pins j] at inz
      rcases List.mem_cons.mp inz with e | rest
      · exact Or.inl (e ▸ ih)
      · exact Or.inr ((List.mem_singleton.mp rest) ▸ ih)
  have badrow : E (pr s t) (W k)=true := by
    apply (andEv _ k ak).mpr
    have eq : a k=u ∧ b k=v := by
      simpa only [List.cons.injEq,and_true] using (pins k).symm.trans hins
    rw [eq.1,eq.2]
    exact ⟨reach s u railS _ (by simp [pr]),reach t v railT _ (by simp [pr])⟩
  have badout : E (pr s t) C.output=false := by
    cases h : E (pr s t) C.output
    · rfl
    · have good := (same s t).mp h
      simp_all
  have live' : Source2071.Live a b C.output (W k) := by
    intro H ho step
    apply live H ho
    intro j hj i hin
    change i∈(g j).inputs at hin
    rw [pins j] at hin
    rcases List.mem_cons.mp hin with e | rest
    · exact e ▸ (step j hj).1
    · exact (List.mem_singleton.mp rest) ▸ (step j hj).2
  have gj (j : Fin m) : gateAt C j.val=g j := PEqualNP.Outside.L_meta_2067.gateAt_some (hg j)
  have liftStep {z i j : Fin m} (hi : W i = a j ∨ W i = b j)
      (reach : z=i ∨ InCone 26 C z.val i.val) : InCone 26 C z.val j.val := by
    have mem : W i ∈ (gateAt C j.val).inputs := by
      rw [gj,pins j]
      rcases hi with h|h <;> simp [h]
    have lt : i.val<j.val := by
      have ai := ha j
      have bi := hb j
      simp only [W] at hi
      rcases hi with h|h <;> omega
    exact (PEqualNP.Outside.L_meta_2067.inCone_iff 26 C z.val j.val).2
      ⟨j.isLt,i.val,lt,mem,reach.imp (congrArg Fin.val) id⟩
  have origin (z : Fin m) (i : ℕ) (f : Source2071.Feed a b z i) :
      ∃ j : Fin m, W j=i ∧ (z=j ∨ InCone 26 C z.val j.val) := by
    induction f with
    | here => exact ⟨z,rfl,Or.inl rfl⟩
    | left j _ ih =>
      obtain ⟨k,hk,root⟩ := ih
      exact ⟨j,rfl,.inr (liftStep (.inl hk) root)⟩
    | right j _ ih =>
      obtain ⟨k,hk,root⟩ := ih
      exact ⟨j,rfl,.inr (liftStep (.inr hk) root)⟩
  have unique : Source2071.SourceOnly a b A d := by
    intro z j az aj f
    apply hd z j az aj
    rcases f with f | f
    · obtain ⟨k,hk,root⟩ := origin z _ f
      exact liftStep (.inl hk) root
    · obtain ⟨k,hk,root⟩ := origin z _ f
      exact liftStep (.inr hk) root
  let X : Vtx := Fin.castAdd 13 p
  let Y : Vtx := Fin.natAdd 13 l
  have edge : adjb X Y=true := (adjSide p l).2 incidence
  have hout : C.output<26+m := by
    by_contra! h
    have yes := (same X Y).2 edge
    change val C.gates C.output (pr X Y)=true at yes
    rw [val_big _ _ _ h] at yes
    contradiction
  have tl : Source2071.Trace a b A (E (one X)) dP := by
    intro j
    exact ⟨(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).1,
      fun no => (traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).2 (orOp j no)⟩
  have tp : Source2071.Trace a b A (E (one Y)) dL := by
    intro j
    exact ⟨(traceL.2 j (g j) (a j) (b j) (hg j) (pins j)).1,
      fun no => (traceL.2 j (g j) (a j) (b j) (hg j) (pins j)).2 (orOp j no)⟩
  have zero (t : Vtx) : E (one t) C.output=false := by
    cases h : E (one t) C.output
    · rfl
    · exact (off t h).elim
  apply Source2071.single_source (x := X.val) (y := Y.val) ha hb unique ak live'
    (vals (pr X Y)) (vals (one X)) (vals (one Y)) (vals (pr s t)) tl tp hout ?_
    ((same X Y).2 edge) (zero X) (zero Y) ?_ ?_ ?_ ?_ badrow badout
  · intro i hi h
    change val C.gates i (pr X Y)=true at h
    rw [val_input _ _ _ hi] at h
    exact (of_decide_eq_true h).imp (congrArg Fin.val) (congrArg Fin.val)
  · change val C.gates X.val (one X)=true
    rw [val_input _ _ _ X.isLt]
    simp [one]
  · change val C.gates Y.val (one Y)=true
    rw [val_input _ _ _ Y.isLt]
    simp [one]
  · rw [traceL.1 _ X.isLt]
    simp [X]
  · rw [traceP.1 _ Y.isLt]
    simp [Y,Nat.add_comm]

end OneSource2071

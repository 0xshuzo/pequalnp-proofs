import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1491

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

end S90
end PEqualNP.Outside.L_meta_1491
open PEqualNP.Outside.L_meta_1491.S90
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover

private lemma noFourCycle_of_girth5 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) :
    NoFourCycle G := by
  intro a b hab
  rw [Finset.card_le_one]
  intro w1 hw1 w2 hw2
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  have hw1a : w1 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw1.1)
  have hw1b : w1 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw1.2)
  have hw2a : w2 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw2.1)
  have hw2b : w2 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw2.2)
  let p : G.Walk a a :=
    SimpleGraph.Walk.cons hw1.1
      (SimpleGraph.Walk.cons hw1.2.symm
        (SimpleGraph.Walk.cons hw2.2
          (SimpleGraph.Walk.cons hw2.1.symm SimpleGraph.Walk.nil)))
  have hcyc : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp [p, SimpleGraph.Walk.edges, Sym2.eq_iff, hw1a, hw1b, hw2a, hw2b, hab, hne,
        hab.symm, Ne.symm hne, hw1a.symm, hw1b.symm, hw2a.symm, hw2b.symm]
    · simp [p]
    · simp [p, SimpleGraph.Walk.support, hw1a, hw2a, hw1b, hw2b, hab, hne, hab.symm, Ne.symm hne,
        hw1a.symm, hw2a.symm, hw1b.symm, hw2b.symm]
  have hlen := hgirth a p hcyc
  simp [p] at hlen

set_option maxRecDepth 14000 in
set_option maxHeartbeats 2500000 in
theorem orient5326 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C →
      let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
      NoFourCycle G ∧ ∀ j∈tops G C,
        (∀ u∈A (opnd C j 0), ∀ v∈A (opnd C j 1), G.Adj u v) ∧ ((A (opnd C j 0)).card ≤ 1 ∨ (A (opnd C j 1)).card ≤ 1) := by
  intro n G inst C girth least
  letI := gateOpDecEq
  let A := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
  have free := noFourCycle_of_girth5 girth
  refine ⟨free,?_⟩
  intro j hj
  have mono (x y : Fin n → Bool) (xy : ∀ i, x i=true → y i=true) (w : ℕ) :
      val C (List.ofFn x) w=true → val C (List.ofFn y) w=true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro on
      by_cases low : w<n
      · let u : Fin n := ⟨w,low⟩
        exact (val_ofFn C y u).trans (xy u ((val_ofFn C x u).symm.trans on))
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      by_cases valid : k<C.gates.length
      · rcases least.1.1 _ (gateAt_mem valid) with hAnd|hOr
        · apply (val_and (n:=n) (x:=List.ofFn y) (by simp) valid hAnd).mpr
          intro t ht
          obtain ⟨lt,hot⟩ := (val_and (n:=n) (x:=List.ofFn x) (by simp) valid hAnd).mp on t ht
          exact ⟨lt,ih t lt hot⟩
        · obtain ⟨t,ht,lt,hot⟩ := (val_or (n:=n) (x:=List.ofFn x) (by simp) valid hOr).mp on
          exact (val_or (n:=n) (x:=List.ofFn y) (by simp) valid hOr).mpr ⟨t,ht,lt,ih t lt hot⟩
      · have off := val_ge (n:=n) (C:=C) (x:=List.ofFn x) (u:=n+k) (by simp) (by omega)
        exact False.elim (Bool.noConfusion (off.symm.trans on))
  have cross : ∀ u∈A (opnd C j 0), ∀ v∈A (opnd C j 1), G.Adj u v := by
    intro u hu v hv
    obtain ⟨atJ,op,clean⟩ := Finset.mem_filter.mp hj
    have live := Finset.mem_range.mp atJ
    obtain ⟨p,q,ins⟩ := List.length_eq_two.mp (least.1.2.2 _ (gateAt_mem live))
    have pu : val C (List.ofFn (pairInput u u)) p=true := by
      have base : val C (List.ofFn (pairInput u u)) (opnd C j 0)=true := (Finset.mem_filter.mp hu).2
      simpa [opnd,ins] using base
    have qv : val C (List.ofFn (pairInput v v)) q=true := by
      have base : val C (List.ofFn (pairInput v v)) (opnd C j 1)=true := (Finset.mem_filter.mp hv).2
      simpa [opnd,ins] using base
    have pOn := mono (pairInput u u) (pairInput u v) (fun i hot =>
      (pairInput_true u v i).mpr (Or.inl (((pairInput_true u u i).mp hot).elim id id))) p pu
    have qOn := mono (pairInput v v) (pairInput u v) (fun i hot =>
      (pairInput_true u v i).mpr (Or.inr (((pairInput_true v v i).mp hot).elim id id))) q qv
    apply (graphFun_pair G u v).mp
    apply clean
    apply (val_and (n:=n) (x:=List.ofFn (pairInput u v)) (by simp) live op).mpr
    intro t ht
    refine ⟨least.1.2.1 _ live _ ht,?_⟩
    rw [ins] at ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact pOn
    · exact qOn
  refine ⟨cross,?_⟩
  by_contra both
  simp only [not_or,not_le] at both
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp both.1
  have sub : A (opnd C j 1) ⊆ Finset.univ.filter (fun b => G.Adj u b ∧ G.Adj v b) :=
    fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross u hu b hb,cross v hv b hb⟩
  exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (free u v ne))) both.2

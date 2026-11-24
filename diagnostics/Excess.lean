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

theorem wireMono5326 {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (x y : Fin n → Bool) (xy : ∀ i, x i=true → y i=true) (w : ℕ) :
      val C (List.ofFn x) w=true → val C (List.ofFn y) w=true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro on
      by_cases low : w<n
      · let u : Fin n := ⟨w,low⟩
        exact (val_ofFn C y u).trans (xy u ((val_ofFn C x u).symm.trans on))
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      by_cases valid : k<C.gates.length
      · rcases ao.1 _ (gateAt_mem valid) with hAnd|hOr
        · apply (val_and (n:=n) (x:=List.ofFn y) (by simp) valid hAnd).mpr
          intro t ht
          obtain ⟨lt,hot⟩ := (val_and (n:=n) (x:=List.ofFn x) (by simp) valid hAnd).mp on t ht
          exact ⟨lt,ih t lt hot⟩
        · obtain ⟨t,ht,lt,hot⟩ := (val_or (n:=n) (x:=List.ofFn x) (by simp) valid hOr).mp on
          exact (val_or (n:=n) (x:=List.ofFn y) (by simp) valid hOr).mpr ⟨t,ht,lt,ih t lt hot⟩
      · have off := val_ge (n:=n) (C:=C) (x:=List.ofFn x) (u:=n+k) (by simp) (by omega)
        exact False.elim (Bool.noConfusion (off.symm.trans on))

theorem excess5326 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (four : NoFourCycle G)
    (C : Circuit) (ao : IsAO2 n C) (j : ℕ) (live : j<C.gates.length) (op : (gateAt C j).op=GateOp.and)
    (c : Fin n) (safe : c∈wmax G C j) :
    let S := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
    ((S (opnd C j 0)) \ G.neighborFinset c).card ≤ 1 ∨ ((S (opnd C j 1)) \ G.neighborFinset c).card ≤ 1 := by
  classical
  let S := fun w : ℕ => Finset.univ.filter (fun u : Fin n => wireVal n C w (pairInput u u)=true)
  let X := S (opnd C j 0) \ G.neighborFinset c
  let Y := S (opnd C j 1) \ G.neighborFinset c
  change X.card ≤ 1 ∨ Y.card ≤ 1
  obtain ⟨p,q,ins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem live))
  have join : ∀ a∈X, ∀ b∈Y, G.Adj a b := by
    intro a ha b hb
    obtain ⟨aOn,notA⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨bOn,notB⟩ := Finset.mem_sdiff.mp hb
    have ca : ¬G.Adj c a := fun h => notA ((SimpleGraph.mem_neighborFinset G c a).mpr h)
    have cb : ¬G.Adj c b := fun h => notB ((SimpleGraph.mem_neighborFinset G c b).mpr h)
    let z := fun i : Fin n => decide (i=c ∨ i=a ∨ i=b)
    have zz (i : Fin n) : z i=true ↔ i=c ∨ i=a ∨ i=b := by simp [z]
    have xc : z c=true := (zz _).mpr (Or.inl rfl)
    have px : val C (List.ofFn (pairInput a a)) p=true := by
      have v : val C (List.ofFn (pairInput a a)) (opnd C j 0)=true := (Finset.mem_filter.mp aOn).2
      simpa [opnd,ins] using v
    have qx : val C (List.ofFn (pairInput b b)) q=true := by
      have v : val C (List.ofFn (pairInput b b)) (opnd C j 1)=true := (Finset.mem_filter.mp bOn).2
      simpa [opnd,ins] using v
    have pz := wireMono5326 C ao (pairInput a a) z (fun i hi => (zz i).mpr (Or.inr (Or.inl (((pairInput_true a a i).mp hi).elim id id)))) p px
    have qz := wireMono5326 C ao (pairInput b b) z (fun i hi => (zz i).mpr (Or.inr (Or.inr (((pairInput_true b b i).mp hi).elim id id)))) q qx
    have high : gateVal n C j z=true := by
      apply (val_and (n:=n) (x:=List.ofFn z) (by simp) live op).mpr
      intro t ht
      refine ⟨ao.2.1 j live t ht,?_⟩
      rw [ins] at ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl
      · exact pz
      · exact qz
    have gf := (Finset.mem_filter.mp safe).2 z high xc
    have pos : ∃ u v, G.Adj u v ∧ z u=true ∧ z v=true := by simpa [graphFun] using gf
    obtain ⟨u,v,edge,hu,hv⟩ := pos
    rcases (zz u).mp hu with rfl|rfl|rfl <;> rcases (zz v).mp hv with rfl|rfl|rfl <;>
      first | exact edge | exact edge.symm | exact False.elim (G.irrefl edge) |
            exact False.elim (ca edge) | exact False.elim (ca edge.symm) |
            exact False.elim (cb edge) | exact False.elim (cb edge.symm)
  by_contra both
  simp only [not_or,not_le] at both
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp both.1
  have sub : Y ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) :=
    fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _,join a ha u hu,join b hb u hu⟩
  exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (four a b ab))) both.2

theorem owner5326 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (four : NoFourCycle G)
    (X : Finset (Fin n)) (big : 4≤X.card) (a b : Fin n)
    (ha : (X \ G.neighborFinset a).card ≤ 1) (hb : (X \ G.neighborFinset b).card ≤ 1) : a=b := by
  by_contra ab
  let A := X \ G.neighborFinset a
  let B := X \ G.neighborFinset b
  let N := Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u)
  have hn : N.card≤1 := four a b ab
  have sub : X ⊆ (A∪B)∪N := by
    intro v hv
    by_cases h : G.Adj a v
    · by_cases i : G.Adj b v
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,i⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,fun z => i ((SimpleGraph.mem_neighborFinset G b v).mp z)⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,fun z => h ((SimpleGraph.mem_neighborFinset G a v).mp z)⟩))
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le (A∪B) N
  have h3 := Finset.card_union_le A B
  change A.card≤1 at ha
  change B.card≤1 at hb
  omega

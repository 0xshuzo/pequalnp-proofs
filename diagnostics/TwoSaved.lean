import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17467

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

private def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wiresLen {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  unfold Circuit.wires Circuit.size
  have h (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega
  rw [h]
  simp

private lemma gateGet {C : Circuit} {j : ℕ} (hj : j < C.size) :
    gateAt C j = C.gates[j]'hj := by
  simp [gateAt, List.getD, List.getElem?_eq_getElem hj]

private lemma gateSpec {n : ℕ} {C : Circuit} (hc : IsAO2 n C) {j : ℕ} (hj : j < C.size) :
    ∃ (op : GateOp) (a b : ℕ), gateAt C j = ⟨op, [a, b]⟩ ∧
      (op = .and ∨ op = .or) ∧ a < n + j ∧ b < n + j := by
  have hm : gateAt C j ∈ C.gates := gateGet hj ▸ List.getElem_mem hj
  have hlen := hc.2.2 _ hm
  have ht : ∀ L : List ℕ, L.length = 2 → ∃ a b, L = [a,b] := by
    intro L h
    match L with
    | [a,b] => exact ⟨a,b,rfl⟩
    | [] | [_] | _ :: _ :: _ :: _ => simp at h
  obtain ⟨a,b,hi⟩ := ht _ hlen
  have hg : gateAt C j = ⟨(gateAt C j).op, [a,b]⟩ := by
    exact congrArg (Gate.mk (gateAt C j).op) hi
  exact ⟨_, a, b, hg, hc.1 _ hm,
    hc.2.1 j hj a (by rw [hi]; simp), hc.2.1 j hj b (by rw [hi]; simp)⟩

private def push (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

private lemma pushSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (push n C op a b).size = C.size + 1 := by simp [push, Circuit.size]

private lemma pushLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ}
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (push n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.1 g hg
    · have e := List.mem_singleton.mp hg
      simpa [e] using hop
  · intro j hj w hw
    have hj' : j < C.size + 1 := by rw [← pushSize n C op a b]; exact hj
    rw [gateGet hj] at hw
    by_cases h : j < C.size
    · rw [show (push n C op a b).gates[j]'hj = C.gates[j]'h from
        List.getElem_append_left h] at hw
      exact hc.2.1 j h w (by rwa [gateGet h])
    · have e : j = C.size := by omega
      subst j
      have hlast : (push n C op a b).gates[C.size]'hj = ⟨op, [a,b]⟩ := by
        simp [push, Circuit.size]
      rw [hlast] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.2.2 g hg
    · simp [List.mem_singleton.mp hg]

private lemma pushWires {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (push n C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [wire C x a, wire C x b]] := by
  simp [push, Circuit.wires, List.foldl_append, wire]

private lemma pushOld {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + C.size) :
    wire (push n C op a b) x w = wire C x w := by
  unfold wire
  rw [pushWires, List.getD_append _ _ _ _ (by rwa [wiresLen])]

private lemma pushNew {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    wire (push n C op a b) x (n + C.size) = op.eval [wire C x a, wire C x b] := by
  conv_lhs => unfold wire; rw [pushWires, ← wiresLen C x]
  simp

private def firstGates (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.take k, 0⟩

private lemma prefixNext {C : Circuit} {k : ℕ} (hk : k < C.size) :
    (firstGates C (k + 1)).gates = (firstGates C k).gates ++ [gateAt C k] := by
  rw [gateGet hk]
  exact List.take_succ_eq_append_getElem hk

private lemma prefixSize {C : Circuit} {k : ℕ} (hk : k ≤ C.size) :
    (firstGates C k).size = k := by simp [firstGates, Circuit.size, Nat.min_eq_left (show k ≤ C.gates.length from hk)]

private lemma prefixOld {n k : ℕ} {C : Circuit} (hk : k < C.size) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + k) :
    wire (firstGates C (k + 1)) x w = wire (firstGates C k) x w := by
  unfold wire Circuit.wires
  rw [prefixNext hk, List.foldl_append]
  exact List.getD_append _ _ _ _ (by
    change w < ((firstGates C k).wires (List.ofFn x)).length
    rwa [wiresLen, prefixSize (Nat.le_of_lt hk)])

private lemma prefixNew {n k a b : ℕ} {C : Circuit} {op : GateOp}
    (hk : k < C.size) (hg : gateAt C k = ⟨op, [a,b]⟩) (x : Fin n → Bool) :
    wire (firstGates C (k + 1)) x (n + k) =
      op.eval [wire (firstGates C k) x a, wire (firstGates C k) x b] := by
  calc
    _ = wire (push n (firstGates C k) op a b) x (n + (firstGates C k).size) := by
      unfold wire Circuit.wires
      rw [prefixNext hk, hg, prefixSize (Nat.le_of_lt hk)]
      rfl
    _ = _ := pushNew _ _ _ _ _

private def pinned {n : ℕ} (v : Fin n) (x : Fin n → Bool) (w : Fin n) : Bool :=
  if w = v then false else x w

private def read {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : Option ℕ) : Bool :=
  w.elim false (wire C x)

private def available (bound : ℕ) (w : Option ℕ) : Prop :=
  ∀ a, w = some a → a < bound

private lemma advance {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : Option ℕ}
    (ha : available (n + C.size) a) (hb : available (n + C.size) b) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ available (n + S.size) u ∧
      C.size ≤ S.size ∧ S.size ≤ C.size + 1 ∧
      ((a = none ∨ b = none) → S.size = C.size) ∧
      (op = .and → a = none ∨ b = none → u = none) ∧
      (∀ x : Fin n → Bool, read S x u = op.eval [read C x a, read C x b]) ∧
      (∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w) := by
  cases a with
  | none =>
    rcases hop with rfl | rfl
    · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
        fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    · exact ⟨C, b, hc, hb, le_rfl, by omega, fun _ => rfl,
        by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
  | some a =>
    cases b with
    | none =>
      rcases hop with rfl | rfl
      · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
          fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
      · exact ⟨C, some a, hc, ha, le_rfl, by omega, fun _ => rfl,
          by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    | some b =>
      let S := push n C op a b
      have hs : S.size = C.size + 1 := pushSize _ _ _ _ _
      refine ⟨S, some (n + C.size), pushLegal hc hop (ha _ rfl) (hb _ rfl), ?_,
        by omega, by omega, by simp, by simp, pushNew _ _ _ _, ?_⟩
      · intro w hw
        injection hw with e
        omega
      · intro x w hw
        cases w with
        | none => rfl
        | some w => exact pushOld _ _ _ _ _ (hw _ rfl)

private lemma cutPrefix {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z) :
    ∀ k ≤ C.size, ∃ (S : Circuit) (loc : ℕ → Option ℕ), IsAO2 n S ∧
      S.size + ((Finset.range k).filter (· ∈ D)).card ≤ k ∧
      (∀ w < n + k, available (n + S.size) (loc w)) ∧
      (∀ w < n + k, w ∈ Z → loc w = none) ∧
      ∀ x w, w < n + k → read S x (loc w) = wire (firstGates C k) (pinned v x) w := by
  intro k
  induction k with
  | zero =>
    intro _
    let loc (w : ℕ) : Option ℕ := if w = v.val then none else some w
    refine ⟨⟨[], 0⟩, loc, ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly],
      by simp [ReadsBack], by simp⟩, by simp [Circuit.size], ?_, ?_, ?_⟩
    · intro w hw a ha
      by_cases e : w = v.val
      · simp [loc, e] at ha
      · have : w = a := by simpa [loc, e] using ha
        simp [Circuit.size]; omega
    · intro w hw hz
      simp [loc, hzin w (by omega) hz]
    · intro x w hw
      have h : w < n := by omega
      have he : (⟨w,h⟩ : Fin n) = v ↔ w = v.val := Fin.ext_iff
      by_cases e : w = v.val <;>
        simp [loc, e, read, wire, Circuit.wires, firstGates, pinned, he, List.getD, h]
  | succ k ih =>
    intro hk
    have hk' : k < C.size := by omega
    obtain ⟨S, loc, hs, cost, av, z, ev⟩ := ih (by omega)
    obtain ⟨op, a, b, hg, hop, ha, hb⟩ := gateSpec hc hk'
    obtain ⟨T, u, ht, uav, grow, cost1, cost0, uz, eu, preserve⟩ :=
      advance hs hop (av a ha) (av b hb)
    have zeroInput (h : ∃ w ∈ (gateAt C k).inputs, w ∈ Z) :
        loc a = none ∨ loc b = none := by
      obtain ⟨w, hw, hz⟩ := h
      rw [hg] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact Or.inl (z _ ha hz)
      · exact Or.inr (z _ hb hz)
    let newLoc (w : ℕ) := if w = n + k then u else loc w
    refine ⟨T, newLoc, ht, ?_, ?_, ?_, ?_⟩
    · rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        have := cost0 (zeroInput (hdg k h))
        omega
      · omega
    · intro w hw q hq
      by_cases e : w = n + k
      · exact uav q (by simpa [newLoc, e] using hq)
      · have := av w (by omega) q (by simpa [newLoc, e] using hq)
        omega
    · intro w hw hz
      by_cases e : w = n + k
      · subst w
        obtain ⟨hand, hin⟩ := hzg k hk' hz
        rw [hg] at hand
        simp [newLoc, uz hand (zeroInput hin)]
      · simp [newLoc, e, z w (by omega) hz]
    · intro x w hw
      by_cases e : w = n + k
      · subst w
        simp only [newLoc, ite_eq_left rfl, eu, prefixNew hk' hg, ev x a ha, ev x b hb]
      · have hw' : w < n + k := by omega
        rw [prefixOld hk' _ hw', show newLoc w = loc w by simp [newLoc, e],
          preserve x _ (av w hw'), ev x w hw']

private lemma cutCircuit {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hd : ∀ j ∈ D, j < C.size) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + D.card ≤ C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  obtain ⟨S, loc, hs, cost, av, _, ev⟩ := cutPrefix hc v Z D hzin hzg hdg _ le_rfl
  have hD : (Finset.range C.size).filter (· ∈ D) = D := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨hd _ h, h⟩⟩
  rw [hD] at cost
  by_cases ho : C.output < n + C.size
  · refine ⟨S, loc C.output, hs, cost, av _ ho, fun x => ?_⟩
    have hp : (firstGates C C.size).gates = C.gates := by simp [firstGates, Circuit.size]
    simpa only [wire, Circuit.wires, hp, circuitFun, Circuit.eval] using ev x _ ho
  · refine ⟨S, none, hs, cost, by simp [available], fun x => ?_⟩
    change false = wire C (pinned v x) C.output
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen]; omega)]

private lemma memReaders {n j k : ℕ} {C : Circuit} :
    k ∈ readers n C j ↔ k < C.size ∧ n + j ∈ (gateAt C k).inputs := by
  simp [readers, Circuit.size]

private lemma cutMany {n d : ℕ} {C : Circuit} (hc : IsAO2 n C) (v : Fin n)
    (h : let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + d < C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  let R := readers 0 C v.val
  change d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
    (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R at h
  have hr (j) (hj : j ∈ R) : j < C.size ∧ v.val ∈ (gateAt C j).inputs := by
    simpa only [R, memReaders, Nat.zero_add] using hj
  rcases h with h | ⟨he, g, hg, hand, hsub⟩
  · obtain ⟨S,u,hs,hcst,hu,hev⟩ := cutCircuit hc v {v.val} R
      (by simp) (by intro j hj hz; simp at hz; have := v.isLt; omega)
      (fun j hj => ⟨v.val, (hr j hj).2, by simp⟩) (fun j hj => (hr j hj).1)
    exact ⟨S,u,hs,by omega,hu,hev⟩
  · obtain ⟨k,hk,hkr⟩ := Finset.not_subset.mp hsub
    have hk' := memReaders.mp hk
    have hz (w : ℕ) : w ∈ ({v.val, n + g} : Finset ℕ) ↔ w = v.val ∨ w = n + g := by simp
    obtain ⟨S,u,hs,hcst,hu,hev⟩ :=
      cutCircuit hc v {v.val, n + g} (insert k R) (by
        intro w hw hm
        rcases (hz w).mp hm with e | e
        · exact e
        · omega) (by
        intro j hj hm
        have hv := v.isLt
        have e : j = g := by rcases (hz _).mp hm with h | h <;> omega
        subst j
        exact ⟨hand, v.val, (hr _ hg).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨n + g, hk'.2, by simp⟩
        · exact ⟨v.val, (hr _ hj).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hk'.1
        · exact (hr _ hj).1)
    rw [Finset.card_insert_of_notMem hkr, ← he] at hcst
    exact ⟨S,u,hs,by omega,hu,hev⟩

private lemma inputWire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : Fin n) :
    wire C x a.val = x a := by
  unfold wire Circuit.wires
  have h (gs : List Gate) (w : List Bool) (hw : a.val < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        a.val false = w.getD a.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih, List.getD_append _ _ _ _ hw]
      simp; omega
  rw [h _ _ (by simp)]
  simp

private lemma orList {n : ℕ} {C : Circuit} (hc : IsAO2 n C) :
    ∀ (tail : List (Fin n)) (a : Fin n),
    ∃ (S : Circuit) (u : ℕ), IsAO2 n S ∧ S.size = C.size + tail.length ∧
      u < n + S.size ∧
      (∀ x : Fin n → Bool, wire S x u = (a :: tail).any x) ∧
      ∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w := by
  intro tail
  induction tail with
  | nil =>
    intro a
    refine ⟨C, a, hc, by simp, by have := a.isLt; omega, ?_, fun _ _ _ => rfl⟩
    intro x
    simpa using inputWire C x a
  | cons b tail ih =>
    intro a
    obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := ih b
    let T := push n S .or a.val u
    have ha : a.val < n + S.size := by have := a.isLt; omega
    have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
    refine ⟨T, n + S.size, pushLegal hs (Or.inr rfl) ha hu, ?_, by omega, ?_, ?_⟩
    · simp only [ht, hlen, List.length_cons]; omega
    · intro x
      rw [show wire T x (n + S.size) = _ from pushNew S .or a.val u x, inputWire, hev]
      simp [GateOp.eval]
    · intro x w hw
      rw [← hpres x w hw]
      cases w with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hw w rfl; omega)

private def withOutput (n : ℕ) (C : Circuit) (u : Option ℕ) : Circuit :=
  ⟨C.gates, u.getD (n + C.size)⟩

private lemma withOutputLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C) (u : Option ℕ) :
    IsAO2 n (withOutput n C u) :=
  hc

private lemma withOutputEval {n : ℕ} (C : Circuit) (u : Option ℕ) (x : Fin n → Bool) :
    circuitFun n (withOutput n C u) x = read C x u := by
  cases u with
  | some u => rfl
  | none =>
    change wire C x (n + C.size) = false
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen])]

private lemma restore {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v a : Fin n) (tail : List (Fin n)) (base : Option ℕ)
    (hb : available (n + C.size) base) :
    ∃ S : Circuit, IsAO2 n S ∧ S.size ≤ C.size + tail.length + 2 ∧
      ∀ x, circuitFun n S x = (read C x base || (x v && (a :: tail).any x)) := by
  obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := orList hc tail a
  let T := push n S .and v.val u
  have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
  have hv : v.val < n + S.size := by have := v.isLt; omega
  have ht' : IsAO2 n T := pushLegal hs (Or.inl rfl) hv hu
  have hbase : available (n + T.size) base := by
    intro w hw
    have := hb _ hw
    omega
  obtain ⟨U,out,hU,_,_,hsz,_,_,he,hp⟩ :=
    advance ht' (op := .or) (Or.inr rfl) hbase
      (show available (n + T.size) (some (n + S.size)) from by
        intro w hw; injection hw with e; omega)
  refine ⟨withOutput n U out, withOutputLegal hU _, ?_, fun x => ?_⟩
  · change U.size ≤ _
    omega
  · rw [withOutputEval, he]
    have old : read T x base = read S x base := by
      cases base with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hb w rfl; omega)
    rw [old, hpres x _ hb]
    change GateOp.or.eval [read C x base, wire T x (n + S.size)] = _
    rw [show wire T x (n + S.size) = _ from pushNew S .and v.val u x, inputWire, hev]
    simp [GateOp.eval]

private def leftEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.1.castAdd r

private def rightEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.2.natAdd l

private lemma endsNe {l r : ℕ} (e f : Fin l × Fin r) : leftEnd e ≠ rightEnd f := by
  intro h
  have he := congrArg Fin.val h
  change e.1.val = l + f.2.val at he
  have := e.1.isLt
  omega

private lemma leftEq {l r : ℕ} {e f : Fin l × Fin r} (h : leftEnd e = leftEnd f) :
    e.1 = f.1 :=
  Fin.ext (congrArg (fun z : Fin (l + r) => z.val) h)

private lemma rightEq {l r : ℕ} {e f : Fin l × Fin r} (h : rightEnd e = rightEnd f) :
    e.2 = f.2 := by
  apply Fin.ext
  have he := congrArg Fin.val h
  change l + e.2.val = l + f.2.val at he
  omega

private def linked {l r : ℕ} (v w : Fin (l + r)) (e : Fin l × Fin r) : Prop :=
  v = leftEnd e ∧ w = rightEnd e ∨ w = leftEnd e ∧ v = rightEnd e

private lemma sameEdge {l r : ℕ} {v w : Fin (l + r)} {e f : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w f) : e = f := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))
  · exact (endsNe e f (ha.symm.trans hd)).elim
  · exact (endsNe f e (hc.symm.trans hb)).elim
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))

private lemma sameNeighbor {l r : ℕ} {v w w' : Fin (l + r)} {e : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w' e) : w = w' := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact hb.trans hd.symm
  · exact (endsNe e e (ha.symm.trans hd)).elim
  · exact (endsNe e e (hc.symm.trans hb)).elim
  · exact ha.trans hc.symm

private noncomputable def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Finset (Fin n) := (G.neighborSet v).toFinite.toFinset

private lemma memNeighbors {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n} :
    w ∈ neighbors G v ↔ G.Adj v w := by
  simp [neighbors]

private lemma neighborsCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (neighbors G v).card = (G.neighborSet v).ncard := by
  exact (Set.ncard_eq_toFinset_card _ _).symm

private lemma chooseEdge {l r : ℕ} {E M : Finset (Fin l × Fin r)}
    {G : SimpleGraph (Fin (l + r))} (v : Fin (l + r))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hd : 2 ≤ (neighbors G v).card) :
    ∃ w ∈ neighbors G v, ∃ e ∈ E, e ∉ M ∧ linked v w e := by
  obtain ⟨w, hw, z, hz, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (neighbors G v).card)
  obtain ⟨e,he,hel⟩ := (adj _ _).mp (memNeighbors.mp hw)
  obtain ⟨f,hf,hfl⟩ := (adj _ _).mp (memNeighbors.mp hz)
  by_cases hem : e ∈ M
  · refine ⟨z,hz,f,hf,?_,hfl⟩
    intro hfm
    apply hne
    have h : e = f := by
      rcases hel with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hfl with ⟨hc,hd⟩ | ⟨hc,hd⟩
      · exact ml e hem f hfm (leftEq (ha.symm.trans hc))
      · exact (endsNe e f (ha.symm.trans hd)).elim
      · exact (endsNe f e (hc.symm.trans hb)).elim
      · exact mr e hem f hfm (rightEq (hb.symm.trans hd))
    exact sameNeighbor hel (h ▸ hfl)
  · exact ⟨w,hw,e,he,hem,hel⟩

private def onEdge {l r : ℕ} (x : Fin (l + r) → Bool) (e : Fin l × Fin r) : Prop :=
  x (leftEnd e) = true ∧ x (rightEnd e) = true

private def edgeFun {l r : ℕ} (E : Finset (Fin l × Fin r)) (x : Fin (l + r) → Bool) : Bool :=
  decide (∃ (i : Fin l) (j : Fin r), (i,j) ∈ E ∧ x (i.castAdd r) = true ∧ x (j.natAdd l) = true)

private lemma edgeTrue {l r : ℕ} {E : Finset (Fin l × Fin r)} {x : Fin (l + r) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, onEdge x e := by
  rw [edgeFun, decide_eq_true_iff]
  exact ⟨fun ⟨i,j,h,hx,hy⟩ => ⟨(i,j),h,hx,hy⟩,
    fun ⟨e,h,hx,hy⟩ => ⟨e.1,e.2,h,hx,hy⟩⟩

private lemma pinEdge {l r : ℕ} {e : Fin l × Fin r} {v : Fin (l + r)} {x : Fin (l + r) → Bool} :
    onEdge (pinned v x) e ↔ v ≠ leftEnd e ∧ v ≠ rightEnd e ∧ onEdge x e := by
  rw [ne_comm (a := v) (b := leftEnd e), ne_comm (a := v) (b := rightEnd e)]
  by_cases hl : leftEnd e = v <;> by_cases hr : rightEnd e = v <;>
    simp [onEdge, pinned, hl, hr]

private lemma eraseSpec {l r : ℕ} {E : Finset (Fin l × Fin r)} {G : SimpleGraph (Fin (l + r))}
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    {v w₀ : Fin (l + r)} {e₀ : Fin l × Fin r} (hl : linked v w₀ e₀)
    {x : Fin (l + r) → Bool} :
    ((∃ e ∈ E, onEdge (pinned v x) e) ∨
      x v = true ∧ ∃ w ∈ (neighbors G v).erase w₀, x w = true) ↔
      ∃ e ∈ E.erase e₀, onEdge x e := by
  constructor
  · rintro (⟨e,he,hx⟩ | ⟨hv,w,hw,hx⟩)
    · obtain ⟨ha,hb,h⟩ := pinEdge.mp hx
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, h⟩
      rintro rfl
      exact hl.elim (fun h => ha h.1) (fun h => hb h.2)
    · obtain ⟨e,he,h⟩ := (adj _ _).mp (memNeighbors.mp (Finset.mem_of_mem_erase hw))
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, ?_⟩
      · rintro rfl
        exact (Finset.mem_erase.mp hw).1 (sameNeighbor h hl)
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hv,hx⟩
        · exact ⟨hx,hv⟩
  · rintro ⟨e,he,hx⟩
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp he
    by_cases ha : v = leftEnd e
    · have h : linked v (rightEnd e) e := Or.inl ⟨ha,rfl⟩
      refine Or.inr ⟨ha.symm ▸ hx.1, rightEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.2⟩
      · intro eq
        exact hne (sameEdge (eq ▸ h) hl)
      · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
    · by_cases hb : v = rightEnd e
      · have h : linked v (leftEnd e) e := Or.inr ⟨rfl,hb⟩
        refine Or.inr ⟨hb.symm ▸ hx.2, leftEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.1⟩
        · intro eq
          exact hne (sameEdge (eq ▸ h) hl)
        · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
      · exact Or.inl ⟨e,hm,pinEdge.mpr ⟨ha,hb,hx⟩⟩

private lemma solve {l r : ℕ} (E M : Finset (Fin l × Fin r)) (C : Circuit)
    (G : SimpleGraph (Fin (l + r)))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (hc : IsAO2 (l + r) C)
    (hev : ∀ x, circuitFun (l + r) C x = edgeFun E x)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (v : Fin (l + r)) (hd : 2 ≤ (G.neighborSet v).ncard)
    (h : let d := (G.neighborSet v).ncard
      let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers (l + r) C g ⊆ R) :
    ∃ e ∈ E, e ∉ M ∧ ∃ S : Circuit, S.size < C.size ∧
      IsAO2 (l + r) S ∧ ∀ x, circuitFun (l + r) S x = edgeFun (E.erase e) x := by
  let N := neighbors G v
  have hN : N.card = (G.neighborSet v).ncard := neighborsCard _ _
  have hd' : 2 ≤ N.card := by omega
  obtain ⟨w,hw,e,he,hem,hl⟩ := chooseEdge v adj ml mr hd'
  let W := N.erase w
  have hW : W.card = N.card - 1 := Finset.card_erase_of_mem hw
  have hpos : 0 < W.card := by omega
  obtain ⟨a,tail,hlist⟩ : ∃ a tail, W.toList = a :: tail := by
    cases eq : W.toList with
    | nil =>
      have hz : W.card = 0 := by rw [← Finset.length_toList, eq]; rfl
      omega
    | cons a tail => exact ⟨a,tail,rfl⟩
  have ht : W.card = tail.length + 1 := by
    rw [← Finset.length_toList, hlist]
    rfl
  obtain ⟨S,base,hs,hsz,hav,hspec⟩ := cutMany hc v h
  obtain ⟨T,ht',htsz,htspec⟩ := restore hs v a tail base hav
  refine ⟨e,he,hem,T,by omega,ht',fun x => ?_⟩
  have hAny : (a :: tail).any x = true ↔ ∃ z ∈ W, x z = true := by
    rw [← hlist, List.any_eq_true]
    simp only [Finset.mem_toList]
  apply Bool.eq_iff_iff.mpr
  rw [htspec, hspec, hev, Bool.or_eq_true, Bool.and_eq_true, edgeTrue, hAny, edgeTrue]
  exact eraseSpec adj hl


private def graph {a b : Nat} (E : Finset (Fin a × Fin b)) : SimpleGraph (Fin (a+b)) :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ E, u = leftEnd e ∧ v = rightEnd e

private def computes {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Prop :=
  IsAO2 (a+b) C ∧ circuitFun (a+b) C = PEqualNP.ReadTwo.fpl a (fun i j => (i,j) ∈ E)

private def leaf {a b : Nat} (E : Finset (Fin a × Fin b)) (e : Fin a × Fin b) : Prop :=
  (∀ f ∈ E, f.1 = e.1 → f = e) ∨ ∀ f ∈ E, f.2 = e.2 → f = e

private def goodEdges {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Set (Fin a × Fin b) :=
  {e | e ∈ E ∧ (leaf E e ∨ ∃ D : Circuit, D.size < C.size ∧ computes (E.erase e) D)}

private def regular {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) : Prop :=
  ∀ v : Fin (a+b), let d := ((graph E).neighborSet v).ncard
    let R := readers 0 C v.val
    2 ≤ d → R.card ≤ d ∧ (d = R.card → ∀ g ∈ R, (gateAt C g).op = .and → readers (a+b) C g ⊆ R)

private theorem adj_graph {a b : Nat} (E : Finset (Fin a × Fin b)) (u v : Fin (a+b)) :
    (graph E).Adj u v ↔ ∃ e ∈ E, linked u v e := by
  constructor
  · rintro ⟨_, ⟨e,he,hu,hv⟩ | ⟨e,he,hv,hu⟩⟩
    · exact ⟨e,he,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,he,Or.inr ⟨hv,hu⟩⟩
  · rintro ⟨e,he,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endsNe e e,Or.inl ⟨e,he,rfl,rfl⟩⟩
    · exact ⟨(endsNe e e).symm,Or.inr ⟨e,he,rfl,rfl⟩⟩

theorem matchingForcesReaders {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (rep : computes E C) (p : Set.InjOn Prod.fst (goodEdges E C))
    (q : Set.InjOn Prod.snd (goodEdges E C)) : regular E C := by
  classical
  let M := Finset.univ.filter (fun f => f ∈ goodEdges E C)
  have mem (f : Fin a × Fin b) : f ∈ M ↔ f ∈ goodEdges E C := by simp [M]
  have ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f :=
    fun e he f hf h => p ((mem e).mp he) ((mem f).mp hf) h
  have mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f :=
    fun e he f hf h => q ((mem e).mp he) ((mem f).mp hf) h
  intro v hd
  let R := readers 0 C v.val
  let d := ((graph E).neighborSet v).ncard
  have impossible (bad : d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
      (gateAt C g).op = .and ∧ ¬readers (a+b) C g ⊆ R) : False := by
    obtain ⟨e,he,out,S,small,legal,ev⟩ := solve E M C (graph E) (adj_graph E) rep.1
      (fun x => congrFun rep.2 x) ml mr v hd bad
    exact out ((mem e).mpr ⟨he,Or.inr ⟨S,small,legal,funext ev⟩⟩)
  constructor
  · exact le_of_not_gt (fun h => impossible (Or.inl h))
  · intro eq g hg hOp
    by_contra no
    exact impossible (Or.inr ⟨eq,g,hg,hOp,no⟩)

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
private theorem pinOne : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp (config := {congrConsts := false})
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp (config := {congrConsts := false}) [stepWire]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp (config := {congrConsts := false}) only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp (config := {congrConsts := false}) at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp (config := {congrConsts := false}) [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp (config := {congrConsts := false}) only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp (config := {congrConsts := false}) [stepWire]; omega)]
          simp (config := {congrConsts := false}) [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa (config := {congrConsts := false}) using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp (config := {congrConsts := false}) [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp (config := {congrConsts := false}) only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have opMono_imp : OpMono (fun a b => a = true → b = true) := by
    intro op hop l f g h
    rcases hop with rfl | rfl
    · simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro h1 i hi; exact h i hi (h1 i hi)
    · simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    simp (config := {congrConsts := false}) only [evalAnd, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2

  have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
      (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp (config := {congrConsts := false}) [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp (config := {congrConsts := false}) [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp (config := {congrConsts := false}) [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp (config := {congrConsts := false}) only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp (config := {congrConsts := false}) only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : R (val C x (n + r)) (val C x i)) :
      R (C.eval x) ((bypass n C r i).eval x) := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · have hgi : val (bypass n C r i) x i = val C x i := by
        rcases hi with hi | hi
        · exact bypass_val_lt hx hr i hi
        · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
      rw [h, aliasWire_self, hgi]; exact hR
    · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

  have bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x :=
    (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

  have bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hout : C.output ≠ n + r)
      (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
      (fun h => h.elim fun k hk => absurd hk.2 (hno k hk.1)) _ hout).symm

  have bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
      ∀ k < (bypass n C r i).gates.length,
        (gateAt (bypass n C r i) k).op = GateOp.and ∨
          (gateAt (bypass n C r i) k).op = GateOp.or := by
    intro k hk
    rw [bypass_length] at hk
    rw [gateAt_bypass hk]
    split_ifs with h
    · exact hAO k (by omega)
    · exact hAO (k + 1) (by omega)

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp (config := {congrConsts := false}) only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp (config := {congrConsts := false}) [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp (config := {congrConsts := false}) only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  -- Erase gates one at a time on the zero restriction. Any false output of a
  -- removed gate can be redirected to the pinned input during this process.
  have pinZero (n : ℕ) (p : Fin n) : ∀ k (C : Circuit), C.size = k → IsAO2 n C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
        C.eval (List.ofFn (Function.update y p false))) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
        ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠
          C.eval (List.ofFn (Function.update x p false))) → D.size < C.size) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x p false)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C hk hC hn
      let row := fun (x : Fin n → Bool) => List.ofFn (Function.update x p false)
      have lengths (x : Fin n → Bool) : (row x).length = n := by simp (config := {congrConsts := false}) [row]
      have pinned (x : Fin n → Bool) : val C (row x) p.val = false := by
        rw [val_input (lengths x) p.isLt]
        change (List.ofFn (Function.update x p false)).getD p.val false = false
        rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})),List.getElem_ofFn]
        simp (config := {congrConsts := false})
      have opGood : ∀ j < C.gates.length,
          (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
        fun j hj => hC.1 _ (gateAt_mem hj)
      have outNe : C.output ≠ p.val := by
        intro eq
        obtain ⟨x,y,hnxy⟩ := hn
        apply hnxy
        rw [eval_eq_val,eval_eq_val,eq,pinned,pinned]
      by_cases reads : ∃ j < C.gates.length, p.val ∈ (gateAt C j).inputs
      · obtain ⟨j,hj,hr⟩ := reads
        have canErase (u : ℕ) (hu : u < n+j)
            (eq : ∀ x : Fin n → Bool, val C (row x) (n+j) = val C (row x) u) :
            ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
              ((∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (row x)) → D.size < C.size) ∧
              ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (row x) := by
          let B := bypass n C j u
          have hlt : B.size < C.size := by
            change (bypass n C j u).gates.length < C.gates.length
            rw [bypass_length]
            omega
          have hB : IsAO2 n B := by
            refine ⟨?_,bypass_readsBack hu hC.2.1,?_⟩
            · intro g hg
              obtain ⟨g',hg',ho,_⟩ := bypass_mem g hg
              simpa (config := {congrConsts := false}) only [ho] using hC.1 g' hg'
            · intro g hg
              obtain ⟨g',hg',_,hl⟩ := bypass_mem g hg
              rw [hl]
              exact hC.2.2 g' hg'
          have same (x : Fin n → Bool) : B.eval (row x) = C.eval (row x) :=
            bypass_eval_eq (lengths x) opGood hj (Or.inl hu) (eq x)
          have hnB : ∃ x y : Fin n → Bool, B.eval (row x) ≠ B.eval (row y) := by
            obtain ⟨x,y,hxy⟩ := hn
            exact ⟨x,y,by rw [same,same]; exact hxy⟩
          obtain ⟨D,hD,hDsize,_,heval⟩ := ih B.size (by omega) B rfl hB hnB
          refine ⟨D,hD,by omega,fun _ => by omega,?_⟩
          intro x
          exact (heval x).trans (same x)
        rcases opGood j hj with hop | hop
        · refine canErase p.val (by have := p.isLt; omega) ?_
          intro x
          rw [pinned]
          apply Bool.eq_false_iff.mpr
          intro h
          have h' := ((val_and (lengths x) hj hop).mp h p.val hr).2
          rw [pinned] at h'
          cases h'
        · obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hC.2.2 _ (gateAt_mem hj))
          have ha : a < n+j := hC.2.1 j hj a (by simp (config := {congrConsts := false}) [hab])
          have hb : b < n+j := hC.2.1 j hj b (by simp (config := {congrConsts := false}) [hab])
          have hmem : p.val = a ∨ p.val = b := by simpa (config := {congrConsts := false}) [hab] using hr
          rcases hmem with h | h
          · refine canErase b hb ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) b <;> rfl
          · refine canErase a ha ?_
            intro x
            rw [val_gate (lengths x) hj,hop,hab,List.map_cons,List.map_cons,ite_eq_left ha,ite_eq_left hb,← h,pinned]
            cases val C (row x) a <;> rfl
      · have absent : ∀ j < C.gates.length, p.val ∉ (gateAt C j).inputs := by
          intro j hj hr
          exact reads ⟨j,hj,hr⟩
        have stable (x : Fin n → Bool) : ∀ w : ℕ, w ≠ p.val →
            val C (List.ofFn x) w = val C (row x) w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hi : w < n
            · rw [val_input (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hi,val_input (lengths x) hi]
              change (List.ofFn x).getD w false =
                (List.ofFn (Function.update x p false)).getD w false
              rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false}) [hi]),
                List.getElem_ofFn,List.getElem_ofFn]
              exact (Function.update_of_ne (fun h => hw (congrArg Fin.val h)) _ _).symm
            · by_cases hl : w < n+C.gates.length
              · let j := w-n
                have hj : j < C.gates.length := by dsimp [j]; omega
                have eq : w = n+j := by dsimp [j]; omega
                rw [eq,val_gate (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) hj,val_gate (lengths x) hj]
                apply congrArg (gateAt C j).op.eval
                apply List.map_congr_left
                intro i hii
                have earlier := hC.2.1 j hj i hii
                rw [ite_eq_left earlier,ite_eq_left earlier]
                exact ih i (by omega) (fun h => absent j hj (h ▸ hii))
              · rw [val_ge (by simp (config := {congrConsts := false}) : (List.ofFn x).length = n) (by omega),val_ge (lengths x) (by omega)]
        have same (x : Fin n → Bool) : C.eval (List.ofFn x) = C.eval (row x) := stable x C.output outNe
        refine ⟨C,hC,le_rfl,?_,same⟩
        rintro ⟨x,hx⟩
        exact (hx (same x)).elim
  intro x1 x2 x3 x4 h1 h2 h3
  exact pinZero x1 x2 x3 x4 h1 h2 h3


private def pairRow {a b : Nat} (e : Fin a × Fin b) (v : Fin (a+b)) : Bool :=
  decide (v = leftEnd e ∨ v = rightEnd e)

private theorem onPair {a b : Nat} (e f : Fin a × Fin b) : onEdge (pairRow e) f ↔ f = e := by
  constructor
  · rintro ⟨hl,hr⟩
    change decide (_ ∨ _) = true at hl hr
    rcases of_decide_eq_true hl with h|h
    · rcases of_decide_eq_true hr with g|g
      · exact False.elim (endsNe e f g.symm)
      · exact Prod.ext (leftEq h) (rightEq g)
    · exact False.elim (endsNe f e h)
  · rintro rfl
    simp [onEdge, pairRow]

private theorem pair_test {a b : Nat} (E : Finset (Fin a × Fin b)) (e : Fin a × Fin b) :
    edgeFun E (pairRow e) = decide (e ∈ E) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeTrue, onPair, decide_eq_true_eq]
  simp

private theorem zero_test {a b : Nat} (E : Finset (Fin a × Fin b)) :
    edgeFun E (fun _ => false) = false := by simp [edgeFun]

private theorem leafEndpoint {a b : Nat} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    (hle : leaf E e) : ∃ v : Fin (a+b), ∀ f ∈ E,
    (v = leftEnd f ∨ v = rightEnd f) ↔ f = e := by
  rcases hle with h|h
  · refine ⟨leftEnd e, fun f hf => ⟨?_,?_⟩⟩
    · rintro (eq|eq)
      · exact h f hf (leftEq eq.symm)
      · exact False.elim (endsNe e f eq)
    · rintro rfl
      exact Or.inl rfl
  · refine ⟨rightEnd e, fun f hf => ⟨?_,?_⟩⟩
    · rintro (eq|eq)
      · exact False.elim (endsNe f e eq.symm)
      · exact h f hf (rightEq eq.symm)
    · rintro rfl
      exact Or.inr rfl

private theorem leafPinned {a b : Nat} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    {v : Fin (a+b)} (endp : ∀ f ∈ E, (v = leftEnd f ∨ v = rightEnd f) ↔ f = e)
    (x : Fin (a+b) → Bool) :
    edgeFun E (Function.update x v false) = edgeFun (E.erase e) x := by
  have eq : Function.update x v false = pinned v x := by
    funext k
    by_cases h : k = v
    · subst k
      simp [pinned]
    · simp [pinned, Function.update_of_ne h, h]
  rw [eq]
  apply Bool.eq_iff_iff.mpr
  rw [edgeTrue, edgeTrue]
  constructor
  · rintro ⟨f,hf,hx⟩
    obtain ⟨hl,hr,hh⟩ := pinEdge.mp hx
    refine ⟨f, Finset.mem_erase.mpr ⟨?_,hf⟩, hh⟩
    intro fe
    exact ((endp f hf).mpr fe).elim hl hr
  · rintro ⟨f,hf,hx⟩
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hf
    exact ⟨f,hm,pinEdge.mpr ⟨fun hl => hne ((endp f hm).mp (Or.inl hl)),
      fun hr => hne ((endp f hm).mp (Or.inr hr)),hx⟩⟩

theorem strictLeaf {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit)
    (rep : computes E C) (e : Fin a × Fin b) (he : e ∈ E) (hle : leaf E e)
    (non : (E.erase e).Nonempty) : ∃ S : Circuit, S.size < C.size ∧ computes (E.erase e) S := by
  obtain ⟨v,hv⟩ := leafEndpoint hle
  obtain ⟨f,hf⟩ := non
  have eq (x : Fin (a+b) → Bool) :
      C.eval (List.ofFn x) = edgeFun E x := congrFun rep.2 x
  have pin (x : Fin (a+b) → Bool) : C.eval (List.ofFn (Function.update x v false)) = edgeFun (E.erase e) x :=
    (eq _).trans (leafPinned hv x)
  have nc : ∃ x y : Fin (a+b) → Bool,
      C.eval (List.ofFn (Function.update x v false)) ≠ C.eval (List.ofFn (Function.update y v false)) := by
    refine ⟨pairRow f, fun _ => false, ?_⟩
    rw [pin, pin, pair_test, zero_test]
    simp [hf]
  have differs : ∃ x : Fin (a+b) → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x v false)) := by
    refine ⟨pairRow e, ?_⟩
    rw [pin, eq, pair_test, pair_test]
    simp [he]
  obtain ⟨S,law,_,cut,ev⟩ := pinOne (a+b) v C.size C rfl rep.1 nc
  exact ⟨S,cut differs,law,funext (fun x => (ev x).trans (pin x))⟩

theorem addEdge {a b : Nat} (E : Finset (Fin a × Fin b)) (C : Circuit) (rep : computes E C)
    (e : Fin a × Fin b) : ∃ S : Circuit, S.size ≤ C.size+2 ∧ computes (insert e E) S := by
  let n := a+b
  let base : Option Nat := if C.output < n+C.size then some C.output else none
  have av : available (n+C.size) base := by
    by_cases h : C.output < n+C.size <;> simp [base, h, available, h]
  have src (x : Fin (a+b) → Bool) : read C x base = edgeFun E x := by
    have hh : wire C x C.output = edgeFun E x := congrFun rep.2 x
    by_cases h : C.output < n+C.size
    · simpa [base,h,read] using hh
    · have bad : wire C x C.output = false := by
        unfold wire
        rw [List.getD_eq_default _ _ (by rw [wiresLen]; change a+b+C.size ≤ C.output; omega)]
      simpa [base,h,read,bad] using hh
  obtain ⟨S,legal,limit,ev⟩ := restore rep.1 (leftEnd e) (rightEnd e) [] base av
  refine ⟨S,by simpa using limit,legal,funext (fun x => ?_)⟩
  change circuitFun (a+b) S x = edgeFun (insert e E) x
  rw [ev, src]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, edgeTrue]
  change ((∃ f ∈ E, onEdge x f) ∨ onEdge x e) ↔ ∃ f ∈ insert e E, onEdge x f
  simp [or_comm]


open Sym2
open scoped Sym2
private theorem girth (n m : ℕ) (E : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (rect : ∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) :
    6 ≤ E.card := by
  classical
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have left (a b : Fin n) : ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b) := by
    rintro h
    obtain ⟨e, _, ⟨_, bad⟩ | ⟨_, bad⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad
  have right (a b : Fin m) : ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b) := by
    intro h
    obtain ⟨e, _, ⟨bad,_⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad.symm
  have lr (a : Fin n) (b : Fin m) (h : G.Adj (Fin.castAdd m a) (Fin.natAdd n b)) : (a,b) ∈ E := by
    obtain ⟨⟨c,d⟩, he, ⟨ac,bd⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h
    · have : a = c := Fin.castAdd_inj.mp ac
      have : b = d := by simpa [Fin.ext_iff] using congrArg Fin.val bd
      subst c; subst d; exact he
    · exact (sep _ _ bad.symm).elim
  have square (v w x y : Fin (n+m)) (hv : v ≠ x) (hw : w ≠ y)
      (h1 : G.Adj v w) (h2 : G.Adj w x) (h3 : G.Adj x y) (h4 : G.Adj y v) : False := by
    cases v using Fin.addCases <;> cases w using Fin.addCases <;> cases x using Fin.addCases <;>
      cases y using Fin.addCases <;> first
      | exact (left _ _) h1 | exact (right _ _) h1 | exact (left _ _) h2 | exact (right _ _) h2
      | exact (left _ _) h3 | exact (right _ _) h3
      | exact rect _ _ _ _ (fun h => hv (congrArg _ h)) (fun h => hw (congrArg _ h))
          ⟨lr _ _ h1,lr _ _ h4.symm,lr _ _ h2.symm,lr _ _ h3⟩
      | exact rect _ _ _ _ (fun h => hw (congrArg _ h)) (fun h => hv (congrArg _ h))
          ⟨lr _ _ h1.symm,lr _ _ h2,lr _ _ h4,lr _ _ h3.symm⟩
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  let col : G.Coloring Bool := SimpleGraph.Coloring.mk (fun u => decide (u.val < n)) (by
    intro i j hij
    obtain ⟨⟨a,b⟩, _, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj _ _).1 hij <;> simp)
  have ev := (col.even_length_iff_congr w).2 Iff.rfl
  have three := hw.three_le_length
  have six : 6 ≤ w.length := by
    by_contra! h
    obtain ⟨k,hk⟩ := ev
    have four : w.length = 4 := by omega
    have neq (a b : ℕ) (ha : a < 4) (hb : b < 4) (ne : a ≠ b) : w.getVert a ≠ w.getVert b :=
      fun eq => ne (hw.getVert_injOn' (by change a ≤ w.length-1; omega) (by change b ≤ w.length-1; omega) eq)
    apply square (w.getVert 0) (w.getVert 1) (w.getVert 2) (w.getVert 3)
      (neq _ _ (by decide) (by decide) (by decide)) (neq _ _ (by decide) (by decide) (by decide))
      (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega))
    simpa [←four, SimpleGraph.Walk.getVert_length] using (w.adj_getVert_succ (i:=3) (by omega))
  let edge := fun e : Fin n × Fin m => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have sub : G.edgeSet ⊆ ↑(E.image edge) := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]; exact Finset.mem_image_of_mem edge he
  exact six.trans (hw.isTrail.length_le_ncard_edgeSet.trans
    ((Set.ncard_le_ncard sub).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=E) (f:=edge))))


private def badGraph {a b : Nat} (E : Finset (Fin a × Fin b)) : Prop :=
  6 ≤ E.card ∧ ∃ C : Circuit, C.size + 3 ≤ 2 * E.card ∧ computes E C ∧
    (PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E) ∧ ¬(graph E).IsAcyclic ∧ regular E C ∧
    Set.InjOn Prod.fst (goodEdges E C) ∧ Set.InjOn Prod.snd (goodEdges E C)

theorem twoSavedDescend {a b : Nat} (E : Finset (Fin a × Fin b)) (e : Fin a × Fin b) (he : e ∈ E)
    (C D : Circuit) (cap : C.size + 3 ≤ 2 * E.card)
    (lin : PEqualNP.ReadTwo.Lin fun i j => (i,j) ∈ E)
    (p : Set.InjOn Prod.fst (goodEdges E C)) (q : Set.InjOn Prod.snd (goodEdges E C))
    (rep : computes (E.erase e) D) (cut : D.size + 2 ≤ C.size)
    (cyclic : ¬(graph (E.erase e)).IsAcyclic) : badGraph (E.erase e) := by
  classical
  let F := E.erase e
  have leF : F ⊆ E := Finset.erase_subset _ _
  have linF : PEqualNP.ReadTwo.Lin (fun i j => (i,j) ∈ F) := by
    intro i k j l hik hjl h
    exact lin i k j l hik hjl ⟨leF h.1,leF h.2.1,leF h.2.2.1,leF h.2.2.2⟩
  have six := girth a b F (graph F) (adj_graph F) cyclic (by
    intro i k j l hik hjl h
    exact linF i k j l hik hjl ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩)
  have card : F.card = E.card - 1 := Finset.card_erase_of_mem he
  have sub : goodEdges F D ⊆ goodEdges E C := by
    intro f hgood
    obtain ⟨hf,reason⟩ := hgood
    have ne : f ≠ e := (Finset.mem_erase.mp hf).1
    have hc : ∃ B : Circuit, B.size < D.size ∧ computes (F.erase f) B := by
      rcases reason with hleaf|hsmall
      · apply strictLeaf F D rep f hf hleaf
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hf]
        omega
      · exact hsmall
    obtain ⟨B,small,ok⟩ := hc
    obtain ⟨A,sz,build⟩ := addEdge _ B ok e
    have erase : insert e (F.erase f) = E.erase f := by
      ext g
      simp only [F, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl|⟨hgf,_,hg⟩)
        · exact ⟨Ne.symm ne,he⟩
        · exact ⟨hgf,hg⟩
      · rintro ⟨hgf,hg⟩
        by_cases hge : g = e
        · exact Or.inl hge
        · exact Or.inr ⟨hgf,hge,hg⟩
    rw [erase] at build
    exact ⟨leF hf, Or.inr ⟨A,by omega,build⟩⟩
  have pF : Set.InjOn Prod.fst (goodEdges F D) := p.mono sub
  have qF : Set.InjOn Prod.snd (goodEdges F D) := q.mono sub
  exact ⟨six,D,by omega,rep,linF,cyclic,matchingForcesReaders F D rep pF qF,pF,qF⟩

end PEqualNP.Outside.L_meta_17467

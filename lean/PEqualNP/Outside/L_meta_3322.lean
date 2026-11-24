import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3322_aux

def allowed (p : GateOp) : Prop := p = .and ∨ p = .or

def pairCode (a b : ℕ) : ℕ := 15 * min a b + max a b

def score (a b c d : ℕ) : ℕ := pairCode a b * 225 + pairCode c d

def prependGates (a b : Fin 14) (c d : Fin 15) (p q : GateOp) (D : Circuit) : Circuit :=
  ⟨⟨p, [a.val, b.val]⟩ :: ⟨q, [c.val, d.val]⟩ :: D.gates, D.output⟩

lemma prefix_eval (a b : Fin 14) (c d : Fin 15) (p q : GateOp) (D : Circuit)
    (x : Fin 14 → Bool) :
    (prependGates a b c d p q D).eval (List.ofFn x) =
      let w := List.ofFn x ++ [p.eval [x a, x b]]
      D.eval (w ++ [q.eval [w.getD c.val false, w.getD d.val false]]) := by
  have lookup (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn] <;> rfl
  simp only [prependGates, Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons, List.map_nil, lookup]

lemma orderPair {n : ℕ} (a b : Fin n) (hne : a ≠ b) :
    ∃ l r : Fin n, l < r ∧ pairCode l.val r.val = pairCode a.val b.val ∧
      ∀ (p : GateOp), allowed p → ∀ v : Fin n → Bool,
        p.eval [v l, v r] = p.eval [v a, v b] := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a, b, h, rfl, fun _ _ _ => rfl⟩
  · refine ⟨b, a, h, ?_, ?_⟩
    · simp only [pairCode, min_comm b.val a.val, max_comm b.val a.val]
    · intro p hp v
      rcases hp with rfl | rfl <;> cases v a <;> cases v b <;> rfl

def feasible (F : (Fin 14 → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ (a b : Fin 14) (c d : Fin 15) (p q : GateOp) (D : Circuit),
    a < b ∧ c < d ∧ allowed p ∧ allowed q ∧ Monotone2 D ∧ D.size ≤ 24 ∧
    (∀ x, (prependGates a b c d p q D).eval (List.ofFn x) = F x) ∧
    score a.val b.val c.val d.val = k

lemma makeFeasible (F : (Fin 14 → Bool) → Bool) (a b : Fin 14) (c d : Fin 15)
    (p q : GateOp) (D : Circuit) (hab : a ≠ b) (hcd : c ≠ d)
    (hp : allowed p) (hq : allowed q) (hmono : Monotone2 D) (hsize : D.size ≤ 24)
    (hfun : ∀ x, (prependGates a b c d p q D).eval (List.ofFn x) = F x) :
    feasible F (score a.val b.val c.val d.val) := by
  obtain ⟨a', b', h1, hk1, he1⟩ := orderPair a b hab
  obtain ⟨c', d', h2, hk2, he2⟩ := orderPair c d hcd
  refine ⟨a', b', c', d', p, q, D, h1, h2, hp, hq, hmono, hsize, ?_, ?_⟩
  · intro x
    rw [prefix_eval, ← hfun x, prefix_eval]
    dsimp only
    rw [he1 p hp x]
    have hq' := he2 q hq (fun i => (List.ofFn x ++ [p.eval [x a, x b]]).getD i.val false)
    rw [show q.eval [(List.ofFn x ++ [p.eval [x a, x b]]).getD c'.val false,
                      (List.ofFn x ++ [p.eval [x a, x b]]).getD d'.val false] = _ from hq']
  · simp only [score, hk1, hk2]

lemma initial (F : (Fin 14 → Bool) → Bool) (C : Circuit) (hmodel : IsAO2 14 C)
    (distinct : ∀ g ∈ C.gates, g.inputs.Nodup) (low : 2 ≤ C.size) (high : C.size ≤ 26)
    (hfun : ∀ x, C.eval (List.ofFn x) = F x) : ∃ k, feasible F k := by
  rcases hmodel with ⟨ops, back, arity⟩
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => simp [Circuit.size] at low
  | cons g rest =>
    cases rest with
    | nil => simp [Circuit.size] at low
    | cons h tail =>
      have gm : g ∈ g :: h :: tail := by simp
      have hm : h ∈ g :: h :: tail := by simp
      obtain ⟨a, b, hg⟩ := List.length_eq_two.mp (arity g gm)
      obtain ⟨c, d, hh⟩ := List.length_eq_two.mp (arity h hm)
      have hg' := back 0 (by simp)
      have hh' := back 1 (by simp)
      change ∀ w ∈ g.inputs, w < 14 at hg'
      change ∀ w ∈ h.inputs, w < 15 at hh'
      rw [hg] at hg'
      rw [hh] at hh'
      let a' : Fin 14 := ⟨a, hg' a (by simp)⟩
      let b' : Fin 14 := ⟨b, hg' b (by simp)⟩
      let c' : Fin 15 := ⟨c, hh' c (by simp)⟩
      let d' : Fin 15 := ⟨d, hh' d (by simp)⟩
      have hab : a ≠ b := by simpa [hg] using distinct g gm
      have hcd : c ≠ d := by simpa [hh] using distinct h hm
      let D : Circuit := ⟨tail, out⟩
      have hmD : Monotone2 D := by
        intro t ht
        have ht' : t ∈ g :: h :: tail :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
        refine ⟨?_, (arity t ht').le⟩
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ops t ht'
      have hsize : D.size ≤ 24 := by
        change tail.length ≤ 24
        change (g :: h :: tail).length ≤ 26 at high
        simp only [List.length_cons] at high
        omega
      have heq : prependGates a' b' c' d' g.op h.op D = (⟨g :: h :: tail, out⟩ : Circuit) := by
        change (⟨⟨g.op, [a,b]⟩ :: ⟨h.op, [c,d]⟩ :: tail, out⟩ : Circuit) = _
        rw [← hg, ← hh]
      refine ⟨_, makeFeasible F a' b' c' d' g.op h.op D
        (fun e => hab (congrArg Fin.val e)) (fun e => hcd (congrArg Fin.val e))
        (ops g gm) (ops h hm) hmD hsize ?_⟩
      intro x
      rw [heq]
      exact hfun x

def wire (s : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if h : i < 14 then (s ⟨i, h⟩).val else i

lemma wire_input (s : Equiv.Perm (Fin 14)) (i : Fin 14) :
    wire s i.val = (s i).val := by simp [wire, i.isLt]

lemma wire_lt (s : Equiv.Perm (Fin 14)) (i : ℕ) : wire s i < 14 ↔ i < 14 := by
  by_cases h : i < 14
  · simp only [wire, dite_eq_left h, h, iff_true]
    exact (s ⟨i, h⟩).isLt
  · simp [wire, h]

lemma wire_inv (s : Equiv.Perm (Fin 14)) (i : ℕ) : wire s.symm (wire s i) = i := by
  by_cases h : i < 14
  · let j : Fin 14 := ⟨i, h⟩
    change wire s.symm (wire s j.val) = j.val
    rw [wire_input, wire_input, s.symm_apply_apply]
  · simp [wire, h]

def liftWire (s : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨wire s i.val, by
    by_cases h : i.val < 14
    · exact lt_trans ((wire_lt s i.val).2 h) (by decide)
    · simpa [wire, h] using i.isLt⟩

lemma lift_injective (s : Equiv.Perm (Fin 14)) : Function.Injective (liftWire s) := by
  intro i j h
  have t : wire s i.val = wire s j.val := congrArg Fin.val h
  apply Fin.ext
  simpa only [wire_inv] using congrArg (wire s.symm) t

lemma lift_formula (s : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (liftWire s i).val =
      if i < (14 : Fin 15) then (s (Fin.ofNat 14 i.val)).val else 14 := by
  change (if h : i.val < 14 then (s ⟨i.val, h⟩).val else i.val) =
    if i.val < 14 then (s (Fin.ofNat 14 i.val)).val else 14
  by_cases h : i.val < 14
  · rw [dif_pos h, if_pos h]
    have e : (⟨i.val, h⟩ : Fin 14) = Fin.ofNat 14 i.val :=
      Fin.ext (Nat.mod_eq_of_lt h).symm
    rw [e]
  · rw [dif_neg h, if_neg h]
    have := i.isLt
    omega

def mapGate (s : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire s)⟩

def rename (s : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mapGate s), wire s C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma evalRel (s : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ W W' : List Bool, 14 ≤ W.length → W'.length = W.length →
      (∀ w, W'.getD (wire s w) false = W.getD w false) →
      ∀ w, ((gs.map (mapGate s)).foldl step W').getD (wire s w) false =
        (gs.foldl step W).getD w false := by
  induction gs with
  | nil => intro W W' hW hlen hbase w; exact hbase w
  | cons g gs ih =>
    intro W W' hW hlen hbase w
    simp only [List.map_cons, List.foldl_cons]
    have hv : (mapGate s g).op.eval ((mapGate s g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hbase a
    apply ih (step W g) (step W' (mapGate s g)) (by simp [step]; omega)
      (by simp [step, hlen]) _ w
    intro u
    simp only [step, hv]
    rcases Nat.lt_trichotomy u W.length with hlt | heq | hgt
    · have hlt' : wire s u < W'.length := by
        by_cases hsmall : u < 14
        · have := (wire_lt s u).2 hsmall
          omega
        · simpa [wire, hsmall, hlen] using hlt
      rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
      exact hbase u
    · have hlarge : ¬ u < 14 := by omega
      rw [show wire s u = u by simp [wire, hlarge]]
      have last (v : List Bool) (x : Bool) (h : u = v.length) :
          (v ++ [x]).getD u false = x := by rw [h]; simp
      rw [last W' _ (by omega), last W _ heq]
    · have hlarge : ¬ u < 14 := by omega
      rw [show wire s u = u by simp [wire, hlarge],
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma rename_eval (s : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) :
    (rename s C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ s)) := by
  apply evalRel s C.gates _ _ (by simp) (by simp) _ C.output
  intro i
  by_cases h : i < 14
  · let j : Fin 14 := ⟨i, h⟩
    change (List.ofFn x).getD (wire s j.val) false = (List.ofFn (x ∘ s)).getD j.val false
    rw [wire_input]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (s j).isLt),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
        List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · rw [show wire s i = i by simp [wire, h],
      List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma rename_prefix (s : Equiv.Perm (Fin 14)) (a b : Fin 14) (c d : Fin 15)
    (p q : GateOp) (D : Circuit) :
    rename s (prependGates a b c d p q D) =
      prependGates (s a) (s b) (liftWire s c) (liftWire s d) p q (rename s D) := by
  change (⟨⟨p, [wire s a.val, wire s b.val]⟩ :: ⟨q, [wire s c.val, wire s d.val]⟩ ::
      D.gates.map (mapGate s), wire s D.output⟩ : Circuit) = _
  rw [wire_input s a, wire_input s b]
  rfl

lemma rename_mono (s : Equiv.Perm (Fin 14)) (D : Circuit) (h : Monotone2 D) :
    Monotone2 (rename s D) := by
  intro g hg
  obtain ⟨g', hmem, rfl⟩ := List.mem_map.1 hg
  exact ⟨(h g' hmem).1, by simpa [mapGate] using (h g' hmem).2⟩

end PEqualNP.Outside.L_meta_3322_aux

open PEqualNP.Outside.L_meta_3322_aux

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro F C model distinct low high computes
  have existsScore := initial F C model distinct low high computes
  obtain ⟨a, b, c, d, p, q, D, hab, hcd, hp, hq, hm, size, heval, hk⟩ :=
    Nat.find_spec existsScore
  refine ⟨a, b, c, d, p, q, D, hab, hcd, hp, hq, ?_, hm, size, ?_⟩
  · intro s hs
    have hsEval (x : Fin 14 → Bool) :
        (prependGates (s a) (s b) (liftWire s c) (liftWire s d) p q (rename s D)).eval
          (List.ofFn x) = F x := by
      rw [← rename_prefix, rename_eval, heval, hs]
    have hsize : (rename s D).size ≤ 24 := by simpa [rename, Circuit.size] using size
    have candidate := makeFeasible F (s a) (s b) (liftWire s c) (liftWire s d) p q
      (rename s D) (s.injective.ne hab.ne) ((lift_injective s).ne hcd.ne)
      hp hq (rename_mono s D hm) hsize hsEval
    have bound : Nat.find existsScore ≤
        score (s a).val (s b).val (liftWire s c).val (liftWire s d).val :=
      Nat.find_min' existsScore candidate
    rw [lift_formula s c, lift_formula s d] at bound
    change score a.val b.val c.val d.val ≤ score (s a).val (s b).val _ _
    rw [hk]
    exact bound
  · intro x
    exact (prefix_eval a b c d p q D x).symm.trans (heval x)

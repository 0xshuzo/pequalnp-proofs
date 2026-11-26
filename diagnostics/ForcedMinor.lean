import PEqualNP.Defs
namespace PetersenFeedbackCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def petBool (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

private def shifted (size pin index : Nat) : Nat :=
  if index < 10 then index
  else if index = 10 then (if pin < 10 then pin else 10 + size)
  else index - 1

private def removeInput (C : Circuit) (pin : Nat) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (shifted C.size pin)⟩),
    shifted C.size pin C.output⟩

private theorem removeInput_mono (C : Circuit) (h : Monotone2 C) (pin : Nat) :
    Monotone2 (removeInput C pin) := by
  intro g hg
  change g ∈ C.gates.map _ at hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  simpa using h j hj

private theorem shortRead (a b : List Bool) (j : Nat) (h : j < a.length) :
    (a ++ b).getD j false = a.getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem longRead (a b : List Bool) (j : Nat) (h : a.length ≤ j) :
    (a ++ b).getD j false = b.getD (j - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem missingRead (a : List Bool) (j : Nat) (h : a.length ≤ j) :
    a.getD j false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem readShift (a b : List Bool) (ha : a.length = 10) (size pin j : Nat)
    (hb : b.length ≤ size) :
    (a ++ (a.getD pin false :: b)).getD j false =
      (a ++ b).getD (shifted size pin j) false := by
  by_cases hj : j < 10
  · simp only [shifted, hj, ↓reduceIte]
    rw [shortRead _ _ j (by omega), shortRead _ _ j (by omega)]
  rw [longRead a _ j (by omega)]
  by_cases he : j = 10
  · subst j
    simp only [ha, Nat.sub_self, List.getD_cons_zero, shifted, lt_irrefl, ↓reduceIte]
    by_cases hp : pin < 10
    · simp only [hp, ↓reduceIte]
      rw [shortRead _ _ pin (by omega)]
    · simp only [hp, ↓reduceIte]
      rw [missingRead a pin (by omega), missingRead (a ++ b) _ (by simp only [List.length_append]; omega)]
  · rw [shifted, ite_eq_right hj, ite_eq_right he, longRead a _ _ (by omega)]
    have hs : j - a.length = (j - 1 - a.length) + 1 := by omega
    rw [hs]
    rfl

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

-- Both evaluations append the same gate values after each gate.
private theorem foldShift (a : List Bool) (ha : a.length = 10) (size pin : Nat)
    (gs : List Gate) (b : List Bool) (hh : b.length + gs.length ≤ size) :
    ∃ out : List Bool, out.length ≤ size ∧
      gs.foldl step (a ++ (a.getD pin false :: b)) = a ++ (a.getD pin false :: out) ∧
      (gs.map (fun g => (⟨g.op, g.inputs.map (shifted size pin)⟩ : Gate))).foldl step (a ++ b) =
        a ++ out := by
  induction gs generalizing b with
  | nil => exact ⟨b, by simpa using hh, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => (a ++ b).getD (shifted size pin i) false))
    have hv : g.op.eval (g.inputs.map (fun i => (a ++ (a.getD pin false :: b)).getD i false)) = v := by
      congr 1
      exact List.map_congr_left (fun j _ => readShift a b ha size pin j (by simp at hh; omega))
    simp only [List.foldl_cons, List.map_cons, step, List.map_map, Function.comp_def, hv, List.append_assoc,
      List.cons_append]
    exact ih (b ++ [v]) (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)

private theorem evalShift (C : Circuit) (pin : Nat) (a : List Bool) (ha : a.length = 10) :
    C.eval (a ++ [a.getD pin false]) = (removeInput C pin).eval a := by
  obtain ⟨b, hb, h₁, h₂⟩ := foldShift a ha C.size pin C.gates [] (by simp [Circuit.size])
  change (C.gates.foldl step (a ++ [a.getD pin false])).getD C.output false =
    ((C.gates.map (fun g => (⟨g.op, g.inputs.map (shifted C.size pin)⟩ : Gate))).foldl step a).getD
      (shifted C.size pin C.output) false
  simp only [List.append_nil] at h₂
  rw [h₁, h₂]
  exact readShift a b ha _ _ _ hb

private def belowWires (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j, a.getD j false = true → b.getD j false = true

private theorem belowSnoc {a b : List Bool} (h : belowWires a b) {c d : Bool}
    (hcd : c = true → d = true) : belowWires (a ++ [c]) (b ++ [d]) := by
  refine ⟨by simpa using h.1, fun j => ?_⟩
  by_cases hj : j < a.length
  · rw [shortRead _ _ _ hj, shortRead _ _ _ (by rw [← h.1]; exact hj)]
    exact h.2 j
  · rw [longRead _ _ _ (by omega), longRead _ _ _ (by rw [← h.1]; omega), ← h.1]
    cases j - a.length with
    | zero => exact hcd
    | succ n => simp [List.getD_eq_getElem?_getD]

private theorem stepMono {g : Gate} (hg : g.op = .and ∨ g.op = .or)
    {a b : List Bool} (h : belowWires a b) : belowWires (step a g) (step b g) := by
  unfold step
  apply belowSnoc h
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_eq_true, List.forall_mem_map, id_eq]
    exact fun ha j hj => h.2 j (ha j hj)
  · simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨j, hj, rfl⟩, ha⟩
    exact ⟨_, ⟨j, hj, rfl⟩, h.2 j ha⟩

private theorem foldMono (gs : List Gate)
    (hs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) {a b : List Bool} (h : belowWires a b) :
    belowWires (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun j hj => hs j (List.mem_cons_of_mem _ hj)) (stepMono (hs g (by simp)) h)

private theorem bitsMono (C : Circuit) (hc : Monotone2 C) {x y : Fin 10 → Bool}
    (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hh : belowWires (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun j => ?_⟩
    by_cases hj : j < 10
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, ↓reduceDIte,
        Option.getD_some] using h ⟨j, hj⟩
    · rw [missingRead _ _ (by simpa using Nat.le_of_not_gt hj)]
      simp
  exact (foldMono C.gates (fun g hg => by simpa using (hc g hg).1) hh).2 C.output

private def probes : List (Nat × Bool) := [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)]

def bits (m : Nat) (i : Fin 10) : Bool := m.testBit i

private def belowBits (x y : Fin 10 → Bool) : Prop := ∀ i, x i = true → y i = true

private theorem belowOfAnd {m n : Nat} (h : m &&& n = m) : belowBits (bits m) (bits n) := by
  intro i hi
  have ht := congrArg (fun a : Nat => a.testBit (i : Nat)) h
  change m.testBit i = true at hi
  change n.testBit i = true
  simpa only [Nat.testBit_and, hi, Bool.true_and] using ht

-- Every true input extends a positive probe, and every false input extends to a negative probe.
private def coveredMask (r : Nat) : Prop :=
  ∃ p ∈ probes, p.2 = petBool (bits r) ∧
    (if p.2 then p.1 &&& r = p.1 else r &&& p.1 = r)

private instance (r : Nat) : Decidable (coveredMask r) :=
  inferInstanceAs (Decidable (∃ p ∈ probes, p.2 = petBool (bits r) ∧
    (if p.2 then p.1 &&& r = p.1 else r &&& p.1 = r)))

private theorem coverMasks₀ : ∀ r : Fin 256, coveredMask r := by decide +kernel
private theorem coverMasks₁ : ∀ r : Fin 256, coveredMask (256 + r) := by decide +kernel
private theorem coverMasks₂ : ∀ r : Fin 256, coveredMask (512 + r) := by decide +kernel
private theorem coverMasks₃ : ∀ r : Fin 256, coveredMask (768 + r) := by decide +kernel

private theorem coverMasks (r : Fin 1024) : coveredMask r := by
  have hr := r.isLt
  by_cases h₁ : r.val < 256
  · exact coverMasks₀ ⟨r, h₁⟩
  by_cases h₂ : r.val < 512
  · have e : 256 + (r.val - 256) = r.val := by omega
    rw [← e]
    exact coverMasks₁ ⟨r.val - 256, by omega⟩
  by_cases h₃ : r.val < 768
  · have e : 512 + (r.val - 512) = r.val := by omega
    rw [← e]
    exact coverMasks₂ ⟨r.val - 512, by omega⟩
  · have e : 768 + (r.val - 768) = r.val := by omega
    rw [← e]
    exact coverMasks₃ ⟨r.val - 768, by omega⟩

private theorem coverProbe (r : Fin 1024) :
    ∃ p ∈ probes, p.2 = petBool (bits r) ∧
      (if p.2 then belowBits (bits p.1) (bits r) else belowBits (bits r) (bits p.1)) := by
  obtain ⟨p, hp, hv, h⟩ := coverMasks r
  refine ⟨p, hp, hv, ?_⟩
  cases hb : p.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> exact belowOfAnd h

private theorem allProbes (x : Fin 10 → Bool) :
    ∃ p ∈ probes, p.2 = petBool x ∧
      (if p.2 then belowBits (bits p.1) x else belowBits x (bits p.1)) := by
  let packed := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 1024 := ⟨packed.toNat, by simpa using packed.isLt⟩
  have hr : bits r = x := by
    funext i
    change packed.getLsbD i = x i
    rw [BitVec.getLsbD_ofBoolListLE]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  simpa only [hr] using coverProbe r

private def remapWire (k j : Nat) : Nat :=
  if j = 0 then k else if j < k then j else j + 1

private def insCircuit (C : Circuit) (x2 : Nat) : Circuit :=
  let pre := C.gates.take (x2 - 10 + 1)
  let post := C.gates.drop (x2 - 10 + 1)
  ⟨pre ++ { op := GateOp.or, inputs := [0, x2] } ::
      post.map (fun g => ⟨g.op, g.inputs.map (remapWire (x2 + 1))⟩),
    remapWire (x2 + 1) C.output⟩

private theorem insCircuit_size (C : Circuit) (x2 : Nat) :
    (insCircuit C x2).size = C.size + 1 := by
  change (C.gates.take (x2 - 10 + 1) ++ ({ op := GateOp.or, inputs := [0, x2] } : Gate) ::
      (C.gates.drop (x2 - 10 + 1)).map _).length = C.gates.length + 1
  simp only [List.length_append, List.length_cons, List.length_map, List.length_take, List.length_drop]
  omega

private theorem insCircuit_mono (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 10 C) (x2 : Nat) :
    Monotone2 (insCircuit C x2) := by
  intro g hg
  change g ∈ C.gates.take (x2 - 10 + 1) ++ { op := GateOp.or, inputs := [0, x2] } ::
      (C.gates.drop (x2 - 10 + 1)).map _ at hg
  simp only [List.mem_append, List.mem_cons, List.mem_map] at hg
  rcases hg with hpre | rfl | ⟨g0, hpost, rfl⟩
  · have hm := List.mem_of_mem_take hpre
    have hop := hAO.1 g hm
    have hlen := hAO.2.2 g hm
    refine ⟨?_, by omega⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact ⟨Or.inr rfl, by simp⟩
  · have hm := List.mem_of_mem_drop hpost
    have hop := hAO.1 g0 hm
    have hlen := hAO.2.2 g0 hm
    refine ⟨?_, by simp [hlen]⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr h

private theorem foldStep_prefix2 (gs : List Gate) (w : List Bool) :
    ∃ suf : List Bool, gs.foldl step w = w ++ suf := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons, step]
    obtain ⟨suf, hsuf⟩ := ih (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
    exact ⟨[g.op.eval (g.inputs.map (fun i => w.getD i false))] ++ suf, by simpa [List.append_assoc] using hsuf⟩

private theorem fold_no0 (gs : List Gate) (hno0 : ∀ g ∈ gs, (0 : Nat) ∉ g.inputs)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (heq : ∀ j : Nat, j ≠ 0 → w1.getD j false = w2.getD j false) :
    ∃ out : List Bool, out.length = gs.length ∧
      gs.foldl step w1 = w1 ++ out ∧ gs.foldl step w2 = w2 ++ out := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons g gs ih =>
    have hg0 : (0 : Nat) ∉ g.inputs := hno0 g (by simp)
    have hval : g.op.eval (g.inputs.map (fun i => w1.getD i false)) =
        g.op.eval (g.inputs.map (fun i => w2.getD i false)) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      exact heq j (fun h0 => hg0 (h0 ▸ hj))
    let v := g.op.eval (g.inputs.map (fun i => w2.getD i false))
    have hlen' : (w1 ++ [v]).length = (w2 ++ [v]).length := by simp [hlen]
    have heq' : ∀ j : Nat, j ≠ 0 → (w1 ++ [v]).getD j false = (w2 ++ [v]).getD j false := by
      intro j hj0
      by_cases hj : j < w1.length
      · rw [shortRead _ _ j hj, shortRead _ _ j (by omega)]
        exact heq j hj0
      · rw [longRead _ _ j (by omega), longRead _ _ j (by omega), hlen]
    obtain ⟨out, hout_len, h1, h2⟩ := ih (fun g' hg' => hno0 g' (List.mem_cons_of_mem _ hg')) (w1 ++ [v]) (w2 ++ [v]) hlen' heq'
    refine ⟨v :: out, by simp [hout_len], ?_, ?_⟩
    · simp only [List.foldl_cons, step, hval]
      simpa [v, List.append_assoc] using h1
    · simp only [List.foldl_cons, step]
      simpa [v, List.append_assoc] using h2

private theorem readRemap (u1 u2 b : List Bool) (k : Nat) (hk : 0 < k) (b0 : Bool)
    (hu1 : u1.length = k) (hu2 : u2.length = k)
    (h0 : u1.getD 0 false = b0)
    (hmid : ∀ j : Nat, j ≠ 0 → j < k → u1.getD j false = u2.getD j false) (j : Nat) :
    (u1 ++ b).getD j false = (u2 ++ (b0 :: b)).getD (remapWire k j) false := by
  by_cases hj0 : j = 0
  · subst hj0
    simp only [remapWire, ↓reduceIte]
    rw [shortRead u1 b 0 (by omega), h0, longRead u2 (b0 :: b) k (by omega)]
    simp [hu2]
  · by_cases hjk : j < k
    · simp only [remapWire, hj0, hjk, ↓reduceIte]
      rw [shortRead u1 b j (by omega), shortRead u2 (b0 :: b) j (by omega)]
      exact hmid j hj0 hjk
    · simp only [remapWire, hj0, hjk, ↓reduceIte]
      rw [longRead u1 b j (by omega), longRead u2 (b0 :: b) (j + 1) (by omega), hu1, hu2]
      have hs : j + 1 - k = (j - k) + 1 := by omega
      rw [hs]
      rfl

private theorem foldRemap (u1 u2 : List Bool) (k : Nat) (hk : 0 < k) (b0 : Bool)
    (hu1 : u1.length = k) (hu2 : u2.length = k)
    (h0 : u1.getD 0 false = b0)
    (hmid : ∀ j : Nat, j ≠ 0 → j < k → u1.getD j false = u2.getD j false)
    (gs : List Gate) (b : List Bool) :
    ∃ out : List Bool,
      gs.foldl step (u1 ++ b) = u1 ++ out ∧
      (gs.map (fun g => (⟨g.op, g.inputs.map (remapWire k)⟩ : Gate))).foldl step (u2 ++ (b0 :: b)) =
        u2 ++ (b0 :: out) := by
  induction gs generalizing b with
  | nil => exact ⟨b, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => (u2 ++ (b0 :: b)).getD (remapWire k i) false))
    have hv : g.op.eval (g.inputs.map (fun i => (u1 ++ b).getD i false)) = v := by
      congr 1
      exact List.map_congr_left (fun j _ => readRemap u1 u2 b k hk b0 hu1 hu2 h0 hmid j)
    simp only [List.foldl_cons, List.map_cons, step, List.map_map, Function.comp_def, hv,
      List.append_assoc, List.cons_append]
    exact ih (b ++ [v])

private theorem insCircuit_eval (C : Circuit) (x2 : Nat)
    (hx2_lo : 10 ≤ x2) (hx2_hi : x2 < 10 + C.size)
    (hno0 : ∀ (j : ℕ) (g : Gate), 10 + j ≤ x2 → C.gates[j]? = some g → (0 : ℕ) ∉ g.inputs)
    (x : Fin 10 → Bool) :
    let v := (C.wires (List.ofFn (Function.update x (0 : Fin 10) false))).getD x2 false
    (insCircuit C x2).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update x (0 : Fin 10) (x 0 || v))) := by
  intro v
  let m := x2 - 10
  let pre := C.gates.take (m + 1)
  let post := C.gates.drop (m + 1)
  have hsplit : C.gates = pre ++ post := (List.take_append_drop (m + 1) C.gates).symm
  have hpre_len : pre.length = m + 1 := by
    simp only [pre, List.length_take]
    change x2 < 10 + C.gates.length at hx2_hi
    omega
  have hpre_no0 : ∀ g ∈ pre, (0 : Nat) ∉ g.inputs := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hjlt : j < m + 1 := by omega
    have hget : C.gates[j]? = some pre[j] := by
      rw [List.getElem?_eq_getElem (by change x2 < 10 + C.gates.length at hx2_hi; omega)]
      simp [pre]
    exact hno0 j pre[j] (by omega) hget
  let a := List.ofFn x
  let a0 := List.ofFn (Function.update x (0 : Fin 10) false)
  let a' := List.ofFn (Function.update x (0 : Fin 10) (x 0 || v))
  have heq_a0 : ∀ j : Nat, j ≠ 0 → a.getD j false = a0.getD j false := by
    intro j hj0
    by_cases hj : j < 10
    · simp only [a, a0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
      have hfin : (⟨j, hj⟩ : Fin 10) ≠ 0 := fun h => hj0 (congrArg Fin.val h)
      simp [Function.update, hfin]
    · rw [missingRead a j (by simpa [a] using Nat.le_of_not_gt hj),
          missingRead a0 j (by simpa [a0] using Nat.le_of_not_gt hj)]
  have heq_a' : ∀ j : Nat, j ≠ 0 → a'.getD j false = a.getD j false := by
    intro j hj0
    by_cases hj : j < 10
    · simp only [a, a', List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
      have hfin : (⟨j, hj⟩ : Fin 10) ≠ 0 := fun h => hj0 (congrArg Fin.val h)
      simp [Function.update, hfin]
    · rw [missingRead a' j (by simpa [a'] using Nat.le_of_not_gt hj),
          missingRead a j (by simpa [a] using Nat.le_of_not_gt hj)]
  obtain ⟨out, hout_len, hpre_a, hpre_a0⟩ := fold_no0 pre hpre_no0 a a0 (by simp [a, a0]) heq_a0
  obtain ⟨out', hout'_len, hpre_a', hpre_a2⟩ := fold_no0 pre hpre_no0 a' a (by simp [a', a]) heq_a'
  have hout_eq : out' = out := by
    have h := hpre_a2.symm.trans hpre_a
    exact List.append_cancel_left h
  rw [hout_eq] at hpre_a'
  -- Show v = (a ++ out).getD x2 false
  have hv_eq : v = (a ++ out).getD x2 false := by
    change (C.gates.foldl step a0).getD x2 false = (a ++ out).getD x2 false
    rw [hsplit, List.foldl_append, hpre_a0]
    obtain ⟨suf, hsuf⟩ := foldStep_prefix2 post (a0 ++ out)
    rw [hsuf, shortRead (a0 ++ out) suf x2 (by simp [a0, hout_len, hpre_len]; omega)]
    rw [longRead a0 out x2 (by simp [a0]; omega), longRead a out x2 (by simp [a]; omega)]
    simp [a0, a]
  -- Now evaluate insCircuit C x2 on a vs C on a'
  let k := x2 + 1
  have hu1_len : (a' ++ out).length = k := by simp [a', hout_len, hpre_len]; omega
  have hu2_len : (a ++ out).length = k := by simp [a, hout_len, hpre_len]; omega
  have hu1_0 : (a' ++ out).getD 0 false = (x 0 || v) := by
    rw [shortRead a' out 0 (by simp [a'])]
    simp [a', List.getD_eq_getElem?_getD]
  have hmid : ∀ j : Nat, j ≠ 0 → j < k → (a' ++ out).getD j false = (a ++ out).getD j false := by
    intro j hj0 hjk
    by_cases hj10 : j < 10
    · rw [shortRead a' out j (by simpa [a'] using hj10), shortRead a out j (by simpa [a] using hj10)]
      exact heq_a' j hj0
    · rw [longRead a' out j (by simp [a']; omega), longRead a out j (by simp [a]; omega)]
      simp [a', a]
  have hor_val : (GateOp.or).eval (([0, x2] : List ℕ).map (fun i => (a ++ out).getD i false)) = (x 0 || v) := by
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have h0a : (a ++ out).getD 0 false = x 0 := by
      rw [shortRead a out 0 (by simp [a])]
      simp [a, List.getD_eq_getElem?_getD]
    rw [h0a, hv_eq]
  obtain ⟨out2, hpost1, hpost2⟩ := foldRemap (a' ++ out) (a ++ out) k (by omega) (x 0 || v) hu1_len hu2_len hu1_0 hmid post []
  simp only [List.append_nil] at hpost1
  change ((pre ++ ({ op := GateOp.or, inputs := [0, x2] } : Gate) ::
      post.map (fun g => (⟨g.op, g.inputs.map (remapWire k)⟩ : Gate))).foldl step a).getD (remapWire k C.output) false =
    (C.gates.foldl step a').getD C.output false
  rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, hpre_a, hpre_a']
  have hstep_or : step (a ++ out) { op := GateOp.or, inputs := [0, x2] } = (a ++ out) ++ [x 0 || v] := by
    unfold step
    rw [hor_val]
  rw [hstep_or, hpost1, hpost2]
  exact (readRemap (a' ++ out) (a ++ out) out2 k (by omega) (x 0 || v) hu1_len hu2_len hu1_0 hmid C.output).symm

private def yesRows : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320,528,576,640]
private def noRows : List Nat := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
private def quietRows : List Nat := [50,104,116,138,208,276,402,548,554,770]

private theorem shape {p : Nat × Bool} (hp : p ∈ probes) :
    p.1 ∈ (if p.2 then yesRows else noRows) := by
  simp only [probes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide


def tap (C : Circuit) (w : Nat) (x : Fin 10 → Bool) : Bool :=
  (C.wires (List.ofFn (Function.update x 0 false))).getD w false

def modified (C : Circuit) (w : Nat) (x : Fin 10 → Bool) : Bool :=
  C.eval (List.ofFn (Function.update x 0 (x 0 || tap C w x)))

theorem trueOnWholeCube (C : Circuit) (w : Nat) (ao : PEqualNP.TopForm.IsAO2 10 C)
    (lo : 10≤w) (hi : w<10+C.size)
    (schedule : ∀ j g, 10+j≤w → C.gates[j]?=some g → 0∉g.inputs)
    (pos : ∀ m ∈ yesRows, modified C w (bits m) = true)
    (neg : ∀ m ∈ noRows, modified C w (bits m) = false) :
    ∀ x, modified C w x = petBool x := by
  intro x
  have ev (z : Fin 10 → Bool) : (insCircuit C w).eval (List.ofFn z) = modified C w z :=
    insCircuit_eval C w lo hi schedule z
  rw [← ev]
  obtain ⟨p,hp,hval,hle⟩ := allProbes x
  rw [← hval]
  have hmono := insCircuit_mono C ao w
  have mem := shape hp
  cases hb : p.2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hle mem
    have no := (ev (bits p.1)).trans (neg _ mem)
    cases h : (insCircuit C w).eval (List.ofFn x)
    · rfl
    · have hh := bitsMono _ hmono hle h
      rw [no] at hh
      contradiction
  · simp only [hb, ↓reduceIte] at hle mem
    exact bitsMono _ hmono hle ((ev (bits p.1)).trans (pos _ mem))

theorem starZeroSlice (C : Circuit) (w : Nat) (center a b : Fin 10)
    (equiv : ∀ x, modified C w x = petBool x)
    (guard : ∀ x, tap C w x = (x center && (x a || x b))) :
    ∀ x : Fin 10 → Bool, C.eval (List.ofFn (Function.update x center false)) =
      petBool (Function.update x center false) := by
  intro x
  have h := equiv (Function.update x center false)
  simpa [modified,guard] using h

end PetersenFeedbackCore

-- The evaluation preliminaries through val_ofFn_lt are from L_meta_3545 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3568


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl


def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

open PEqualNP.TopForm

theorem first_reader {n : Nat} (C : Circuit) (rb : ReadsBack n C) (z : Fin n)
    (X Y : Fin n → Bool) (off : ∀ v : Fin n, v ≠ z → X v = Y v)
    (zero : X z = false) (out : C.output ≠ z.val)
    (diff : circuitFun n C X ≠ circuitFun n C Y)
    (andOnly : ∀ j < C.gates.length, z.val ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.and) :
    ∃ j < C.gates.length, z.val ∈ (gateAt C j).inputs ∧
      ∀ i ∈ (gateAt C j).inputs, i ≠ z.val → val C (List.ofFn X) i = true := by
  classical
  let old := val C (List.ofFn X)
  let new := val C (List.ofFn Y)
  have ex : ∃ w : Nat, w ≠ z.val ∧ old w ≠ new w := ⟨C.output,out,diff⟩
  let w := Nat.find ex
  obtain ⟨wz,wc⟩ : w ≠ z.val ∧ old w ≠ new w := Nat.find_spec ex
  have earlier (i : Nat) (hi : i < w) (iz : i ≠ z.val) : old i = new i := by
    by_contra h
    exact Nat.find_min ex hi ⟨iz,h⟩
  have lo : n ≤ w := by
    by_contra! small
    apply wc
    change val C (List.ofFn X) w = val C (List.ofFn Y) w
    rw [val_ofFn_lt _ _ _ small,val_ofFn_lt _ _ _ small]
    exact off _ (fun e => wz (congrArg Fin.val e))
  have hi : w < n+C.gates.length := by
    by_contra! big
    apply wc
    change val C (List.ofFn X) w = val C (List.ofFn Y) w
    rw [val_ge (by simp) (n:=n) big,val_ge (by simp) (n:=n) big]
  let j := w-n
  have wj : n+j=w := by dsimp only [j]; omega
  have valid : j<C.gates.length := by omega
  have leval : old w = (gateAt C j).op.eval ((gateAt C j).inputs.map old) := by
    rw [←wj]
    exact val_gate_rb (by simp) valid (rb j valid)
  have reval : new w = (gateAt C j).op.eval ((gateAt C j).inputs.map new) := by
    rw [←wj]
    exact val_gate_rb (by simp) valid (rb j valid)
  have before (i) (e : i ∈ (gateAt C j).inputs) : i < w := wj ▸ rb j valid i e
  have reads : z.val ∈ (gateAt C j).inputs := by
    by_contra h
    apply wc
    rw [leval,reval]
    congr 1
    apply List.map_congr_left
    intro i e
    exact earlier i (before i e) (fun eq => h (eq ▸ e))
  have hop := andOnly j valid reads
  have z0 : old z.val = false := (val_ofFn C X z).trans zero
  have low : old w ≠ true := by
    intro yes
    rw [leval,hop,eval_and_iff] at yes
    have h := yes z.val reads
    rw [z0] at h
    contradiction
  have high : new w = true := by
    cases l : old w <;> cases r : new w <;> simp_all
  rw [reval,hop,eval_and_iff] at high
  refine ⟨j,valid,reads,?_⟩
  intro i e iz
  exact (earlier i (before i e) iz).trans (high i e)

end PEqualNP.Outside.L_meta_3568

-- Wire bypass lemmas from the published L_meta_1485.
namespace PEqualNP.Outside.L_meta_3568.Bypass

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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
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
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
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
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
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

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
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

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma isAO2_bypass {n : ℕ} {D : Circuit} {r i : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (hi : i < n + r) : PEqualNP.TopForm.IsAO2 n (bypass n D r i) := by
  refine ⟨?_, bypass_readsBack hi hD.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]; exact hD.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hl⟩ := bypass_mem g hg
    rw [hl]; exact hD.2.2 g' hg'

end PEqualNP.Outside.L_meta_3568.Bypass

-- Slice compiler from the published L_meta_18145.
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

private abbrev W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  scan boolStep gs (List.ofFn x)

private theorem inputAt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (W n gs x).getD i false = x ⟨i,hi⟩ := by
  rw [scan_prefix boolStep _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem wireAtGate {n : ℕ} (C : Circuit) (h : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    (W n C.gates x).getD (n+j) false = boolStep (W n C.gates x) C.gates[j] := by
  simpa only [List.length_ofFn] using
    (scan_gate boolStep C.gates (List.ofFn x) false j hj (fun r s he => by
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro i hi
      apply he
      have := h.2.1 j hj i (by rwa [gateAt_eq_getElem hj])
      simpa using this))

private def readOpt (w : List Bool) (ref : Option ℕ) : Bool :=
  (ref.map fun i => w.getD i false).getD false

private def validRef (lim : ℕ) (ref : Option ℕ) : Prop :=
  ∀ i, ref = some i → i < lim

private theorem optPrefix (w : List Bool) (v : Bool) (ref : Option ℕ) (ok : validRef w.length ref) :
    readOpt (w ++ [v]) ref = readOpt w ref := by
  cases ref with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (ok i rfl)

private inductive Action where
  | reuse (ref : Option ℕ)
  | add (g : Gate)

private def Action.ref (lim : ℕ) : Action → Option ℕ
  | .reuse r => r
  | .add _ => some lim

private def Action.newGates : Action → List Gate
  | .reuse _ => []
  | .add g => [g]

private def Action.eval (w : List Bool) : Action → Bool
  | .reuse r => readOpt w r
  | .add g => boolStep w g

private def Action.Well (limit : ℕ) : Action → Prop
  | .reuse r => validRef limit r
  | .add g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < limit

private theorem newGatesSmall (act : Action) : act.newGates.length ≤ 1 := by cases act <;> simp [Action.newGates]

private def pick (op : GateOp) (a b : Option ℕ) : Action :=
  match a, b with
  | some i, some j => .add ⟨op,[i,j]⟩
  | none, v | v, none => .reuse (if op.eval [false,true] then v else none)

private theorem pickSound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (w : List Bool) : (pick op a b).eval w =
      op.eval [readOpt w a,readOpt w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [pick,Action.eval,readOpt,GateOp.eval,boolStep]

private theorem pickWell (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (lim : ℕ) (va : validRef lim a) (vb : validRef lim b) :
    (pick op a b).Well lim := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [pick,Action.Well,validRef,GateOp.eval]

private theorem actionApply {n : ℕ} (gs : List Gate) (legal : IsAO2 n (⟨gs,0⟩ : Circuit))
    (act : Action) (well : act.Well (n+gs.length)) :
    IsAO2 n (⟨gs++act.newGates,0⟩ : Circuit) := by
  cases act with
  | reuse r => simpa [Action.newGates] using legal
  | add g =>
    obtain ⟨hop,hlen,back⟩ := well
    refine ⟨?_,?_,?_⟩
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.1 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hop
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append,List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · have he : gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
          rw [gateAt,gateAt,List.getD_append _ _ _ _ hlt]
        exact legal.2.1 j hlt i (he ▸ hi)
      · have heq : j = gs.length := by omega
        subst j
        have he : gateAt ⟨gs++[g],0⟩ gs.length = g := by
          rw [gateAt,List.getD_append_right _ _ _ _ (by simp),Nat.sub_self,List.getD_cons_zero]
        exact back i (he ▸ hi)
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.2.2 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hlen

private theorem oldSource (act : Action) (w : List Bool) (ref : Option ℕ)
    (vr : validRef w.length ref) :
    readOpt (scan boolStep act.newGates w) ref = readOpt w ref := by
  cases act with
  | reuse r => rfl
  | add g => exact optPrefix w _ ref vr

private theorem resultSource (act : Action) (w : List Bool) (ok : act.Well w.length) :
    readOpt (scan boolStep act.newGates w) (act.ref w.length) = act.eval w := by
  cases act with
  | reuse r => rfl
  | add g =>
    change (w ++ [boolStep w g]).getD w.length false = boolStep w g
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self,List.getD_cons_zero]

private theorem refAvailable (act : Action) (lim : ℕ) (hw : act.Well lim) :
    validRef (lim+act.newGates.length) (act.ref lim) := by
  cases act with
  | reuse r => simpa [Action.ref,Action.newGates,Action.Well] using hw
  | add g => simp [Action.ref,Action.newGates,validRef]

private theorem validEnlarge (ref : Option ℕ) {a b : ℕ} (h : a ≤ b) (vr : validRef a ref) : validRef b ref :=
  fun i hi => Nat.lt_of_lt_of_le (vr i hi) h

private abbrev fixed {n : ℕ} (x : Fin n → Bool) (p : Fin n) := Function.update x p false

private structure Prefix (n : ℕ) (C : Circuit) (p : Fin n) (S : Finset ℕ) (j : ℕ) where
  gs : List Gate
  f : ℕ → Option ℕ
  legal : IsAO2 n (⟨gs,0⟩ : Circuit)
  cost : gs.length + (S.filter (· < j)).card ≤ j
  valids : ∀ i < n+j, validRef (n+gs.length) (f i)
  sound : ∀ i < n+j, ∀ x : Fin n → Bool,
    readOpt (W n gs x) (f i) = (W n C.gates (fixed x p)).getD i false

private theorem countFilterStep (S : Finset ℕ) (j : ℕ) :
    (S.filter (· < j+1)).card = (S.filter (· < j)).card + if j ∈ S then 1 else 0 := by
  by_cases hm : j ∈ S
  · have e : S.filter (· < j+1) = insert j (S.filter (· < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hl⟩
        by_cases e : i = j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [e,Finset.card_insert_of_notMem (by simp),ite_eq_left hm]
  · have e : S.filter (· < j+1) = S.filter (· < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hl⟩
        exact ⟨hi,by have hn : i ≠ j := fun eq => hm (eq ▸ hi); omega⟩
      · rintro ⟨hi,hl⟩; exact ⟨hi,by omega⟩
    rw [e,ite_eq_right hm,Nat.add_zero]

private def Prefix.step {n : ℕ} {C : Circuit} {p : Fin n} {S : Finset ℕ} {j : ℕ}
    (P : Prefix n C p S j) (act : Action) (hw : act.Well (n+P.gs.length))
    (hshort : act.newGates.length + (if j ∈ S then 1 else 0) ≤ 1)
    (ok : ∀ x : Fin n → Bool, act.eval (W n P.gs x) =
      (W n C.gates (fixed x p)).getD (n+j) false) : Prefix n C p S (j+1) := by
  let new := P.gs ++ act.newGates
  let ff (i : ℕ) := if i = n+j then act.ref (n+P.gs.length) else P.f i
  refine ⟨new,ff,actionApply P.gs P.legal act hw,?_,?_,?_⟩
  · have hc := P.cost
    rw [countFilterStep]
    simp only [new,List.length_append]
    omega
  · intro i hi
    by_cases he : i = n+j
    · simpa [ff,new,he,Nat.add_assoc] using refAvailable act (n+P.gs.length) hw
    · change validRef _ (if i = n+j then _ else P.f i)
      rw [ite_eq_right he]
      exact validEnlarge _ (by simp [new]) (P.valids _ (by omega))
  · intro i hi x
    have len : (W n P.gs x).length = n+P.gs.length := by rw [scan_length,List.length_ofFn]
    rw [show W n new x = scan boolStep act.newGates (W n P.gs x) by exact scan_append boolStep _ _ _]
    by_cases he : i = n+j
    · subst i
      simp only [ff,ite_true]
      rw [← len,resultSource _ _ (by rw [len]; exact hw)]
      exact ok x
    · simp only [ff,he,ite_false]
      rw [oldSource _ _ _ (by rw [len]; exact P.valids _ (by omega))]
      exact P.sound _ (by omega) x

private theorem build {n : ℕ} {C : Circuit} (p : Fin n) (S : Finset ℕ)
    (hC : IsAO2 n C)
    (aliases : ∀ j ∈ S, ∃ i < n+j, ∀ x : Fin n → Bool,
      (W n C.gates (fixed x p)).getD (n+j) false = (W n C.gates (fixed x p)).getD i false)
    (j : ℕ) (bound : j ≤ C.gates.length) : Nonempty (Prefix n C p S j) := by
  induction j with
  | zero =>
    refine ⟨⟨[],fun i => if i = p.val then none else some i,by simp [IsAO2,PEqualNP.EdgeOwnership.AndOrOnly,ReadsBack],by simp,?_,?_⟩⟩
    · intro i hi
      by_cases he : i = p.val
      · simp [he,validRef]
      · simpa [he,validRef] using hi
    · intro i hi x
      have hi' : i < n := by simpa using hi
      rw [inputAt C.gates _ i hi']
      by_cases he : i = p.val
      · have hp : (⟨i,hi'⟩ : Fin n) = p := Fin.ext he
        simp [he,readOpt,fixed]
      · have hp : (⟨i,hi'⟩ : Fin n) ≠ p := fun h => he (congrArg Fin.val h)
        simp only [he,ite_false,readOpt,Option.map_some,Option.getD_some]
        rw [inputAt [] x i hi']
        simp [fixed,Function.update_of_ne hp]
  | succ j ih =>
    obtain ⟨P⟩ := ih (by omega)
    have hj : j < C.gates.length := by omega
    by_cases hm : j ∈ S
    · obtain ⟨i,hi,he⟩ := aliases j hm
      refine ⟨P.step (.reuse (P.f i)) (P.valids i hi) (by simp [Action.newGates,hm]) (fun x => ?_)⟩
      exact (P.sound i hi x).trans (he x).symm
    · obtain ⟨hop,hin,ha,hb⟩ := ao2_gate_props hC hj
      let g := gateAt C j
      let a := opnd C j 0
      let b := opnd C j 1
      let act := pick g.op (P.f a) (P.f b)
      refine ⟨P.step act (pickWell _ hop _ _ _ (P.valids a ha) (P.valids b hb)) ?_ (fun x => ?_)⟩
      · simpa [hm] using newGatesSmall act
      · rw [wireAtGate C hC j hj,← gateAt_eq_getElem hj]
        rw [pickSound g.op hop, P.sound a ha, P.sound b hb]
        change g.op.eval [_ , _] = boolStep _ g
        rw [boolStep,show g.inputs = [a,b] from hin]
        rfl



theorem compile : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x4,         x6 < x2.size ∧           ∃ x8 < x1 + x6,             ∀ (x9 : Fin x1 → Bool),               have x10 : List Bool := x2.wires (List.ofFn (Function.update x9 x3 Bool.false));               x10.getD (x1 + x6) Bool.false = x10.getD x8 Bool.false) →       (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.ofFn (Function.update x7 x3 Bool.false)) ≠ x2.eval (List.ofFn (Function.update x8 x3 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + x4.card ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.ofFn (Function.update x9 x3 Bool.false))) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3568.Slice in
  intro n C p S hC hAlias nconst
  obtain ⟨P⟩ := build p S hC (fun j hj => (hAlias j hj).2) C.gates.length (Nat.le_refl _)
  have within : C.output < n + C.gates.length := by
    by_contra! h
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      change (W n C.gates (fixed z p)).getD C.output false = false
      apply List.getD_eq_default
      rwa [scan_length,List.length_ofFn]
    exact hn ((zero x).trans (zero y).symm)
  cases he : P.f C.output with
  | none =>
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      have hz := P.sound C.output within z
      rw [he] at hz
      exact hz.symm
    exact False.elim (hn ((zero x).trans (zero y).symm))
  | some o =>
    have hsize := P.cost
    have hs : S.filter (· < C.gates.length) = S := Finset.filter_true_of_mem (fun _ hi => (hAlias _ hi).1)
    rw [hs] at hsize
    refine ⟨⟨P.gs,o⟩,P.legal,hsize,?_⟩
    intro x
    change (W n P.gs x).getD o false = (W n C.gates (fixed x p)).getD C.output false
    simpa only [he,readOpt,Option.map_some,Option.getD_some] using P.sound C.output within x

end PEqualNP.Outside.L_meta_3568.Slice

namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

variable {n : Nat} {C : Circuit}

private abbrev V (C : Circuit) (x : Fin n → Bool) (w : Nat) :=
  (C.wires (List.ofFn x)).getD w false

private theorem vin (x : Fin n → Bool) (p : Fin n) : V C x p.val = x p := by
  change Bypass.val C (List.ofFn x) p.val = x p
  rw [Bypass.val_input (List.length_ofFn) p.isLt, List.getD_eq_getElem _ _ (by simpa using p.isLt)]
  simp

private theorem vgate (hao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    V C x (n+j) = (gateAt C j).op.eval
      [V C x (opnd C j 0), V C x (opnd C j 1)] := by
  obtain ⟨_, hin, ha, hb⟩ := Slice.ao2_gate_props hao hj
  change Bypass.val C _ _ = _
  rw [Bypass.val_gate (List.length_ofFn) hj, hin]
  simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
  rfl

private theorem inputs_pair (hao : IsAO2 n C) {j w : Nat} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) :
    ∃ t < n+j, (opnd C j 0 = w ∧ opnd C j 1 = t) ∨
      (opnd C j 0 = t ∧ opnd C j 1 = w) := by
  obtain ⟨_, hi, ha, hb⟩ := Slice.ao2_gate_props hao hj
  rw [hi] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with h | h
  · exact ⟨_,hb,Or.inl ⟨h.symm,rfl⟩⟩
  · exact ⟨_,ha,Or.inr ⟨rfl,h.symm⟩⟩

private theorem vseparate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) {j w : Nat} (hj : j < C.gates.length) (hw : w < n+j) :
    ¬ ∀ (x : Fin n → Bool), V C x (n+j) = V C x w := by
  intro same
  let D := Bypass.bypass n C j w
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_eq List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hw) (same x)
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hw) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j w).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private theorem live (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {j : Nat} (hj : j < C.gates.length)
    (hout : C.output ≠ n+j) : ∃ k < C.gates.length, n+j ∈ (gateAt C k).inputs := by
  by_contra! h
  let D := Bypass.bypass n C j p.val
  have hp : p.val < n+j := by have := p.isLt; omega
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_unread List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hp) hout h
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hp) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j p.val).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private def Zero (C : Circuit) (p : Fin n) (w : Nat) : Prop :=
  ∀ x : Fin n → Bool, x p = false → V C x w = false

private theorem inputZero (p : Fin n) : Zero C p p.val := by
  intro x hx
  simpa only [vin] using hx

private theorem zeroAnd (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and)
    (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) : Zero C p (n+j) := by
  obtain ⟨t,_,h | h⟩ := inputs_pair hao hj hw <;> intro x hx <;>
    rw [vgate hao j hj x, hand, h.1, h.2, hz x hx] <;> simp [GateOp.eval]

private theorem aliasOfZeroRead (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) :
    ∃ i < n+j, ∀ (x : Fin n → Bool), x p = false → V C x (n+j) = V C x i := by
  rcases (Slice.ao2_gate_props hao hj).1 with hand | hor
  · exact ⟨p.val,by have := p.isLt; omega,fun x hx => (zeroAnd hao hj hand hw hz x hx).trans
      (by rw [vin,hx])⟩
  · obtain ⟨t,ht,h | h⟩ := inputs_pair hao hj hw <;> refine ⟨t,ht,?_⟩ <;> intro x hx <;>
      rw [vgate hao j hj x, hor, h.1, h.2, hz x hx] <;> simp [GateOp.eval]

private theorem noJointReader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {k j : Nat} (hk : k < C.gates.length)
    (pk : p.val ∈ (gateAt C k).inputs) (jk : n+j ∈ (gateAt C k).inputs)
    (hz : Zero C p (n+j)) : False := by
  obtain ⟨t,_,h | h⟩ := inputs_pair least.1 hk pk
  all_goals
    have ne : n+j ≠ p.val := by have := p.isLt; omega
    have hin := (Slice.ao2_gate_props least.1 hk).2.1
    rw [hin,h.1,h.2] at jk
    have ht : n+j = t := by simpa [ne] using jk
    subst t
    rcases (Slice.ao2_gate_props least.1 hk).1 with ha | ho
    · apply vseparate G least hk (w := n+j) (least.1.2.1 k hk _ (by rw [hin,h.1,h.2]; simp))
      intro x
      rw [vgate least.1 k hk x,ha,h.1,h.2,vin]
      cases hx : x p with
      | false => rw [hz x hx] <;> rfl
      | true => simp [GateOp.eval]
    · apply vseparate G least hk (w := p.val) (by have := p.isLt; omega)
      intro x
      rw [vgate least.1 k hk x,ho,h.1,h.2,vin]
      cases hx : x p with
      | false => rw [hz x hx] <;> rfl
      | true => simp [GateOp.eval]

noncomputable def direct (C : Circuit) (p : Fin n) : Finset Nat :=
  (Finset.range C.gates.length).filter fun j => p.val ∈ (gateAt C j).inputs

theorem count_direct_plus_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n)
    (hpos : ∃ x : Fin n → Bool, x p = false ∧ circuitFun n C x = true)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
      C.eval (List.ofFn (Function.update y p false)))
    (reader : ∃ j < C.gates.length, (gateAt C j).op = .and ∧ p.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + (direct C p).card + 1 ≤ C.size ∧
      ∀ x, circuitFun n D x = circuitFun n C (Function.update x p false) := by
  classical
  obtain ⟨j,hj,hand,hp⟩ := reader
  have hz := zeroAnd least.1 hj hand hp (inputZero p)
  obtain ⟨x,hx,hon⟩ := hpos
  have hout : C.output ≠ n+j := by
    intro eqv
    change V C x C.output = true at hon
    rw [eqv,hz x hx] at hon
    contradiction
  obtain ⟨k,hk,jk⟩ := live G least p hj hout
  have kn : k ∉ direct C p := by
    intro mem
    exact noJointReader G least p hk (Finset.mem_filter.mp mem).2 jk hz
  have aliases (g : Nat) (hg : g ∈ insert k (direct C p)) :
      g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
        V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
    have pack (hgt : g < C.gates.length) (w : Nat) (hw : w ∈ (gateAt C g).inputs)
        (zero : Zero C p w) : g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
          V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
      obtain ⟨i,hi,he⟩ := aliasOfZeroRead least.1 hgt hw zero
      exact ⟨hgt,i,hi,fun x => he _ (by simp)⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact pack hk _ jk hz
    · obtain ⟨hg,hread⟩ := Finset.mem_filter.mp hg
      exact pack (Finset.mem_range.mp hg) p.val hread (inputZero p)
  obtain ⟨D,hao,hle,hfun⟩ := Slice.compile n C p (insert k (direct C p)) least.1 aliases hnc
  rw [Finset.card_insert_of_notMem kn] at hle
  exact ⟨D,hao,by omega,hfun⟩

end PEqualNP.Outside.L_meta_3568.Reader
namespace PEqualNP.Outside.L_meta_3568
open PEqualNP.CircuitLowerBounds

def WireMap {n : Nat} (C : Circuit) (p : Fin n) (D : Circuit) : Prop :=
  ∀ i < n+C.gates.length, (∃ x : Fin n → Bool, val C (List.ofFn (Function.update x p false)) i = true) →
    ∃ k < n+D.gates.length, ∀ x : Fin n → Bool,
      val D (List.ofFn x) k = val C (List.ofFn (Function.update x p false)) i

namespace Slice
theorem compile_marked : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x4,         x6 < x2.size ∧           ∃ x8 < x1 + x6,             ∀ (x9 : Fin x1 → Bool),               have x10 : List Bool := x2.wires (List.ofFn (Function.update x9 x3 Bool.false));               x10.getD (x1 + x6) Bool.false = x10.getD x8 Bool.false) →       (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.ofFn (Function.update x7 x3 Bool.false)) ≠ x2.eval (List.ofFn (Function.update x8 x3 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + x4.card ≤ x2.size ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.ofFn (Function.update x9 x3 Bool.false))) ∧ WireMap x2 x3 x8) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3568.Slice in
  intro n C p S hC hAlias nconst
  obtain ⟨P⟩ := build p S hC (fun j hj => (hAlias j hj).2) C.gates.length (Nat.le_refl _)
  have within : C.output < n + C.gates.length := by
    by_contra! h
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      change (W n C.gates (fixed z p)).getD C.output false = false
      apply List.getD_eq_default
      rwa [scan_length,List.length_ofFn]
    exact hn ((zero x).trans (zero y).symm)
  cases he : P.f C.output with
  | none =>
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      have hz := P.sound C.output within z
      rw [he] at hz
      exact hz.symm
    exact False.elim (hn ((zero x).trans (zero y).symm))
  | some o =>
    have hsize := P.cost
    have hs : S.filter (· < C.gates.length) = S := Finset.filter_true_of_mem (fun _ hi => (hAlias _ hi).1)
    rw [hs] at hsize
    refine ⟨⟨P.gs,o⟩,P.legal,hsize,?_,?_⟩
    · intro x
      change (W n P.gs x).getD o false = (W n C.gates (fixed x p)).getD C.output false
      simpa only [he,readOpt,Option.map_some,Option.getD_some] using P.sound C.output within x
    · intro i hi positive
      cases fi : P.f i with
      | none =>
        obtain ⟨x,hx⟩ := positive
        have zero := P.sound i hi x
        rw [fi] at zero
        change false = val C (List.ofFn (Function.update x p false)) i at zero
        rw [hx] at zero
        contradiction
      | some k =>
        refine ⟨k,P.valids i hi k fi,fun x => ?_⟩
        change (W n P.gs x).getD k false = (W n C.gates (fixed x p)).getD i false
        simpa only [fi,readOpt,Option.map_some,Option.getD_some] using P.sound i hi x

end Slice

end PEqualNP.Outside.L_meta_3568

namespace PEqualNP.Outside.L_meta_3568.Reader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PetersenFeedbackCore

theorem firstStarMinor (C : Circuit) (ao : IsAO2 10 C) (size : C.size ≤ 18)
    (length : 2 ≤ C.gates.length)
    (first : gateAt C 0 = ⟨.or,[2,6]⟩) (second : gateAt C 1 = ⟨.and,[1,10]⟩)
    (equiv : ∀ x, modified C 11 x = petBool x) :
    ∃ D : Circuit, IsAO2 10 D ∧ D.size ≤ 16 ∧
      (∀ x : Fin 10 → Bool, circuitFun 10 D x = petBool (Function.update x 1 false)) ∧
      ∃ k < 10 + D.size, ∀ (x : Fin 10 → Bool), val D (List.ofFn x) k = (x 2 || x 6) := by
  classical
  have firstVal (x : Fin 10 → Bool) : val C (List.ofFn x) 10 = (x 2 || x 6) := by
    have v := val_gate_rb (C:=C) (n:=10) (x:=List.ofFn x) List.length_ofFn (j:=0) (by omega) (ao.2.1 0 (by omega))
    rw [first] at v
    simpa [GateOp.eval, val_ofFn_lt C x 2 (by decide), val_ofFn_lt C x 6 (by decide)] using v
  have secondVal (x : Fin 10 → Bool) : val C (List.ofFn x) 11 = (x 1 && (x 2 || x 6)) := by
    have v := val_gate_rb (C:=C) (n:=10) (x:=List.ofFn x) List.length_ofFn (j:=1) (by omega) (ao.2.1 1 (by omega))
    rw [second] at v
    simpa [GateOp.eval,val_ofFn_lt C x 1 (by decide),firstVal] using v
  have guard (x : Fin 10 → Bool) : tap C 11 x = (x 1 && (x 2 || x 6)) := by
    change val C (List.ofFn _) 11 = _
    simpa using secondVal (Function.update x 0 false)
  have slice := starZeroSlice C 11 1 2 6 equiv guard
  have high (x : Fin 10 → Bool) (h : x 0 = true) : circuitFun 10 C x = petBool x := by
    have H := equiv x
    unfold modified at H
    rw [show (x 0 || tap C 11 x) = x 0 by simp [h], Function.update_eq_self] at H
    exact H
  have directRead (j : Nat) (hj : j<C.gates.length) (hr : 1 ∈ (gateAt C j).inputs) :
      j ∈ direct C (1 : Fin 10) := by simpa [direct,hj] using hr
  have one : 1 ∈ direct C (1 : Fin 10) :=
    directRead 1 (by omega) (by rw [second]; decide)
  have diff : circuitFun 10 C (bits 1) ≠ circuitFun 10 C (bits 3) := by
    rw [high _ (by decide), high _ (by decide)]
    decide
  have out : C.output ≠ (1 : Fin 10).val := by
    intro e
    have y := high (bits 17) (by decide)
    change val C (List.ofFn (bits 17)) C.output = petBool (bits 17) at y
    rw [e, val_ofFn] at y
    revert y
    decide
  have branch : ∃ j ∈ direct C (1 : Fin 10), j≠1 := by
    by_contra no
    have only (j : Nat) (hj : j<C.gates.length) (hr : 1 ∈ (gateAt C j).inputs) : j=1 := by
      by_contra ne
      exact no ⟨j,directRead j hj hr,ne⟩
    have allAnd (j : Nat) (hj : j<C.gates.length) (hr : (1 : Fin 10).val ∈ (gateAt C j).inputs) :
        (gateAt C j).op = .and := by rw [only j hj hr,second]
    obtain ⟨j,hj,hr,others⟩ := first_reader C ao.2.1 (1 : Fin 10) (bits 1) (bits 3)
      (by decide) (by decide) out diff allAnd
    have ej := only j hj hr
    subst j
    have bad := others 10 (by rw [second]; decide) (by decide)
    rw [firstVal] at bad
    revert bad
    decide
  obtain ⟨j,hj,ne⟩ := branch
  have two : 1 < (direct C (1 : Fin 10)).card := Finset.one_lt_card.mpr ⟨j,hj,1,one,ne⟩
  let S := direct C (1 : Fin 10)
  have aliases : ∀ j ∈ S, j < C.size ∧ ∃ i < 10+j, ∀ x : Fin 10 → Bool,
      V C (Function.update x 1 false) (10+j) = V C (Function.update x 1 false) i := by
    intro j hj
    obtain ⟨lt,read⟩ : j<C.gates.length ∧ (1 : Fin 10).val ∈ (gateAt C j).inputs := by
      simpa [S,direct] using hj
    obtain ⟨i,hi,e⟩ := aliasOfZeroRead ao lt read (inputZero (1 : Fin 10))
    exact ⟨lt,i,hi,fun x => e _ (by simp)⟩
  have nc : ∃ x y : Fin 10 → Bool, C.eval (List.ofFn (Function.update x 1 false)) ≠
      C.eval (List.ofFn (Function.update y 1 false)) := by
    refine ⟨bits 12,bits 0,?_⟩
    rw [slice,slice]
    decide
  obtain ⟨D,legal,cost,works,transfer⟩ := Slice.compile_marked 10 C 1 S ao aliases nc
  change D.size + (direct C (1 : Fin 10)).card ≤ C.size at cost
  obtain ⟨k,bound,track⟩ := transfer 10 (by omega) ⟨bits 4,by rw [firstVal]; decide⟩
  refine ⟨D,legal,by omega,fun x => (works x).trans (slice x),k,bound,?_⟩
  intro x
  rw [track,firstVal]
  simp

end PEqualNP.Outside.L_meta_3568.Reader

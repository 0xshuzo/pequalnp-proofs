import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3921_729
    (binaryBound : ∀ (D : Circuit), FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (finite : let seeds : List (BitVec 29) := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18813609]
      ∀ program : List (BitVec 29), program.length ≤ 13 →
      (∀ j (hj : j < program.length), program[j] ∉ seeds ++ program.take j ∧
        ∃ a ∈ seeds ++ program.take j, ∃ b ∈ seeds ++ program.take j,
          program[j] = a &&& b ∨ program[j] = a ||| b) →
      (65535 : BitVec 29) ∉ seeds ++ program) :
∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         (1 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro pins len _ allowed hasOne C fan budget
  let F := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let input := fun (ls : List ℕ) (x : Fin 9 → Bool) =>
    let z := List.ofFn x ++ [!x 0]
    z ++ [GateOp.or.eval (ls.map fun i => z.getD i false)]
  by_contra missed
  have correct (x : Fin 9 → Bool) : C.eval (input pins x) = F x :=
    Classical.not_not.mp (fun wrong => missed ⟨x,wrong⟩)
  let first : Gate := ⟨.not,[0]⟩
  let second : Gate := ⟨.or,pins⟩
  let D : Circuit := ⟨first :: second :: C.gates,C.output⟩
  have dfan : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl),by decide⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),len.le⟩
    exact fan g hg
  have dcorrect (x : Fin 9 → Bool) : D.eval (List.ofFn x) = F x := by
    have read0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    change C.eval (((List.ofFn x) ++ [!(List.ofFn x).getD 0 false]) ++
      [GateOp.or.eval (pins.map fun j => ((List.ofFn x) ++ [!(List.ofFn x).getD 0 false]).getD j false)]) = F x
    rw [read0]
    exact correct x
  let charged (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  have n := binaryBound D dfan dcorrect
  change 14 ≤ (first :: second :: C.gates).countP charged at n
  have hn : charged first = false := rfl
  have ho : charged second = true := rfl
  simp [List.countP_cons,hn,ho] at n
  change C.gates.length ≤ 13 at budget
  have le := List.countP_le_length (p := charged) (l := C.gates)
  have allBinary : C.gates.countP charged = C.gates.length := by omega
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨basis,arity⟩ := fan g hg
    refine ⟨?_,arity⟩
    rcases basis with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have keep := List.countP_eq_length.mp allBinary g hg
      change g.op = .not at h
      simp [charged,h] at keep
  have shapes : pins ∈ ([[1,1],[1,5],[5,1]] : List (List ℕ)) := by
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
    · simp at len
    · simp at len
    · have ha := allowed a (by simp)
      have hb := allowed b (by simp)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · decide
      · decide
      · decide
      · exact False.elim ((by decide : (1 : ℕ) ∉ [5,5]) hasOne)
    · simp at len
  let bit (i : Fin 29) (v : BitVec 29) := v.getLsbD i.val
  have evalAnd : ∀ a, GateOp.and.eval a = a.all id := fun _ => rfl
  have evalOr : ∀ a, GateOp.or.eval a = a.any id := fun _ => rfl
  let gateWord (w : List (BitVec 29)) (g : Gate) : BitVec 29 :=
    let args := g.inputs.map fun j => w.getD j 0
    let a : BitVec 29 := args.getD 0 (BitVec.allOnes 29) &&& args.getD 1 (BitVec.allOnes 29)
    let b : BitVec 29 := args.getD 0 0 ||| args.getD 1 0
    GateOp.rec (motive := fun _ => BitVec 29) a b b (fun _ => b) b g.op

  let wordStep (w : List (BitVec 29)) (g : Gate) := w ++ [gateWord w g]

  let boolStep (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

  have zero_bit (i : Fin 29) : (0 : BitVec 29).getLsbD i.val = false :=
    BitVec.getLsbD_zero

  have read_bit (w : List (BitVec 29)) (i : Fin 29) (j : Nat) :
      (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
    simpa only [bit, zero_bit] using (List.getD_map w 0 (n := j) (bit i))

  have step_bits (w : List (BitVec 29)) (i : Fin 29) (g : Gate)
      (hg : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
      (wordStep w g).map (bit i) = boolStep (w.map (bit i)) g := by
    obtain ⟨op, args⟩ := g
    change op = .and ∨ op = .or at hg
    change args.length ≤ 2 at hlen
    have shapes : args = [] ∨ (∃ a, args = [a]) ∨ ∃ a b, args = [a, b] := by
      cases args with
      | nil => exact Or.inl rfl
      | cons a tail =>
        cases tail with
        | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
        | cons b tail =>
          cases tail with
          | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
          | cons _ _ => simp at hlen
    rcases hg with rfl | rfl <;>
      rcases shapes with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
      simp only [wordStep, boolStep, gateWord, evalAnd, evalOr, List.map_append, List.map_cons,
        List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, read_bit,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, bit,
        BitVec.getLsbD_and, BitVec.getLsbD_or, zero_bit, BitVec.getLsbD_allOnes,
        i.isLt, decide_true, Bool.and_true, Bool.or_false]

  have run_bits (gs : List Gate) (w : List (BitVec 29)) (i : Fin 29)
      (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      obtain ⟨hop, hlen⟩ := hm g List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons, ih _ (fun k hk => hm k (List.mem_cons_of_mem g hk)),
        step_bits w i g hop hlen]

  let Binary (pool : List (BitVec 29)) (v : BitVec 29) : Prop :=
    ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

  let Valid (base values : List (BitVec 29)) : Prop :=
    ∀ j (hj : j < values.length), values[j] ∉ base ++ values.take j ∧
      Binary (base ++ values.take j) values[j]

  have valid_append {base program : List (BitVec 29)} {v : BitVec 29} (h : Valid base program)
      (hfresh : v ∉ base ++ program) (hv : Binary (base ++ program) v) :
      Valid base (program ++ [v]) := by
    intro j hj
    by_cases hj' : j < program.length
    · simpa only [List.getElem_append_left hj',
        List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
    · have heq : j = program.length := by simp at hj; omega
      subst j
      simpa using And.intro hfresh hv

  have read_mem {α : Type} {xs pool : List α} (h : xs ⊆ pool) {d : α} (hd : d ∈ pool)
      (i : Nat) : xs.getD i d ∈ pool := by
    rw [List.getD_eq_getElem?_getD]
    cases hv : xs[i]? with
    | none => exact hd
    | some v => exact h (List.mem_of_getElem? hv)

  have gate_binary {w pool : List (BitVec 29)} (g : Gate) (hw : w ⊆ pool)
      (hz : 0 ∈ pool) (ht : BitVec.allOnes 29 ∈ pool) : Binary pool (gateWord w g) := by
    have hargs : (g.inputs.map fun j => w.getD j 0) ⊆ pool := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
      exact read_mem hw hz j
    dsimp only [gateWord]
    cases h : g.op
    · exact ⟨_, read_mem hargs ht 0, _, read_mem hargs ht 1, Or.inl rfl⟩
    all_goals exact ⟨_, read_mem hargs hz 0, _, read_mem hargs hz 1, Or.inr rfl⟩

  have record_step {base program w : List (BitVec 29)} (g : Gate) (hz : 0 ∈ base)
      (ht : BitVec.allOnes 29 ∈ base) (h : Valid base program) (hw : w ⊆ base ++ program) :
      ∃ next : List (BitVec 29), next.length ≤ program.length + 1 ∧ Valid base next ∧
        wordStep w g ⊆ base ++ next := by
    let v := gateWord w g
    by_cases hmem : v ∈ base ++ program
    · refine ⟨program, by omega, h, ?_⟩
      exact List.append_subset.mpr ⟨hw, by simpa [v] using hmem⟩
    · have hv := gate_binary g hw (List.mem_append_left _ hz) (List.mem_append_left _ ht)
      refine ⟨program ++ [v], by simp, valid_append h hmem hv, ?_⟩
      rw [← List.append_assoc]
      exact List.append_subset.mpr ⟨fun _ ha => List.mem_append_left _ (hw ha),
        fun _ ha => List.mem_append_right _ ha⟩

  have record_run (gs : List Gate) (base program w : List (BitVec 29)) (hz : 0 ∈ base)
      (ht : BitVec.allOnes 29 ∈ base) (h : Valid base program) (hw : w ⊆ base ++ program) :
      ∃ final : List (BitVec 29), final.length ≤ program.length + gs.length ∧ Valid base final ∧
        gs.foldl wordStep w ⊆ base ++ final := by
    induction gs generalizing program w with
    | nil => exact ⟨program, by simp, h, hw⟩
    | cons g gs ih =>
      obtain ⟨next, hlen, hnext, hwires⟩ := record_step g hz ht h hw
      obtain ⟨final, hsize, hfinal, hout⟩ := ih next (wordStep w g) hnext hwires
      exact ⟨final, by simp; omega, hfinal, hout⟩

  let seeds : List (BitVec 29) := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18813609]
  let given := fun (ls : List ℕ) =>
    ([503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407] : List (BitVec 29)) ++ [if 5 ∈ ls then 18813609 else 18022921]
  let rows := ([6, 12, 24, 66, 132, 160, 264, 288, 320, 3, 13, 17, 33, 133, 265, 321, 42, 50, 104, 116, 138, 200, 208, 276, 402, 69, 201, 261, 385] : List ℕ)
  let point := fun (i : Fin 29) (k : Fin 9) => (rows.getD i.val 0).testBit k.val
  have rowData : ∀ ls ∈ ([[1,1],[1,5],[5,1]] : List (List ℕ)), ∀ i : Fin 29,
      (given ls).map (bit i) = input ls (point i) ∧ bit i 65535 = F (point i) := by
    intro ls hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide +kernel
  have hinit : given pins ⊆ seeds ++ [] := by
    rcases (show pins = [1,1] ∨ pins = [1,5] ∨ pins = [5,1] by simpa using shapes) with rfl | rfl | rfl
    all_goals decide
  obtain ⟨program, hlen, hvalid, hw⟩ := record_run C.gates seeds [] (given pins)
    (by decide) (by decide) (by intro j hj; simp at hj) hinit
  let wires := C.gates.foldl wordStep (given pins)
  have houtput : wires.getD C.output 0 = 65535 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 29 := ⟨j,hj⟩
    obtain ⟨hin,hout⟩ := rowData pins shapes i
    change bit i (wires.getD C.output 0) = bit i 65535
    rw [← read_bit, hout, ← correct (point i)]
    change ((C.gates.foldl wordStep (given pins)).map (bit i)).getD C.output false =
      (C.gates.foldl boolStep (input pins (point i))).getD C.output false
    rw [run_bits C.gates (given pins) i hm, hin]
  apply finite program (by simp only [List.length_nil, Nat.zero_add] at hlen; omega) hvalid
  change (65535 : BitVec 29) ∈ seeds ++ program
  rw [← houtput]
  exact read_mem hw (List.mem_append_left _ (by decide)) C.output

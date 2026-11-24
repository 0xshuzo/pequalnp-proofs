import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3186_aux

-- The bitvector simulation adapts the checked gate-table argument in L_meta_719.
abbrev W := BitVec 24
def ops (x y : W) : List W := [x &&& y, x ||| y]
abbrev basicOps (a b : W) := ops a b

def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 24 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bit (k : Fin 24) (z : W) : Bool := z[k.val]

theorem read_bit (w : List W) (i : ℕ) (k : Fin 24) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 24, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : List W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 24 ∨ u ∈ available

theorem classify {available : List W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 24 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 24 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 24 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

def Fresh (av : List W) (z : W) : Prop :=
  z ∉ av ∧ z ≠ 0 ∧ z ≠ -1 ∧ ∃ a ∈ av, ∃ b ∈ av, z = a &&& b ∨ z = a ||| b

def Good (av fs : List W) : Prop :=
  ∀ j : Fin fs.length, Fresh (av ++ fs.take j.val) (fs.get j)

theorem prependGood {av fs : List W} {z : W} (hz : Fresh av z)
    (rest : Good (av ++ [z]) fs) : Good av (z :: fs) := by
  intro j
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => simpa using hz
  | succ j =>
    have hj' : j < fs.length := by simpa using hj
    simpa [List.append_assoc] using rest ⟨j, hj'⟩

theorem compile (gs : List Gate) (out : ℕ) (t : W) (nt : t ≠ 0) (ot : t ≠ -1)
    (hg : ∀ g ∈ gs, legal g) (w av : List W) (hw : represents av w)
    (he : ∀ k : Fin 24, (gs.foldl step (w.map (bit k))).getD out false = bit k t) :
    ∃ fs : List W, fs.length ≤ gs.length ∧ t ∈ av ++ fs ∧ Good av fs := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = t := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    rcases read_wire w out with zero | member
    · exact False.elim (nt (hval.symm.trans zero))
    · rw [hval] at member
      rcases hw _ member with zero | one | mem
      · exact False.elim (nt zero)
      · exact False.elim (ot one)
      · refine ⟨[], by simp, by simpa using mem, ?_⟩
        intro j
        exact Fin.elim0 j
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k t := by
      intro k
      simpa only [List.foldl_cons, hstep] using he k
    have tailLegal : ∀ q ∈ gs, legal q := fun q h => hg q (by simp [h])
    have extend {a : List W} (inc : av ⊆ a) (ok : z = 0 ∨ z = BitVec.allOnes 24 ∨ z ∈ a) :
        represents a (w ++ [z]) := by
      intro y hy
      rcases List.mem_append.mp hy with old | new
      · rcases hw y old with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (by simpa using inc h))
      · have eq := List.mem_singleton.mp new
        subst y
        simpa using ok
    by_cases trivial : z = 0 ∨ z = BitVec.allOnes 24 ∨ z ∈ av
    · obtain ⟨fs, bound, mem, good⟩ := ih tailLegal (w ++ [z]) av (extend (fun _ h => h) trivial) he'
      exact ⟨fs, by simp; omega, mem, good⟩
    · rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, _, hop⟩
      · exact False.elim (trivial (.inl h))
      · exact False.elim (trivial (.inr (.inl h)))
      · exact False.elim (trivial (.inr (.inr (by simpa using h))))
      · have fresh : Fresh av z := by
          refine ⟨fun h => trivial (.inr (.inr h)), fun h => trivial (.inl h),
            fun h => trivial (.inr (.inl h)), a, ha,
            b, hb, ?_⟩
          simpa [basicOps, ops] using hop
        obtain ⟨fs, bound, mem, good⟩ := ih tailLegal (w ++ [z]) (av ++ [z])
          (extend (fun _ h => List.mem_append_left _ h) (.inr (.inr (by simp)))) he'
        exact ⟨z :: fs, by simpa using bound, by simpa [List.append_assoc] using mem,
          prependGood fresh good⟩

theorem unchanged (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

end PEqualNP.Outside.L_meta_3186_aux

open PEqualNP.Outside.L_meta_3186_aux

theorem PEqualNP.Outside.L_meta_3186 : ∀ (x1 : Fin (9 : ℕ) → BitVec (24 : ℕ)) (x2 x3 : BitVec (24 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     x3 ≠ (0 : BitVec (24 : ℕ)) →       x3 ≠ (-1 : BitVec (24 : ℕ)) →         (∀ (x8 : Fin (24 : ℕ)),             have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => (x1 x9).getLsbD ↑x8;             (x4.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x2.getLsbD ↑x8 ∧ x4.eval (List.ofFn x9) = x3.getLsbD ↑x8) →           have x9 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x2];           ∃ (x10 : List (BitVec (24 : ℕ))),             x10.length ≤ x4.size - (1 : ℕ) ∧               x3 ∈ x9 ++ x10 ∧                 ∀ (x11 : Fin x10.length),                   have x12 : List (BitVec (24 : ℕ)) := x9 ++ List.take (↑x11) x10;                   x10.get x11 ∉ x12 ∧ x10.get x11 ≠ (0 : BitVec (24 : ℕ)) ∧ x10.get x11 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x13 ∈ x12, ∃ x14 ∈ x12, x10.get x11 = x13 &&& x14 ∨ x10.get x11 = x13 ||| x14 := by
  intro col h t C law zt ot obs
  let w := List.ofFn col
  let p := w ++ [h]
  have plen : w.length = 9 := by simp [w]
  have rows (k : Fin 24) : w.map (bit k) = List.ofFn (fun u => (col u).getLsbD k.val) := by
    rfl
  cases C with
  | mk gates out =>
    cases gates with
    | nil =>
      have evalRows (k : Fin 24) : (([] : List Gate).foldl step (w.map (bit k))).getD out false = bit k t := by
        simpa only [rows, List.foldl_nil, Circuit.eval, Circuit.wires, bit, BitVec.getLsbD_eq_getElem k.isLt] using (obs k).2
      obtain ⟨fs, size, mem, good⟩ := compile [] out t zt ot (by simp) w p
        (by intro y hy; exact Or.inr (Or.inr (by simp [p, hy]))) evalRows
      exact ⟨fs, size, mem, good⟩
    | cons g gs =>
      obtain ⟨v, _, sim⟩ := gate_table w w (fun _ h => h) g (law g (by simp))
      have vEq : v = h := by
        apply BitVec.eq_of_getElem_eq
        intro i hi
        let k : Fin 24 := ⟨i,hi⟩
        have seen := (obs k).1
        rw [← rows k] at seen
        change (gs.foldl step (step (w.map (bit k)) g)).getD 9 false = _ at seen
        rw [sim k, unchanged gs _ 9 (by simp [plen]), read_bit] at seen
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (show w.length ≤ 9 by omega), plen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at seen
        simpa [bit, k, BitVec.getLsbD_eq_getElem hi] using seen
      subst v
      have evalRows (k : Fin 24) : (gs.foldl step (p.map (bit k))).getD out false = bit k t := by
        have seen := (obs k).2
        rw [← rows k] at seen
        change (gs.foldl step (step (w.map (bit k)) g)).getD out false = _ at seen
        simpa only [sim k, p, bit, BitVec.getLsbD_eq_getElem k.isLt] using seen
      obtain ⟨fs, size, mem, good⟩ := compile gs out t zt ot
        (fun q hq => law q (by simp [hq])) p p (by intro y hy; exact .inr (.inr (by simpa using hy))) evalRows
      exact ⟨fs, by simpa [Circuit.size] using size, mem, good⟩

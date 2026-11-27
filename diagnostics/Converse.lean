import PEqualNP.Defs

namespace P7808Stock.S2642_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht, List.length_append, hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

/-! Erasing one gate -/

/-- Where wire `i` of the erased circuit sits in the old one (`k = n + m`). -/
def up (k i : ℕ) : ℕ := if i < k then i else i + 1

/-- The renamed copy of a gate after the erased one. -/
def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
  unfold up eraseRedirect
  split_ifs <;> omega

theorem sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
    (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
    V.length = U.length + 1 →
    ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
      ∀ g ∈ rest, n + m ∉ g.inputs) →
    ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
      (rest.foldl step V).getD (up (n + m) i) false
  | [], U, V, hrel, _, _, _ => by simpa using hrel
  | g :: rest, U, V, hrel, hk, hlen, hS => by
    have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hS with ⟨hS, -⟩ | hS
        · simpa [eraseRedirect] using hS
        · exact absurd hr (hS g (List.mem_cons_self ..))
      · rw [hrel, up_redir n m p r hrk]
    set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
    have hU : step U (ren n m p g) = U ++ [a] := by
      simp only [step, ren, List.map_map]
      congr 3
      exact List.map_congr_left fun r hr => hread r hr
    have hV : step V g = V ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, hU, hV]
    apply sim n m p rest
    · intro i
      rcases lt_trichotomy i U.length with hi | rfl | hi
      · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
      · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
        rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
        simp
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
    · simp; omega
    · simp; omega
    · rcases hS with ⟨hS, hp⟩ | hS
      · left
        refine ⟨?_, ?_⟩
        · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
          rcases hp with hp | hp
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
          · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
            rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
            exact hS
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; simp at hp ⊢; omega
      · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
    (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
    (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval y = C.eval y := by
  obtain ⟨hg, ho⟩ := erase_gates n C m p hm
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set A := (C.gates.take m).foldl step y with hA
  have hAl : A.length = n + m := by
    rw [hA, fold_length, hy, List.length_take]; omega
  set rest := C.gates.drop (m + 1) with hrest
  have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
  have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
    rw [wires_eq, hg, List.foldl_append]
  have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
  have hWl : (C.wires y).length = n + C.gates.length := by
    rw [wires_eq, fold_length, hy]
  have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
    intro i hi
    rw [hW, fold_getD_lt _ _ _ (by omega)]
  have hsim := sim n m p rest A (step A C.gates[m]) (by
      intro i
      by_cases hi : i < n + m
      · simp only [up, if_pos hi, step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [up, if_neg hi]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
    (by omega) hVl (by
      rcases hc with hc | ⟨-, hc⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hstable _ (by omega)]
          rcases hp with hp | hp
          · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
          · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; omega
      · exact Or.inr hc)
  unfold Circuit.eval
  rw [ho, hW', hsim, ← hW]
  by_cases hout : C.output = n + m
  · rcases hc with hc | ⟨hc, -⟩
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout]
      rcases hp with hp | hp
      · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
        rw [hu]; exact hc.symm
      · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
        rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · exact absurd hout hc
  · rw [up_redir n m p _ hout]

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  unfold Circuit.size
  rw [(erase_gates n C m p hm).1]
  simp
  omega

theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (eraseGate n C m p) := by
  intro g hg
  rw [(erase_gates n C m p hm).1, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [ren] using h2⟩

/-! Fixing two inputs to false without new gates -/

/-- Reads of input wires `a` and `b` go to wire `B`, which does not exist. -/
def sub (a b B i : ℕ) : ℕ := if i = a ∨ i = b then B else i

def fixC (a b : ℕ) (C : Circuit) (B : ℕ) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (sub a b B)⟩), sub a b B C.output⟩

/-- The invariant between the fixed circuit's wires `U` and the old wires `V` on the restricted
input, with `k` gates still to come. -/
def Inv (a b B : ℕ) (U V : List Bool) (k : ℕ) : Prop :=
  U.length = V.length ∧ (∀ i, i ≠ a → i ≠ b → U.getD i false = V.getD i false) ∧
    V.getD a false = false ∧ V.getD b false = false ∧ a < V.length ∧ b < V.length ∧
    V.length + k ≤ B ∧ B ≠ a ∧ B ≠ b

theorem inv_read (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V k) (r : ℕ) :
    U.getD (sub a b B r) false = V.getD r false := by
  obtain ⟨-, hrel, hVa, hVb, -, -, hB, hBa, hBb⟩ := h
  unfold sub
  split_ifs with hr
  · rw [hrel B hBa hBb, getD_ge _ _ (by omega)]
    rcases hr with rfl | rfl
    · exact hVa.symm
    · exact hVb.symm
  · push_neg at hr
    exact hrel r hr.1 hr.2

theorem inv_snoc (a b B : ℕ) (U V : List Bool) (k : ℕ) (h : Inv a b B U V (k + 1)) (v : Bool) :
    Inv a b B (U ++ [v]) (V ++ [v]) k := by
  obtain ⟨hl, hrel, hVa, hVb, ha, hb, hB, hBa, hBb⟩ := h
  refine ⟨by simp [hl], fun i hia hib => ?_, ?_, ?_, by simp; omega, by simp; omega,
    by simp; omega, hBa, hBb⟩
  · rcases lt_trichotomy i V.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi, hrel i hia hib]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl, hl]
    · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
  · rw [List.getD_append _ _ _ _ ha]; exact hVa
  · rw [List.getD_append _ _ _ _ hb]; exact hVb

theorem fix_fold (a b B : ℕ) : ∀ (gs : List Gate) (U V : List Bool), Inv a b B U V gs.length →
    Inv a b B ((gs.map fun g => (⟨g.op, g.inputs.map (sub a b B)⟩ : Gate)).foldl step U)
      (gs.foldl step V) 0
  | [], U, V, h => by simpa using h
  | g :: gs, U, V, h => by
    set v := g.op.eval (g.inputs.map fun i => V.getD i false)
    have hU : step U ⟨g.op, g.inputs.map (sub a b B)⟩ = U ++ [v] := by
      simp only [step, List.map_map]
      congr 3
      exact List.map_congr_left fun r _ => inv_read a b B U V _ h r
    simp only [List.map_cons, List.foldl_cons, hU]
    exact fix_fold a b B gs _ _ (inv_snoc a b B U V gs.length h v)

theorem fix_eval (n : ℕ) (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
    (fixC a b C (n + C.gates.length)).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
  set y := Function.update (Function.update x a false) b false
  have hinit : Inv a b (n + C.gates.length) (List.ofFn x) (List.ofFn y) C.gates.length := by
    refine ⟨by simp, fun i hia hib => ?_, ?_, ?_, by simp, by simp, by simp, by omega, by omega⟩
    · by_cases hi : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn, List.getElem_ofFn]
        have h1 : (⟨i, hi⟩ : Fin n) ≠ b := fun h => hib (by rw [← h])
        have h2 : (⟨i, hi⟩ : Fin n) ≠ a := fun h => hia (by rw [← h])
        simp only [y, Function.update_of_ne h1, Function.update_of_ne h2]
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      by_cases hab : a = b
      · simp [y, hab]
      · simp [y, Function.update_of_ne hab]
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp [y]
  have := fix_fold a b (n + C.gates.length) C.gates _ _ hinit
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact inv_read a b _ _ _ _ this C.output

theorem fix_size (a b B : ℕ) (C : Circuit) : (fixC a b C B).size = C.size := by
  simp [fixC, Circuit.size]

theorem fix_fanin (a b B : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (fixC a b C B) := by
  intro g hg
  simp only [fixC, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h1, h2⟩ := hC g' hg'
  exact ⟨h1, by simpa using h2⟩

/-! The chain of erasures -/

theorem main : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  intro n k a b Cs h0 hstep
  have chain : ∀ j, j ≤ k → PEqualNP.MetaComplexity.FanInTwo (Cs j) ∧ (Cs j).size + j = (Cs 0).size ∧
      ∀ x : Fin n → Bool,
        (Cs j).eval (List.ofFn (Function.update (Function.update x a false) b false)) =
          (Cs 0).eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, by simp, fun _ => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨hf, hs, he⟩ := ih (by omega)
      obtain ⟨m, p, hm, hp, heq, hc⟩ := hstep j (by omega)
      have hml : m < (Cs j).gates.length := hm
      refine ⟨heq ▸ erase_fanin n _ m p hml hf, ?_, fun x => ?_⟩
      · have := erase_size n (Cs j) m p hml
        rw [heq]; omega
      · rw [heq, ← he x]
        apply erase_eval n (Cs j) m p _ (by simp) hml
        · rcases hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr hp
        · rcases hc with hc | hc
          · exact Or.inl (hc x)
          · exact Or.inr hc
  obtain ⟨hf, hs, he⟩ := chain k le_rfl
  refine ⟨fixC a b (Cs k) (n + (Cs k).gates.length), fix_fanin _ _ _ _ hf, ?_, fun x => ?_⟩
  · rw [fix_size]; exact hs
  · rw [fix_eval, he]

end P7808Stock.S2642_aux

theorem P7808Stock.S2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  exact P7808Stock.S2642_aux.main

namespace P7808Stock.S7810

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem gates_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
  simp only [eraseGate, if_pos hm]

theorem out_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  simp only [eraseGate, if_pos hm]

theorem len_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [gates_erase n C m p hm]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem pref (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < n + m) :
    ((eraseGate n C m p).wires x).getD i false = (C.wires x).getD i false := by
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  have key : C.gates.foldl step x = (C.gates.drop m).foldl step
      ((C.gates.take m).foldl step x) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [wires_eq, wires_eq, gates_erase n C m p hm, List.foldl_append,
    fold_stab _ (List.foldl step x (List.take m C.gates)) _ (by omega), key,
    fold_stab _ (List.foldl step x (List.take m C.gates)) _ (by omega)]

def Inv (n : ℕ) {ι : Type} (xs : ι → List Bool) (C : Circuit) (S : Finset ℕ) : Prop :=
  ∀ j ∈ S, j < C.gates.length ∧
    ((∃ p, ((p < n + j ∧ (p < n ∨ p - n ∉ S)) ∨ n + C.gates.length ≤ p) ∧
        ∀ a, (C.wires (xs a)).getD (n + j) false = (C.wires (xs a)).getD p false) ∨
     (C.output ≠ n + j ∧ ∀ k, k ∉ S → ∀ g, C.gates[k]? = some g → n + j ∉ g.inputs))

def Stp (n : ℕ) {ι : Type} (xs : ι → List Bool) (C D : Circuit) : Prop :=
  ∃ m p, m < C.size ∧ (p < n + m ∨ n + C.size ≤ p) ∧ D = eraseGate n C m p ∧
    ((∀ a, (C.wires (xs a)).getD (n + m) false = (C.wires (xs a)).getD p false) ∨
     (C.output ≠ n + m ∧ ∀ g ∈ List.drop (m + 1) C.gates, n + m ∉ g.inputs))

theorem pres (n : ℕ) {ι : Type} (xs : ι → List Bool) (hxs : ∀ a, (xs a).length = n)
    (C : Circuit) (S : Finset ℕ) (m p : ℕ) (hm : m < C.gates.length)
    (hmax : ∀ j ∈ S, j ≤ m) (hp : ∀ j ∈ S, j ≠ m → p ≠ n + j) (H : Inv n xs C S) :
    Inv n xs (eraseGate n C m p) (S.erase m) := by
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  have hjne := Finset.ne_of_mem_erase hj
  have hjm : j < m := by have := hmax j hjS; omega
  have hlen := len_erase n C m p hm
  obtain ⟨_, H2⟩ := H j hjS
  refine ⟨by omega, ?_⟩
  rcases H2 with ⟨q, hq, he⟩ | ⟨ho, hr⟩
  · left
    refine ⟨q, ?_, ?_⟩
    · rcases hq with ⟨h1, h2⟩ | h2
      · refine Or.inl ⟨h1, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (fun h => h2 (Finset.mem_of_mem_erase h))
      · exact Or.inr (by omega)
    · intro a
      rw [pref n C m p hm _ (hxs a) _ (by omega), he a]
      rcases hq with ⟨h1, _⟩ | h2
      · rw [pref n C m p hm _ (hxs a) _ (by omega)]
      · rw [getD_big _ _ (by rw [wires_eq, fold_len, hxs a]; omega),
          getD_big _ _ (by rw [wires_eq, fold_len, hxs a]; omega)]
  · right
    have hred : ∀ i, eraseRedirect n m p i = n + j → i = n + j := by
      intro i hi
      unfold eraseRedirect at hi
      split_ifs at hi
      · exact absurd hi (hp j hjS hjne)
      · omega
      · exact hi
    refine ⟨?_, ?_⟩
    · rw [out_erase n C m p hm]
      intro h; exact ho (hred _ h)
    · intro k hk g hg
      rw [gates_erase n C m p hm, List.getElem?_append] at hg
      by_cases hkm : k < m
      · rw [if_pos (by rw [List.length_take]; omega), List.getElem?_take, if_pos hkm] at hg
        refine hr k (fun h => hk (Finset.mem_erase.2 ⟨by omega, h⟩)) g hg
      · rw [if_neg (by rw [List.length_take]; omega), List.getElem?_map, List.getElem?_drop] at hg
        rw [List.length_take, Nat.min_eq_left (by omega)] at hg
        rcases hg' : C.gates[m + 1 + (k - m)]? with _ | g'
        · rw [hg'] at hg; simp at hg
        · rw [hg'] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          simp only [List.mem_map, not_exists, not_and]
          intro i hi hie
          have := hred i hie
          subst this
          exact hr (m + 1 + (k - m)) (fun h => by have := hmax _ h; omega) g' hg' hi

theorem multi (n : ℕ) {ι : Type} (xs : ι → List Bool) (hxs : ∀ a, (xs a).length = n) :
    ∀ (k : ℕ) (C : Circuit) (S : Finset ℕ), S.card = k → Inv n xs C S →
    ∃ f : ℕ → Circuit, f 0 = C ∧ ∀ t < k, Stp n xs (f t) (f (t + 1)) := by
  intro k
  induction k with
  | zero => intro C S _ _; exact ⟨fun _ => C, rfl, fun t ht => absurd ht (by omega)⟩
  | succ k ih =>
    intro C S hS H
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    have hmS := S.max'_mem hne
    have hmax : ∀ j ∈ S, j ≤ S.max' hne := fun j hj => S.le_max' j hj
    generalize S.max' hne = m at hmS hmax
    obtain ⟨hm, H2⟩ := H m hmS
    have hcard : (S.erase m).card = k := by
      rw [Finset.card_erase_of_mem hmS]; omega
    have fin : ∀ p, Inv n xs (eraseGate n C m p) (S.erase m) →
        Stp n xs C (eraseGate n C m p) →
        ∃ f : ℕ → Circuit, f 0 = C ∧ ∀ t < k + 1, Stp n xs (f t) (f (t + 1)) := by
      intro p hI hSt
      obtain ⟨f, hf0, hf⟩ := ih _ _ hcard hI
      refine ⟨fun t => if t = 0 then C else f (t - 1), rfl, ?_⟩
      intro t ht
      rcases t with _ | t
      · simp only [if_true, Nat.zero_add, if_neg (Nat.one_ne_zero), Nat.sub_self, hf0]
        exact hSt
      · simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
        exact hf t (by omega)
    rcases H2 with ⟨p, hp, he⟩ | ⟨ho, hr⟩
    · apply fin p
      · apply pres n xs hxs C S m p hm hmax _ H
        intro j hjS hjne
        have := hmax j hjS
        rcases hp with ⟨h1, h2 | h2⟩ | h2
        · omega
        · intro h; apply h2; rw [h]; simpa using hjS
        · omega
      · refine ⟨m, p, hm, ?_, rfl, Or.inl he⟩
        rcases hp with ⟨h1, _⟩ | h2
        · exact Or.inl h1
        · exact Or.inr h2
    · apply fin (n + C.gates.length)
      · apply pres n xs hxs C S m _ hm hmax _ H
        intro j hjS hjne
        have := hmax j hjS
        omega
      · refine ⟨m, _, hm, Or.inr (le_refl _), rfl, Or.inr ⟨ho, ?_⟩⟩
        intro g hg
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
        rw [List.getElem?_drop] at hi
        exact hr _ (fun h => by have := hmax _ h; omega) g hi

end P7808Stock.S7810

open P7808Stock.S7810 PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves in
theorem P7808Stock.S7810 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),   (∀ x6 ∈ x5, x6 < x4.size) →     (∀ x7 ∈ x5,         (∃ (x9 : ℕ),             (x9 < x1 + x7 ∧ (x9 < x1 ∨ x9 - x1 ∉ x5) ∨ x1 + x4.size ≤ x9) ∧               ∀ (x10 : Fin x1 → Bool),                 have x11 : List Bool := x4.wires (List.ofFn (Function.update (Function.update x10 x2 Bool.false) x3 Bool.false));                 x11.getD (x1 + x7) Bool.false = x11.getD x9 Bool.false) ∨           x4.output ≠ x1 + x7 ∧ PEqualNP.MetaComplexity.NestedCover.readsIn x4 (Finset.range x4.size \ x5) (x1 + x7) = (0 : ℕ)) →       ∃ (x8 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),         x8 (0 : ℕ) = x4 ∧           ∀ x9 < x5.card,             ∃ (x11 : ℕ) (x12 : ℕ),               x11 < (x8 x9).size ∧                 (x12 < x1 + x11 ∨ x1 + (x8 x9).size ≤ x12) ∧                   x8 (x9 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x8 x9) x11 x12 ∧                     ((∀ (x13 : Fin x1 → Bool),                         have x14 : List Bool := (x8 x9).wires (List.ofFn (Function.update (Function.update x13 x2 Bool.false) x3 Bool.false));                         x14.getD (x1 + x11) Bool.false = x14.getD x12 Bool.false) ∨                       (x8 x9).output ≠ x1 + x11 ∧ ∀ x13 ∈ List.drop (x11 + (1 : ℕ)) (x8 x9).gates, x1 + x11 ∉ x13.inputs) := by
  intro n i1 i2 C S hlt H
  have hI : Inv n (fun f : Fin n → Bool =>
      List.ofFn (Function.update (Function.update f i1 Bool.false) i2 Bool.false)) C S := by
    intro j hj
    refine ⟨hlt j hj, ?_⟩
    rcases H j hj with ⟨p, hp, he⟩ | ⟨ho, hr⟩
    · exact Or.inl ⟨p, hp, he⟩
    · refine Or.inr ⟨ho, ?_⟩
      intro k hk g hg
      unfold PEqualNP.MetaComplexity.NestedCover.readsIn at hr
      rw [Finset.sum_eq_zero_iff] at hr
      have hkl : k < C.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hg
        exact absurd hg (by simp)
      have := hr k (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hkl, hk⟩)
      rw [List.count_eq_zero] at this
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, hg]; rfl
      rw [e] at this
      exact this
  obtain ⟨f, hf0, hf⟩ := multi n _ (by intro a; simp) S.card C S rfl hI
  refine ⟨f, hf0, ?_⟩
  intro t ht
  obtain ⟨m, p, h1, h2, h3, h4⟩ := hf t ht
  exact ⟨m, p, h1, h2, h3, h4⟩

namespace Pair7808.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
def zero₂ {n:Nat} (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

def marked {n:Nat} (u v:Fin n) (F:Circuit) : Prop :=
  ∃H:Finset Nat, 7≤H.card ∧ ∀ k∈H, k<F.size ∧
    ((∃w:Nat, (w<n+k ∧ (w<n ∨ w-n∉H) ∨ n+F.size≤w) ∧
       ∀ x:Fin n→Bool, let W := F.wires (List.ofFn (zero₂ u v x))
                         W.getD (n+k) false=W.getD w false) ∨
     F.output≠n+k ∧ readsIn F (Finset.range F.size \ H) (n+k)=0)


def ordinary {n:Nat} (C:Circuit) (u v:Fin n) := ∃D:Circuit, FanInTwo D ∧ D.size+7≤C.size ∧
    circuitFun n D=(fun x => circuitFun n C (zero₂ u v x))
theorem marked_to_ordinary {n:Nat} {u v:Fin n} (C F:Circuit) (fan:FanInTwo F) (small:F.size≤C.size)
    (same:circuitFun n F=circuitFun n C) (h:marked u v F) : ordinary C u v := by
  obtain ⟨H,hseven,hH⟩ := h
  obtain ⟨seq,start,del⟩ := P7808Stock.S7810 n u v F H
    (fun k hk => (hH k hk).1) (fun k hk => (hH k hk).2)
  have fan0 : FanInTwo (seq 0) := start.symm ▸ fan
  obtain ⟨D,fanD,budget,correct⟩ := P7808Stock.S2642 n 7 u v seq fan0 (fun i hi => del i (by omega))
  rw [start] at budget correct
  refine ⟨D,fanD,by omega,?_⟩
  funext x
  exact (correct x).trans (congrFun same (zero₂ u v x))

end Pair7808.Builder

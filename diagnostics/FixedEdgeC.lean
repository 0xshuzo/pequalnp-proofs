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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pair7808
namespace Builder
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

theorem appendTerm {n s k : ℕ} {f t : (Fin n → Bool) → Bool} (c : HasCircuitSize n f s) (term : Bld n t k) :
    HasCircuitSize n (fun x => f x || t x) (s+k+1) := by
  obtain ⟨C,fan,cheap,correct⟩ := c
  let m := n+C.gates.length
  obtain ⟨gs,wout,ok,budget,range,computes⟩ := term m (by dsimp [m]; omega)
  let old := if C.output<m then C.output else m+gs.length+1
  let D : Circuit := ⟨C.gates++gs++[⟨.or,[old,wout]⟩],m+gs.length⟩
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    change g ∈ C.gates++gs++[_] at hg
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact fan _ h
      · exact ok _ h
    · obtain rfl := List.mem_singleton.mp h
      simp
  · change (C.gates++gs++[_]).length ≤ s+k+1
    change C.gates.length ≤ s at cheap
    simp
    omega
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    let finalW := wiresFrom gs w
    have lengthW : w.length=m := by simp [w,m,length_wiresFrom]
    have lengthFinal : finalW.length=m+gs.length := by simp [finalW,length_wiresFrom,lengthW]
    have first : finalW.getD old false = f x := by
      have eq : w.getD C.output false = f x := correct x
      rw [← eq]
      by_cases existsWire : C.output < m
      · change (wiresFrom gs w).getD old false = _
        rw [show old=C.output by simp [old,existsWire],getD_wiresFrom _ _ _ (by omega)]
      · rw [show old=m+gs.length+1 by simp [old,existsWire]]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have same : (fun i : Fin n => w.getD i.val false)=x := by
      funext i
      change (wiresFrom C.gates (List.ofFn x)).getD i.val false = _
      rw [getD_wiresFrom _ _ _ (by simp),getD_ofFn]
    have second : finalW.getD wout false = t x := (computes w lengthW).trans (congrArg t same)
    change (wiresFrom (C.gates++gs++[_]) (List.ofFn x)).getD (m+gs.length) false = _
    rw [wiresFrom_append,wiresFrom_append]
    change (finalW++[GateOp.or.eval [finalW.getD old false,finalW.getD wout false]]).getD (m+gs.length) false = _
    rw [← lengthFinal,getD_snoc_eq,first,second]
    simp [GateOp.eval]


def addr (B i : Nat) := if i<B then i else B+7
def sealGate (B : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (addr B)⟩
def sealed (n:Nat) (D:Circuit) : Circuit :=
  let B := n+D.size
  ⟨D.gates.map (sealGate B), addr B D.output⟩
lemma addr_get (B:Nat) (w:List Bool) (lim:w.length≤B) (i:Nat) :
    w.getD (addr B i) false = w.getD i false := by
  by_cases hi:i<B
  · simp [addr,hi]
  · rw [addr,if_neg hi,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
lemma seal_run (B:Nat) (gs:List Gate) (w:List Bool) (lim:w.length+gs.length≤B) :
    wiresFrom (gs.map (sealGate B)) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map (fun i => w.getD i false))
    have eq : (sealGate B g).op.eval ((sealGate B g).inputs.map (fun i => w.getD i false)) = val := by
      change g.op.eval ((g.inputs.map (addr B)).map _) = _
      rw [List.map_map]
      have e : (fun i => (fun j => w.getD j false) (addr B i)) = (fun i => w.getD i false) := by
        funext i; exact addr_get B w (by omega) i
      change g.op.eval (g.inputs.map (fun i => w.getD (addr B i) false)) = val
      rw [e]
    change wiresFrom (gs.map (sealGate B)) (w++[_]) = wiresFrom gs (w++[_])
    rw [eq]
    apply ih
    simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *
    omega
lemma seal_size (n:Nat) (D:Circuit) : (sealed n D).size = D.size := by simp [sealed,Circuit.size]
lemma seal_fan (n:Nat) (D:Circuit) (fan:FanInTwo D) : FanInTwo (sealed n D) := by
  intro g h
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
  simpa [sealGate] using fan z hz
lemma seal_eval (n:Nat) (D:Circuit) : circuitFun n (sealed n D) = circuitFun n D := by
  funext x
  change (wiresFrom (D.gates.map (sealGate (n+D.size))) (List.ofFn x)).getD (addr (n+D.size) D.output) false = _
  rw [seal_run _ _ _ (by simp [Circuit.size]),addr_get _ _ (by simp [length_wiresFrom,Circuit.size])]
  rfl
lemma seal_no (n:Nat) (D:Circuit) (g:Gate) (hg:g∈(sealed n D).gates) (w:Nat)
    (lo:n+D.size≤w) (hi:w<n+D.size+7) : w∉g.inputs := by
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hg
  intro h
  obtain ⟨i,_,e⟩ := List.mem_map.mp h
  change addr (n+D.size) i=w at e
  unfold addr at e
  split at e <;> omega

open PEqualNP.MetaComplexity.NestedCover
def zero₂ {n:Nat} (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

def marked {n:Nat} (u v:Fin n) (F:Circuit) : Prop :=
  ∃H:Finset Nat, 7≤H.card ∧ ∀ k∈H, k<F.size ∧
    ((∃w:Nat, (w<n+k ∧ (w<n ∨ w-n∉H) ∨ n+F.size≤w) ∧
       ∀ x:Fin n→Bool, let W := F.wires (List.ofFn (zero₂ u v x)); W.getD (n+k) false=W.getD w false) ∨
     F.output≠n+k ∧ readsIn F (Finset.range F.size \ H) (n+k)=0)

lemma read_safe (gs : List Gate) (w : List Bool) (i:Nat)
    (hi : i < w.length ∨ w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false=w.getD i false := by
  rcases hi with h|h
  · exact getD_wiresFrom _ _ _ h
  · rw [List.getD_eq_default _ _ (by rw [length_wiresFrom];omega),List.getD_eq_default _ _ (by omega)]

theorem appendMarked {n:Nat} (u v:Fin n) (t:(Fin n→Bool)→Bool) (D:Circuit) (fan:FanInTwo D)
    (term:Bld n t 6) (off:∀x,t (zero₂ u v x)=false) :
    ∃F:Circuit, FanInTwo F ∧ F.size=D.size+7 ∧
      circuitFun n F=(fun x=>circuitFun n D x || t x) ∧ marked u v F := by
  let m := n+D.size
  let E := sealed n D
  have Le : E.gates.length=D.size := seal_size n D
  have old : E.output<m ∨ E.output=m+7 := by
    change addr m D.output < m ∨ addr m D.output=m+7
    unfold addr; split <;> omega
  obtain ⟨gs,o,ok,len,range,run⟩ := term m (by dsimp [m];omega)
  let pad : List Gate := List.replicate (6-gs.length) ⟨.or,[]⟩
  let Q := gs++pad
  have qlen : Q.length=6 := by simp [Q,pad];omega
  let last : Gate := ⟨.or,[E.output,o]⟩
  let F : Circuit := ⟨E.gates++Q++[last],m+6⟩
  have sz : F.size=D.size+7 := by simp [F,Circuit.size,Le,qlen]
  have okF : FanInTwo F := by
    intro g hg
    change g∈E.gates++Q++[last] at hg
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact seal_fan n D fan g h
      · rcases List.mem_append.mp h with h|h
        · exact ok g h
        · obtain rfl := List.eq_of_mem_replicate h
          simp
    · obtain rfl := List.mem_singleton.mp h
      simp [last]
  have data (x:Fin n→Bool) :
      F.eval (List.ofFn x)=(circuitFun n D x || t x) ∧
      (F.wires (List.ofFn x)).getD E.output false=circuitFun n D x := by
    let w := wiresFrom E.gates (List.ofFn x)
    let z := wiresFrom Q w
    have lw:w.length=m := by simp [w,length_wiresFrom,Le,m]
    have lz:z.length=m+6 := by simp [z,length_wiresFrom,lw,qlen]
    have ed : w.getD E.output false = circuitFun n D x := congrFun (seal_eval n D) x
    have zo : z.getD E.output false=circuitFun n D x := by
      rw [←ed]
      apply read_safe
      rw [lw,qlen]
      omega
    have xeq : (fun i:Fin n=>w.getD i.val false) = x := by
      funext i
      exact (getD_wiresFrom E.gates (List.ofFn x) i.val (by simp)).trans (by simp)
    have loc : z.getD o false=t x := by
      change (wiresFrom (gs++pad) w).getD o false=_
      rw [wiresFrom_append,getD_wiresFrom _ _ _ (by rw [length_wiresFrom,lw];omega),run w lw,xeq]
    have final : F.wires (List.ofFn x)= z ++ [z.getD E.output false || z.getD o false] := by
      change wiresFrom (E.gates++Q++[last]) (List.ofFn x)=_
      rw [wiresFrom_append,wiresFrom_append]
      simp [last,wiresFrom,GateOp.eval,z,w]
    constructor
    · change (F.wires (List.ofFn x)).getD (m+6) false=_
      rw [final,←lz,getD_snoc_eq,zo,loc]
    · rw [final,←zo]
      rcases old with h|h
      · exact List.getD_append _ _ _ _ (by omega)
      · rw [List.getD_eq_default _ _ (by simp [lz];omega),List.getD_eq_default _ _ (by omega)]
  refine ⟨F,okF,sz,funext (fun x=>(data x).1),?_⟩
  let H := Finset.Ico D.size (D.size+7)
  have hcard : H.card=7 := by simp [H]
  have remain : Finset.range F.size \ H = Finset.range D.size := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_range,H,Finset.mem_Ico,sz]
    omega
  refine ⟨H,hcard.ge,?_⟩
  intro k hk
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hk
  refine ⟨by omega,?_⟩
  by_cases ke : k=D.size+6
  · left
    refine ⟨E.output,?_,?_⟩
    · rcases old with h|h
      · left
        refine ⟨by dsimp [m] at h;omega,?_⟩
        by_cases low : E.output<n
        · exact Or.inl low
        · right
          intro mem
          have := (Finset.mem_Ico.mp mem).1
          dsimp [m] at h
          omega
      · right
        dsimp [m] at h
        omega
    · intro x
      have val := data (zero₂ u v x)
      have eq : n+k=F.output := by change n+k=m+6;dsimp [m];omega
      change (F.wires _).getD (n+k) false = (F.wires _).getD E.output false
      rw [eq,val.2]
      change F.eval _=_
      rw [val.1,off,Bool.or_false]
  · right
    refine ⟨by change m+6≠n+k;dsimp [m];omega,?_⟩
    rw [remain]
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    have jlt : j<E.gates.length := by rw [Le];exact Finset.mem_range.mp hj
    have hget : gateAt F j=E.gates[j] := by
      unfold gateAt
      change (E.gates++Q++[last]).getD j _=_
      rw [List.getD_append _ _ _ _ (by simp;omega),List.getD_append _ _ _ _ jlt]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem jlt]
    rw [hget,List.count_eq_zero]
    apply seal_no n D E.gates[j] (List.getElem_mem _)
    all_goals omega

open PEqualNP.MetaComplexity.NestedCover
variable {n : Nat}
def zeroPair (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

lemma true_zero (x:Fin n→Bool) (u v i:Fin n) :
    zeroPair u v x i=true ↔ i≠u ∧ i≠v ∧ x i=true := by
  by_cases h:i=v
  · subst i; simp [zeroPair]
  · by_cases q:i=u
    · subst i; simp [zeroPair,h]
    · simp [zeroPair,h,q]

def hit (S:Finset (Fin n)) (x:Fin n→Bool) := decide (∃i∈S,x i=true)
def term (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :=
  (x u && hit (G.neighborFinset u) x) || (x v && hit ((G.neighborFinset v).erase u) x)

lemma termCost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (edge:G.Adj u v)
    (uc:(G.neighborFinset u).card=3) (vc:(G.neighborFinset v).card=3) :
    Bld n (term G u v) 6 := by
  have mem : u∈G.neighborFinset v := (G.mem_neighborFinset _ _).mpr edge.symm
  have er : ((G.neighborFinset v).erase u).card=2 := by rw [Finset.card_erase_of_mem mem,vc]
  have a := bld_anyFinset (G.neighborFinset u) (Finset.card_pos.mp (by omega))
  have b := bld_anyFinset ((G.neighborFinset v).erase u) (Finset.card_pos.mp (by omega))
  have t := bld_or (bld_and (bld_var u) a) (bld_and (bld_var v) b)
  rwa [uc,er] at t

lemma termOff (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :
    term G u v (zeroPair u v x)=false := by
  have a := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v u).mp h).1 rfl)
  have b := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v v).mp h).2.1 rfl)
  simp [term,a,b]

lemma splitGraph (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (u v:Fin n) (ha:u∉A) (hb:v∉A) (x:Fin n→Bool) :
    (graphFun G A (zeroPair u v x) || term G u v x) = graphFun G A x := by
  have spec (y:Fin n→Bool) : graphFun G A y=true ↔ (∃a∈A,y a=true) ∨ ∃a b,G.Adj a b ∧ y a=true ∧ y b=true := by
    simp [graphFun]
  have le (i:Fin n) (h:zeroPair u v x i=true) := ((true_zero x u v i).mp h).2.2
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,spec,term,hit,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · rcases h with ⟨a,aa,xa⟩ | ⟨a,b,ab,xa,xb⟩
      · exact Or.inl ⟨a,aa,le a xa⟩
      · exact Or.inr ⟨a,b,ab,le a xa,le b xb⟩
    · rcases h with ⟨xu,j,hj,xj⟩|⟨xv,j,hj,xj⟩
      · exact Or.inr ⟨u,j,(G.mem_neighborFinset _ _).mp hj,xu,xj⟩
      · exact Or.inr ⟨v,j,(G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hj).2,xv,xj⟩
  · rintro (⟨a,aa,xa⟩|⟨a,b,ab,xa,xb⟩)
    · exact Or.inl (Or.inl ⟨a,aa,(true_zero _ _ _ _).mpr ⟨fun e=>ha (e ▸ aa),fun e=>hb (e ▸ aa),xa⟩⟩)
    · by_cases au:a=u
      · subst a
        exact Or.inr (Or.inl ⟨xa,b,(G.mem_neighborFinset _ _).mpr ab,xb⟩)
      by_cases bu:b=u
      · subst b
        exact Or.inr (Or.inl ⟨xb,a,(G.mem_neighborFinset _ _).mpr ab.symm,xa⟩)
      by_cases av:a=v
      · subst a
        exact Or.inr (Or.inr ⟨xa,b,Finset.mem_erase.mpr ⟨bu,(G.mem_neighborFinset _ _).mpr ab⟩,xb⟩)
      by_cases bv:b=v
      · subst b
        exact Or.inr (Or.inr ⟨xb,a,Finset.mem_erase.mpr ⟨au,(G.mem_neighborFinset _ _).mpr ab.symm⟩,xa⟩)
      exact Or.inl (Or.inr ⟨a,b,ab,(true_zero _ _ _ _).mpr ⟨au,av,xa⟩,
        (true_zero _ _ _ _).mpr ⟨bu,bv,xb⟩⟩)

lemma neighbors_cost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3) (u v:Fin n) (edge:G.Adj u v) :
    u∉A ∧ (G.neighborFinset u).card=3 := by
  have h := rule u
  have eq : (G.neighborSet u).ncard=(G.neighborFinset u).card := by
    symm
    rw [←Set.ncard_coe_finset,SimpleGraph.coe_neighborFinset]
  rw [eq] at h
  have pos := Finset.card_pos.mpr (show (G.neighborFinset u).Nonempty from ⟨v,(G.mem_neighborFinset _ _).mpr edge⟩)
  by_cases hu:u∈A
  · rw [if_pos hu] at h
    omega
  · simpa [hu] using And.intro hu h

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

def simulated (C:Circuit) (u v:Fin n) := ∃F:Circuit, FanInTwo F ∧ F.size≤C.size ∧
    circuitFun n F=circuitFun n C ∧ marked u v F

theorem pair_iff (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3)
    (u v:Fin n) (edge:G.Adj u v) (C:Circuit) (same:circuitFun n C=graphFun G A) :
    simulated C u v ↔ ordinary C u v := by
  constructor
  · rintro ⟨F,ff,small,eq,h⟩
    exact marked_to_ordinary C F ff small eq h
  · rintro ⟨D,df,cap,ev⟩
    obtain ⟨ha,cu⟩ := neighbors_cost G A rule u v edge
    obtain ⟨hb,cv⟩ := neighbors_cost G A rule v u edge.symm
    obtain ⟨F,ff,sf,ef,hf⟩ := appendMarked u v (term G u v) D df (termCost G u v edge cu cv) (termOff G u v)
    refine ⟨F,ff,by omega,?_,hf⟩
    funext x
    rw [ef,ev,same]
    exact splitGraph G A u v ha hb x

theorem cycle_iff {k:Nat} (pick:Fin k→Fin n) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A:Finset (Fin n)) (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3)
    (C:Circuit) (same:circuitFun n C=graphFun G A) :
    (∃i j,G.Adj (pick i) (pick j) ∧ simulated C (pick i) (pick j)) ↔
    (∃i j,G.Adj (pick i) (pick j) ∧ ordinary C (pick i) (pick j)) := by
  constructor <;> rintro ⟨i,j,h,p⟩
  · exact ⟨i,j,h,(pair_iff G A rule _ _ h C same).mp p⟩
  · exact ⟨i,j,h,(pair_iff G A rule _ _ h C same).mpr p⟩

end Builder
end Pair7808

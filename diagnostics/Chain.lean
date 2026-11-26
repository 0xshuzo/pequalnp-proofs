import PEqualNP.Defs
namespace Research5962.Trace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
set_option maxHeartbeats 1500000
def wstep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
  fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
theorem wfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool),
    (gs.foldl wstep xs).length = xs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro xs; simp
  | cons g rest ih =>
    intro xs
    simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem wfold_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (xs : List Bool) (r : ℕ),
    r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
  intro gs
  induction gs with
  | nil => intro xs r _; rfl
  | cons g rest ih =>
    intro xs r hr
    simp only [List.foldl_cons]
    have hr' : r < (wstep xs g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [ih (wstep xs g) r hr']
    simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
theorem wireVal_input : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (r : ℕ)
    (hr : r < 14), PEqualNP.CleanedNonEdge.wireVal 14 D r x = x ⟨r, hr⟩ := by
  intro D x r hr
  have hlen : (List.ofFn x).length = 14 := List.length_ofFn
  have hlt : r < (List.ofFn x).length := by omega
  change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
  rw [wfold_getD_lt D.gates (List.ofFn x) r hlt, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hr]
theorem wireVal_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (k : ℕ)
    (g : PEqualNP.CircuitLowerBounds.Gate),
    D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
    PEqualNP.CleanedNonEdge.wireVal 14 D (14 + k) x =
      g.op.eval (g.inputs.map fun i => PEqualNP.CleanedNonEdge.wireVal 14 D i x) := by
  intro D x k g hgk hlt
  have hk : k < D.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgk
    cases hgk
  have hg_eq : D.gates[k] = g := Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hgk)
  have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
    rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  let pref := (D.gates.take k).foldl wstep (List.ofFn x)
  have hpref_len : pref.length = 14 + k := by
    dsimp only [pref]
    rw [wfold_len, List.length_ofFn, List.length_take]
    omega
  have hwires_eq : D.wires (List.ofFn x) =
      (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
    change D.gates.foldl wstep (List.ofFn x) = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpref_get : ∀ i < 14 + k, pref.getD i false = PEqualNP.CleanedNonEdge.wireVal 14 D i x := by
    intro i hi
    change pref.getD i false = (D.wires (List.ofFn x)).getD i false
    rw [hwires_eq]
    have hi1 : i < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ i hi1]
    have hi0 : i < pref.length := by omega
    simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
  change (D.wires (List.ofFn x)).getD (14 + k) false = _
  rw [hwires_eq]
  have hidx : 14 + k < (wstep pref g).length := by
    simp only [wstep, List.length_append, List.length_singleton]; omega
  rw [wfold_getD_lt _ _ (14 + k) hidx]
  have hstep_at : (wstep pref g).getD (14 + k) false =
      g.op.eval (g.inputs.map fun i => pref.getD i false) := by
    simp only [wstep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hpref_len]
    simp
  rw [hstep_at]
  congr 1
  exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
theorem cones_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih =>
    intro cs
    rw [List.foldl_cons, ih]
    dsimp only [PEqualNP.EdgeOwnership.coneStep]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
theorem cones_char : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (i j : ℕ),
    i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
        14 ≤ w ∧ w < 14 + j ∧
        (i = w - 14 ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep 14 (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD k [] := by
      intro k hk
      dsimp only [PEqualNP.EdgeOwnership.coneStep]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - 14) (by omega)]; exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - 14) (by omega)] at h3; exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep 14
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + gs.length))).flatMap
            (fun w => (w - 14) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []).getD (w - 14) []) := by
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e1, e2, List.mem_flatMap]
      constructor
      · rintro ⟨w, hw, hmem⟩
        rw [List.mem_filter, decide_eq_true_eq] at hw
        refine ⟨by simp, w, hw.1, hw.2.1, hw.2.2, ?_⟩
        rw [key (w - 14) (by omega)]
        simpa using hmem
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - 14) (by omega)] at h3
        exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true ⟨h1, h2⟩⟩, by simpa using h3⟩
    · have e3 : (PEqualNP.EdgeOwnership.coneStep 14
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep 14) []) g).getD j [] = [] := by
        apply List.getD_eq_default
        dsimp only [PEqualNP.EdgeOwnership.coneStep]
        simp only [List.length_append, List.length_singleton, hlen]
        omega
      rw [e3]
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hlt
      simp only [List.length_append, List.length_singleton] at hlt
      omega
theorem inCone_iff : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
    PEqualNP.EdgeOwnership.InCone 14 D i j ↔
      j < D.gates.length ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs,
        14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ PEqualNP.EdgeOwnership.InCone 14 D i (w - 14)) :=
  fun D i j => cones_char D.gates i j
abbrev Sig := Bool × Bool × Bool
def trace (C : Circuit) (w : ℕ) : Sig :=
  (wireVal 14 C w (pairInput 0 7), wireVal 14 C w (pairInput 0 0), wireVal 14 C w (pairInput 7 7))
def op (t x y : Bool) := if t then x && y else x || y
def combine (t : Bool) (a b : Sig) : Sig := (op t a.1 b.1, op t a.2.1 b.2.1, op t a.2.2 b.2.2)
def joint : Sig := (true,false,false)
def mixed (a b : Sig) : Prop :=
  (a=(true,true,false) ∧ b=(true,false,true)) ∨ (b=(true,true,false) ∧ a=(true,false,true))
instance (a b : Sig) : Decidable (mixed a b) := by unfold mixed; infer_instance
theorem localSplit : ∀ (t : Bool) (a b : Sig), combine t a b = joint →
    a=joint ∨ b=joint ∨ (t=true ∧ mixed a b) := by decide +kernel

abbrev Shape (C : Circuit) := ∀ j g, C.gates[j]? = some g →
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j
def crossing (C : Circuit) (j : ℕ) := (gateAt C j).op = .and ∧
  mixed (trace C (opnd C j 0)) (trace C (opnd C j 1))
def present (C : Circuit) (j w : ℕ) := 14 ≤ w ∧ (w=14+j ∨ InCone 14 C j (w-14))

theorem signal_step (C : Circuit) (shape : Shape C) {j : Nat} (hj : j < C.gates.length) :
    ∃ (t : Bool) (a b : ℕ), a < 14+j ∧ b < 14+j ∧
    (gateAt C j).inputs = [a,b] ∧ opnd C j 0 = a ∧ opnd C j 1 = b ∧
    (t=true → (gateAt C j).op = .and) ∧
    trace C (14+j) = combine t (trace C a) (trace C b) := by
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  have he : gateAt C j = g := by
    change C.gates.getD j _ = g
    exact List.getD_eq_getElem _ _ hj
  obtain ⟨ot,a,b,ins,_,ha,hb⟩ := shape j g hg
  have ok : ∀ q ∈ g.inputs, q<14+j := by
    intro q h
    rw [ins] at h
    rcases (show q=a ∨ q=b by simpa using h) with rfl | rfl <;> assumption
  have source0 : opnd C j 0 = a := by simp [opnd,he,ins]
  have source1 : opnd C j 1 = b := by simp [opnd,he,ins]
  have run := fun x => wireVal_gate C x j g hg ok
  rcases ot with hand | hor
  · refine ⟨true,a,b,ha,hb,he ▸ ins,source0,source1,fun _ => he ▸ hand,?_⟩
    simp only [trace,combine,op,ite_true,run,hand,ins,GateOp.eval,List.map_cons,List.map_nil,
      List.all_cons,List.all_nil,id_eq,Bool.and_true]
  · refine ⟨false,a,b,ha,hb,he ▸ ins,source0,source1,by simp,?_⟩
    simp only [trace,combine,op,Bool.false_eq_true,ite_false,run,hor,ins,GateOp.eval,
      List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]

theorem originates (C : Circuit) (shape : Shape C) (w : ℕ) (h : trace C w = joint) :
    ∃ j, present C j w ∧ crossing C j := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    by_cases small : w<14
    · have impossible : ∀ i : Fin 14, (pairInput (0:Fin 14) 7 i,
          pairInput (0:Fin 14) 0 i,pairInput (7:Fin 14) 7 i) ≠ joint := by decide +kernel
      apply False.elim
      apply impossible ⟨w,small⟩
      simpa only [trace,wireVal_input C _ _ small] using h
    let t := w-14
    have eq : w=14+t := by dsimp [t]; omega
    have valid : t<C.gates.length := by
      by_contra! bad
      have bound : (C.wires (List.ofFn (pairInput (0:Fin 14) 7))).length ≤ w := by
        change (C.gates.foldl wstep _).length ≤ _
        rw [wfold_len,List.length_ofFn]
        omega
      have falseVal : wireVal 14 C w (pairInput 0 7) = false := List.getD_eq_default _ _ bound
      have yes := congrArg Prod.fst h
      exact Bool.noConfusion (falseVal.symm.trans yes)
    obtain ⟨bit,a,b,ha,hb,ins,source0,source1,isAnd,run⟩ := signal_step C shape valid
    have extend (q : ℕ) (hq : q ∈ (gateAt C t).inputs) (lt : q<w) (jq : trace C q=joint) :
        ∃ j, present C j w ∧ crossing C j := by
      obtain ⟨j,⟨q14,rel⟩,orig⟩ := ih q lt jq
      refine ⟨j,⟨by omega,Or.inr ((inCone_iff C j t).mpr ⟨valid,q,hq,q14,by omega,?_⟩)⟩,orig⟩
      rcases rel with rfl | rel
      · exact Or.inl (by omega)
      · exact Or.inr rel
    have res := localSplit bit (trace C a) (trace C b) (run.symm.trans (eq ▸ h))
    rcases res with ja | jb | ⟨band,tw⟩
    · exact extend a (by simp [ins]) (by omega) ja
    · exact extend b (by simp [ins]) (by omega) jb
    · refine ⟨t,⟨by omega,Or.inl eq⟩,isAnd band,?_⟩
      rw [source0,source1]
      exact tw

theorem crossing_excludes_mark (C : Circuit) (j : ℕ) (cut : crossing C j)
    (i : Fin 14) (side : i=0 ∨ i=7) :
    ¬ (∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput i i) = false) := by
  intro off
  have l := off 0
  have r := off 1
  rcases side with rfl|rfl <;> rcases cut.2 with ⟨a,b⟩ | ⟨a,b⟩
  · have t := congrArg (fun s : Sig => s.2.1) a
    change wireVal 14 C (opnd C j 0) (pairInput 0 0) = true at t
    exact Bool.noConfusion (l.symm.trans t)
  · have t := congrArg (fun s : Sig => s.2.1) a
    change wireVal 14 C (opnd C j 1) (pairInput 0 0) = true at t
    exact Bool.noConfusion (r.symm.trans t)
  · have t := congrArg (fun s : Sig => s.2.2) b
    change wireVal 14 C (opnd C j 1) (pairInput 7 7) = true at t
    exact Bool.noConfusion (r.symm.trans t)
  · have t := congrArg (fun s : Sig => s.2.2) b
    change wireVal 14 C (opnd C j 0) (pairInput 7 7) = true at t
    exact Bool.noConfusion (l.symm.trans t)

theorem strict_ancestor (C : Circuit) (shape : Shape C) (a : Nat) (i : Fin 14)
    (side : i=0 ∨ i=7) (clean : trace C (14+a) = joint)
    (mark : ∀ t : Fin 2, wireVal 14 C (opnd C a t) (pairInput i i) = false) :
    ∃ j, InCone 14 C j a ∧ crossing C j := by
  obtain ⟨j,⟨_,eq | deep⟩,h⟩ := originates C shape _ clean
  · have ja : j=a := by omega
    subst j
    exact False.elim (crossing_excludes_mark C a h i side mark)
  · exact ⟨j,by simpa using deep,h⟩
end Research5962.Trace

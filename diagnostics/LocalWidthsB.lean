import PEqualNP.Defs

namespace Plane2974

namespace Pin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

def ival (V : List Bool) : Option ℕ → Bool
  | none => false
  | some p => V.getD p false

theorem ival_append (V t : List Bool) : ∀ e : Option ℕ, (∀ p, e = some p → p < V.length) →
    ival (V ++ t) e = ival V e
  | none, _ => rfl
  | some p, h => List.getD_append _ _ _ _ (h p rfl)

def pass (op : GateOp) (e : Option ℕ) : Option ℕ :=
  match op with
  | GateOp.and => none
  | _ => e

def stepIm (op : GateOp) (m : ℕ) : Option ℕ → Option ℕ → Option ℕ
  | some _, some _ => some m
  | some p, none => pass op (some p)
  | none, iq => pass op iq

def stepOut (op : GateOp) : Option ℕ → Option ℕ → List Gate
  | some p, some q => [⟨op, [p, q]⟩]
  | _, _ => []

def step (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate) : List (Option ℕ) × List Gate :=
  (s.1 ++ [stepIm g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
      (s.1.getD (g.inputs.getD 1 0) none)],
    s.2 ++ stepOut g.op (s.1.getD (g.inputs.getD 0 0) none) (s.1.getD (g.inputs.getD 1 0) none))

theorem stepOut_length (op : GateOp) (ip iq : Option ℕ) : (stepOut op ip iq).length ≤ 1 := by
  cases ip <;> cases iq <;> simp [stepOut]

theorem stepOut_full (op : GateOp) (ip iq : Option ℕ) (h : (stepOut op ip iq).length = 1) :
    ip ≠ none ∧ iq ≠ none := by
  cases ip <;> cases iq <;> simp [stepOut] at h ⊢

theorem entry_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (V : List Bool)
    (ip iq : Option ℕ) :
    ival (wiresFrom (stepOut op ip iq) V) (stepIm op V.length ip iq)
      = op.eval [ival V ip, ival V iq] := by
  rcases hop with rfl | rfl <;> cases ip <;> cases iq <;>
    simp [stepIm, stepOut, pass, wiresFrom, ival, GateOp.eval]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v bp bq : Bool)
    (hu : u = true → bp = true) (hv : v = true → bq = true) (h : op.eval [u, v] = true) :
    op.eval [bp, bq] = true := by
  rcases hop with rfl | rfl <;> cases u <;> cases v <;> cases bp <;> cases bq <;>
    simp_all [GateOp.eval]

theorem stepIm_lt (op : GateOp) (B : ℕ) (ip iq : Option ℕ) (hp : ∀ p, ip = some p → p < B)
    (hq : ∀ p, iq = some p → p < B) :
    ∀ p, stepIm op B ip iq = some p → p < B + (stepOut op ip iq).length := by
  intro p h
  cases ip with
  | none =>
    cases op <;> simp only [stepIm, pass] at h
    all_goals first
      | exact Nat.lt_of_lt_of_le (hq p h) (Nat.le_add_right _ _)
      | simp at h
  | some p1 =>
    cases iq with
    | none =>
      cases op <;> simp only [stepIm, pass] at h
      all_goals first
        | exact Nat.lt_of_lt_of_le (hp p h) (Nat.le_add_right _ _)
        | simp at h
    | some q1 =>
      simp only [stepIm, Option.some.injEq] at h
      subst h
      simp [stepOut]

def Good (n : ℕ) (s : List (Option ℕ) × List Gate) : Prop :=
  (∀ i p, s.1.getD i none = some p → p < n + s.2.length) ∧
  (∀ g ∈ s.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < s.2.length, ∀ i ∈ (s.2.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

theorem good_step (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Good n s) : Good n (step n s g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hlt := stepIm_lt g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
    (s.1.getD (g.inputs.getD 1 0) none) (fun p hp => h1 _ p hp) (fun p hp => h1 _ p hp)
  refine ⟨?_, ?_, ?_⟩
  · intro i p hp
    show p < n + (s.2 ++ stepOut g.op _ _).length
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hil : i = s.1.length
    · subst hil
      have hp' : stepIm g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
          (s.1.getD (g.inputs.getD 1 0) none) = some p := by
        rw [← hp]
        exact (getD_snoc_eq _ _ _).symm
      exact hlt p hp'
    · have hp' : s.1.getD i none = some p := by
        rw [← hp]
        exact (getD_snoc_ne _ _ _ _ hil).symm
      exact Nat.lt_of_lt_of_le (h1 i p hp') (Nat.le_add_right _ _)
  · intro g' hg'
    rcases List.mem_append.1 hg' with hin | hin
    · exact h2 g' hin
    · cases hip : s.1.getD (g.inputs.getD 0 0) none <;>
        cases hiq : s.1.getD (g.inputs.getD 1 0) none <;>
        simp only [hip, hiq, stepOut, List.mem_singleton, List.not_mem_nil] at hin
      subst hin
      exact ⟨hop, rfl⟩
  · intro j hj i hi
    by_cases hjl : j < s.2.length
    · rw [show (step n s g).2 = s.2 ++ stepOut g.op _ _ from rfl,
        List.getD_append _ _ _ _ hjl] at hi
      exact h3 j hjl i hi
    · cases hip : s.1.getD (g.inputs.getD 0 0) none <;>
        cases hiq : s.1.getD (g.inputs.getD 1 0) none <;>
        simp only [step, hip, hiq, stepOut, List.append_nil, List.length_append,
          List.length_singleton] at hj hi
      all_goals try omega
      rename_i p1 q1
      have hje : j = s.2.length := by omega
      subst hje
      rw [getD_snoc_eq] at hi
      rcases List.mem_cons.1 hi with rfl | hi2
      · exact h1 _ _ hip
      · rcases List.mem_cons.1 hi2 with rfl | hi3
        · exact h1 _ _ hiq
        · simp at hi3

theorem good_fold (n : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Good n s →
      Good n (gs.foldl (step n) s) := by
  induction gs with
  | nil => intro s _ h; exact h
  | cons g gs ih =>
    intro s hok h
    exact ih (step n s g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (good_step n s g (hok g List.mem_cons_self) h)

def Sem (a : ℕ) (X : List Bool) (s : List (Option ℕ) × List Gate) (W : List Bool) : Prop :=
  s.1.length = W.length ∧
  (∀ i, ival (wiresFrom s.2 X) (s.1.getD i none) = true → W.getD i false = true) ∧
  (X.getD a false = false → ∀ i, ival (wiresFrom s.2 X) (s.1.getD i none) = W.getD i false)

theorem sem_step (n a : ℕ) (X : List Bool) (hX : X.length = n)
    (s : List (Option ℕ) × List Gate) (W : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hg : Good n s) (h : Sem a X s W) :
    Sem a X (step n s g) (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · obtain ⟨hl, hS1, hS2⟩ := h
    have hop' : op = GateOp.and ∨ op = GateOp.or := hop
    have lV : (wiresFrom s.2 X).length = n + s.2.length := by rw [length_wiresFrom, hX]
    have hnew : wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X
        = wiresFrom (stepOut op (s.1.getD p none) (s.1.getD q none)) (wiresFrom s.2 X) :=
      wiresFrom_append _ _ _
    obtain ⟨t, ht, -⟩ := wiresFrom_prefix (stepOut op (s.1.getD p none) (s.1.getD q none))
      (wiresFrom s.2 X)
    have hval := entry_val op hop' (wiresFrom s.2 X) (s.1.getD p none) (s.1.getD q none)
    rw [lV] at hval
    have stable : ∀ i, ival (wiresFrom s.2 X ++ t) (s.1.getD i none)
        = ival (wiresFrom s.2 X) (s.1.getD i none) := fun i =>
      ival_append _ t _ (fun p' hp' => by rw [lV]; exact hg.1 i p' hp')
    refine ⟨by simp [step, hl], ?_, ?_⟩
    · intro i
      show ival (wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X)
          ((s.1 ++ [stepIm op (n + s.2.length) (s.1.getD p none) (s.1.getD q none)]).getD i none)
            = true →
          (W ++ [op.eval [W.getD p false, W.getD q false]]).getD i false = true
      rw [hnew]
      by_cases hil : i = s.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq, hval]
        exact eval_mono op hop' _ _ _ _ (hS1 p) (hS1 q)
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega), ht, stable]
        exact hS1 i
    · intro hxa i
      show ival (wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X)
          ((s.1 ++ [stepIm op (n + s.2.length) (s.1.getD p none) (s.1.getD q none)]).getD i none)
            = (W ++ [op.eval [W.getD p false, W.getD q false]]).getD i false
      rw [hnew]
      by_cases hil : i = s.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq, hval, hS2 hxa p, hS2 hxa q]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega), ht, stable]
        exact hS2 hxa i
  · simp at hlen

theorem sem_fold (n a : ℕ) (X : List Bool) (hX : X.length = n) (gs : List Gate) :
    ∀ (s : List (Option ℕ) × List Gate) (W : List Bool),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      Good n s → Sem a X s W → Sem a X (gs.foldl (step n) s) (wiresFrom gs W) := by
  induction gs with
  | nil => intro s W _ _ h; exact h
  | cons g gs ih =>
    intro s W hok hg h
    have hgo := hok g List.mem_cons_self
    exact ih (step n s g) _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (good_step n s g hgo.1 hg) (sem_step n a X hX s W g hgo.1 hgo.2 hg h)

def init (n a : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = a then none else some i

theorem init_length (n a : ℕ) : (init n a).length = n := by
  simp [init]

theorem init_getD (n a k : ℕ) :
    (init n a).getD k none = if k < n ∧ k ≠ a then some k else none := by
  by_cases hk : k < n
  · by_cases hv : k = a
    · subst hv
      simp [init, hk]
    · simp [init, hk, hv]
  · rw [List.getD_eq_default _ _ (by rw [init_length]; omega)]
    simp [hk]

theorem good_init (n a : ℕ) : Good n (init n a, []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i p hp
    have hp' : (init n a).getD i none = some p := hp
    rw [init_getD] at hp'
    split at hp'
    · rename_i hc
      simp only [Option.some.injEq] at hp'
      subst hp'
      exact Nat.lt_of_lt_of_le hc.1 (Nat.le_add_right _ _)
    · simp at hp'
  · intro g hg
    simp at hg
  · intro j hj
    simp at hj

theorem sem_init (n a : ℕ) (X : List Bool) (hX : X.length = n) : Sem a X (init n a, []) X := by
  refine ⟨by simp [init_length, hX], ?_, ?_⟩
  · intro i
    show ival X ((init n a).getD i none) = true → X.getD i false = true
    rw [init_getD]
    split
    · exact id
    · intro h
      simp [ival] at h
  · intro hxa i
    show ival X ((init n a).getD i none) = X.getD i false
    rw [init_getD]
    split
    · rfl
    · rename_i hc
      show false = X.getD i false
      by_cases hi : i < n
      · have hia : i = a := by
          by_contra hne
          exact hc ⟨hi, hne⟩
        rw [hia, hxa]
      · rw [List.getD_eq_default _ _ (by omega)]

theorem step_snd_len (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate) :
    (step n s g).2.length ≤ s.2.length + 1 := by
  have := stepOut_length g.op (s.1.getD (g.inputs.getD 0 0) none)
    (s.1.getD (g.inputs.getD 1 0) none)
  simp only [step, List.length_append]
  omega

theorem fold_snd_len (n : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    (gs.foldl (step n) s).2.length ≤ s.2.length + gs.length := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    have h1 := ih (step n s g)
    have h2 := step_snd_len n s g
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem fold_full (n a : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    a < s.1.length → s.1.getD a none = none → (∀ g ∈ gs, g.inputs.length = 2) →
    (gs.foldl (step n) s).2.length = s.2.length + gs.length → ∀ g ∈ gs, a ∉ g.inputs := by
  induction gs with
  | nil => intro s _ _ _ _ g hg; simp at hg
  | cons g gs ih =>
    intro s ha hna hlen hfull g' hg'
    have h1 := fold_snd_len n gs (step n s g)
    have h2 := step_snd_len n s g
    simp only [List.foldl_cons, List.length_cons] at hfull
    have e1 : (step n s g).2.length = s.2.length + 1 := by omega
    have e2 : (gs.foldl (step n) (step n s g)).2.length = (step n s g).2.length + gs.length := by
      omega
    rcases List.mem_cons.1 hg' with heq | hin
    · subst heq
      have e3 : (stepOut g'.op (s.1.getD (g'.inputs.getD 0 0) none)
          (s.1.getD (g'.inputs.getD 1 0) none)).length = 1 := by
        simp only [step, List.length_append] at e1
        omega
      obtain ⟨hp, hq⟩ := stepOut_full _ _ _ e3
      have hl2 := hlen g' List.mem_cons_self
      obtain ⟨op, inputs⟩ := g'
      rcases inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
      · simp at hl2
      · simp at hl2
      · intro hmem
        rcases List.mem_cons.1 hmem with rfl | hmem2
        · exact hp hna
        · rcases List.mem_cons.1 hmem2 with rfl | hmem3
          · exact hq hna
          · simp at hmem3
      · simp at hl2
    · exact ih (step n s g) (by simp only [step, List.length_append, List.length_singleton]; omega)
        (by
          show (s.1 ++ [_]).getD a none = none
          rw [getD_snoc_ne _ _ _ _ (by omega)]
          exact hna)
        (fun g0 hg0 => hlen g0 (List.mem_cons_of_mem _ hg0)) e2 g' hin

theorem off_fold (a : ℕ) (gs : List Gate) : ∀ W W' : List Bool, W.length = W'.length →
    (∀ g ∈ gs, a ∉ g.inputs) → (∀ i, i ≠ a → W.getD i false = W'.getD i false) →
    ∀ i, i ≠ a → (wiresFrom gs W).getD i false = (wiresFrom gs W').getD i false := by
  induction gs with
  | nil => intro W W' _ _ h; exact h
  | cons g gs ih =>
    intro W W' hl hno h
    have hv : g.op.eval (g.inputs.map fun i => W.getD i false)
        = g.op.eval (g.inputs.map fun i => W'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact h k (fun hka => hno g List.mem_cons_self (hka ▸ hk))
    have hstep : ∀ i, i ≠ a →
        (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD i false
          = (W' ++ [g.op.eval (g.inputs.map fun i => W'.getD i false)]).getD i false := by
      intro i hi
      rw [hv]
      by_cases hil : i = W.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        exact h i hi
    exact ih _ _ (by simp [hl]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) hstep

def outIdx (m : ℕ) : Option ℕ → ℕ
  | none => m
  | some p => p

theorem eval_out (n : ℕ) (out : List Gate) (e : Option ℕ) (X : List Bool) (hX : X.length = n) :
    (Circuit.mk out (outIdx (n + out.length) e)).eval X = ival (wiresFrom out X) e := by
  cases e with
  | none =>
    show (wiresFrom out X).getD (n + out.length) false = false
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom, hX])
  | some p => rfl

theorem erase (n : ℕ) (C : Circuit) (a b : Fin n) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (_hab : a ≠ b) (h1 : circuitFun n C (fun i => decide (i = a)) = false)
    (h2 : circuitFun n C (fun i => decide (i = b)) = false)
    (h3 : circuitFun n C (fun i => decide (i = a ∨ i = b)) = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
      ∀ x : Fin n → Bool, x a = false → circuitFun n D x = circuitFun n C x := by
  obtain ⟨hand, -, hlen2⟩ := hAO
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hand g hg, hlen2 g hg⟩
  have hgood : Good n (C.gates.foldl (step n) (init n a, [])) :=
    good_fold n C.gates _ (fun g hg => (hok g hg).1) (good_init n a)
  have hsem : ∀ X : List Bool, X.length = n →
      Sem a X (C.gates.foldl (step n) (init n a, [])) (wiresFrom C.gates X) :=
    fun X hX => sem_fold n a X hX C.gates _ _ hok (good_init n a) (sem_init n a X hX)
  have hD : ∀ x : Fin n → Bool,
      circuitFun n ⟨(C.gates.foldl (step n) (init n a, [])).2,
        outIdx (n + (C.gates.foldl (step n) (init n a, [])).2.length)
          ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none)⟩ x
      = ival (wiresFrom (C.gates.foldl (step n) (init n a, [])).2 (List.ofFn x))
          ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none) :=
    fun x => eval_out n _ _ _ (by simp)
  refine ⟨⟨(C.gates.foldl (step n) (init n a, [])).2,
    outIdx (n + (C.gates.foldl (step n) (init n a, [])).2.length)
      ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none)⟩,
    ⟨fun g hg => (hgood.2.1 g hg).1, hgood.2.2, fun g hg => (hgood.2.1 g hg).2⟩, ?_, ?_, ?_⟩
  · show (C.gates.foldl (step n) (init n a, [])).2.length < C.gates.length
    have hle := fold_snd_len n C.gates (init n a, [])
    by_contra hnot
    have heq : (C.gates.foldl (step n) (init n a, [])).2.length
        = (init n a, ([] : List Gate)).2.length + C.gates.length := by
      simp only [List.length_nil] at hle ⊢
      omega
    have hno := fold_full n a C.gates (init n a, []) (by simp [init_length])
      (by
        show (init n a).getD a none = none
        rw [init_getD]
        simp)
      hlen2 heq
    by_cases ho : C.output = (a : ℕ)
    · have h1' : (wiresFrom C.gates (List.ofFn fun i => decide (i = a))).getD C.output false
          = false := h1
      obtain ⟨t, ht, -⟩ := wiresFrom_prefix C.gates (List.ofFn fun i => decide (i = a))
      rw [ht, ho, List.getD_append _ _ _ _ (by simp), ofFn_getD] at h1'
      simp at h1'
    · have hagree := off_fold a C.gates (List.ofFn fun i => decide (i = a ∨ i = b))
        (List.ofFn fun i => decide (i = b)) (by simp) hno
        (by
          intro i hi
          rw [ofFn_getD, ofFn_getD]
          by_cases hin : i < n
          · have hne : (⟨i, hin⟩ : Fin n) ≠ a := fun h => hi (congrArg Fin.val h)
            simp [hin, hne]
          · simp [hin])
        C.output ho
      have h3' : (wiresFrom C.gates (List.ofFn fun i => decide (i = a ∨ i = b))).getD
          C.output false = true := h3
      have h2' : (wiresFrom C.gates (List.ofFn fun i => decide (i = b))).getD C.output false
          = false := h2
      rw [hagree, h2'] at h3'
      exact Bool.false_ne_true h3'
  · intro x hx
    rw [hD x] at hx
    exact (hsem (List.ofFn x) (by simp)).2.1 C.output hx
  · intro x hxa
    rw [hD x]
    exact (hsem (List.ofFn x) (by simp)).2.2 (by rw [ofFn_getD]; simp [hxa]) C.output

end Pin

namespace GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end GraphProof


namespace GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end GraphProof


namespace GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

theorem point_contains_edge (hC : Monotone2 C) (he : GraphEval C G)
    {u v : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true :=
  acts_mono hC (point_mono (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)))
    C.output ((he u v).mpr edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem pairShape {a b : ℕ} {is : List ℕ} (ha : a∈is) (hb : b∈is) (ne : a≠b) (len : is.length≤2) :
    is=[a,b] ∨ is=[b,a] := by
  match is with
  | [] => simp at ha
  | [_] => simp_all
  | [u,v] =>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp_all
  | _::_::_::_ => simp at len

theorem localMeeting (hC : Monotone2 C) (xy xp yl : Fin n → Bool)
    (hxy : val C xy C.output=true) (hx : val C xp C.output=false) (hy : val C yl C.output=false)
    (splitInput : ∀ i, xy i=true → xp i=true ∨ yl i=true) :
    ∃ p g a b, C.gates[p]?=some g ∧ g.op=GateOp.and ∧ Live n C (n+p) ∧
      a<n+p ∧ b<n+p ∧ (g.inputs=[a,b] ∨ g.inputs=[b,a]) ∧ val C xp a=true ∧ val C yl b=true := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C xy i = true ∧
    val C xp i = false ∧ val C yl i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, hxy, hx, hy⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C xy i = true) :
      val C xp i = true ∨ val C yl i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    rcases splitInput i ht with on|on
    · rw [hv] at on; contradiction
    · rw [hw] at on; contradiction
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C xy (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C xp (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C yl (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C xy i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C xy (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C xp i = true ∨ val C yl i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,ha',hb',pairShape ha hb hne hl.2,hva,hwb⟩

end GraphProof
end Plane2974
namespace Plane8311

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

def Flags {N : ℕ} (S : Fin N → Finset (Fin N)) :=
  Finset.univ.filter fun e : Fin N × Fin N => e.1 ∈ S e.2

def Guarded {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) : Prop :=
  ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ → ℕ),                   PEqualNP.MetaComplexity.Monotone2 x12 ∧                     List.take C.size x12.gates = C.gates ∧                       x12.size ≤ (5 : ℕ) * C.size + (2 : ℕ) ∧                         have x14 : Finset (Fin N) → Finset (Fin N) → ℕ → Bool := fun (x14 x15 : Finset (Fin N)) (x16 : ℕ) => (x12.wires (PEqualNP.GenericRejection.incidenceInput x14 x15)).getD x16 Bool.false;                         have x15 : Finset (Fin N) → Finset (Fin N) → Prop := fun (x15 x16 : Finset (Fin N)) => ∃ x17 < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x12 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x12 x17).inputs.length = (2 : ℕ) ∧ ∃ (x18 : Fin (2 : ℕ)), (x14 x15 ∅ (PEqualNP.TopForm.opnd x12 x17 x18) && x14 ∅ x16 (PEqualNP.TopForm.opnd x12 x17 ((1 : Fin (2 : ℕ)) - x18)) && (x14 x15 ∅ (x13 x17) || x14 ∅ x16 (x13 x17))) = Bool.true;                         (∀ (x16 x17 : Finset (Fin N)), x15 x16 x17 → PEqualNP.GenericRejection.incidenceFun S x16 x17 = Bool.true) ∧ ∀ (x16 : Finset (Fin N × Fin N)), (∀ x17 ∈ x16, x17.1 ∈ S x17.2 ∧ ¬x15 {x17.1} {x17.2}) → x16.card ≤ (86 : ℕ) * C.size

open NestedCover PEqualNP.TopForm Plane2974.GraphProof

def bank {N : ℕ} (X Y : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y))

def W {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) (i : ℕ) :=
  (C.wires (incidenceInput X Y)).getD i false

theorem valBank {N : ℕ} (C : Circuit) (X Y : Finset (Fin N)) (i : ℕ) :
    val C (bank X Y) i=W C X Y i := by
  change (C.wires (List.ofFn (bank X Y))).getD i false=_
  rw [show List.ofFn (bank X Y)=incidenceInput X Y from List.ofFn_fin_append _ _]
  rfl

def Mix {N : ℕ} (C : Circuit) (j : ℕ) (X Y : Finset (Fin N)) : Prop :=
  (gateAt C j).op=.and ∧ (gateAt C j).inputs.length=2 ∧ ∃ b : Fin 2,
    W C X ∅ (opnd C j b)=true ∧ W C ∅ Y (opnd C j (1-b))=true

def Safe {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (j : ℕ) : Prop :=
  ∀ X Y, Mix C j X Y → incidenceFun S X Y=true

def Genuine {N : ℕ} (C : Circuit) (j : ℕ) (p l : Fin N) : Prop :=
  Live (N+N) C (N+N+j) ∧ (∀ b, opnd C j b<N+N+j) ∧ Mix C j {p} {l}

noncomputable def badEdges {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (j : ℕ) :
    Finset (Fin N × Fin N) := by
  classical
  exact (Flags S).filter (fun e => Genuine C j e.1 e.2 ∧ ¬Safe S C j)

theorem quiet {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (sound : ∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true) :
    (∀ X : Finset (Fin N), W C X ∅ C.output=false) ∧ (∀ Y : Finset (Fin N), W C ∅ Y C.output=false) := by
  constructor
  · intro X
    apply Bool.eq_false_iff.mpr
    intro h
    simpa [incidenceFun] using sound X ∅ h
  · intro Y
    apply Bool.eq_false_iff.mpr
    intro h
    simpa [incidenceFun] using sound ∅ Y h

theorem genuineExists {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (mon : Monotone2 C)
    (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true)
    (p l : Fin N) (incident : p∈S l) : ∃ j<C.size, Genuine C j p l := by
  classical
  obtain ⟨offP,offL⟩ := quiet S C sound
  let P : Finset (Fin N) := {p}
  let L : Finset (Fin N) := {l}
  have splitInput : ∀ i, bank P L i=true → bank P ∅ i=true ∨ bank ∅ L i=true := by
    intro i
    induction i using Fin.addCases with
    | left a => intro h; exact Or.inl (by simpa [bank] using h)
    | right b =>
      intro h
      apply Or.inr
      have get (A B : Finset (Fin N)) : bank A B (Fin.natAdd N b) = decide (b∈B) := Fin.addCases_right ..
      rw [get] at h ⊢
      exact h
  obtain ⟨j,g,a,b,hg,hand,live,la,lb,dirs,onP,onL⟩ := localMeeting mon (bank P L) (bank P ∅) (bank ∅ L)
    (by rw [valBank]; exact pos l p incident) (by rw [valBank]; exact offP P)
    (by rw [valBank]; exact offL L) splitInput
  have gate : gateAt C j = g := by simp [gateAt,List.getD_eq_getElem?_getD,hg]
  rw [valBank] at onP onL
  refine ⟨j,(List.getElem?_eq_some_iff.mp hg).1,live,?_,?_,?_,?_⟩
  · intro d
    fin_cases d <;> rcases dirs with h|h <;> simp [opnd,gate,h,la,lb]
  · rw [gate]; exact hand
  · rcases dirs with h|h <;> simp [gate,h]
  · rcases dirs with h|h
    · exact ⟨0,by simpa [opnd,gate,h,P,L] using onP,by simpa [opnd,gate,h,P,L] using onL⟩
    · exact ⟨1,by simpa [opnd,gate,h,P,L] using onP,by simpa [opnd,gate,h,P,L] using onL⟩

theorem localPricing {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (mon : Monotone2 C)
    (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true)
    (price : ∀ j<C.size, (badEdges S C j).card≤86) : Guarded S C := by
  classical
  let k (j : ℕ) := if Safe S C j then opnd C j 0 else C.output
  let seen (X Y : Finset (Fin N)) := ∃ j<C.size, (gateAt C j).op=.and ∧
    (gateAt C j).inputs.length=2 ∧ ∃ b : Fin 2, (W C X ∅ (opnd C j b) && W C ∅ Y (opnd C j (1-b)) &&
      (W C X ∅ (k j) || W C ∅ Y (k j)))=true
  obtain ⟨offP,offL⟩ := quiet S C sound
  have exactSeen (X Y) : seen X Y ↔ ∃ j<C.size, Safe S C j ∧ Mix C j X Y := by
    constructor
    · rintro ⟨j,hj,hand,har,b,hb⟩
      simp only [Bool.and_eq_true,Bool.or_eq_true] at hb
      refine ⟨j,hj,?_,hand,har,b,hb.1⟩
      by_contra no
      rcases hb.2 with h|h
      · simp only [k,if_neg no,offP] at h; cases h
      · simp only [k,if_neg no,offL] at h; cases h
    · rintro ⟨j,hj,ok,hand,har,b,hp,hl⟩
      refine ⟨j,hj,hand,har,b,?_⟩
      simp only [Bool.and_eq_true,Bool.or_eq_true,k,if_pos ok]
      refine ⟨⟨hp,hl⟩,?_⟩
      fin_cases b
      · exact Or.inl hp
      · exact Or.inr hl
  refine ⟨C,k,mon,by simp [Circuit.size],by omega,?_,?_⟩
  · intro X Y h
    obtain ⟨j,_,ok,mix⟩ := (exactSeen X Y).mp h
    exact ok X Y mix
  · intro E subset
    have covered : E ⊆ (Finset.range C.size).biUnion (badEdges S C) := by
      intro e he
      obtain ⟨inc,miss⟩ := subset e he
      obtain ⟨j,hj,real⟩ := genuineExists S C mon pos sound e.1 e.2 inc
      apply Finset.mem_biUnion.mpr
      refine ⟨j,Finset.mem_range.mpr hj,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩,real,?_⟩⟩
      exact fun ok => miss ((exactSeen {e.1} {e.2}).mpr ⟨j,hj,ok,real.2.2⟩)
    calc
      E.card ≤ ((Finset.range C.size).biUnion (badEdges S C)).card := Finset.card_le_card covered
      _ ≤ ∑ j ∈ Finset.range C.size, (badEdges S C j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range C.size, 86 := Finset.sum_le_sum (fun j hj => price j (Finset.mem_range.mp hj))
      _ = 86*C.size := by simp [Nat.mul_comm]

noncomputable def owner {N : ℕ} (C : Circuit) (p l : Fin N) : ℕ := by
  classical
  exact if h : ∃ j<C.size, Genuine C j p l then Nat.find h else C.size

noncomputable def debt {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (j : ℕ) : Finset (Fin N × Fin N) := by
  classical
  exact (Flags S).filter (fun e => owner C e.1 e.2=j ∧ ¬∃ t<C.size, Safe S C t ∧ Mix C t {e.1} {e.2})

theorem allocatedPricing {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (mon : Monotone2 C)
    (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true)
    (cost : ℕ → ℕ) (price : ∀ j<C.size, (debt S C j).card≤cost j)
    (total : ∑ j ∈ Finset.range C.size, cost j ≤86*C.size) : Guarded S C := by
  classical
  let k (j : ℕ) := if Safe S C j then opnd C j 0 else C.output
  let seen (X Y : Finset (Fin N)) := ∃ j<C.size, (gateAt C j).op=.and ∧
    (gateAt C j).inputs.length=2 ∧ ∃ b : Fin 2, (W C X ∅ (opnd C j b) && W C ∅ Y (opnd C j (1-b)) &&
      (W C X ∅ (k j) || W C ∅ Y (k j)))=true
  obtain ⟨offP,offL⟩ := quiet S C sound
  have exactSeen (X Y) : seen X Y ↔ ∃ j<C.size, Safe S C j ∧ Mix C j X Y := by
    constructor
    · rintro ⟨j,hj,hand,har,b,hb⟩
      simp only [Bool.and_eq_true,Bool.or_eq_true] at hb
      refine ⟨j,hj,?_,hand,har,b,hb.1⟩
      by_contra no
      rcases hb.2 with h|h
      · simp only [k,if_neg no,offP] at h; cases h
      · simp only [k,if_neg no,offL] at h; cases h
    · rintro ⟨j,hj,ok,hand,har,b,hp,hl⟩
      refine ⟨j,hj,hand,har,b,?_⟩
      simp only [Bool.and_eq_true,Bool.or_eq_true,k,if_pos ok]
      refine ⟨⟨hp,hl⟩,?_⟩
      fin_cases b
      · exact Or.inl hp
      · exact Or.inr hl
  refine ⟨C,k,mon,by simp [Circuit.size],by omega,?_,?_⟩
  · intro X Y h
    obtain ⟨j,_,ok,mix⟩ := (exactSeen X Y).mp h
    exact ok X Y mix
  · intro E subset
    have covered : E ⊆ (Finset.range C.size).biUnion (debt S C) := by
      intro e he
      obtain ⟨inc,miss⟩ := subset e he
      have witness := genuineExists S C mon pos sound e.1 e.2 inc
      have low : owner C e.1 e.2<C.size := by
        simp only [owner,dif_pos witness]
        exact (Nat.find_spec witness).1
      apply Finset.mem_biUnion.mpr
      refine ⟨_,Finset.mem_range.mpr low,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩,rfl,?_⟩⟩
      exact fun covered => miss ((exactSeen {e.1} {e.2}).mpr covered)
    calc
      E.card ≤ ((Finset.range C.size).biUnion (debt S C)).card := Finset.card_le_card covered
      _ ≤ ∑ j ∈ Finset.range C.size, (debt S C j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range C.size, cost j := Finset.sum_le_sum (fun j hj => price j (Finset.mem_range.mp hj))
      _ ≤ 86*C.size := total

end Plane8311

namespace Plane8311.RichGuards

theorem singleSide {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noSquare : ∀ a b l m, a≠b → l≠m → R a l → R a m → R b l → R b m → False)
    (A : Finset α) (B : Finset β)
    (complete : ∀ a∈A, ∀ l∈B, R a l) (two : 2≤B.card) : A.card≤1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ne
  obtain ⟨l,hl,m,hm,nlm⟩ := Finset.one_lt_card.mp (by omega : 1<B.card)
  exact noSquare a b l m ne nlm (complete a ha l hl) (complete a ha m hm)
    (complete b hb l hl) (complete b hb m hm)

def rich {α β : Type*} [DecidableEq α] (G A : Finset α) (B : Finset β) : Finset α :=
  if 2 ≤ B.card then G∩A else ∅

theorem richSize {α β : Type*} [DecidableEq α] [DecidableEq β] (R : α → β → Prop)
    (noSquare : ∀ a b l m, a≠b → l≠m → R a l → R a m → R b l → R b m → False)
    (G A : Finset α) (B : Finset β)
    (safe : ∀ a∈A, ∀ l∈B, a∈G → R a l) : (rich G A B).card≤1 := by
  unfold rich
  split
  next h =>
    apply singleSide R noSquare _ B _ h
    intro a ha l hl
    exact safe a (Finset.mem_inter.mp ha).2 l hl (Finset.mem_inter.mp ha).1
  · simp

theorem smallGuard {α β : Type*} [DecidableEq α] [DecidableEq β] (R : α → β → Prop)
    (noSquare : ∀ a b l m, a≠b → l≠m → R a l → R a m → R b l → R b m → False)
    (A₀ A₁ P : Finset α) (B₀ B₁ L : Finset β)
    (safe₀ : ∀ p∈A₀, ∀ l∈B₀, p∈P ∨ l∈L → R p l)
    (safe₁ : ∀ p∈A₁, ∀ l∈B₁, p∈P ∨ l∈L → R p l) :
    ∃ (U : Finset α) (V : Finset β), U⊆P ∧ V⊆L ∧ U.card≤2 ∧ V.card≤2 ∧
      (∀ p∈A₀, ∀ l∈B₀, (p∈P ∧ 2≤B₀.card) ∨ (l∈L ∧ 2≤A₀.card) → p∈U ∨ l∈V) ∧
      (∀ p∈A₁, ∀ l∈B₁, (p∈P ∧ 2≤B₁.card) ∨ (l∈L ∧ 2≤A₁.card) → p∈U ∨ l∈V) := by
  let U := rich P A₀ B₀ ∪ rich P A₁ B₁
  let V := rich L B₀ A₀ ∪ rich L B₁ A₁
  have dual := fun l m a b lm ab al bl am bm => noSquare a b l m ab lm al am bl bm
  have u₀ := richSize R noSquare P A₀ B₀ (fun p hp l hl h => safe₀ p hp l hl (Or.inl h))
  have u₁ := richSize R noSquare P A₁ B₁ (fun p hp l hl h => safe₁ p hp l hl (Or.inl h))
  have v₀ := richSize (fun l p => R p l) dual L B₀ A₀ (fun l hl p hp h => safe₀ p hp l hl (Or.inr h))
  have v₁ := richSize (fun l p => R p l) dual L B₁ A₁ (fun l hl p hp h => safe₁ p hp l hl (Or.inr h))
  have sub {ι κ : Type*} [DecidableEq ι] (G A : Finset ι) (B : Finset κ) : rich G A B ⊆ G := by
    unfold rich
    split
    · exact Finset.inter_subset_left
    · exact Finset.empty_subset _
  refine ⟨U,V,Finset.union_subset (sub ..) (sub ..),Finset.union_subset (sub ..) (sub ..),
    (Finset.card_union_le _ _).trans (by omega),(Finset.card_union_le _ _).trans (by omega),?_,?_⟩
  · intro p hp l hl h
    rcases h with ⟨ip,hb⟩|⟨il,ha⟩
    · exact Or.inl (Finset.mem_union_left _ (by simp [rich,hb,ip,hp]))
    · exact Or.inr (Finset.mem_union_left _ (by simp [rich,ha,il,hl]))
  · intro p hp l hl h
    rcases h with ⟨ip,hb⟩|⟨il,ha⟩
    · exact Or.inl (Finset.mem_union_right _ (by simp [rich,hb,ip,hp]))
    · exact Or.inr (Finset.mem_union_right _ (by simp [rich,ha,il,hl]))

end Plane8311.RichGuards

namespace Plane2974.Small

theorem two_mul_le_sq_add_sq (x y : ℕ) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  by_cases h : x ≤ y
  · obtain ⟨k, rfl⟩ : ∃ k, y = x + k := ⟨y - x, by omega⟩
    have h1 : x ^ 2 + (x + k) ^ 2 = 2 * (x * (x + k)) + k ^ 2 := by ring
    rw [h1]
    exact Nat.le_add_right _ _
  · obtain ⟨k, rfl⟩ : ∃ k, x = y + k := ⟨x - y, by omega⟩
    have h1 : (y + k) ^ 2 + y ^ 2 = 2 * ((y + k) * y) + k ^ 2 := by ring
    rw [h1]
    exact Nat.le_add_right _ _

theorem sum_const_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ℕ) :
    ∑ _x ∈ s, c = s.card * c := by
  refine Finset.induction_on s (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, ih]
  simp [ha]
  ring

theorem sq_sum_le_card_mul_sum_sq_nat {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h1 : 2 * (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * f j) := by
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h2 : ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * f j) ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum fun j _ => ?_
    exact two_mul_le_sq_add_sq (f i) (f j)
  have h3 : ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) = 2 * (s.card * ∑ i ∈ s, f i ^ 2) := by
    have h3a : ∀ i, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) = s.card * f i ^ 2 + ∑ j ∈ s, f j ^ 2 := by
      intro i
      rw [Finset.sum_add_distrib, sum_const_nat]
    simp_rw [h3a]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_const_nat]
    ring
  rw [← h1] at h2
  rw [h3] at h2
  exact Nat.le_of_mul_le_mul_left h2 (by omega)

theorem mul_self_sub_self (n : ℕ) : n * n - n = n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.add_sub_cancel]

theorem offDiag_card_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  exact mul_self_sub_self s.card

theorem sq_eq_add_mul_pred (n : ℕ) : n ^ 2 = n + n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

theorem card_filter_product_eq_sum {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) :
    ((X ×ˢ Y).filter (fun p => p ∈ E)).card =
      ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card := by
  have hS : (X ×ˢ Y).filter (fun p => p ∈ E) =
      X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨a', ha', b', ⟨hb', hab'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ha', hb'⟩, hab'⟩
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
    obtain ⟨b₁, _, h₁⟩ := hp₁
    obtain ⟨b₂, _, h₂⟩ := hp₂
    exact hne (Prod.mk.inj (h₁.trans h₂.symm)).1
  rw [hS, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_image_of_injective]
  exact fun b₁ b₂ h => (Prod.mk.inj h).2

theorem sum_pairs_le_offDiag {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B))
    (hE : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (X : Finset A) (Y : Finset B) :
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) ≤
      Y.card * (Y.card - 1) := by
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq₁ hq₂
    have hqne : q.1 ≠ q.2 := by tauto
    have h11 : (a₁, q.1) ∈ E := by tauto
    have h12 : (a₁, q.2) ∈ E := by tauto
    have h21 : (a₂, q.1) ∈ E := by tauto
    have h22 : (a₂, q.2) ∈ E := by tauto
    exact hE a₁ a₂ q.1 q.2 hne hqne ⟨h11, h12, h21, h22⟩
  have hsub : X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) ⊆ Y.offDiag := by
    rw [Finset.biUnion_subset]
    intro a _ q hq
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq ⊢
    tauto
  calc
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) =
      ∑ a ∈ X, ((Y.filter (fun b => (a, b) ∈ E)).offDiag).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (offDiag_card_eq (Y.filter (fun b => (a, b) ∈ E))).symm
    _ = (X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Y.offDiag.card := Finset.card_le_card hsub
    _ = Y.card * (Y.card - 1) := offDiag_card_eq Y

theorem c4sq : ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (E : Finset (A × B)), (∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → ∀ (X : Finset A) (Y : Finset B), (((X ×ˢ Y).filter (fun p => p ∈ E)).card) ^ 2 ≤ X.card * (((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1)) := by
  intro A B _ _ _ _ E hE X Y
  let N : A → Finset B := fun a => Y.filter (fun b => (a, b) ∈ E)
  have he : ((X ×ˢ Y).filter (fun p => p ∈ E)).card = ∑ a ∈ X, (N a).card :=
    card_filter_product_eq_sum E X Y
  have hpairs : ∑ a ∈ X, (N a).card * ((N a).card - 1) ≤ Y.card * (Y.card - 1) :=
    sum_pairs_le_offDiag E hE X Y
  have hsum_sq : ∑ a ∈ X, (N a).card ^ 2 ≤
      ((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1) := by
    calc
      ∑ a ∈ X, (N a).card ^ 2 = ∑ a ∈ X, ((N a).card + (N a).card * ((N a).card - 1)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact sq_eq_add_mul_pred _
      _ = (∑ a ∈ X, (N a).card) + ∑ a ∈ X, (N a).card * ((N a).card - 1) :=
        Finset.sum_add_distrib
      _ = ((X ×ˢ Y).filter (fun p => p ∈ E)).card +
          ∑ a ∈ X, (N a).card * ((N a).card - 1) := by rw [← he]
      _ ≤ ((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1) :=
        Nat.add_le_add (Nat.le_refl _) hpairs
  calc
    (((X ×ˢ Y).filter (fun p => p ∈ E)).card) ^ 2 = (∑ a ∈ X, (N a).card) ^ 2 := by rw [he]
    _ ≤ X.card * ∑ a ∈ X, (N a).card ^ 2 :=
      sq_sum_le_card_mul_sum_sq_nat X (fun a => (N a).card)
    _ ≤ X.card * (((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1)) :=
      Nat.mul_le_mul (Nat.le_refl _) hsum_sq

end Plane2974.Small

namespace Plane8311
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.TopForm

def pointSide {N : ℕ} (C : Circuit) (j : ℕ) (b : Fin 2) : Finset (Fin N) :=
  Finset.univ.filter fun p => W C {p} ∅ (opnd C j b)=true
def lineSide {N : ℕ} (C : Circuit) (j : ℕ) (b : Fin 2) : Finset (Fin N) :=
  Finset.univ.filter fun l => W C ∅ {l} (opnd C j (1-b))=true
def box {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) (j : ℕ) (b : Fin 2) :=
  ((pointSide C j b ×ˢ lineSide C j b).filter (fun e => e∈Flags S))

theorem widthBound {N : ℕ} (S : Fin N → Finset (Fin N))
    (unique : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (A B : Finset (Fin N)) (ha : A.card≤12) (hb : B.card≤11) :
    (((A ×ˢ B).filter (fun e => e∈Flags S)).card) ≤ 42 := by
  let e := ((A ×ˢ B).filter (fun x => x∈Flags S)).card
  have h := Plane2974.Small.c4sq (Fin N) (Fin N) (Flags S) (by
    intro p r l m pr lm rect
    rcases rect with ⟨pl,pm,rl,rm⟩
    simp only [Flags,Finset.mem_filter,Finset.mem_univ,true_and] at pl pm rl rm
    exact lm ((unique p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)) A B
  change e^2 ≤ A.card*(e+B.card*(B.card-1)) at h
  have degree : B.card*(B.card-1)≤110 := Nat.mul_le_mul hb (by omega : B.card-1≤10)
  have bound : e^2≤12*(e+110) := h.trans (Nat.mul_le_mul ha (Nat.add_le_add_left degree _))
  change e≤42
  by_contra! large
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show 43≤e by omega)
  rw [hz] at bound
  nlinarith

theorem boundedSides {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit)
    (unique : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (mon : Monotone2 C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, C.eval (incidenceInput X Y)=true → incidenceFun S X Y=true)
    (width : ∀ j<C.size, ¬ Safe S C j → ∀ b : Fin 2,
      (pointSide (N:=N) C j b).card≤12 ∧ (lineSide (N:=N) C j b).card≤11) : Guarded S C := by
  classical
  apply localPricing S C mon pos sound
  intro j hj
  by_cases safe : Safe S C j
  · have zero : badEdges S C j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact (Finset.mem_filter.mp he).2.2 safe
    simp [zero]
  have all (b : Fin 2) : (box S C j b).card≤42 :=
    widthBound S unique _ _ (width j hj safe b).1 (width j hj safe b).2
  have sub : badEdges S C j ⊆ box S C j 0 ∪ box S C j 1 := by
    intro e he
    obtain ⟨flag,real,_⟩ := Finset.mem_filter.mp he
    obtain ⟨b, hp,hl⟩ := real.2.2.2.2
    have inbox : e ∈ box S C j b := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩⟩,flag⟩
    fin_cases b
    · exact Finset.mem_union_left _ inbox
    · exact Finset.mem_union_right _ inbox
  have total := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have h0 := all 0
  have h1 := all 1
  omega

end Plane8311

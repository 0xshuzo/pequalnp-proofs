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

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ val C (point {w}) (n+p) = false := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
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
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
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
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
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
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2, hs3⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs,_⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := point_contains_edge hC he (u:=v) (v:=a₀) (by simp) (by simp [S]) ha₀
  have hZ : val C z C.output = true := point_contains_edge hC he (u:=w) (v:=b₀) (by simp) (by simp [S]) hb₀
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end GraphProof


namespace GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

end GraphProof
namespace Plane

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)


theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
    (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)
  symm := ⟨by
    rintro u v ⟨p,l,h,hp,hl⟩
    exact ⟨p,l,h,hp.symm,hl.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨p,l,h,hp,hl⟩
    exact left_ne_right p l ((hp.elim id id).trans (hl.elim id id).symm)⟩

theorem adj_ll {N : ℕ} (I : Fin N → Fin N → Prop) (p r : Fin N) :
    ¬ (graph I).Adj (Fin.castAdd N p) (Fin.castAdd N r) := by
  rintro ⟨a,b,_,_,h⟩
  exact h.elim (fun he => left_ne_right p b he.symm) (fun he => left_ne_right r b he.symm)

theorem adj_rr {N : ℕ} (I : Fin N → Fin N → Prop) (l m : Fin N) :
    ¬ (graph I).Adj (Fin.natAdd N l) (Fin.natAdd N m) := by
  rintro ⟨a,b,_,h,_⟩
  exact h.elim (left_ne_right a l) (left_ne_right a m)

theorem adj_lr {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hp := Fin.castAdd_inj.mp (ha.resolve_right (left_ne_right a l))
    have hl := (Fin.natAdd_inj N).mp (hb.resolve_left (left_ne_right p b).symm)
    simpa [hp,hl] using hab
  · intro hi
    exact ⟨p,l,hi,Or.inl rfl,Or.inr rfl⟩

theorem adj_rl {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    (graph I).Adj (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l :=
  ((graph I).adj_comm _ _).trans (adj_lr I p l)

theorem no_square {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (uv : u ≠ v) (ab : a ≠ b)
    (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
    (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
  have rect {p r l m : Fin N} (pr : p ≠ r) (lm : l ≠ m)
      (pl : I p l) (rl : I r l) (pm : I p m) (rm : I r m) : False :=
    lm ((hu p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp_all only [adj_ll,adj_rr,adj_lr,adj_rl]
  all_goals first
    | exact rect (fun e => uv (congrArg (Fin.castAdd N) e)) (fun e => ab (congrArg (Fin.natAdd N) e)) ua va ub vb
    | exact rect (fun e => ab (congrArg (Fin.castAdd N) e)) (fun e => uv (congrArg (Fin.natAdd N) e)) ua ub va vb

end Plane
namespace Extra

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Plane2974.GraphProof Plane2974.Plane
open Relation

lemma trace_split_branch {n : ℕ} {C : Circuit} {w : Fin n} {x m1 m2 : ℕ}
    (Q1 : Trace n C (Carries C w) x m1) (Q2 : Trace n C (Carries C w) x m2)
    (hne : m1 ≠ m2) (h1 : ¬ Carries C w m1) (h2 : ¬ Carries C w m2) :
    ∃ z, x ≤ z ∧ Live n C z ∧ Carries C w z ∧ Branch n C z := by
  induction Q1 using ReflTransGen.head_induction_on with
  | refl =>
    rcases Q2.cases_head with heq | ⟨y, hstep, _⟩
    · exact (hne heq).elim
    · exact (h1 hstep.1).elim
  | @head a b hab Q1' ih =>
    rcases Q2.cases_head with heq | ⟨c, hac, Q2'⟩
    · subst heq
      exact (h2 hab.1).elim
    · by_cases hbc : b = c
      · subst hbc
        obtain ⟨z, hzle, hzlive, hzc, hzb⟩ := ih Q2'
        exact ⟨z, hab.2.1.1.le.trans hzle, hzlive, hzc, hzb⟩
      · refine ⟨a, le_rfl, live_before hab.2.1 hab.2.2, hab.1, ?_⟩
        unfold Branch
        have hsub : ({b, c} : Finset ℕ) ⊆ readers n C a := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact mem_readers.mpr hab.2
          · exact mem_readers.mpr hac.2
        have hc2 : ({b, c} : Finset ℕ).card = 2 := Finset.card_pair hbc
        exact hc2 ▸ Finset.card_le_card hsub

end Extra
namespace Charge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Plane2974.GraphProof Plane2974.Extra
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
theorem budget (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card+B.card ≤ C.gates.length+1
  omega


lemma strict_budget {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    (h3 : ∃ b ∈ living n C, Branch n C b ∧ 3 ≤ (readers n C b).card) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  obtain ⟨b0, hb0W, hb0_br, hb0_3⟩ := h3
  have hb0B : b0 ∈ B := Finset.mem_filter.mpr ⟨hb0W, hb0_br⟩
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a - n)
    · intro a ha
      have h : a < n + C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a - n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a - n = b - n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hb0_ne : b0 ≠ C.output := fun h => hoNone (h ▸ (Finset.mem_filter.mp hb0B).2)
  have hlow : R.card + B.card + 1 ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) = R.card := by
      calc _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) :=
            Finset.sum_congr rfl (fun a _ => by by_cases h : a = C.output <;> simp [h])
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]; simp [B]
    have hb0W' : b0 ∈ W := hb0W
    have e1 : (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_ite_eq', ite_eq_left hb0W']
    calc R.card + B.card + 1
      _ = (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) +
          (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) +
          (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) := by rw [eR, eB, e1]
      _ = ∑ a ∈ W, ((if a = C.output then 0 else 1) + (if Branch n C a then 1 else 0) + (if a = b0 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ ≤ ∑ a ∈ W, (readers n C a).card := by
        apply Finset.sum_le_sum
        intro a ha
        have hl := (mem_living.1 ha).2
        by_cases hab0 : a = b0
        · subst hab0
          have hbr : Branch n C a := (Finset.mem_filter.mp hb0B).2
          simp only [hb0_ne, ↓reduceIte, hbr]
          omega
        · by_cases heq : a = C.output
          · subst a; simp [hoNone, hab0]
          · by_cases hb : Branch n C a
            · have hb' : 2 ≤ (readers n C a).card := hb
              simpa [heq, hb, hab0] using hb'
            · simpa [heq, hb, hab0] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm : (∑ a ∈ W, (readers n C a).card) =
      ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2 * S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2 * S.card := by
      simp [S, Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card + B.card ≤ C.gates.length
  omega


theorem injective_on (hC : Monotone2 C) (he : GraphEval C G)
    {v w : Fin n} (htwins : v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]


set_option maxHeartbeats 4000000 in
theorem strict_cover
    (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (other : ∀ v ∈ X, ∀ w, ∃ u, G.Adj v u ∧ u ≠ w)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (eval : GraphEval C G) :
    ∃ S ⊆ X, (∀ v w, G.Adj v w → v ∈ S ∨ w ∈ S) ∧
      X.card + S.card ≤ C.size + 1 ∧
      (X.card + S.card ≤ C.size ∨ ∀ w ∈ S, ∀ v1 v2 v3,
        v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
        G.Adj w v1 → G.Adj w v2 → G.Adj w v3 → v1 ∈ S ∨ v2 ∈ S ∨ v3 ∈ S) := by
  classical
  let S := X.filter (Eligible C)
  have hS (v) : v ∈ S ↔ v ∈ X ∧ Eligible C v := by simp [S]
  have degree (v) (hv : v ∈ X) : ∃ w, G.Adj v w := by
    obtain ⟨w,hw,_⟩ := other v hv v
    exact ⟨w,hw⟩
  have twins (v) (hv : v ∈ X) (w) (ne : v ≠ w) (_ : ¬G.Adj v w) :
      ∃ u, ¬(G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a,va⟩ := degree v hv
    obtain ⟨b,vb,ba⟩ := other v hv a
    by_cases wa : G.Adj w a
    · by_cases wb : G.Adj w b
      · exact (square v w a b ne ba.symm va vb wa wb).elim
      · exact ⟨b,fun h => wb (h.mp vb)⟩
    · exact ⟨a,fun h => wa (h.mp va)⟩
  have hits (v w) (vw : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨a,va,aw⟩ := other v (inX vw) w
    obtain ⟨b,wb,bv⟩ := other w (inX vw.symm) v
    have ab : ¬G.Adj a b := fun e => square v b w a bv.symm aw.symm vw va wb.symm e.symm
    exact (covers_edge hC eval vw va aw wb bv (Or.inr ab)).imp
      (fun h => (hS v).mpr ⟨inX vw,h⟩) (fun h => (hS w).mpr ⟨inX vw.symm,h⟩)
  obtain ⟨a0,b0,ab0⟩ := edge
  have hlt_out := (edge_at_output eval ab0).2
  have houtput : C.output ∈ living n C := mem_living.mpr ⟨hlt_out,ReflTransGen.refl⟩
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f, hu]
  have hf_maps : ∀ u ∈ S, f u ∈ B := by
    intro u hu
    have hs := ((hS u).mp hu).2
    have hb := firstBranch_spec u hs
    have hw := (next_le hb.1).trans_lt hlt_out
    rw [hf u hs]
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw, hb.1⟩, hb.2.2⟩
  have hf_inj : Set.InjOn f S := by
    intro u hu v hv same
    have hsu := ((hS u).mp hu).2
    have hsv := ((hS v).mp hv).2
    rw [hf u hsu, hf v hsv] at same
    exact injective_on hC eval (twins u ((hS u).mp hu).1 v) hsu hsv same
  have hcap : S.card ≤ B.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hbud_raw := budget hC eval X degree houtput
  have hB_card_eq : B.card = (open Classical in ((living n C).filter (Branch n C)).card) := by
    congr 1
  have hbud : X.card + B.card ≤ C.size + 1 := by rw [hB_card_eq]; exact hbud_raw
  refine ⟨S,Finset.filter_subset _ _,hits,by omega,?_⟩
  by_cases good : X.card + S.card ≤ C.size
  · exact Or.inl good
  apply Or.inr
  intro w hwS v1 v2 v3 h12 h13 h23 hw1 hw2 hw3
  by_contra! no
  obtain ⟨hv1,hv2,hv3⟩ := no
  have hBE : B.card = S.card := by omega
  have hB_img : S.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hf_maps u hu
    · rw [Finset.card_image_of_injOn hf_inj, hBE]
  have hB_deg2 : ∀ b ∈ B, (readers n C b).card = 2 := by
    intro b hb
    have hge2 : 2 ≤ (readers n C b).card := (Finset.mem_filter.mp hb).2
    by_contra hne2
    have hge3 : 3 ≤ (readers n C b).card := by omega
    have hstr_raw := strict_budget hC eval X degree houtput
      ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hge3⟩
    have hstr : X.card + B.card ≤ C.size := by rw [hB_card_eq]; exact hstr_raw
    omega
  have hwEl : Eligible C w := ((hS w).mp hwS).2
  have hmeet : ∀ v : Fin n, G.Adj w v →
      ∃ m a b g, C.gates[m - n]? = some g ∧ n ≤ m ∧
        LNext n C a m ∧ LNext n C b m ∧
        Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ ¬ Carries C w m := by
    intro v hwv
    obtain ⟨p, g, a, b, hg, _, _, ha, hb, hva, hwa, hwb, hvb, h2, hwm⟩ := meeting_gate hC eval (G.adj_symm hwv)
    refine ⟨n + p, a, b, g, by simpa using hg, by omega, ha, hb, hva, hwa, hwb, hvb, h2, ?_⟩
    rw [carries_iff hC]
    simp [hwm]
  obtain ⟨m1, a1, b1, g1, hg1, hm1ge, ha1, hb1, hv1a1, hwa1, hwb1, _, h2g1, hwm1⟩ := hmeet v1 hw1
  obtain ⟨m2, a2, b2, g2, hg2, hm2ge, ha2, hb2, hv2a2, hwa2, hwb2, _, h2g2, hwm2⟩ := hmeet v2 hw2
  obtain ⟨m3, a3, b3, g3, hg3, hm3ge, ha3, hb3, hv3a3, hwa3, hwb3, _, h2g3, hwm3⟩ := hmeet v3 hw3
  have hm_ne : ∀ (u1 u2 : Fin n) (m a b c : ℕ) (g : Gate),
      u1 ∉ S → u1 ≠ u2 → G.Adj w u1 → G.Adj w u2 →
      C.gates[m - n]? = some g → n ≤ m →
      LNext n C a m → LNext n C c m →
      Carries C u1 a → ¬ Carries C w a → Carries C w b →
      Carries C u2 c → ¬ Carries C w c →
      (∀ i ∈ g.inputs, i = a ∨ i = b) → False := by
    intro u1 u2 m a b c g u1out hu12 hwu1 hwu2 hgm hmge ham hcm hu1a hwa hwb hu2c hwc h2g
    have hc_in : c ∈ g.inputs := by
      obtain ⟨⟨_, p', g', hg', hm', hmem⟩, _⟩ := hcm
      have hp' : p' = m - n := by omega
      subst hp'
      rw [hgm] at hg'; cases hg'
      exact hmem
    have hca : c = a := by
      rcases h2g c hc_in with rfl | rfl
      · rfl
      · exact (hwc hwb).elim
    rw [hca] at hu2c
    have hu1_not : ¬ Eligible C u1 := fun h => u1out ((hS u1).mpr ⟨inX hwu1.symm,h⟩)
    obtain ⟨w', hu1w', hw'ne⟩ := other u1 (inX hwu1.symm) w
    have hnot_u2w' : ¬ G.Adj u2 w' := fun h =>
      square u1 u2 w w' hu12 hw'ne.symm hwu1.symm hu1w' hwu2.symm h
    let x := point ({u2, w'} : Finset (Fin n))
    let y := point (insert u1 ({u2, w'} : Finset (Fin n)))
    have hax : val C x a = true :=
      acts_mono hC (point_mono (by simp)) a ((carries_iff hC).mp hu2c).1
    have hay : val C y a = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) a hax
    have hpath := singleton_path (live_before ham.1 ham.2) hu1a
    have huniq : ∀ k j j', k < a → Carries C u1 k → LNext n C k j → LNext n C k j' → j = j' :=
      fun k j j' _ => no_eligible_unique hu1_not k j j'
    have hxy_out : val C x C.output = val C y C.output := by
      by_contra hdiff
      rcases influence hpath huniq (fun _ hi => (point_insert hi).symm) ReflTransGen.refl hdiff with bad | bad
      · exact (Nat.not_lt_of_ge (next_le (live_before ham.1 ham.2))) bad.1
      · exact bad.2 (hax.trans hay.symm)
    have hx0 : val C x C.output = false := point_pair_quiet eval hnot_u2w'
    have hy1 : val C y C.output = true := point_contains_edge hC eval (u := u1) (v := w')
      (by simp) (by simp) hu1w'
    exact Bool.false_ne_true (hx0.symm.trans (hxy_out.trans hy1))
  have hm12 : m1 ≠ m2 := fun h => hm_ne v1 v2 m1 a1 b1 a2 g1 hv1 h12 hw1 hw2 hg1 hm1ge ha1 (h ▸ ha2) hv1a1 hwa1 hwb1 hv2a2 hwa2 h2g1
  have hm13 : m1 ≠ m3 := fun h => hm_ne v1 v3 m1 a1 b1 a3 g1 hv1 h13 hw1 hw3 hg1 hm1ge ha1 (h ▸ ha3) hv1a1 hwa1 hwb1 hv3a3 hwa3 h2g1
  have hm23 : m2 ≠ m3 := fun h => hm_ne v2 v3 m2 a2 b2 a3 g2 hv2 h23 hw2 hw3 hg2 hm2ge ha2 (h ▸ ha3) hv2a2 hwa2 hwb2 hv3a3 hwa3 h2g2
  let bw := firstBranch C w hwEl
  have hbw_spec := firstBranch_spec w hwEl
  have hbw_path : Trace n C (Carries C w) w.val bw := singleton_path hbw_spec.1 hbw_spec.2.1
  have hstep_from_bw : ∀ (m b : ℕ), LNext n C b m → Carries C w b → ¬ Carries C w m →
      ∃ r ∈ readers n C bw, Trace n C (Carries C w) r m := by
    intro m b hbm hwb hwm
    have hPm : Trace n C (Carries C w) w.val m :=
      (singleton_path (live_before hbm.1 hbm.2) hwb).tail ⟨hwb, hbm⟩
    rcases align hbw_path (firstBranch_unique w hwEl) m hPm with bad | htail
    · exact (hwm bad.2).elim
    · rcases htail.cases_head with heq | ⟨r, hr, hrest⟩
      · exact (hwm (heq ▸ hbw_spec.2.1)).elim
      · exact ⟨r, mem_readers.mpr hr.2, hrest⟩
  obtain ⟨r1, hr1, hQ1⟩ := hstep_from_bw m1 b1 hb1 hwb1 hwm1
  obtain ⟨r2, hr2, hQ2⟩ := hstep_from_bw m2 b2 hb2 hwb2 hwm2
  obtain ⟨r3, hr3, hQ3⟩ := hstep_from_bw m3 b3 hb3 hwb3 hwm3
  have hbwB : bw ∈ B := by
    have h1 := hf_maps w hwS
    rwa [hf w hwEl] at h1
  have hcard2 : (readers n C bw).card = 2 := hB_deg2 bw hbwB
  have hpig : r1 = r2 ∨ r1 = r3 ∨ r2 = r3 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h12', h13', h23'⟩ := hnot
    have hsub : ({r1, r2, r3} : Finset ℕ) ⊆ readers n C bw := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({r1, r2, r3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12', h13']), Finset.card_pair h23']
    have hle := Finset.card_le_card hsub
    omega
  have hget_z : ∃ z, bw < z ∧ Live n C z ∧ Carries C w z ∧ Branch n C z := by
    rcases hpig with heq | heq | heq
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ2 hm12 hwm1 hwm2
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ3 hm13 hwm1 hwm3
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ2 hQ3 hm23 hwm2 hwm3
      exact ⟨z, (mem_readers.mp hr2).1.1.trans_le hzle, hzl, hzc, hzb⟩
  obtain ⟨z, hbw_lt_z, hzlive, hzcw, hzb⟩ := hget_z
  have hzB : z ∈ B :=
    Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hzlive).trans_lt hlt_out, hzlive⟩, hzb⟩
  rw [← hB_img] at hzB
  obtain ⟨u, huS, hfu⟩ := Finset.mem_image.mp hzB
  have huEl : Eligible C u := ((hS u).mp huS).2
  rw [hf u huEl] at hfu
  have huw_ne : u ≠ w := by
    intro h; subst h
    have : firstBranch C u huEl = bw := rfl
    omega
  obtain ⟨a, hua⟩ := degree u ((hS u).mp huS).1
  obtain ⟨b, hub, hba⟩ := other u ((hS u).mp huS).1 a
  have hex_vprime : ∃ v', G.Adj u v' ∧ ¬ G.Adj w v' := by
    by_cases hwa : G.Adj w a
    · by_cases hwb : G.Adj w b
      · exact (square u w a b huw_ne hba.symm hua hub hwa hwb).elim
      · exact ⟨b, hub, hwb⟩
    · exact ⟨a, hua, hwa⟩
  obtain ⟨v', huv', hnot_wv'⟩ := hex_vprime
  have hzw : val C (point {w}) z = true := ((carries_iff hC).mp hzcw).1
  have hz1 : val C (point ({w, v'} : Finset (Fin n))) z = true :=
    acts_mono hC (point_mono (by simp)) z hzw
  have hz2 : val C (point (insert u ({w, v'} : Finset (Fin n)))) z = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) z hz1
  have heq_out := value_at_branch huEl
    (x := point ({w, v'} : Finset (Fin n)))
    (y := point (insert u ({w, v'} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm)
    (by rw [hfu, hz1, hz2])
  have hx0 : val C (point ({w, v'} : Finset (Fin n))) C.output = false :=
    point_pair_quiet eval hnot_wv'
  have hy1 : val C (point (insert u ({w, v'} : Finset (Fin n)))) C.output = true :=
    point_contains_edge hC eval (u := u) (v := v') (by simp) (by simp) huv'
  exact Bool.false_ne_true (hx0.symm.trans (heq_out.trans hy1))

end Charge

namespace Charge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Plane2974.GraphProof

theorem sparse_charge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (deg : ∀ v ∈ X, 3 ≤ (G.neighborSet v).ncard)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (eval : GraphEval C G) :
    ∃ S ⊆ X, (∀ v w, G.Adj v w → v ∈ S ∨ w ∈ S) ∧
      X.card + S.card ≤ C.size + 1 ∧
      (X.card + S.card ≤ C.size ∨ X.card < 2*S.card) := by
  classical
  have other (v) (hv : v ∈ X) (w) : ∃ u, G.Adj v u ∧ u ≠ w := by
    have size := deg v hv
    rw [Set.ncard_eq_toFinset_card'] at size
    by_contra! bad
    have sub : (G.neighborSet v).toFinset ⊆ {w} := by
      intro u hu
      exact Finset.mem_singleton.mpr (bad u (by simpa using hu))
    have h := Finset.card_le_card sub
    simp only [Finset.card_singleton] at h
    omega
  obtain ⟨S,sX,hit,base,rest⟩ := strict_cover G C X inX other square edge hC eval
  refine ⟨S,sX,hit,base,?_⟩
  rcases rest with done | two
  · exact Or.inl done
  right
  let Y := X \ S
  have lo (v) (vy : v ∈ Y) : 3 ≤ (S.filter fun w => G.Adj v w).card := by
    have sub : (G.neighborSet v).toFinset ⊆ S.filter fun w => G.Adj v w := by
      intro w hw
      have vw : G.Adj v w := by simpa using hw
      exact Finset.mem_filter.mpr ⟨(hit v w vw).resolve_left (Finset.mem_sdiff.mp vy).2,vw⟩
    have size := deg v (Finset.mem_sdiff.mp vy).1
    rw [Set.ncard_eq_toFinset_card'] at size
    exact size.trans (Finset.card_le_card sub)
  have hi (w) (ws : w ∈ S) : (Y.filter fun v => G.Adj w v).card ≤ 2 := by
    let D := Y.filter fun v => G.Adj w v
    by_contra! bad
    change 2 < D.card at bad
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu]; omega : 0 < (D.erase u).card)
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hv,Finset.card_erase_of_mem hu]; omega : 0 < ((D.erase u).erase v).card)
    obtain ⟨vu,vd⟩ := Finset.mem_erase.mp hv
    obtain ⟨zv,zu'⟩ := Finset.mem_erase.mp hz
    obtain ⟨zu,zd⟩ := Finset.mem_erase.mp zu'
    have meet := two w ws u v z vu.symm zu.symm zv.symm (Finset.mem_filter.mp hu).2
      (Finset.mem_filter.mp vd).2 (Finset.mem_filter.mp zd).2
    rcases meet with m|m|m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2 m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp vd).1).2 m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp zd).1).2 m
  have swap : (∑ v ∈ Y, (S.filter fun w => G.Adj v w).card) =
      ∑ w ∈ S, (Y.filter fun v => G.Adj w v).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro v _
    by_cases e : G.Adj v w
    · simp [e,e.symm]
    · have e' : ¬G.Adj w v := fun f => e f.symm
      simp [e,e']
  have D := (Finset.sum_le_sum lo).trans (swap.le.trans (Finset.sum_le_sum hi))
  simp only [Finset.sum_const,smul_eq_mul] at D
  have part := Finset.card_sdiff_add_card_eq_card sX
  change Y.card + S.card = X.card at part
  obtain ⟨a,b,ab⟩ := edge
  have pos := Finset.card_pos.mpr ⟨a,inX ab⟩
  omega

end Charge
end Plane2974

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

open PEqualNP.CircuitLowerBounds

theorem arith (a b s e : ℕ) (hs : s ≤ 4512) (hab : a + b ≤ s + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    (he : e ^ 2 ≤ a * (e + b * (b - 1))) : e ≤ 24 * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hc : 1 + c - 1 = c := by omega
  rw [hc] at he
  have h0 : 24 * (1 + c + d + c + 1) ≤ e + 23 := by omega
  zify at he h0 hab hs
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hlim : 2 * (1 + (c : ℤ)) + d ≤ 4513 := by linarith
  set B : ℤ := 1 + c with hB
  have hB1 : 1 ≤ B := by linarith
  have hcB : (c : ℤ) = B - 1 := by linarith
  rw [hcB] at he h0
  have h1 : 48 * B + 24 * d - 23 ≤ (e : ℤ) := by linarith
  have h2 : (48 * B + 24 * d - 23) * (47 * B + 23 * d - 23) ≤ (e : ℤ) * (e - (B + d)) := by
    have p1 : 0 ≤ 48 * B + 24 * (d : ℤ) - 23 := by linarith
    have p2 : 0 ≤ 47 * B + 23 * (d : ℤ) - 23 := by linarith
    exact mul_le_mul h1 (by linarith) p2 (by linarith)
  have h3 : (48 * B + 24 * d - 23) * (47 * B + 23 * d - 23) ≤ (B + d) * (B * (B - 1)) := by
    nlinarith [he, h2]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    push_cast at h3 hlim
    have hB2 : B ≤ 2256 := by linarith
    have k1 : 0 ≤ (B - 1) * (2256 - B) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ B * ((B - 1) * (2256 - B)) := mul_nonneg (by linarith) k1
    nlinarith [h3, k2]
  · have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hB2 : B ≤ 2256 := by linarith
    have k1 : 0 ≤ B * (B * (4513 - 2 * B - d)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k2 : 0 ≤ B * ((d - 1) * (2256 - B)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k3 : 0 ≤ (d - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have k4 : 0 ≤ (B - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h3, k1, k2, k3, k4]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dep (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ S : Finset ℕ, S.card ≤ gs.length + T.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ t ∈ T, (run gs x).getD t false = (run gs y).getD t false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun T => ⟨T, by simp, fun x y _ _ h t ht => by simpa [run] using h t ht⟩
  | append_singleton gs g ih =>
    intro T
    have ih' := ih (fun g' h' => hg g' (by simp [h']))
    have hlen := hg g (by simp)
    by_cases hk : n + gs.length ∈ T
    · obtain ⟨S, hS, hdet⟩ := ih' (T.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, ?_⟩
      · have h1 := Finset.card_union_le (T.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one hk
        have h3 := List.toFinset_card_le g.inputs
        rw [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy t ht
        have hd := hdet x y hx hy hxy
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy]
        by_cases htk : t = n + gs.length
        · rw [if_pos htk, if_pos htk]
          congr 1
          exact List.map_congr_left fun i hi => hd i (by simp [hi])
        · rw [if_neg htk, if_neg htk]
          exact hd t (by simp [htk, ht])
    · obtain ⟨S, hS, hdet⟩ := ih' T
      refine ⟨S, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · intro x y hx hy hxy t ht
        have htk : t ≠ n + gs.length := fun h => hk (h ▸ ht)
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy,
          if_neg htk, if_neg htk]
        exact hdet x y hx hy hxy t ht

variable {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def Acc (C : Circuit) : Finset (Fin N × Fin N) :=
  {x8 : Fin N × Fin N | I x8.1 x8.2 ∧
    (PEqualNP.MetaComplexity.circuitFun (N + N) C fun (x9 : Fin (N + N)) =>
      decide (x9 = Fin.castAdd N x8.1 ∨ x9 = Fin.natAdd N x8.2)) = true}

def Snd (q : ℕ) (C : Circuit) : Prop := ∀ (x9 : Fin (N + N) → Bool),
  Fintype.card { x10 : Fin N // x9 (Fin.natAdd N x10) = true } ≤ q →
  (¬ ∃ (x11 : Fin N) (x12 : Fin N), I x11 x12 ∧ x9 (Fin.castAdd N x11) = true ∧
    x9 (Fin.natAdd N x12) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C x9 = false

theorem single_false {C : Circuit} (hq : 1 ≤ q) (hS : Snd I q C) (v : Fin (N + N)) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C (fun x => decide (x = v)) = false := by
  refine hS _ ?_ ?_
  · refine le_trans ?_ hq
    rw [Fintype.card_subtype]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have h1 := of_decide_eq_true (Finset.mem_filter.1 ha).2
    have h2 := of_decide_eq_true (Finset.mem_filter.1 hb).2
    have h3 := congrArg Fin.val (h1.trans h2.symm)
    simp at h3
    exact Fin.ext h3
  · rintro ⟨a, b, -, ha, hb⟩
    have h3 := congrArg Fin.val ((of_decide_eq_true ha).trans (of_decide_eq_true hb).symm)
    simp at h3
    have := a.2
    omega

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (v : Fin n) : (List.ofFn f).getD v false = f v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem main (hq : 1 ≤ q) (hI : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hS : Snd I q C) (hsz : C.size ≤ 4512) :
    (Acc I C).card ≤ 24 * C.size := by
  classical
  obtain ⟨S, hScard, hdet⟩ := dep (N + N) C.gates hlen {C.output}
  have hfun : ∀ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x =
      (run C.gates (List.ofFn x)).getD C.output false := fun x => rfl
  have agree : ∀ x y : Fin (N + N) → Bool, (∀ v : Fin (N + N), (v : ℕ) ∈ S → x v = y v) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x =
        PEqualNP.MetaComplexity.circuitFun (N + N) C y := by
    intro x y h
    rw [hfun, hfun]
    refine hdet _ _ (by simp) (by simp) (fun i hi => ?_) _ (by simp)
    by_cases hin : i < N + N
    · rw [ofFn_getD x ⟨i, hin⟩, ofFn_getD y ⟨i, hin⟩]
      exact h ⟨i, hin⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  set X : Finset (Fin N) := Finset.univ.filter fun p => (p : ℕ) ∈ S with hX
  set Y : Finset (Fin N) := Finset.univ.filter fun l => N + (l : ℕ) ∈ S with hY
  have hXY : X.card + Y.card ≤ C.size + 1 := by
    have e1 : (X.image fun p : Fin N => (p : ℕ)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have e2 : (Y.image fun l : Fin N => N + (l : ℕ)).card = Y.card :=
      Finset.card_image_of_injective _ fun a b h => Fin.ext (by simpa using h)
    have hdis : Disjoint (X.image fun p : Fin N => (p : ℕ)) (Y.image fun l : Fin N => N + (l : ℕ)) := by
      rw [Finset.disjoint_left]
      rintro i hi hj
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨l, -, h⟩ := Finset.mem_image.1 hj
      have := p.2
      omega
    have hsub : (X.image fun p : Fin N => (p : ℕ)) ∪ (Y.image fun l : Fin N => N + (l : ℕ)) ⊆ S := by
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hp).2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hl).2
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, e1, e2] at h
    simp only [Finset.card_singleton] at hScard
    exact h.trans hScard
  have hmem : ∀ e ∈ Acc I C, e.1 ∈ X ∧ e.2 ∈ Y := by
    intro e he
    obtain ⟨-, -, ht⟩ := Finset.mem_filter.1 he
    constructor
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.natAdd N e.2)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.castAdd N e.1 := fun hc => hn (by rw [hc] at hv; simpa using hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_left hne, Or.inr⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.castAdd N e.1)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.natAdd N e.2 := fun hc => hn (by rw [hc] at hv; exact hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_right hne, Or.inl⟩
  have hc4 : ∀ a a' : Fin N, ∀ b b' : Fin N, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ Acc I C ∧ (a, b') ∈ Acc I C ∧ (a', b) ∈ Acc I C ∧ (a', b') ∈ Acc I C) := by
    rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
    have g1 := (Finset.mem_filter.1 h1).2.1
    have g2 := (Finset.mem_filter.1 h2).2.1
    have g3 := (Finset.mem_filter.1 h3).2.1
    have g4 := (Finset.mem_filter.1 h4).2.1
    exact hb ((hI a a' ha).unique ⟨g1, g3⟩ ⟨g2, g4⟩)
  rcases (Acc I C).eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he]; simp
  have hXp : 1 ≤ X.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).1⟩
  have hYp : 1 ≤ Y.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).2⟩
  have f1 : ((X ×ˢ Y).filter fun p => p ∈ Acc I C) = Acc I C := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => h.2, fun h => ⟨hmem p h, h⟩⟩
  rcases le_total Y.card X.card with hle | hle
  · have h := c4sq (Fin N) (Fin N) (Acc I C) hc4 X Y
    rw [f1] at h
    exact arith X.card Y.card C.size _ hsz hXY hYp hle h
  · have h := c4sq (Fin N) (Fin N) ((Acc I C).image Prod.swap) (by
      rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
      have sw : ∀ p q : Fin N, (p, q) ∈ (Acc I C).image Prod.swap → (q, p) ∈ Acc I C := by
        intro p q h
        obtain ⟨r, hr, hrs⟩ := Finset.mem_image.1 h
        have : r = (q, p) := by rw [← Prod.swap_swap r, hrs]; rfl
        rwa [← this]
      exact hc4 b b' a a' hb ha ⟨sw _ _ h1, sw _ _ h3, sw _ _ h2, sw _ _ h4⟩) Y X
    have f2 : ((Y ×ˢ X).filter fun p => p ∈ (Acc I C).image Prod.swap) =
        (Acc I C).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hmem r hr).2, (hmem r hr).1⟩
    rw [f2, Finset.card_image_of_injective _ Prod.swap_injective] at h
    exact arith Y.card X.card C.size _ hsz (by omega) hXp hle h

end Plane2974.Small

namespace Plane2974.Dom

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega

theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)


def PairCorrect (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ u v, val D (sem_two u v) (outW n D) = true ↔ G u v

theorem sem_supp_out (hG : sem_Gr G) (hC : PairCorrect G D) : supp n D (outW n D) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  apply hG.2.1 v
  apply (hC v v).mp
  have same : sem_two v v = single v := by funext i; simp [sem_two,single]
  rw [same]
  exact mem_supp.mp hv

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])

  have h3 : val D (sem_ins v (sem_two u z)) (outW n D) = true := by
    apply val_mono hS (sem_two v z) _ _ _ ((hC v z).mpr hvz)
    intro i hi
    simp only [sem_two,sem_ins,Bool.or_eq_true,decide_eq_true_eq] at hi ⊢
    tauto
  rw [← hout] at h3
  exact huz ((hC u z).mp h3)

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : PairCorrect G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC u v).2 huv, by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : PairCorrect G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

end SemCore

section K4Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : PairCorrect G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

end K4Generic

theorem pair_neighbor_bound {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (correct : PairCorrect G D)
    (T B : Finset (Fin n)) (covered : ∀ v ∈ B, ∃ t ∈ T, G v t) :
    n + B.card ≤ D.length + 1 + 2*T.card := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hG h.1 correct
  obtain ⟨pos,hpos⟩ := k4_assigned hG h correct
  let J := B ∩ ineligSet n D
  obtain ⟨hs,hcard⟩ := k4_exits_ge hpos T J (fun i hi =>
    ⟨(Finset.mem_inter.mp hi).2,covered i (Finset.mem_inter.mp hi).1⟩)
  have hJ := Finset.card_le_card hs
  rw [hcard] at hJ
  have hflow := carrier_flow_union h T (by rw [sem_supp_out hG correct]; simp)
  have hsur := surplus_carrierT_le h.1 b hb T
  have hsum := surplus_identity h
  have htotal := Bplus_le_total n D
  have included : B ⊆ J ∪ eligSet n D := by
    intro i hi
    by_cases e : i ∈ eligSet n D
    · exact Finset.mem_union_right _ e
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi,sem_mem_inelig.mpr e⟩)
  have hB := (Finset.card_le_card included).trans (Finset.card_union_le _ _)
  have hT : (T ∩ eligSet n D).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
  omega

end Plane2974.Dom

namespace Plane2974.Dom
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def extend {n m : ℕ} (r : Fin n → Option (Fin m)) (x : Fin m → Bool) (i : Fin n) : Bool :=
  match r i with
  | none => false
  | some v => x v

theorem compressed {m n : ℕ} (r : Fin n → Option (Fin m)) (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin m → Bool, circuitFun n C (extend r x) ≠ b)
    (hnp : ∀ i : Fin m, ∃ x : Fin m → Bool, circuitFun n C (extend r x) ≠ x i)
    (hess : ∀ i : Fin m, ∃ x y : Fin m → Bool, (∀ k, k ≠ i → x k = y k) ∧
      circuitFun n C (extend r x) ≠ circuitFun n C (extend r y)) :
    ∃ D : Dag, StrictLive m D ∧ D.length ≤ C.size ∧
      ∀ x : Fin m → Bool, val D x (outW m D) = circuitFun n C (extend r x) := by
  let refs : List Ref := List.ofFn fun i : Fin n =>
    match r i with
    | none => Sum.inl false
    | some v => Sum.inr v.val
  have h0 : na_Good m (refs, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun t ht => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    cases eq : r i with
    | none => simp [na_ok,eq]
    | some v => simpa [na_ok,eq] using v.isLt
  have evaluate (x : Fin m → Bool) :
      refs.map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn (extend r x) := by
    apply List.ext_getElem
    · simp [refs]
    · intro i hi hj
      have hin : i < n := by simpa [refs] using hi
      simp only [refs,List.getElem_map,List.getElem_ofFn]
      cases eq : r ⟨i,hin⟩ with
      | none => simp [eq,refVal,extend]
      | some v => simp [eq,refVal,wl,extend,List.getD_eq_getElem?_getD]
  obtain ⟨⟨hS,hok⟩, hlen, hsem⟩ := na_fold_spec m C.gates hmono _ h0
  generalize C.gates.foldl (na_step m) (refs, ([] : Dag)) = st at hS hok hlen hsem
  obtain ⟨ls,D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev (x : Fin m → Bool) :
      circuitFun n C (extend r x) = refVal (wl D (List.ofFn x)) (na_look ls C.output) := by
    rw [na_look_val,hsem x (List.ofFn (extend r x)) (evaluate x)]
    rfl
  have hk := na_look_ok _ ls hok C.output
  rcases hr : na_look ls C.output with b|k
  · obtain ⟨x,hx⟩ := hnc b
    exfalso
    apply hx
    rw [hev x,hr]
    rfl
  · rw [hr] at hk
    have bound : k < m + D.length := hk
    by_cases input : k < m
    · obtain ⟨x,hx⟩ := hnp ⟨k,input⟩
      exfalso
      apply hx
      rw [hev x,hr]
      exact val_input D x k input
    · have hl : (D.take (k-m+1)).length = k-m+1 := by rw [List.length_take]; omega
      obtain ⟨D',good,small,sem⟩ := exists_strictLive_of_strict
        (fun x => circuitFun n C (extend r x)) hess (D.take (k-m+1)) (na_strict_take hS _)
        (fun he => by rw [he] at hl; simp at hl)
        (fun x => by
          have ho : outW m (D.take (k-m+1)) = k := by unfold outW; rw [hl]; omega
          rw [ho,val_take D x (k-m+1) k (by omega) (by omega),hev x,hr]
          rfl)
      refine ⟨D',good,?_,sem⟩
      simp only [List.length_nil,Nat.zero_add] at hlen
      unfold Circuit.size
      omega

theorem circuit_neighbor_bound {n m : ℕ} (r : Fin n → Option (Fin m)) (C : Circuit)
    (hmono : Monotone2 C) (G : Fin m → Fin m → Prop) (hG : sem_Gr G)
    (hm : 0 < m)
    (hpairs : ∀ i j, circuitFun n C (extend r (sem_two i j)) = true ↔ G i j)
    (T B : Finset (Fin m)) (covered : ∀ v ∈ B, ∃ t ∈ T, G v t) :
    m + B.card ≤ C.size + 1 + 2*T.card := by
  have singleton (i : Fin m) : circuitFun n C (extend r (single i)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    apply hG.2.1 i
    apply (hpairs i i).mp
    have same : sem_two i i = single i := by funext v; simp [sem_two,single]
    rwa [same]
  have neighbor (i : Fin m) : ∃ j, G i j := by
    obtain ⟨j,hj,_⟩ := hG.2.2.2 i i
    exact ⟨j,hj⟩
  have cst (b : Bool) : ∃ x : Fin m → Bool, circuitFun n C (extend r x) ≠ b := by
    let i : Fin m := ⟨0,hm⟩
    cases b with
    | false =>
      obtain ⟨j,hj⟩ := neighbor i
      exact ⟨sem_two i j,by rw [(hpairs _ _).mpr hj]; decide⟩
    | true => exact ⟨single i,by rw [singleton]; decide⟩
  have proj (i : Fin m) : ∃ x : Fin m → Bool, circuitFun n C (extend r x) ≠ x i :=
    ⟨single i,by simp [singleton,single]⟩
  have ess (i : Fin m) : ∃ x y : Fin m → Bool, (∀ k, k ≠ i → x k = y k) ∧
      circuitFun n C (extend r x) ≠ circuitFun n C (extend r y) := by
    obtain ⟨j,hj⟩ := neighbor i
    exact ⟨sem_two i j,single j,fun k hk => by simp [sem_two,single,hk],
      by rw [(hpairs _ _).mpr hj,singleton]; decide⟩
  obtain ⟨D,live,small,ev⟩ := compressed r C hmono cst proj ess
  have pairs : PairCorrect G D := by
    intro i j
    rw [ev]
    exact hpairs i j
  have h := pair_neighbor_bound hG live pairs T B covered
  omega

end Plane2974.Dom

namespace Plane2974.Dom
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Plane2974.GraphProof

theorem active_neighbor_budget {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (deg : ∀ v ∈ X, 3 ≤ (G.neighborSet v).ncard)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (ev : GraphEval C G)
    (T B : Finset (Fin n)) (hT : T ⊆ X) (hB : B ⊆ X)
    (cover : ∀ v ∈ B, ∃ t ∈ T, G.Adj v t) :
    X.card + B.card ≤ C.size + 1 + 2*T.card := by
  classical
  let e : X ≃ Fin X.card := Fintype.equivFinOfCardEq (Fintype.card_coe X)
  let ix (u : Fin X.card) : Fin n := (e.symm u).val
  have inj : Function.Injective ix := Subtype.val_injective.comp e.symm.injective
  let back (u : Fin n) (hu : u ∈ X) : Fin X.card := e ⟨u,hu⟩
  have inv (u : Fin n) (hu : u ∈ X) : ix (back u hu) = u := by simp [ix,back]
  have mem (u : Fin X.card) : ix u ∈ X := (e.symm u).property
  let r (u : Fin n) : Option (Fin X.card) := if hu : u ∈ X then some (back u hu) else none
  have extPair (a b : Fin X.card) : extend r (sem_two a b) = sem_two (ix a) (ix b) := by
    funext v
    by_cases hv : v ∈ X
    · have eq (c : Fin X.card) : back v hv = c ↔ v = ix c :=
        ⟨fun h => by rw [←h,inv],fun h => inj ((inv _ _).trans h)⟩
      simp [extend,r,hv,sem_two,eq]
    · have ne (c : Fin X.card) : v ≠ ix c := fun h => hv (h ▸ mem c)
      simp [extend,r,hv,sem_two,ne]
  let restricted (u v : Fin X.card) := G.Adj (ix u) (ix v)
  have pairs (u v) : circuitFun n C (extend r (sem_two u v)) = true ↔ restricted u v := by
    rw [extPair]
    have xp : sem_two (ix u) (ix v) = point ({ix u, ix v} : Finset (Fin n)) := by
      funext a
      by_cases h : a = ix u <;> by_cases k : a = ix v <;> simp [sem_two,point,h,k]
    rw [xp]
    exact ev _ _
  have other (v) (hv : v ∈ X) (w) : ∃ u, G.Adj v u ∧ u ≠ w := by
    have size := deg v hv
    rw [Set.ncard_eq_toFinset_card'] at size
    by_contra! bad
    have sub : (G.neighborSet v).toFinset ⊆ {w} := by
      intro u hu
      exact Finset.mem_singleton.mpr (bad u (Set.mem_toFinset.mp hu))
    have le := Finset.card_le_card sub
    simp only [Finset.card_singleton] at le
    omega
  have graph : sem_Gr restricted := by
    refine ⟨fun _ _ h => h.symm,fun u => G.loopless.irrefl (ix u),?_,?_⟩
    · intro u v uv
      obtain ⟨a,ua,-⟩ := other (ix u) (mem u) (ix v)
      obtain ⟨b,ub,ba⟩ := other (ix u) (mem u) a
      by_cases va : G.Adj (ix v) a
      · have vb : ¬ G.Adj (ix v) b := fun h => square _ _ _ _ (fun eq => uv (inj eq)) ba.symm ua ub va h
        exact ⟨back b (inX ub.symm),by simpa [restricted,inv] using ub,by simpa [restricted,inv] using vb⟩
      · exact ⟨back a (inX ua.symm),by simpa [restricted,inv] using ua,by simpa [restricted,inv] using va⟩
    · intro u v
      obtain ⟨a,ua,av⟩ := other (ix u) (mem u) (ix v)
      exact ⟨back a (inX ua.symm),by simpa [restricted,inv] using ua,
        fun eq => av (by simpa only [inv] using congrArg ix eq)⟩
  let pull (A : Finset (Fin n)) := Finset.univ.filter fun u : Fin X.card => ix u ∈ A
  have card (A : Finset (Fin n)) (hA : A ⊆ X) : (pull A).card = A.card := by
    have eq : (pull A).image ix = A := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hu).2
      · intro v hv
        refine Finset.mem_image.mpr ⟨back v (hA hv),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,inv _ _⟩
        rwa [inv]
    exact (Finset.card_image_of_injective _ inj).symm.trans (congrArg Finset.card eq)
  obtain ⟨a,b,ab⟩ := edge
  have hm := Finset.card_pos.mpr ⟨a,inX ab⟩
  have bound := circuit_neighbor_bound r C hC restricted graph hm pairs (pull T) (pull B) (by
    intro u hu
    obtain ⟨t,ht,ut⟩ := cover (ix u) (Finset.mem_filter.mp hu).2
    exact ⟨back t (hT ht),Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [inv] using ht⟩,
      by simpa only [restricted,inv] using ut⟩)
  simpa only [card T hT,card B hB] using bound

end Plane2974.Dom

namespace Plane2974.Charge

private theorem pencil_count {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (E : Finset (Fin N × Fin N)) (P : Finset (Fin N))
    (incident : ∀ e ∈ E, I e.1 e.2 ∧ e.1 ∈ P)
    (regular : ∀ l, (Finset.univ.filter fun a => I a l).card = q+1)
    (unique : ∀ p a l m, p ≠ a → I p l → I a l → I p m → I a m → l=m) :
    q*E.card ≤ ∑ a : Fin N, (P.filter fun p => ∃ l, (p,l) ∈ E ∧ I a l).card := by
  classical
  let cols (e : Fin N × Fin N) := (Finset.univ.filter fun a => I a e.2).erase e.1
  let triples := E.sigma cols
  let pairs := Finset.univ.sigma fun a : Fin N => P.filter fun p => ∃ l, (p,l) ∈ E ∧ I a l
  have cs (e) (he : e ∈ E) : (cols e).card = q := by
    have hm : e.1 ∈ Finset.univ.filter (fun a => I a e.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(incident e he).1⟩
    simp [cols, Finset.card_erase_of_mem hm, regular]
  have equal : triples.card = q*E.card := by
    rw [Finset.card_sigma]
    calc
      _ = ∑ _ ∈ E, q := Finset.sum_congr rfl cs
      _ = _ := by simp [Nat.mul_comm]
  have inject : triples.card ≤ pairs.card := by
    apply Finset.card_le_card_of_injOn (fun t => ⟨t.2,t.1.1⟩)
    · rintro ⟨⟨p,l⟩,a⟩ ht
      obtain ⟨he,ha⟩ := Finset.mem_sigma.mp ht
      have al := (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨(incident _ he).2,l,he,al⟩⟩
    · rintro ⟨⟨p,l⟩,a⟩ h ⟨⟨r,m⟩,b⟩ k eq
      have ab : a=b := congrArg Sigma.fst eq
      have pr : p=r := congrArg (fun z : Σ _ : Fin N, Fin N => z.2) eq
      subst b
      subst r
      obtain ⟨he,ha⟩ := Finset.mem_sigma.mp h
      obtain ⟨ke,ka⟩ := Finset.mem_sigma.mp k
      obtain ⟨ap,al⟩ := Finset.mem_erase.mp ha
      have lm := unique p a l m ap.symm (incident _ he).1 (Finset.mem_filter.mp al).2
        (incident _ ke).1 (Finset.mem_filter.mp (Finset.mem_erase.mp ka).2).2
      subst m
      rfl
  simpa only [equal,pairs,Finset.card_sigma] using inject

private theorem sum_slice {N : ℕ} (R : Fin N → Fin N → Prop) [DecidableRel R]
    (A : Finset (Fin N)) (k : ℕ) (deg : ∀ a, (Finset.univ.filter (R a)).card = k) :
    (∑ t : Fin N, (A.filter fun a => R a t).card) = A.card*k := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a ∈ A, k := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [Finset.card_filter] using deg a
    _ = _ := by simp

end Plane2974.Charge
namespace Plane2974.Charge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Plane2974.GraphProof Plane2974.Plane
set_option maxHeartbeats 3500000 in
theorem dense_budget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) (hu : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hRej : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) :
    let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N e.1 ∨ k=Fin.natAdd N e.2))=true
    (∀ v : Fin (N+N), let d := (E.filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
          d=0 ∨ 3 ≤ d) → ∃ V : ℕ, N*V+2*q*E.card ≤ N*(C.size+1)+2*(q+1)*V ∧ 2*E.card ≤ (q+1)*V := by
  classical
  intro E dense
  let pt : Fin N → Fin (N+N) := Fin.castAdd N
  let ln : Fin N → Fin (N+N) := Fin.natAdd N
  let J := fun p l : Fin N => (p,l) ∈ E
  let G := graph J
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  let X := P.image pt ∪ L.image ln
  let owns := fun (v : Fin (N+N)) (e : Fin N × Fin N) => v=pt e.1 ∨ v=ln e.2
  let star := fun (v : Fin (N+N)) => E.filter (owns v)
  let op := fun (v : Fin (N+N)) (e : Fin N × Fin N) => if v=pt e.1 then ln e.2 else pt e.1
  have apart (p l) : pt p ≠ ln l := left_ne_right _ _
  have pinj : Function.Injective pt := Fin.castAdd_injective N N
  have linj : Function.Injective ln := Fin.natAdd_injective N N
  have memE (p l : Fin N) : J p l ↔ I p l ∧
      circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l))=true := by
    change (p,l) ∈ Finset.univ.filter _ ↔ _
    simp
  have repr {p l : Fin N} {a b : Fin (N+N)}
      (hp : Fin.castAdd N p = a ∨ Fin.castAdd N p = b) (hl : Fin.natAdd N l=a ∨ Fin.natAdd N l=b) :
      (fun z : Fin (N + N) => decide (z = a ∨ z = b)) =
          (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
    funext z
    have hne : Fin.castAdd N p ≠ Fin.natAdd N l := left_ne_right p l
    rcases hp with rfl | rfl <;> rcases hl with h2 | h2
    · exact (hne h2.symm).elim
    · subst h2; rfl
    · subst h2; simp [or_comm]
    · exact (hne h2.symm).elim
  have eval : GraphEval C G := by
    intro a b
    have hfn : point ({a, b} : Finset (Fin (N + N))) = fun z => decide (z = a ∨ z = b) := by
      funext z; simp [point]
    change circuitFun (N + N) C (point {a, b}) = true ↔ G.Adj a b
    rw [hfn]
    constructor
    · intro ht
      have old : (graph I).Adj a b := by
        by_contra hnot
        have hcnt : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } ≤ q := by
          have hle2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card ≤ 2 := by
            have hsub : Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b) ⊆
                (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)) ∪
                (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)) := by
              intro l hl
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
              exact hl
            have hc1 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)).card ≤ 1 := by
              rw [Finset.card_le_one]
              intro l1 hl1 l2 hl2
              exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
            have hc2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)).card ≤ 1 := by
              rw [Finset.card_le_one]
              intro l1 hl1 l2 hl2
              exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
            exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
          have hceq : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } =
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card := by
            rw [← Fintype.card_coe]
            apply Fintype.card_congr
            apply Equiv.subtypeEquivRight
            intro l; simp
          omega
        have hno : ¬ ∃ p l : Fin N, I p l ∧
            decide (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) = true ∧
            decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true := by
          rintro ⟨p, l, hpl, hp, hl⟩
          simp only [decide_eq_true_eq] at hp hl
          exact hnot ⟨p, l, hpl, hp, hl⟩
        have hf := hRej (fun z => decide (z = a ∨ z = b)) hcnt hno
        rw [hf] at ht
        exact Bool.false_ne_true ht
      obtain ⟨p,l,hi,hp,hl⟩ := old
      exact ⟨p,l,(memE p l).mpr ⟨hi,(repr hp hl) ▸ ht⟩,hp,hl⟩
    · rintro ⟨p,l,h,hp,hl⟩
      rw [repr hp hl]
      exact ((memE p l).mp h).2
  have asOld {v w} (e : G.Adj v w) : (graph I).Adj v w := by
    obtain ⟨p,l,hi,hp,hl⟩ := e
    exact ⟨p,l,((memE _ _).mp hi).1,hp,hl⟩
  have square (v w c d) (vw : v ≠ w) (cd : c ≠ d)
      (vc : G.Adj v c) (vd : G.Adj v d) (wc : G.Adj w c) (wd : G.Adj w d) : False :=
    no_square I hu v w c d vw cd (asOld vc) (asOld vd) (asOld wc) (asOld wd)
  have leftX (e : Fin N × Fin N) (he : e ∈ E) : pt e.1 ∈ X :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩,rfl⟩)
  have rightX (e : Fin N × Fin N) (he : e ∈ E) : ln e.2 ∈ X :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩,rfl⟩)
  have inX {v w} (edge : G.Adj v w) : v ∈ X := by
    obtain ⟨p,l,hi,hp,hl⟩ := edge
    rcases hp with pV|pW
    · exact pV ▸ leftX (p,l) hi
    · rcases hl with lV|lW
      · exact lV ▸ rightX (p,l) hi
      · exact (apart p l (pW.trans lW.symm)).elim
  have sides (v) (e : Fin N × Fin N) (o : owns v e) :
      (v = pt e.1 ∧ op v e = ln e.2) ∨ (v = ln e.2 ∧ op v e = pt e.1) := by
    rcases o with hp|hl
    · exact Or.inl ⟨hp,if_pos hp⟩
    · exact Or.inr ⟨hl,if_neg (fun hp => apart _ _ (hp.symm.trans hl))⟩
  have opInj (v) : Set.InjOn (op v) (star v) := by
    intro e he f hf eq
    rcases sides v e (Finset.mem_filter.mp he).2 with ⟨ve,oe⟩|⟨ve,oe⟩ <;>
      rcases sides v f (Finset.mem_filter.mp hf).2 with ⟨vf,of'⟩|⟨vf,of'⟩
    · exact Prod.ext (pinj (ve.symm.trans vf)) (linj (oe.symm.trans (eq.trans of')))
    · exact (apart _ _ (ve.symm.trans vf)).elim
    · exact (apart _ _ (vf.symm.trans ve)).elim
    · exact Prod.ext (pinj (oe.symm.trans (eq.trans of'))) (linj (ve.symm.trans vf))
  have deg (v) (vx : v ∈ X) : 3 ≤ (G.neighborSet v).ncard := by
    have witness : (star v).Nonempty := by
      rcases Finset.mem_union.mp vx with h|h <;> obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
        exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩⟩
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
        exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩⟩
    have d : 3 ≤ (star v).card := (dense v).resolve_left (Nat.ne_of_gt (Finset.card_pos.mpr witness))
    rw [Set.ncard_eq_toFinset_card']
    apply d.trans
    apply Finset.card_le_card_of_injOn (op v) _ (opInj v)
    intro e he
    have je := (Finset.mem_filter.mp he).1
    rcases sides v e (Finset.mem_filter.mp he).2 with ⟨ve,oe⟩|⟨ve,oe⟩
    · rw [oe,ve]
      exact Set.mem_toFinset.mpr ((adj_lr J _ _).mpr je)
    · rw [oe,ve]
      exact Set.mem_toFinset.mpr ((adj_rl J _ _).mpr je)
  by_cases no : E = ∅
  · exact ⟨0, by simp [no], by simp [no]⟩
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr no
  have disjoint (A B : Finset (Fin N)) : Disjoint (A.image pt) (B.image ln) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨p,_,ep⟩ := Finset.mem_image.mp hv
    obtain ⟨l,_,el⟩ := Finset.mem_image.mp hw
    exact apart _ _ (ep.trans el.symm)
  let both (A B : Finset (Fin N)) := A.image pt ∪ B.image ln
  have card_both (A B) : (both A B).card = A.card + B.card := by
    rw [Finset.card_union_of_disjoint (disjoint _ _),Finset.card_image_of_injective _ pinj,
      Finset.card_image_of_injective _ linj]
  have sub (A B) (ha : A ⊆ P) (hb : B ⊆ L) : both A B ⊆ X :=
    Finset.union_subset_union (Finset.image_subset_image ha) (Finset.image_subset_image hb)
  let TP (t : Fin N) := P.filter fun p => I p t
  let TL (t : Fin N) := L.filter fun l => I t l
  let BP (t : Fin N) := P.filter fun p => ∃ l, J p l ∧ I t l
  let BL (t : Fin N) := L.filter fun l => ∃ p, J p l ∧ I p t
  have pb (t : Fin N) : X.card + ((BP t).card+(BL t).card) ≤
      C.size+1+2*((TP t).card+(TL t).card) := by
    have budget := Plane2974.Dom.active_neighbor_budget G C X inX deg square
      ⟨pt e.1,ln e.2,(adj_lr J _ _).mpr he⟩ hC eval
      (both (TP t) (TL t)) (both (BP t) (BL t)) (sub _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (sub _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _)) (by
        intro v hv
        rcases Finset.mem_union.mp hv with hp|hl
        · obtain ⟨p,pIn,rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨l,hit,on⟩ := (Finset.mem_filter.mp pIn).2
          have active : l ∈ L := Finset.mem_image.mpr ⟨(p,l),hit,rfl⟩
          refine ⟨ln l,Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨l,Finset.mem_filter.mpr ⟨active,on⟩,rfl⟩),(adj_lr J _ _).mpr hit⟩
        · obtain ⟨l,lIn,rfl⟩ := Finset.mem_image.mp hl
          obtain ⟨p,hit,on⟩ := (Finset.mem_filter.mp lIn).2
          have active : p ∈ P := Finset.mem_image.mpr ⟨(p,l),hit,rfl⟩
          refine ⟨pt p,Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨p,Finset.mem_filter.mpr ⟨active,on⟩,rfl⟩),(adj_rl J _ _).mpr hit⟩)
    simpa only [card_both] using budget
  have col (l) : (Finset.univ.filter fun p => I p l).card = q+1 := by
    simpa only [Fintype.card_subtype] using hcol l
  have row := lines_through q N I (by omega) hN col hu
  have w1 : q*E.card ≤ ∑ t, (BP t).card := pencil_count q I E P
    (fun e he => ⟨((memE _ _).mp he).1,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩) col
    (fun p a l m pa pl al pm am => (hu p a pa).unique ⟨pl,al⟩ ⟨pm,am⟩)
  let rev := E.map (Equiv.prodComm _ _).toEmbedding
  have revMem (u v : Fin N) : (u,v) ∈ rev ↔ (v,u) ∈ E := Finset.mem_map_equiv
  have w2raw := pencil_count q (fun l p => I p l) rev L (by
    rintro ⟨l,p⟩ he
    have hit := (revMem l p).mp he
    exact ⟨((memE _ _).mp hit).1,Finset.mem_image.mpr ⟨(p,l),hit,rfl⟩⟩) row
    (by intro l m p a lm pl pm al am
        by_contra pa
        exact lm ((hu p a pa).unique ⟨pl,al⟩ ⟨pm,am⟩))
  have w2 : q*E.card ≤ ∑ t, (BL t).card := by
    simpa only [BL,J,revMem,rev,Finset.card_map] using w2raw
  have tP : ∑ t, (TP t).card = P.card*(q+1) := sum_slice I P _ row
  have tL : ∑ t, (TL t).card = L.card*(q+1) := sum_slice (fun l p => I p l) L _ col
  have all := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => pb t)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,tP,tL] at all
  have xcard : X.card = P.card + L.card := card_both _ _
  have budget : N*X.card+2*q*E.card ≤ N*(C.size+1)+2*(q+1)*X.card := by
    rw [xcard] at all ⊢
    nlinarith only [all,w1,w2]
  have degree (A : Finset (Fin N × Fin N)) (Y : Finset (Fin N)) (R : Fin N → Fin N → Prop)
      [DecidableRel R] (ends : ∀ z ∈ A, z.1 ∈ Y ∧ R z.1 z.2)
      (reg : ∀ z, (Finset.univ.filter (R z)).card = q+1) : A.card ≤ Y.card*(q+1) := by
    let F := Y.sigma fun a => Finset.univ.filter (R a)
    have count : F.card = Y.card*(q+1) := by
      simp [F,Finset.card_sigma,reg]
    rw [←count]
    apply Finset.card_le_card_of_injOn (fun e => ⟨e.1,e.2⟩)
    · intro e he
      exact Finset.mem_sigma.mpr ⟨(ends e he).1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ends e he).2⟩⟩
    · rintro ⟨a,b⟩ _ ⟨p,l⟩ _ eq
      exact Prod.ext (congrArg Sigma.fst eq) (congrArg (fun z : Σ _ : Fin N, Fin N => z.2) eq)
  have dP := degree E P I (fun z hz => ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,((memE _ _).mp hz).1⟩) row
  have dL := degree rev L (fun l p => I p l) (by
    rintro ⟨l,p⟩ h
    have hit := (revMem l p).mp h
    exact ⟨Finset.mem_image.mpr ⟨(p,l),hit,rfl⟩,((memE _ _).mp hit).1⟩) col
  simp only [rev,Finset.card_map] at dL
  refine ⟨X.card,budget,?_⟩
  rw [xcard]
  nlinarith only [dP,dL]

end Plane2974.Charge

namespace Recovered3471
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.TopForm

def Flags {N : ℕ} (S : Fin N → Finset (Fin N)) :=
  Finset.univ.filter fun e : Fin N × Fin N => e.1 ∈ S e.2

theorem four_square (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 2 ≤ q) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    4*q^2 ≤ C.size + 3 := by
  classical
  let I := fun p l : Fin N => p ∈ S l
  have deg (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa [I,Fintype.card_subtype] using col l
  have row := Plane2974.Plane.lines_through q N I (by omega) ord (fun l => by simpa [I] using col l) uniq
  have hit (p l : Fin N) (h : I p l) : circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true := by
    let x : Fin (N+N) → Bool := Fin.addCases (fun a => decide (a∈({p}:Finset (Fin N)))) (fun b => decide (b∈({l}:Finset (Fin N))))
    have raw : List.ofFn x = incidenceInput {p} {l} := List.ofFn_fin_append _ _
    have fn : x = (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · change x (Fin.castAdd N a) = _
        rw [show x (Fin.castAdd N a) = decide (a∈({p}:Finset (Fin N))) from Fin.addCases_left ..]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,Plane2974.Plane.left_ne_right a l,or_false]
      · change x (Fin.natAdd N b) = _
        rw [show x (Fin.natAdd N b) = decide (b∈({l}:Finset (Fin N))) from Fin.addCases_right ..]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (Plane2974.Plane.left_ne_right p b),false_or]
    rw [←fn]
    change C.eval (List.ofFn x)=true
    rw [raw]
    exact pos l p h
  have off (x : Fin (N+N) → Bool) (lim : Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q)
      (none : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) : circuitFun (N+N) C x=false := by
    let X := Finset.univ.filter (fun p => x (Fin.castAdd N p)=true)
    let Y := Finset.univ.filter (fun l => x (Fin.natAdd N l)=true)
    have eq : x = Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y)) := by
      funext i
      refine Fin.addCases (fun p => ?_) (fun l => ?_) i
      · rw [Fin.addCases_left]; simp [X]
      · rw [Fin.addCases_right]; simp [Y]
    have raw : List.ofFn x = incidenceInput X Y := by rw [eq]; exact List.ofFn_fin_append _ _
    change C.eval (List.ofFn x)=false
    rw [raw]
    apply sound X Y
    · simpa [Y,Fintype.card_subtype] using lim
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact none ⟨p,l,hp,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
    circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N e.1 ∨ k=Fin.natAdd N e.2)) = true)
  have same : E=Flags S := by
    ext e
    simp only [E,Flags,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.left,fun h => ⟨h,hit _ _ h⟩⟩
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have density : ∀ v : Fin (N+N), let d := (E.filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
        d=0 ∨ 3 ≤ d := by
    intro v
    right
    change 3 ≤ (E.filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
    rw [same]
    induction v using Fin.addCases with
    | left p =>
      apply (show 3 ≤ (Finset.univ.filter (fun l => I p l)).card by rw [row]; omega).trans
      apply Finset.card_le_card_of_injOn (fun l => (p,l))
      · intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩,Or.inl rfl⟩
      · intro a _ b _ h; exact congrArg Prod.snd h
    | right l =>
      apply (show 3 ≤ (S l).card by rw [col]; omega).trans
      apply Finset.card_le_card_of_injOn (fun p => (p,l))
      · intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,Or.inr rfl⟩
      · intro a _ b _ h; exact congrArg Prod.fst h
  obtain ⟨V,budget,edges⟩ := Plane2974.Charge.dense_budget q N I C hq ord deg uniq mon off density
  have fcard : E.card = N*(q+1) := by
    let X : Finset (Fin N) := Finset.univ
    have count := Plane2974.Small.card_filter_product_eq_sum E X X
    have all : ((X ×ˢ X).filter (fun p => p ∈ E)) = E := by ext; simp [X]
    have fibers (p : Fin N) : (X.filter (fun l => (p,l) ∈ E)).card = q+1 := by
      rw [same]
      simpa [X,Flags,I] using row p
    rw [all] at count
    simpa [fibers,X] using count
  change N*V+2*q*E.card ≤ N*(C.size+1)+2*(q+1)*V at budget
  change 2*E.card ≤ (q+1)*V at edges
  rw [fcard] at budget edges
  have vmin : 2*N ≤ V := by
    have h : 2*N*(q+1) ≤ V*(q+1) := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using edges
    exact Nat.le_of_mul_le_mul_right h (by omega)
  have coef : 2*(q+1) ≤ N := by
    rw [ord]
    nlinarith [Nat.mul_le_mul_left q hq]
  have nonneg : 2*N*N+2*(q+1)*V ≤ N*V+4*N*(q+1) := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le vmin
    obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le coef
    nlinarith only [Nat.zero_le (a*b),ha,hb,
      congrArg (fun z : ℕ => N*z) ha, congrArg (fun z : ℕ => 2*(q+1)*z) ha,
      congrArg (fun z : ℕ => a*z) hb]
  have scaled : N*(2*N+2*q*(q+1)) ≤ N*(C.size+1+4*(q+1)) := by
    nlinarith only [nonneg,budget]
  have positive : 0<N := by omega
  have base := Nat.le_of_mul_le_mul_left scaled positive
  nlinarith only [base,ord]

theorem through398 (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hi : q ≤ 398) (ord : N=q^2+q+1) (col : ∀ l, (S l).card=q+1)
    (uniq : ∀ p r : Fin N, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    N*q ≤ 100*C.size := by
  have size := four_square q N S C (by omega) ord col uniq ao pos sound
  rw [ord]
  have cub := Nat.mul_le_mul_left (q^2) hi
  have sq := Nat.mul_le_mul_left q hq
  nlinarith only [size,cub,sq,hq]

end Recovered3471

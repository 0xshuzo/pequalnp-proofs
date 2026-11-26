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


namespace Plane2974.Charge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Plane2974.GraphProof
open Plane2974.Plane
open Plane2974

open Finset
private theorem incidenceSquare {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) := by
  classical
  let neighbors (l : Fin N) := P.filter fun p => (p, l) ∈ E
  have count : E.card = ∑ l ∈ L, (neighbors l).card := by
    rw [← Finset.card_sigma]
    apply Finset.card_nbij' (fun e => ⟨e.2, e.1⟩) (fun e => (e.2, e.1))
    · intro e he
      exact mem_sigma.mpr ⟨(ends e he).2, mem_filter.mpr ⟨(ends e he).1, he⟩⟩
    · exact fun e he => (mem_filter.mp (mem_sigma.mp he).2).2
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
  let triples := L.sigma fun l => (neighbors l).offDiag
  have pairs_le : triples.card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp (mem_sigma.mp ht).2
      exact mem_offDiag.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp hb).1, hab⟩
    · intro ⟨u, a, b⟩ hu ⟨v, c, d⟩ hv heq
      change (a, b) = (c, d) at heq
      cases heq
      obtain ⟨hau, hbu, hab⟩ := mem_offDiag.mp (mem_sigma.mp hu).2
      obtain ⟨hav, hbv, _⟩ := mem_offDiag.mp (mem_sigma.mp hv).2
      cases unique a b u v hab (mem_filter.mp hau).2 (mem_filter.mp hbu).2
        (mem_filter.mp hav).2 (mem_filter.mp hbv).2
      rfl
  have squares : (∑ l ∈ L, (neighbors l).card ^ 2) = triples.card + E.card := by
    rw [count]
    simp only [triples, card_sigma, offDiag_card, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by rw [Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => 1 : Fin N → ℕ)
    (fun l => (neighbors l).card)
  simp only [one_mul, one_pow, sum_const, Nat.nsmul_eq_mul, mul_one, ← count, squares] at cauchy
  rw [pow_two] at cauchy
  rw [offDiag_card, ← Nat.mul_sub_one] at pairs_le
  exact cauchy.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right pairs_le _))

private theorem incidenceBounds {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card ≤ P.card * L.card ∧
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) ∧
    E.card * E.card ≤ P.card * (L.card * (L.card - 1) + E.card) := by
  refine ⟨?_, incidenceSquare E P L ends unique, ?_⟩
  · rw [← card_product]
    exact card_le_card fun e he => mem_product.mpr (ends e he)
  · let rev := E.map (Equiv.prodComm _ _).toEmbedding
    have mem_rev (a b : Fin N) : (a, b) ∈ rev ↔ (b, a) ∈ E := mem_map_equiv
    have swapEnds : ∀ e ∈ rev, e.1 ∈ L ∧ e.2 ∈ P := by
      rintro ⟨a, b⟩ he
      exact (ends _ ((mem_rev a b).mp he)).symm
    have swapUnique (a b u v : Fin N) (hab : a ≠ b) (hau : (a, u) ∈ rev)
        (hbu : (b, u) ∈ rev) (hav : (a, v) ∈ rev) (hbv : (b, v) ∈ rev) : u = v := by
      by_contra hne
      exact hab (unique u v a b hne ((mem_rev _ _).mp hau) ((mem_rev _ _).mp hav)
        ((mem_rev _ _).mp hbu) ((mem_rev _ _).mp hbv))
    simpa only [rev, card_map] using incidenceSquare rev L P swapEnds swapUnique

theorem bound31 (a b s e : ℕ) (hs : s ≤ 7564) (hab : a + b ≤ s + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    (he : e ^ 2 ≤ a * (e + b * (b - 1))) : e ≤ 31 * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hc : 1 + c - 1 = c := by omega
  rw [hc] at he
  have h0 : 31 * (1 + c + d + c + 1) ≤ e + 30 := by omega
  zify at he h0 hab hs
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hlim : 2 * (1 + (c : ℤ)) + d ≤ 7565 := by linarith
  set B : ℤ := 1 + c with hB
  have hB1 : 1 ≤ B := by linarith
  have hcB : (c : ℤ) = B - 1 := by linarith
  rw [hcB] at he h0
  have h1 : 62 * B + 31 * d - 30 ≤ (e : ℤ) := by linarith
  have h2 : (62 * B + 31 * d - 30) * (61 * B + 30 * d - 30) ≤ (e : ℤ) * (e - (B + d)) := by
    have p1 : 0 ≤ 62 * B + 31 * (d : ℤ) - 30 := by linarith
    have p2 : 0 ≤ 61 * B + 30 * (d : ℤ) - 30 := by linarith
    exact mul_le_mul h1 (by linarith) p2 (by linarith)
  have h3 : (62 * B + 31 * d - 30) * (61 * B + 30 * d - 30) ≤ (B + d) * (B * (B - 1)) := by
    nlinarith [he, h2]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    push_cast at h3 hlim
    have hB2 : B ≤ 3782 := by linarith
    have k1 : 0 ≤ (B - 1) * (3782 - B) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ B * ((B - 1) * (3782 - B)) := mul_nonneg (by linarith) k1
    nlinarith [h3, k2]
  · have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hB2 : B ≤ 3782 := by linarith
    have k1 : 0 ≤ B * (B * (7565 - 2 * B - d)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k2 : 0 ≤ B * ((d - 1) * (3782 - B)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k3 : 0 ≤ (d - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have k4 : 0 ≤ (B - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h3, k1, k2, k3, k4]

set_option maxHeartbeats 3500000 in
theorem dense_small (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hu : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (legal : IsAO2 (N+N) C)
    (hRej : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) :
    let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N e.1 ∨ k=Fin.natAdd N e.2))=true
    C.size ≤ 9770 →
      (∀ v : Fin (N+N), let d := (E.filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
          d=0 ∨ 3 ≤ d) → E.card ≤ 24*C.size := by
  classical
  intro E small dense
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
  · simp [no]
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr no
  have hC : Monotone2 C := fun g hg => ⟨legal.1 g hg,(legal.2.2 g hg).le⟩
  obtain ⟨S,sX,cover,base,strict⟩ := sparse_charge G C X inX deg square
    ⟨pt e.1,ln e.2,(adj_lr J _ _).mpr he⟩ hC eval
  have dis : Disjoint (P.image pt) (L.image ln) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨p,_,pV⟩ := Finset.mem_image.mp hv
    obtain ⟨l,_,lV⟩ := Finset.mem_image.mp hw
    exact apart _ _ (pV.trans lV.symm)
  have cardX : X.card = P.card + L.card := by
    rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ pinj,Finset.card_image_of_injective _ linj]
  have mb := Finset.card_pos.mpr ⟨e,he⟩
  have pp : 0 < P.card := Finset.card_pos.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  have lp : 0 < L.card := Finset.card_pos.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  have B := incidenceBounds E P L (fun z hz => ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩)
    (fun i j u v ij iu ju iv jv => (hu i j ij).unique
      ⟨((memE i u).mp iu).1,((memE j u).mp ju).1⟩ ⟨((memE i v).mp iv).1,((memE j v).mp jv).1⟩)
  by_cases few : 31*X.card ≤ 24*C.size
  · have smallX : X.card ≤ 7564 := by omega
    have m31 : E.card ≤ 31*X.card := by
      rcases le_total L.card P.card with le|le
      · apply bound31 P.card L.card X.card _ smallX (by omega) lp le
        simpa [pow_two,Nat.add_comm] using B.2.2
      · apply bound31 L.card P.card X.card _ smallX (by omega) pp le
        simpa [pow_two,Nat.add_comm] using B.2.1
    omega
  let H := (S ×ˢ X).filter fun z => G.Adj z.1 z.2
  let dest (z : Fin N × Fin N) : Fin (N+N) × Fin (N+N) :=
    if pt z.1 ∈ S then (pt z.1,ln z.2) else (ln z.2,pt z.1)
  have before : E.card ≤ H.card := by
    apply Finset.card_le_card_of_injOn dest
    · intro z h
      have edge : G.Adj (pt z.1) (ln z.2) := (adj_lr J _ _).mpr h
      by_cases l : pt z.1 ∈ S
      · simpa only [dest,if_pos l] using (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨l,rightX z h⟩,edge⟩ : (pt z.1,ln z.2) ∈ H)
      · have r := (cover _ _ edge).resolve_left l
        simpa only [dest,if_neg l] using (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨r,leftX z h⟩,edge.symm⟩ : (ln z.2,pt z.1) ∈ H)
    · intro z hz u hu eq
      by_cases zh : pt z.1 ∈ S <;> by_cases uh : pt u.1 ∈ S <;> simp only [dest,zh,uh,if_true,if_false] at eq
      · exact Prod.ext (pinj (congrArg Prod.fst eq)) (linj (congrArg Prod.snd eq))
      · exact (apart _ _ (congrArg Prod.fst eq)).elim
      · exact (apart _ _ (congrArg Prod.snd eq)).elim
      · exact Prod.ext (pinj (congrArg Prod.snd eq)) (linj (congrArg Prod.fst eq))
  have incidence := incidenceSquare H S X (fun z hz => Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    (fun a b u v ab au bu av bv => by
      by_contra uv
      exact square a b u v ab uv (Finset.mem_filter.mp au).2 (Finset.mem_filter.mp av).2
        (Finset.mem_filter.mp bu).2 (Finset.mem_filter.mp bv).2)
  have sp : 0 < S.card := by
    rcases cover _ _ ((adj_lr J e.1 e.2).mpr he) with h|h
    · exact Finset.card_pos.mpr ⟨_,h⟩
    · exact Finset.card_pos.mpr ⟨_,h⟩
  have XS : X.card ≤ C.size := by omega
  by_cases mini : C.size ≤ 4512
  · apply Plane2974.Small.main I (by omega) hu C (fun g hg => (legal.2.2 g hg).le) hRej mini
  have cap : S.card - 1 ≤ 2207 := by omega
  have k1 := Nat.mul_le_mul_left S.card cap
  have k2 : S.card*(S.card-1) ≤ 501*C.size := by omega
  have upp := (Nat.mul_le_mul_left X.card (Nat.add_le_add_right k2 H.card)).trans (Nat.mul_le_mul_right _ XS)
  have key := incidence.trans upp
  by_contra! bad
  have sp0 : (0:ℤ) < C.size := by exact_mod_cast (show 0<C.size by omega)
  have natPos : 24*C.size ≤ H.card := by omega
  have positive : 0 ≤ (H.card : ℤ)-24*C.size := by zify at natPos; linarith
  have a₁ : 0 ≤ (H.card : ℤ)-C.size := by linarith
  have a₂ := mul_nonneg positive a₁
  have a₃ := mul_nonneg (show (0:ℤ) ≤ C.size by positivity) positive
  zify at key
  nlinarith only [a₂,a₃,key,sq_pos_of_pos sp0]

end Plane2974.Charge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem Plane2974.Charge.small9770 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → x5.size ≤ 9770 → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order degree unique legal sound hs
  let pt : Fin N → Fin (N+N) := Fin.castAdd N
  let ln : Fin N → Fin (N+N) := Fin.natAdd N
  let owns (v : Fin (N+N)) (e : Fin N × Fin N) := v = pt e.1 ∨ v = ln e.2
  let pair (e : Fin N × Fin N) (v : Fin (N+N)) := decide (owns v e)
  let E (D : Circuit) := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true
  let incident (D : Circuit) (v : Fin (N+N)) := (E D).filter (owns v)
  let Sound (D : Circuit) := ∀ x : Fin (N+N) → Bool,
    Fintype.card {l : Fin N // x (ln l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ x (pt p) = true ∧ x (ln l) = true) →
    circuitFun (N+N) D x = false
  have apart (p l : Fin N) : pt p ≠ ln l := by
    intro equal
    have h := congrArg Fin.val equal
    change p.val = N+l.val at h
    omega
  have inj (k l : Fin N) (e : ln k = ln l) : k = l := by
    apply Fin.ext
    have h := congrArg Fin.val e
    change N+k.val = N+l.val at h
    omega
  have memE (D : Circuit) (e : Fin N × Fin N) :
      e ∈ E D ↔ I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true := by simp [E]
  have offPoint (D : Circuit) (neg : Sound D) (p : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = pt p)) = false := by
    apply neg
    · simp [fun l => (apart p l).symm]
    · rintro ⟨r,l,_,_,bad⟩
      exact (apart p l) (of_decide_eq_true bad).symm
  have offLine (D : Circuit) (neg : Sound D) (l : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = ln l)) = false := by
    apply neg
    · rw [Fintype.card_subtype]
      have sub : (Finset.univ.filter fun k : Fin N => decide (ln k = ln l) = true) ⊆ {l} := by
        intro k hk
        exact Finset.mem_singleton.mpr (inj k l (of_decide_eq_true (Finset.mem_filter.mp hk).2))
      have h := Finset.card_le_card sub
      simp only [Finset.card_singleton] at h
      exact h.trans (by omega)
    · rintro ⟨p,k,_,bad,_⟩
      exact apart p l (of_decide_eq_true bad)
  have bound (k : ℕ) : ∀ D : Circuit, D.size = k → IsAO2 (N+N) D → Sound D → D.size ≤ 9770 →
      (E D).card ≤ 24 * D.size := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hk ao neg small
      by_cases core : ∀ v, (incident D v).card = 0 ∨ 24 < (incident D v).card
      · apply Plane2974.Charge.dense_small q N I D (by omega) unique ao neg small
        intro v
        rcases core v with zero|many
        · exact Or.inl zero
        · exact Or.inr (by change 3 ≤ (incident D v).card; omega)
      push Not at core
      obtain ⟨v, present, cheap⟩ := core
      obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero present)
      obtain ⟨member, endpoint⟩ := Finset.mem_filter.mp he
      have accepted := ((memE D e).mp member).2
      have smaller : ∃ D' : Circuit, IsAO2 (N+N) D' ∧ D'.size < D.size ∧
          (∀ x, circuitFun (N+N) D' x = true → circuitFun (N+N) D x = true) ∧
          ∀ x : Fin (N+N) → Bool, x v = false → circuitFun (N+N) D' x = circuitFun (N+N) D x := by
        change v = pt e.1 ∨ v = ln e.2 at endpoint
        rcases endpoint with rfl | rfl
        · exact Plane2974.Pin.erase (N+N) D (pt e.1) (ln e.2) ao (apart _ _)
            (offPoint D neg _) (offLine D neg _) accepted
        · apply Plane2974.Pin.erase (N+N) D (ln e.2) (pt e.1) ao (apart _ _).symm
            (offLine D neg _) (offPoint D neg _)
          simpa only [pair,owns,or_comm] using accepted
      obtain ⟨D',valid,save,below,same⟩ := smaller
      have keepsSound : Sound D' := by
        intro x hx noEdges
        cases e : circuitFun (N+N) D' x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion ((below x e).symm.trans (neg x hx noEdges)))
      have sub : E D ⊆ E D' ∪ incident D v := by
        intro a ha
        by_cases hv : owns v a
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha,hv⟩)
        · obtain ⟨flag,hit⟩ := (memE D a).mp ha
          have noBit : pair a v = false := by simp [pair,hv]
          exact Finset.mem_union_left _ ((memE D' a).mpr ⟨flag,(same (pair a) noBit).trans hit⟩)
      have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      have prev := ih D'.size (by omega) D' rfl valid keepsSound (by omega)
      omega
  have h := bound C.size C rfl legal sound hs
  simpa only [Fintype.card_subtype] using h


theorem Plane2974.within9770 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → x5.size ≤ 9770 → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order col unique legal sound small
  have h := Plane2974.Charge.small9770 q N I C hq order col unique legal sound small
  rw [Fintype.card_subtype] at h ⊢
  refine (Finset.card_le_card ?_).trans h
  intro e he
  obtain ⟨hi, ha, _⟩ := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ha⟩

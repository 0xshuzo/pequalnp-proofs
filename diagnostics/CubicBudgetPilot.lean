import PEqualNP.Defs

namespace CubicReaderCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readers (C : Circuit) (v : ℕ) : ℕ :=
  (C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v).length

def appearances (C : Circuit) (i : ℕ) := (C.output :: C.gates.flatMap Gate.inputs).count i

def internalExtra (n : ℕ) (C : Circuit) :=
  ∑ i ∈ Finset.range C.gates.length, (appearances C (n+i) - 1)

def emptySlots (C : Circuit) := 2 * C.gates.length - (C.gates.flatMap Gate.inputs).length

/-- Count every primary reader on the cubic core, one use of each isolated
OR input and one use of each gate output in a minimum circuit. -/
theorem raw_budget (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hC : FanInTwo C) (heval : circuitFun n C = f)
    (hmin : ∀ m, HasCircuitSize n f m → C.size ≤ m) :
    A.card + (∑ v ∈ Aᶜ, readers C v.val) + internalExtra n C + emptySlots C ≤ C.size + 1 := by
  classical
  let wiresFrom : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append : ∀ (gs₁ gs₂ : List Gate) (w : List Bool),
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    intro gs₁ gs₂ w
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_length : ∀ (gs : List Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wiresFrom]
    | cons g gs ih =>
      intro w
      have h1 : wiresFrom (g :: gs) w =
          wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [h1, ih]
      simp
      omega
  have getD_snoc_lt : ∀ (w : List Bool) (v : Bool) (i : ℕ), i < w.length →
      (w ++ [v]).getD i false = w.getD i false := by
    intro w v i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ (w : List Bool) (v : Bool) (i : ℕ), i = w.length →
      (w ++ [v]).getD i false = v := by
    intro w v i hi
    subst hi
    simp
  have ofFn_getD_lt : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
  let substWire : ℕ → ℕ → ℕ → ℕ := fun k0 a i =>
    if i < k0 then i else if i = k0 then a else i - 1
  let substGate : ℕ → ℕ → Gate → Gate := fun k0 a g =>
    ⟨g.op, g.inputs.map (substWire k0 a)⟩
  let deleteGate : Circuit → ℕ → ℕ → Circuit := fun C j a =>
    ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (n + j) a),
      substWire (n + j) a C.output⟩
  have deleteGate_ok : ∀ (C : Circuit) (j a : ℕ), FanInTwo C → FanInTwo (deleteGate C j a) := by
    intro C j a hok g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hok g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      have h0 := hok g0 (List.mem_of_mem_drop hg0)
      exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
  have deleteGate_len : ∀ (C : Circuit) (j a : ℕ), j < C.gates.length →
      (deleteGate C j a).gates.length = C.gates.length - 1 := by
    intro C j a hj
    simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  have deleteDeadGate : ∀ (C : Circuit) (hC : FanInTwo C) (j : ℕ) (hj : j < C.gates.length),
      C.output ≠ n + j →
      (∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (n + j) ∉ C.gates[j'].inputs) →
      HasCircuitSize n (circuitFun n C) (C.gates.length - 1) := by
    intro C hC j hj hout hno
    refine ⟨deleteGate C j 0, deleteGate_ok C j 0 hC,
      by show (deleteGate C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len C j 0 hj], ?_⟩
    intro x
    show ((deleteGate C j 0).wires (List.ofFn x)).getD (substWire (n + j) 0 C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        rw [h2] at h1
        simpa only [List.append_assoc, List.singleton_append] using h1.symm
      set w₂ := wiresFrom (C.gates.take j) (List.ofFn x) with hw₂
      set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
      have hw₂_len : w₂.length = n + j := by
        rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      have hw₁_len : w₁.length = n + j + 1 := by
        rw [hw₁, wiresFrom_length, hw₂_len]; simp
      have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (n + j) ∉ g.inputs := by
        intro g hg
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_drop]
        exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
      have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
          w₁'.length = w₂'.length + 1 → n + j ≤ w₂'.length →
          (∀ g ∈ gs, (n + j) ∉ g.inputs) →
          (∀ i < w₁'.length, i ≠ n + j → w₂'.getD (substWire (n + j) 0 i) false = w₁'.getD i false) →
          ∀ i < (wiresFrom gs w₁').length, i ≠ n + j →
            (wiresFrom (gs.map (substGate (n + j) 0)) w₂').getD (substWire (n + j) 0 i) false =
              (wiresFrom gs w₁').getD i false := by
        intro gs
        induction gs with
        | nil =>
          intro w₁' w₂' _ _ _ hag i hi hne
          exact hag i hi hne
        | cons g rest ih =>
          intro w₁' w₂' hlen' hk' hnod hag'
          have hstep1 : wiresFrom (g :: rest) w₁' =
              wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)]) := rfl
          have hstep2 : wiresFrom ((g :: rest).map (substGate (n + j) 0)) w₂' =
              wiresFrom (rest.map (substGate (n + j) 0))
                (w₂' ++ [(substGate (n + j) 0 g).op.eval
                  ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false)]) := rfl
          rw [hstep1, hstep2]
          have hmap : ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false) =
              (g.inputs.map fun i => w₁'.getD i false) := by
            simp only [substGate, List.map_map]
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hne : i ≠ n + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
            by_cases hlti : i < w₁'.length
            · exact hag' i hlti hne
            · have hge : w₂'.length ≤ substWire (n + j) 0 i := by
                dsimp [substWire]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
          rw [hmap]
          apply ih _ _ (by simp [hlen']) (by simp; omega)
            (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
          intro i hi hne
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlti : i < w₁'.length
          · have hsublt : substWire (n + j) 0 i < w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_lt _ _ _ hsublt, getD_snoc_lt _ _ _ hlti]
            exact hag' i hlti hne
          · have hieq : i = w₁'.length := by omega
            have hsubeq : substWire (n + j) 0 i = w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ hsubeq, getD_snoc_eq _ _ _ hieq]
      show (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (n + j) 0)) (List.ofFn x)).getD
          (substWire (n + j) 0 C.output) false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
      rw [wiresFrom_append, ← hw₂]
      conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
      have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = n + C.gates.length := by
        rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
      apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ C.output (by omega) hout
      intro u hu hune
      have hltu : u < n + j := by omega
      simp only [substWire, hltu, ↓reduceIte]
      have hw1e : w₁ = w₂ ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w₂.getD i false)] := rfl
      rw [hw1e, getD_snoc_lt _ _ _ (by omega)]
    · have hge1 : (deleteGate C j 0).gates.length + n ≤ substWire (n + j) 0 C.output := by
        rw [deleteGate_len C j 0 hj]
        dsimp [substWire]
        split_ifs <;> omega
      have h1 : ((deleteGate C j 0).wires (List.ofFn x)).length =
          n + (deleteGate C j 0).gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have h2 : (C.wires (List.ofFn x)).length = n + C.gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  let reads : ℕ → Gate → Bool := fun v g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  have gate_eval_agree : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g.inputs.length ≤ 2 → ∀ (w₁ w₂ : List Bool) (v : ℕ),
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      reads v g = false →
      g.op.eval (g.inputs.map fun i => w₁.getD i false) =
        g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
    intro g hop hlen w₁ w₂ v hag hnr
    have hnr' : v ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
      intro hm
      have ht : reads v g = true := List.contains_iff_mem.2 hm
      rw [hnr] at ht
      cases ht
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    rcases hop' with h | h | h
    · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
        rw [h]
        have : GateOp.and.eval [false] = false := rfl
        rw [this]
        exact List.take_of_length_le hlen
      rw [ht2] at hnr'
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun he => hnr' (he ▸ hi))
    · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
        rw [h]
        have : GateOp.or.eval [false] = false := rfl
        rw [this]
        exact List.take_of_length_le hlen
      rw [ht2] at hnr'
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun he => hnr' (he ▸ hi))
    · rw [h] at hnr' ⊢
      have : GateOp.not.eval [false] = true := rfl
      rw [this] at hnr'
      rcases hgins : g.inputs with _ | ⟨a, rest⟩
      · rfl
      · rw [hgins] at hnr'
        have hav : a ≠ v := fun he => hnr' (by simp [he])
        show (!(w₁.getD a false)) = (!(w₂.getD a false))
        rw [hag a hav]
  have wiresFrom_agree_eff : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (v : ℕ) (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      (∀ g ∈ gs, reads v g = false) →
      ∀ i, i ≠ v → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    intro gs
    induction gs with
    | nil => intro _ v w₁ w₂ _ hag _ i hi; exact hag i hi
    | cons g rest ih =>
      intro hok v w₁ w₂ hlen hag hnr i hi
      have h1 : wiresFrom (g :: rest) w₁ =
          wiresFrom rest (w₁ ++ [g.op.eval (g.inputs.map fun k => w₁.getD k false)]) := rfl
      have h2 : wiresFrom (g :: rest) w₂ =
          wiresFrom rest (w₂ ++ [g.op.eval (g.inputs.map fun k => w₂.getD k false)]) := rfl
      rw [h1, h2]
      have hge := gate_eval_agree g (hok g List.mem_cons_self).1 (hok g List.mem_cons_self).2
        w₁ w₂ v hag (hnr g List.mem_cons_self)
      apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) v _ _
        (by simp [hlen]) _ (fun g' hg' => hnr g' (List.mem_cons_of_mem _ hg')) i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
        exact hag j hj
      · by_cases heq : j = w₁.length
        · rw [getD_snoc_eq _ _ _ heq, getD_snoc_eq _ _ _ (by omega), hge]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  let slots : Circuit → List ℕ := fun D => D.output :: D.gates.flatMap Gate.inputs
  have gateSlotBound : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g tail ih =>
      intro h
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have countBound : ∀ (xs : List ℕ) (S : Finset ℕ), ∑ i ∈ S, xs.count i ≤ xs.length := by
    intro xs
    induction xs with
    | nil => intro S; simp
    | cons a xs ih =>
      intro S
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> have := ih S <;> omega
  have filteredSlots : ∀ (v : ℕ) (gs : List Gate),
      (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
    intro v gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.count_append, List.filter_cons]
      by_cases h : reads v g = true
      · simp only [h, ↓reduceIte]
        have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
        have hp := List.count_pos_iff.mpr hm
        simp only [List.length_cons]
        omega
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        omega
  let cnt : ℕ → ℕ := fun i => (slots C).count i
  have marked : ∀ a ∈ A, 1 ≤ cnt a.val := by
    intro a ha
    apply List.count_pos_iff.2
    by_contra hn
    have hout : C.output ≠ a.val := fun he => hn (by simp [slots, he])
    have hnr : ∀ g ∈ C.gates, reads a.val g = false := by
      intro g hg
      cases hr : reads a.val g with
      | false => rfl
      | true =>
        have hm : a.val ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.1 hr)
        exact absurd (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨g, hg, hm⟩)) hn
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun j => decide (j = a)
    have hag : ∀ i, i ≠ a.val → (List.ofFn z).getD i false = (List.ofFn y).getD i false := by
      intro i hi
      by_cases hlt : i < n
      · rw [ofFn_getD_lt z i hlt, ofFn_getD_lt y i hlt]
        have hne : (⟨i, hlt⟩ : Fin n) ≠ a := fun e => hi (congrArg Fin.val e)
        simp [z, y, hne]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have heq : circuitFun n C z = circuitFun n C y :=
      wiresFrom_agree_eff C.gates hC a.val (List.ofFn z) (List.ofFn y) (by simp) hag hnr
        C.output hout
    rw [heval] at heq
    have hz : f z = false := by
      cases hfz : f z with
      | false => rfl
      | true =>
        rcases (hf z).1 hfz with ⟨b, _, hb⟩ | ⟨b, _, _, hb, _⟩ <;> simp [z] at hb
    have hy : f y = true := (hf y).2 (Or.inl ⟨a, ha, by simp [y]⟩)
    rw [hz, hy] at heq
    cases heq
  have unmarked : ∀ a ∈ Aᶜ, readers C a.val ≤ cnt a.val := by
    intro a _
    have h := filteredSlots a.val C.gates
    change (C.gates.filter (reads a.val)).length ≤ cnt a.val
    simp only [cnt, slots, List.count_cons]
    omega
  have internal : ∀ i ∈ Finset.range C.gates.length, 1 ≤ cnt (n + i) := by
    intro i hi
    apply List.count_pos_iff.2
    by_contra hn
    have hout : C.output ≠ n + i := fun e => hn (by simp [slots, e])
    have hno : ∀ j, (hj : j < C.gates.length) → i < j → n + i ∉ C.gates[j].inputs := by
      intro j hj _ hm
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj, hm⟩))
    have bad := hmin _ (heval ▸ deleteDeadGate C hC i (Finset.mem_range.1 hi) hout hno)
    change C.gates.length ≤ C.gates.length - 1 at bad
    have hipos : 0 < C.gates.length := lt_of_le_of_lt (Nat.zero_le i) (Finset.mem_range.1 hi)
    omega
  have lowerA := Finset.sum_le_sum marked
  have lowerB := Finset.sum_le_sum unmarked
  have lowerI := Finset.sum_le_sum internal
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerA lowerI
  have decompose : (∑ i ∈ Finset.range C.gates.length, cnt (n+i)) =
      C.gates.length + internalExtra n C := by
    have partition := Finset.sum_congr (s:=Finset.range C.gates.length) rfl
      (fun i hi => (show cnt (n+i) = 1 + (cnt (n+i)-1) by have := internal i hi; omega))
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,Finset.card_range,
      internalExtra,appearances,cnt,slots] using partition
  have inSum := A.sum_add_sum_compl (fun a : Fin n => cnt a.val)
  rw [Fin.sum_univ_eq_sum_range] at inSum
  have countAll := countBound (slots C) (Finset.range (n + C.gates.length))
  change ∑ i ∈ Finset.range (n + C.gates.length), cnt i ≤ (slots C).length at countAll
  rw [Finset.sum_range_add] at countAll
  have len := gateSlotBound C.gates (fun g hg => (hC g hg).2)
  simp only [slots, List.length_cons] at countAll
  unfold emptySlots
  change _ ≤ C.gates.length + 1
  omega

def spare (n : ℕ) (A : Finset (Fin n)) (C : Circuit) :=
  (∑ v ∈ Aᶜ, (readers C v.val - 2)) + internalExtra n C + emptySlots C

theorem core_budget (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (fan : FanInTwo C) (ev : circuitFun n C = f)
    (minC : ∀ m, HasCircuitSize n f m → C.size ≤ m)
    (low : ∀ v ∉ A, 2 ≤ readers C v.val) :
    A.card + 2 * Aᶜ.card + spare n A C ≤ C.size + 1 := by
  classical
  have pay := raw_budget n G A f C hf fan ev minC
  have ps : (∑ v ∈ Aᶜ, readers C v.val) =
      2*Aᶜ.card + ∑ v ∈ Aᶜ, (readers C v.val-2) := by
    have eq := Finset.sum_congr (s:=Aᶜ) rfl (fun v hv =>
      (show readers C v.val = 2 + (readers C v.val-2) by have := low v (Finset.mem_compl.mp hv); omega))
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm Aᶜ.card 2] using eq
  unfold spare
  omega

/-- The target follows whenever a suitable number of unmarked vertices
can be removed to make the cubic core bipartite. -/
theorem almost_bipartite (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (hnoA : ∀ i j, G.Adj i j → i ∉ A)
    (htau : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (fan : FanInTwo C) (ev : circuitFun n C = f)
    (minC : ∀ m, HasCircuitSize n f m → C.size ≤ m)
    (low : ∀ v ∉ A, 2 ≤ readers C v.val)
    (T : Finset (Fin n)) (core : T ⊆ Aᶜ) (budget : T.card ≤ 2 * spare n A C)
    (color : Fin n → Bool)
    (proper : ∀ i j, G.Adj i j → i ∉ T → j ∉ T → color i ≠ color j) :
    A.card + G.edgeSet.ncard + k ≤ C.size + 1 := by
  classical
  let U := Aᶜ \ T
  let left := U.filter (fun v => color v = false)
  let right := U.filter (fun v => color v = true)
  have cover (b : Bool) : ∀ i j, G.Adj i j →
      i ∈ T ∪ U.filter (fun v => color v = b) ∨ j ∈ T ∪ U.filter (fun v => color v = b) := by
    intro i j hij
    by_cases ip : i ∈ T
    · exact Or.inl (Finset.mem_union_left _ ip)
    by_cases jp : j ∈ T
    · exact Or.inr (Finset.mem_union_left _ jp)
    have iU : i ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hnoA i j hij),ip⟩
    have jU : j ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (hnoA j i hij.symm),jp⟩
    have different := proper i j hij ip jp
    by_cases h : color i = b
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨iU,h⟩))
    · have h' : color j = b := by cases b <;> cases hci : color i <;> cases hcj : color j <;> simp_all
      exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨jU,h'⟩))
  have l := htau _ (cover false)
  have r := htau _ (cover true)
  have lr : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro v hv h
    exact Bool.false_ne_true ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp h).2)
  have un : left ∪ right = U := by
    ext v
    simp only [left,right,Finset.mem_union,Finset.mem_filter]
    cases color v <;> simp
  have ct := Finset.card_union_of_disjoint lr
  rw [un] at ct
  have cl := Finset.card_union_le T left
  have cr := Finset.card_union_le T right
  change k ≤ (T ∪ left).card at l
  change k ≤ (T ∪ right).card at r
  have ucard : U.card = Aᶜ.card - T.card := Finset.card_sdiff_of_subset core
  have tc := Finset.card_le_card core
  have twice : 2*k ≤ Aᶜ.card + T.card := by omega
  have bound := core_budget n G A f C hf fan ev minC low
  have dA : ∀ a ∈ A, G.degree a = 0 := by
    intro a ha
    exact (G.degree_eq_zero a).2 (fun j h => hnoA a j h ha)
  have dB : ∀ a ∈ Aᶜ, G.degree a = 3 := by
    intro a ha
    rw [← G.ncard_neighborSet]
    exact hdeg a (Finset.mem_compl.1 ha)
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
  have hk : k ≤ Aᶜ.card := htau Aᶜ (fun u v huv => Or.inl (Finset.mem_compl.2 (hnoA u v huv)))
  have hedgeEq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  omega

end CubicReaderCount

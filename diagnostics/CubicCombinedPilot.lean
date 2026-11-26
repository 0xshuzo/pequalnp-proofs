import PEqualNP.Outside.L_meta_9004
import PEqualNP.Outside.L_meta_1743

import Mathlib
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
    have partition := Finset.sum_congr (s₁:=Finset.range C.gates.length) rfl
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
    have eq := Finset.sum_congr (s₁:=Aᶜ) rfl (fun v hv =>
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

namespace CubicGirthPacking

variable {n : ℕ} (G : SimpleGraph (Fin n))

def Independent (I : Finset (Fin n)) := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

private theorem noTriangle
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    {a b c : Fin n} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  let w : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
  have cyc : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨by simp [w,SimpleGraph.Walk.isPath_def,ab.ne,ab.ne.symm,bc.ne,ca.ne],by change 3 ≤ 3; decide⟩
  have h := girth _ w cyc
  change 7 ≤ 3 at h
  omega

private theorem noFive
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    {a b c d e : Fin n} (nd : [b,c,d,e,a].Nodup)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e) (ea : G.Adj e a) :
    False := by
  let w : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons de (.cons ea .nil))))
  have cyc : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨by simpa [w,SimpleGraph.Walk.isPath_def] using nd,by change 3 ≤ 5; decide⟩
  have h := girth _ w cyc
  change 7 ≤ 5 at h
  omega

private theorem exchange {U I T S : Finset (Fin n)}
    (iu : I ⊆ U) (ind : Independent G I)
    (maximal : ∀ J ⊆ U, Independent G J → J.card ≤ I.card)
    (ti : T ⊆ I) (so : S ⊆ U \ I) (si : Independent G S)
    (neighbors : ∀ a ∈ S, ∀ b ∈ I, G.Adj a b → b ∈ T) : S.card ≤ T.card := by
  classical
  let J := (I \ T) ∪ S
  have ju : J ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with h|h
    · exact iu (Finset.mem_sdiff.mp h).1
    · exact (Finset.mem_sdiff.mp (so h)).1
  have ji : Independent G J := by
    intro a ha b hb edge
    rcases Finset.mem_union.mp ha with ha|ha <;> rcases Finset.mem_union.mp hb with hb|hb
    · exact ind _ (Finset.mem_sdiff.mp ha).1 _ (Finset.mem_sdiff.mp hb).1 edge
    · exact (Finset.mem_sdiff.mp ha).2 (neighbors b hb a (Finset.mem_sdiff.mp ha).1 edge.symm)
    · exact (Finset.mem_sdiff.mp hb).2 (neighbors a ha b (Finset.mem_sdiff.mp hb).1 edge)
    · exact si a ha b hb edge
  have dis : Disjoint (I \ T) S := Finset.disjoint_left.mpr (fun a ha hs =>
    (Finset.mem_sdiff.mp (so hs)).2 (Finset.mem_sdiff.mp ha).1)
  have count := maximal J ju ji
  have size := Finset.card_union_of_disjoint dis
  have left := Finset.card_sdiff_add_card_eq_card ti
  change ((I \ T) ∪ S).card ≤ I.card at count
  omega

private theorem countPairs [DecidableRel G.Adj] (X Y : Finset (Fin n)) :
    (∑ x ∈ X, (Y.filter fun y => G.Adj x y).card) =
      ∑ y ∈ Y, (X.filter fun x => G.Adj y x).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : G.Adj a b
  · simp [h,h.symm]
  · have hb : ¬ G.Adj b a := fun e => h e.symm
    simp [h,hb]

set_option maxHeartbeats 4000000 in
/-- A cubic graph of girth at least six has an independent set containing
at least a five-fourteenths fraction of its nonisolated vertices. -/
theorem five_fourteenths (A : Finset (Fin n))
    (cubic : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (ordinary : ∀ v w, G.Adj v w → v ∉ A)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) :
    ∃ I ⊆ Aᶜ, Independent G I ∧ 5 * Aᶜ.card ≤ 14 * I.card := by
  classical
  let U := Aᶜ
  let candidates := U.powerset.filter (Independent G)
  have empty : (∅ : Finset (Fin n)) ∈ candidates := by simp [candidates,Independent]
  obtain ⟨I,hi,hm⟩ := candidates.exists_max_image Finset.card ⟨∅,empty⟩
  have iu : I ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hi).1
  have ind : Independent G I := (Finset.mem_filter.mp hi).2
  have maximal (J : Finset (Fin n)) (ju : J ⊆ U) (ji : Independent G J) : J.card ≤ I.card :=
    hm J (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ju,ji⟩)
  let O := U \ I
  let N (v : Fin n) := I.filter fun i => G.Adj v i
  let L := O.filter fun v => (N v).card = 1
  let M := O.filter fun v => (N v).card = 2
  let P := I.filter fun i => ∃ a ∈ L, G.Adj a i
  let Q := I \ P
  have psub : P ⊆ I := Finset.filter_subset _ _
  have degree (v : Fin n) (vu : v ∈ U) : (G.neighborSet v).toFinset.card = 3 := by
    rw [← Set.ncard_eq_toFinset_card']
    exact cubic v (Finset.mem_compl.mp vu)
  have countRange (v : Fin n) (vo : v ∈ O) : 1 ≤ (N v).card ∧ (N v).card ≤ 3 := by
    have vu := (Finset.mem_sdiff.mp vo).1
    have cap : N v ⊆ (G.neighborSet v).toFinset := by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2
    refine ⟨?_,(Finset.card_le_card cap).trans (degree v vu).le⟩
    by_contra! none
    have no : N v = ∅ := Finset.card_eq_zero.mp (by omega)
    have stuck := exchange G iu ind maximal (T:=∅) (S:={v}) (by simp) (Finset.singleton_subset_iff.mpr vo)
      (by intro a ha b hb; simpa only [Finset.mem_singleton.mp ha,Finset.mem_singleton.mp hb] using (G.loopless.irrefl v))
      (by
        intro a ha b hb ab
        have eq : a = v := Finset.mem_singleton.mp ha
        have hit : b ∈ N v := Finset.mem_filter.mpr ⟨hb,eq ▸ ab⟩
        simpa [no] using hit)
    simp at stuck
  have unique {a i : Fin n} (al : a ∈ L) (ii : i ∈ I) (ai : G.Adj a i) :
      ∀ b ∈ I, G.Adj a b → b = i := by
    have one := (Finset.mem_filter.mp al).2
    have cap : (N a).card ≤ 1 := one.le
    intro b bi ab
    exact Finset.card_le_one.mp cap b (Finset.mem_filter.mpr ⟨bi,ab⟩) i (Finset.mem_filter.mpr ⟨ii,ai⟩)
  have atMostOne (i : Fin n) (ii : i ∈ I) : (L.filter fun a => G.Adj i a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨al,ia⟩ := Finset.mem_filter.mp ha
    obtain ⟨bl,ib⟩ := Finset.mem_filter.mp hb
    by_contra ab
    have sa : ({a,b} : Finset (Fin n)) ⊆ O := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|h
      · exact (Finset.mem_filter.mp al).1
      · simpa only [Finset.mem_singleton.mp h] using (Finset.mem_filter.mp bl).1
    have ni : ¬ G.Adj a b := fun e => noTriangle G girth ia e ib.symm
    have si : Independent G {a,b} := by
      intro v hv w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
      all_goals first | exact G.loopless.irrefl _ | exact ni | exact fun e => ni e.symm
    have ex := exchange G iu ind maximal (T:={i}) (by simpa using ii) sa si (by
      intro z hz y yi zy
      apply Finset.mem_singleton.mpr
      rcases Finset.mem_insert.mp hz with rfl|h
      · exact unique al ii ia.symm _ yi zy
      · obtain rfl := Finset.mem_singleton.mp h
        exact unique bl ii ib.symm _ yi zy)
    simp [ab] at ex
  have lbound : L.card ≤ P.card := by
    have h (a : Fin n) (al : a ∈ L) : (P.filter fun i => G.Adj a i).card = 1 := by
      have eq : P.filter (fun i => G.Adj a i) = N a := by
        ext i
        simp only [P,N,Finset.mem_filter]
        exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,a,al,h.2⟩,h.2⟩⟩
      rw [eq]
      exact (Finset.mem_filter.mp al).2
    have c := countPairs G L P
    rw [Finset.sum_congr rfl h] at c
    have cap (i : Fin n) (hi : i ∈ P) : (L.filter fun a => G.Adj i a).card ≤ 1 :=
      atMostOne i (psub hi)
    have b := Finset.sum_le_sum cap
    simpa using (c.le.trans b)
  have twoTouch (z : Fin n) (zm : z ∈ M) : ∃ i ∈ Q, G.Adj z i := by
    obtain ⟨zo,cs⟩ := Finset.mem_filter.mp zm
    obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (by omega : 1 < (N z).card)
    obtain ⟨ii,zi⟩ := Finset.mem_filter.mp hi
    obtain ⟨ji,zj⟩ := Finset.mem_filter.mp hj
    have full : N z = {i,j} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
      · simp [ij,cs]
    by_contra! bad
    have ip : i ∈ P := by
      by_contra ni
      exact bad i (Finset.mem_sdiff.mpr ⟨ii,ni⟩) zi
    have jp : j ∈ P := by
      by_contra nj
      exact bad j (Finset.mem_sdiff.mpr ⟨ji,nj⟩) zj
    obtain ⟨l,ll,li⟩ := (Finset.mem_filter.mp ip).2
    obtain ⟨r,rr,rj⟩ := (Finset.mem_filter.mp jp).2
    have lo := (Finset.mem_filter.mp ll).1
    have ro := (Finset.mem_filter.mp rr).1
    have lr : l ≠ r := by
      rintro rfl
      exact ij (unique rr ji rj i ii li)
    have lz : l ≠ z := by
      rintro rfl
      have := (Finset.mem_filter.mp ll).2
      omega
    have rz : r ≠ z := by
      rintro rfl
      have := (Finset.mem_filter.mp rr).2
      omega
    have li' : l ≠ i := li.ne
    have rj' : r ≠ j := rj.ne
    have lj : l ≠ j := fun e => (Finset.mem_sdiff.mp lo).2 (e ▸ ji)
    have ri : r ≠ i := fun e => (Finset.mem_sdiff.mp ro).2 (e ▸ ii)
    have zl : ¬G.Adj z l := fun zv => noTriangle G girth zi li.symm zv.symm
    have zr : ¬G.Adj z r := fun zv => noTriangle G girth zj rj.symm zv.symm
    have llr : ¬G.Adj l r := by
      intro e
      apply noFive G girth (a:=i) (b:=z) (c:=j) (d:=r) (e:=l) _ zi.symm zj rj.symm e.symm li
      simp [zj.ne,rz.symm,lz.symm,zi.ne,rj'.symm,lj.symm,ij.symm,lr.symm,ri,li']
    have so : ({z,l,r} : Finset (Fin n)) ⊆ O := by
      simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro zo (And.intro lo ro)
    have si : Independent G {z,l,r} := by
      intro v hv w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl
      all_goals first | exact G.loopless.irrefl _ | assumption | exact fun e => zl e.symm | exact fun e => zr e.symm | exact fun e => llr e.symm
    have ex := exchange G iu ind maximal (T:={i,j}) (by simpa using And.intro ii ji) so si (by
      intro x hx y yi xy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · have hit : y ∈ N z := Finset.mem_filter.mpr ⟨yi,xy⟩
        simpa [full] using hit
      · exact Or.inl (unique ll ii li _ yi xy)
      · exact Or.inr (unique rr ji rj _ yi xy))
    simp [ij,lz.symm,rz.symm,lr] at ex
  have mBound : M.card ≤ 3 * Q.card := by
    have lo (z : Fin n) (zM : z ∈ M) : 1 ≤ (Q.filter fun i => G.Adj z i).card := by
      obtain ⟨i,hi,zi⟩ := twoTouch z zM
      exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,zi⟩⟩
    have hi (i : Fin n) (iq : i ∈ Q) : (M.filter fun z => G.Adj i z).card ≤ 3 := by
      have sub : M.filter (fun z => G.Adj i z) ⊆ (G.neighborSet i).toFinset :=
        fun z hz => by simpa using (Finset.mem_filter.mp hz).2
      exact (Finset.card_le_card sub).trans (degree i (iu (Finset.mem_sdiff.mp iq).1)).le
    have comp := (Finset.sum_le_sum lo).trans ((countPairs G M Q).le.trans (Finset.sum_le_sum hi))
    simpa [Nat.mul_comm] using comp
  have total : (∑ v ∈ O, (N v).card) = 3*I.card := by
    have deg (i : Fin n) (ii : i ∈ I) : (O.filter fun v => G.Adj i v).card = 3 := by
      have eq : O.filter (fun v => G.Adj i v) = (G.neighborSet i).toFinset := by
        ext v
        simp only [Finset.mem_filter,Set.mem_toFinset,SimpleGraph.mem_neighborSet,O,Finset.mem_sdiff,U,Finset.mem_compl]
        exact ⟨fun h => h.2,fun e => ⟨⟨ordinary v i e.symm,fun vi => ind i ii v vi e⟩,e⟩⟩
      rw [eq]
      exact degree i (iu ii)
    change (∑ v ∈ O, (I.filter fun i => G.Adj v i).card) = _
    rw [countPairs,Finset.sum_congr rfl deg]
    simp [Nat.mul_comm]
  have per (v : Fin n) (h : v ∈ O) :
      (N v).card + 2*(if (N v).card=1 then 1 else 0) + (if (N v).card=2 then 1 else 0) = 3 := by
    have b := countRange v h
    split_ifs <;> omega
  have per' (v : Fin n) (h : v ∈ O) :
      (if (N v).card=1 then 1 else 0) + 2*(if (N v).card=2 then 1 else 0) ≤ (N v).card := by
    have b := countRange v h
    split_ifs <;> omega
  have id := Finset.sum_congr (s₁:=O) rfl per
  have bound := Finset.sum_le_sum per'
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.card_filter,Finset.sum_const,smul_eq_mul,total] at id bound
  change 3*I.card + 2*L.card + M.card = O.card*3 at id
  change L.card + 2*M.card ≤ 3*I.card at bound
  have q := Finset.card_sdiff_add_card_eq_card psub
  have o := Finset.card_sdiff_add_card_eq_card iu
  change Q.card + P.card = I.card at q
  change O.card + I.card = U.card at o
  refine ⟨I,iu,ind,?_⟩
  change 5*U.card ≤ 14*I.card
  omega

end CubicGirthPacking


namespace CubicThreshold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CubicReaderCount CubicGirthPacking

variable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))

private theorem edgeBalance (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (apart : ∀ i j, G.Adj i j → i ∉ A) : 2 * G.edgeSet.ncard = 3 * Aᶜ.card := by
  classical
  have dA : ∀ a ∈ A, G.degree a = 0 := by
    intro a ha
    exact (G.degree_eq_zero a).2 (fun j h => apart a j h ha)
  have dB : ∀ a ∈ Aᶜ, G.degree a = 3 := by
    intro a ha
    rw [← G.ncard_neighborSet]
    exact deg a (Finset.mem_compl.mp ha)
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dB] at degreeSum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
  rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  omega

private theorem of_independent {k : ℕ}
    (apart : ∀ i j, G.Adj i j → i ∉ A) (I : Finset (Fin n)) (iU : I ⊆ Aᶜ)
    (ind : Independent G I)
    (demand : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) :
    k + I.card ≤ Aᶜ.card := by
  classical
  have cov : ∀ i j, G.Adj i j → i ∈ Aᶜ \ I ∨ j ∈ Aᶜ \ I := by
    intro i j ij
    by_cases hi : i ∈ I
    · refine Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (apart j i ij.symm),?_⟩)
      exact fun hj => ind i hi j hj ij
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (apart i j ij),hi⟩)
  have cost := demand _ cov
  have c := Finset.card_sdiff_add_card_eq_card iU
  omega

theorem high_surplus (k : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (apart : ∀ i j, G.Adj i j → i ∉ A)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (demand : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (spec : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (fan : FanInTwo C) (eval : circuitFun n C = f)
    (minimal : ∀ m, HasCircuitSize n f m → C.size ≤ m)
    (low : ∀ v ∉ A, 2 ≤ readers C v.val)
    (budget : Aᶜ.card ≤ 7 * spare n A C) :
    A.card + G.edgeSet.ncard + k ≤ C.size + 1 := by
  have base := core_budget n G A f C spec fan eval minimal low
  have es := edgeBalance G A deg apart
  obtain ⟨I,iU,ind,large⟩ := five_fourteenths G A deg apart girth
  have small := of_independent G A apart I iU ind demand
  omega

/-- Every failure of the posted inequality has an edge whose two closed
neighborhoods consist entirely of unmarked vertices with exactly two readers. -/
theorem clean_edge (k : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (apart : ∀ i j, G.Adj i j → i ∉ A)
    (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
    (demand : ∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (spec : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (fan : FanInTwo C) (eval : circuitFun n C = f)
    (minimal : ∀ m, HasCircuitSize n f m → C.size ≤ m)
    (low : ∀ v ∉ A, 2 ≤ readers C v.val)
    (failure : C.size + 1 < A.card + G.edgeSet.ncard + k) :
    ∃ u v, G.Adj u v ∧ ∀ z, z = u ∨ z = v ∨ G.Adj u z ∨ G.Adj v z →
      z ∉ A ∧ readers C z.val = 2 := by
  classical
  let U := Aᶜ
  let H := U.filter fun v => 3 ≤ readers C v.val
  let B (v : Fin n) := insert v (G.neighborSet v).toFinset
  let closed := H.biUnion B
  let S := U \ closed
  have density : 7 * spare n A C < U.card := by
    by_contra! plentiful
    have b := high_surplus G A k f C deg apart girth demand spec fan eval minimal low plentiful
    omega
  have high : H.card ≤ spare n A C := by
    have pointwise (v : Fin n) (_ : v ∈ U) :
        (if 3 ≤ readers C v.val then 1 else 0) ≤ readers C v.val - 2 := by
      split_ifs <;> omega
    have sum := Finset.sum_le_sum pointwise
    rw [← Finset.card_filter] at sum
    change H.card ≤ ∑ v ∈ Aᶜ, (readers C v.val-2) at sum
    unfold spare
    omega
  have bound : closed.card ≤ H.card * 4 := by
    apply Finset.card_biUnion_le_card_mul
    intro v vh
    have vU := (Finset.mem_filter.mp vh).1
    have d := deg v (Finset.mem_compl.mp vU)
    rw [Set.ncard_eq_toFinset_card'] at d
    exact (Finset.card_insert_le _ _).trans (by omega)
  have big : U.card ≤ S.card + closed.card := by
    have sub : U ⊆ S ∪ closed := by
      intro v vu
      by_cases c : v ∈ closed
      · exact Finset.mem_union_right _ c
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨vu,c⟩)
    exact (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have base := core_budget n G A f C spec fan eval minimal low
  have es := edgeBalance G A deg apart
  have edge : ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
    by_contra! empty
    have sub : S ⊆ Aᶜ := fun _ h => (Finset.mem_sdiff.mp h).1
    have small := of_independent G A apart S sub empty demand
    change U.card ≤ _ at big
    change 7 * spare n A C < Aᶜ.card at density
    change Aᶜ.card ≤ S.card + closed.card at big
    omega
  obtain ⟨u,hu,v,hv,uv⟩ := edge
  have near (x : Fin n) (xs : x ∈ S) (z : Fin n) (zu : z ∈ U) (mem : x ∈ B z) :
      z ∉ A ∧ readers C z.val = 2 := by
    have ordinary := Finset.mem_compl.mp zu
    refine ⟨ordinary,?_⟩
    have lower := low z ordinary
    by_contra! ne
    have zh : z ∈ H := Finset.mem_filter.mpr ⟨zu,by omega⟩
    exact (Finset.mem_sdiff.mp xs).2 (Finset.mem_biUnion.mpr ⟨z,zh,mem⟩)
  refine ⟨u,v,uv,?_⟩
  intro z hz
  rcases hz with rfl|rfl|h|h
  · exact near u hu u (Finset.mem_sdiff.mp hu).1 (Finset.mem_insert_self _ _)
  · exact near v hv v (Finset.mem_sdiff.mp hv).1 (Finset.mem_insert_self _ _)
  · exact near u hu z (Finset.mem_compl.mpr (apart z u h.symm)) (Finset.mem_insert_of_mem (by simpa using h.symm))
  · exact near v hv z (Finset.mem_compl.mpr (apart z v h.symm)) (Finset.mem_insert_of_mem (by simpa using h.symm))

end CubicThreshold

namespace CubicRawPair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_9004

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))

private theorem andPair (u v : Fin n) (g : Gate) (p : g.inputs.Perm [u.val,v.val])
    (op : g.op = .and) (x : Fin n → Bool) (t : List Bool) :
    atBank g (List.ofFn x ++ t) = (x u && x v) := by
  rcases List.perm_pair.mp p with e|e <;>
    simp only [atBank,e,op,List.map_cons,List.map_nil,raw,GateOp.eval] <;>
    simp [Bool.and_comm]

private theorem mask {C : Circuit} {v : Fin n} {S : Finset (Fin n)}
    (fan : FanInTwo C) (out : n ≤ C.output)
    (fixed : ∀ g ∈ C.gates, v.val ∈ pins g → ∀ t,
      atBank g (List.ofFn (mark S) ++ t) = atBank g (List.ofFn (mark (insert v S)) ++ t)) :
    circuitFun n C (mark S) = circuitFun n C (mark (insert v S)) := by
  apply lockstep_all C _ _ out
  intro g hg t
  by_cases hit : v.val ∈ pins g
  · exact fixed g hg hit t
  · apply eval_from_pins _ _ _ (fan g hg)
    intro i hi
    apply same_pin
    rintro j rfl
    have jv : j ≠ v := by rintro rfl; exact hit hi
    simp [mark,jv]

private theorem offPair {a b : Fin n} (ao : a ∉ A) (bo : b ∉ A) (apart : ¬ G.Adj a b) :
    graphFun G A (mark {a,b}) = false := by
  simpa using off_triple G A a a b ao ao bo (G.loopless.irrefl a) apart apart

/-- An AND and an OR on distinct unmarked primary mates cannot be the only
effective readers of a cubic vertex. -/
theorem mixed_same (C : Circuit) (v a b : Fin n)
    (degree : (G.neighborSet v).ncard = 3)
    (girth : girthFive G) (ordinary : ∀ i j, G.Adj i j → i ∉ A)
    (bo : b ∉ A) (va : v ≠ a) (vb : v ≠ b)
    (fan : FanInTwo C) (ev : circuitFun n C = graphFun G A)
    (forms : ∀ g ∈ C.gates, v.val ∈ pins g →
      (g.op = .and ∧ g.inputs.Perm [v.val,a.val]) ∨ (g.op = .or ∧ g.inputs.Perm [v.val,b.val])) :
    a = b := by
  by_contra ab
  obtain ⟨p,q,s,vp,vq,vs,pq,ps,qs⟩ := three_neighbors G v degree
  obtain ⟨r,vr,ra,_,rb,br⟩ := free_neighbor girth va vb vp vq vs pq ps qs
  have out := not_raw_output G A C ev ordinary ⟨v,r,vr⟩
  have eq := mask (v:=v) (S:={b,r}) fan out (by
    intro g hg hv t
    rcases forms g hg hv with ⟨op,pair⟩|⟨op,pair⟩
    · rw [andPair v a g pair op,andPair v a g pair op]
      simp [mark,va.symm,ab,ra.symm]
    · rw [or_pair v b g pair op,or_pair v b g pair op]
      simp [mark])
  rw [ev,offPair G A bo (ordinary _ _ vr.symm) br,on_edge G A vr _ (by simp) (by simp)] at eq
  contradiction

/-- If both readers are raw-input ANDs, setting their mates to zero
leaves an untouched third neighbor witnessing dependence. -/
theorem not_two_and (C : Circuit) (v a b : Fin n)
    (degree : (G.neighborSet v).ncard = 3)
    (girth : girthFive G) (ordinary : ∀ i j, G.Adj i j → i ∉ A)
    (va : v ≠ a) (vb : v ≠ b)
    (fan : FanInTwo C) (ev : circuitFun n C = graphFun G A)
    (forms : ∀ g ∈ C.gates, v.val ∈ pins g → g.op = .and ∧
      (g.inputs.Perm [v.val,a.val] ∨ g.inputs.Perm [v.val,b.val])) : False := by
  obtain ⟨p,q,s,vp,vq,vs,pq,ps,qs⟩ := three_neighbors G v degree
  obtain ⟨r,vr,ra,_,rb,_⟩ := free_neighbor girth va vb vp vq vs pq ps qs
  have out := not_raw_output G A C ev ordinary ⟨v,r,vr⟩
  have eq := mask (v:=v) (S:={r}) fan out (by
    intro g hg hv t
    obtain ⟨op,pair|pair⟩ := forms g hg hv
    · rw [andPair v a g pair op,andPair v a g pair op]
      simp [mark,va.symm,ra.symm]
    · rw [andPair v b g pair op,andPair v b g pair op]
      simp [mark,vb.symm,rb.symm])
  rw [ev,off_one G A r (ordinary _ _ vr.symm),on_edge G A vr _ (by simp) (by simp)] at eq
  contradiction

def Comparator (v a : Fin n) (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.Perm [v.val,a.val]

/-- When a mixed pair shares a primary mate, another gate must read that
mate. Otherwise exchanging the two inputs preserves every gate output. -/
theorem outside_reader (C : Circuit) (v a : Fin n)
    (degree : (G.neighborSet v).ncard = 3)
    (girth : girthFive G) (ordinary : ∀ i j, G.Adj i j → i ∉ A)
    (ao : a ∉ A) (va : v ≠ a)
    (fan : FanInTwo C) (ev : circuitFun n C = graphFun G A)
    (forms : ∀ g ∈ C.gates, v.val ∈ pins g → Comparator v a g) :
    ∃ g ∈ C.gates, a.val ∈ pins g ∧ ¬ Comparator v a g := by
  by_contra! no
  obtain ⟨p,q,s,vp,vq,vs,pq,ps,qs⟩ := three_neighbors G v degree
  obtain ⟨r,vr,ra,ar,_,_⟩ := free_neighbor girth va va vp vq vs pq ps qs
  have out := not_raw_output G A C ev ordinary ⟨v,r,vr⟩
  have eq := lockstep_all C (mark {v,r}) (mark {a,r}) out (by
    intro g hg t
    by_cases hit : v.val ∈ pins g ∨ a.val ∈ pins g
    · obtain ⟨op,pair⟩ := hit.elim (forms g hg) (no g hg)
      rcases op with op|op
      · rw [andPair v a g pair op,andPair v a g pair op]
        simp [mark,va,va.symm,vr.ne,ra.symm]
      · rw [or_pair v a g pair op,or_pair v a g pair op]
        simp [mark]
    · apply eval_from_pins _ _ _ (fan g hg)
      intro i hi
      apply same_pin
      rintro j rfl
      have jv : j ≠ v := by rintro rfl; exact hit (Or.inl hi)
      have ja : j ≠ a := by rintro rfl; exact hit (Or.inr hi)
      simp [mark,jv,ja])
  change circuitFun n C _ = circuitFun n C _ at eq
  rw [ev,on_edge G A vr _ (by simp) (by simp),offPair G A ao (ordinary _ _ vr.symm) ar] at eq
  contradiction

/-- The fourth saving can be taken at the common mate of a mixed pair. -/
theorem mate_cut (C : Circuit) (v a : Fin n)
    (degree : (G.neighborSet v).ncard = 3)
    (girth : girthFive G) (ordinary : ∀ i j, G.Adj i j → i ∉ A)
    (ao : a ∉ A) (va : v ≠ a)
    (fan : FanInTwo C) (ev : circuitFun n C = graphFun G A)
    (minimum : ∀ m, HasCircuitSize n (graphFun G A) m → C.size ≤ m)
    (forms : ∀ g ∈ C.gates, v.val ∈ pins g → Comparator v a g)
    (gAnd gOr : Gate) (hand : gAnd ∈ C.gates) (hor : gOr ∈ C.gates)
    (opAnd : gAnd.op = .and) (opOr : gOr.op = .or)
    (insAnd : gAnd.inputs.Perm [v.val,a.val]) (insOr : gOr.inputs.Perm [v.val,a.val]) :
    ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x a false)) t := by
  obtain ⟨other,ho,readsOther,outside⟩ := outside_reader G A C v a degree girth ordinary ao va fan ev forms
  obtain ⟨p,q,s,vp,vq,vs,pq,ps,qs⟩ := three_neighbors G v degree
  obtain ⟨r,vr,ra,_,_,_⟩ := free_neighbor girth va va vp vq vs pq ps qs
  apply PEqualNP.Outside.L_meta_1743 n (graphFun G A) C a fan ev minimum
  · refine ⟨mark ∅,mark {v,r},?_⟩
    have off₁ : Function.update (mark ∅) a false = mark (∅ : Finset (Fin n)) := by
      funext i
      by_cases e : i=a <;> simp [e,mark,Function.update_of_ne]
    have off₂ : Function.update (mark {v,r}) a false = mark {v,r} := by
      funext i
      by_cases e : i=a <;> simp [e,mark,va.symm,ra.symm,Function.update_of_ne]
    rw [off₁,off₂,on_edge G A vr {v,r} (by simp) (by simp)]
    simp [graphFun,mark]
  · let rs := C.gates.filter fun g => (pins g).contains a.val
    have hAnd : gAnd ∈ rs := by
      apply List.mem_filter.mpr
      refine ⟨hand,List.contains_iff_mem.mpr ?_⟩
      rcases List.perm_pair.mp insAnd with e|e <;> simp [pins,opAnd,e,GateOp.eval]
    have hOr : gOr ∈ rs := by
      apply List.mem_filter.mpr
      refine ⟨hor,List.contains_iff_mem.mpr ?_⟩
      rcases List.perm_pair.mp insOr with e|e <;> simp [pins,opOr,e,GateOp.eval]
    have hOther : other ∈ rs := List.mem_filter.mpr ⟨ho,List.contains_iff_mem.mpr readsOther⟩
    have d₁ : gAnd ≠ gOr := by rintro rfl; rw [opAnd] at opOr; contradiction
    have d₂ : gAnd ≠ other := fun e => outside (e ▸ And.intro (Or.inl opAnd) insAnd)
    have d₃ : gOr ≠ other := fun e => outside (e ▸ And.intro (Or.inr opOr) insOr)
    classical
    have sub : ({gAnd,gOr,other} : Finset Gate) ⊆ rs.toFinset := by
      intro g hg
      simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      rcases hg with rfl|rfl|rfl <;> apply List.mem_toFinset.mpr <;> assumption
    have card := (Finset.card_le_card sub).trans (List.toFinset_card_le rs)
    simp [d₁,d₂,d₃] at card
    change 4 ≤ rs.length ∨ rs.length = 3 ∧ ∃ g ∈ rs, g.op ≠ .or
    by_cases four : 4 ≤ rs.length
    · exact Or.inl four
    · refine Or.inr ⟨by omega,gAnd,hAnd,?_⟩
      rw [opAnd]
      intro e
      cases e

end CubicRawPair

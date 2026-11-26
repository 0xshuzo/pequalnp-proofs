import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23391

open PEqualNP.CircuitLowerBounds


open PEqualNP.MetaComplexity

def formulaVars {n : ℕ} : DMFormula n → Set (Fin n)
  | .lit i _ => {i}
  | .and f g => formulaVars f ∪ formulaVars g
  | .or f g => formulaVars f ∪ formulaVars g

def positiveReadOnce {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False
  | .or f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False

def singletonInput {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun i => decide (i = a)

def pairInput {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i => decide (i = a ∨ i = b)

def cornerIndices {n : ℕ} (a b c d : Fin n) : Set (Fin n) := {a, b, c, d}

theorem formula_agree {n : ℕ} (f : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ i ∈ formulaVars f, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | lit i b =>
      have hi := h i (by simp [formulaVars])
      simp [DMFormula.eval, hi]
  | and f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]
  | or f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]

theorem formula_zero {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f) :
    f.eval (fun _ => false) = false := by
  induction f with
  | lit i b =>
      change b = true at h
      simp [DMFormula.eval, h]
  | and f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]
  | or f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]

theorem formula_mono {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    f.eval x = true → f.eval y = true := by
  induction f with
  | lit i b =>
      change b = true at h
      simpa [DMFormula.eval, h] using hxy i
  | and f g ihf ihg =>
      simp only [DMFormula.eval, Bool.and_eq_true]
      rintro ⟨hxF, hxG⟩
      exact ⟨ihf h.1 hxF, ihg h.2.1 hxG⟩
  | or f g ihf ihg =>
      simp only [DMFormula.eval, Bool.or_eq_true]
      rintro (hxF | hxG)
      · exact Or.inl (ihf h.1 hxF)
      · exact Or.inr (ihg h.2.1 hxG)

theorem input_pair_comm {n : ℕ} (a b : Fin n) : pairInput a b = pairInput b a := by
  funext i
  simp [pairInput, or_comm]

theorem formula_pair_swap {n : ℕ} (f : DMFormula n) (a : Fin n) {b c : Fin n}
    (hb : b ∉ formulaVars f) (hc : c ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (pairInput a c) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  have hindC : i ≠ c := fun he => hc (he ▸ hi)
  simp [pairInput, hindB, hindC]

theorem formula_pair_singleton {n : ℕ} (f : DMFormula n) (a : Fin n) {b : Fin n}
    (hb : b ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (singletonInput a) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  simp [pairInput, singletonInput, hindB]

theorem some_vars_of_pair {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f) {a b : Fin n}
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∨ b ∈ formulaVars f := by
  classical
  by_contra hab
  have hzero : f.eval (pairInput a b) = f.eval (fun _ => false) := by
    apply formula_agree
    intro i hi
    have hiA : i ≠ a := fun he => hab (Or.inl (he ▸ hi))
    have hiB : i ≠ b := fun he => hab (Or.inr (he ▸ hi))
    simp [pairInput, hiA, hiB]
  rw [h, formula_zero f hf] at hzero
  contradiction

theorem both_vars_of_pair {n : ℕ} (f : DMFormula n) {a b : Fin n}
    (hsa : f.eval (singletonInput a) = false)
    (hsb : f.eval (singletonInput b) = false)
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∧ b ∈ formulaVars f := by
  classical
  constructor
  · by_contra hA
    have he := formula_pair_singleton f b hA
    rw [← input_pair_comm a b, h, hsb] at he
    contradiction
  · by_contra hB
    have he := formula_pair_singleton f a hB
    rw [h, hsa] at he
    contradiction

theorem opposite_vars_of_and_pair {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b : Fin n}
    (hF : f.eval (pairInput a b) = true) (hG : g.eval (pairInput a b) = true) :
    a ∈ formulaVars f ↔ b ∉ formulaVars f := by
  rcases some_vars_of_pair f hf hF with hFa | hFb
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact False.elim (hfg a hFa hGa)
    · exact ⟨fun _ hFb => hfg b hFb hGb, fun _ => hFa⟩
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact ⟨fun hFa => False.elim (hfg a hFa hGa), fun hnFb => False.elim (hnFb hFb)⟩
    · exact False.elim (hfg b hFb hGb)

theorem formula_and_corner_side {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hacF : f.eval (pairInput a c) = true) (hacG : g.eval (pairInput a c) = true)
    (hadF : f.eval (pairInput a d) = true) (hadG : g.eval (pairInput a d) = true)
    (hbcF : f.eval (pairInput b c) = true) (hbcG : g.eval (pairInput b c) = true) :
    f.eval (pairInput b d) = true := by
  classical
  have hac := opposite_vars_of_and_pair f g hf hg hfg hacF hacG
  have had := opposite_vars_of_and_pair f g hf hg hfg hadF hadG
  have hbc := opposite_vars_of_and_pair f g hf hg hfg hbcF hbcG
  by_cases hA : a ∈ formulaVars f
  · exact (formula_pair_swap f b (had.mp hA) (hac.mp hA)).trans hbcF
  · have hC : c ∈ formulaVars f :=
      Classical.byContradiction (fun hnC => hA (hac.mpr hnC))
    have hB : b ∉ formulaVars f := fun hb => hbc.mp hb hC
    have he : f.eval (pairInput b d) = f.eval (pairInput a d) := by
      rw [input_pair_comm b d, input_pair_comm a d]
      exact formula_pair_swap f d hB hA
    exact he.trans hadF

theorem force_or_corner {n : ℕ} (f g : DMFormula n)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hsF : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hsG : ∀ i ∈ cornerIndices a b c d, g.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true ∨ g.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true ∨ g.eval (pairInput b c) = true) :
    f.eval (pairInput a d) = true ∧ f.eval (pairInput b c) = true := by
  have ha := both_vars_of_pair f (hsF a (by simp [cornerIndices]))
    (hsF c (by simp [cornerIndices])) hac
  constructor
  · rcases had with had | had
    · exact had
    · exact False.elim (hfg a ha.1
        (both_vars_of_pair g (hsG a (by simp [cornerIndices]))
          (hsG d (by simp [cornerIndices])) had).1)
  · rcases hbc with hbc | hbc
    · exact hbc
    · exact False.elim (hfg c ha.2
        (both_vars_of_pair g (hsG b (by simp [cornerIndices]))
          (hsG c (by simp [cornerIndices])) hbc).2)

theorem positive_read_once_corners {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f)
    (a b c d : Fin n)
    (hs : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true) : f.eval (pairInput b d) = true := by
  induction f with
  | lit i polarity =>
      change polarity = true at hf
      have ha : i = a ∨ i = c := by
        simpa [DMFormula.eval, hf, pairInput] using hac
      have hin : i ∈ cornerIndices a b c d := by
        rcases ha with h | h <;> simp [cornerIndices, h]
      have hi := hs i hin
      simp [DMFormula.eval, hf, singletonInput] at hi
  | and f g ihF ihG =>
      simp only [DMFormula.eval, Bool.and_eq_true] at hac had hbc ⊢
      exact
        ⟨formula_and_corner_side f g hf.1 hf.2.1 hf.2.2
            hac.1 hac.2 had.1 had.2 hbc.1 hbc.2,
          formula_and_corner_side g f hf.2.1 hf.1 (fun i hg hf' => hf.2.2 i hf' hg)
            hac.2 hac.1 had.2 had.1 hbc.2 hbc.1⟩
  | or f g ihF ihG =>
      simp only [DMFormula.eval, Bool.or_eq_true] at hac had hbc ⊢
      have hsF (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          f.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : f.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      have hsG (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          g.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : g.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      rcases hac with hacF | hacG
      · have h := force_or_corner f g hf.2.2 hsF hsG hacF had hbc
        exact Or.inl (ihF hf.1 hsF hacF h.1 h.2)
      · have h := force_or_corner g f (fun i hg hf' => hf.2.2 i hf' hg) hsG hsF
          hacG had.symm hbc.symm
        exact Or.inr (ihG hf.2.1 hsG hacG h.1 h.2)

theorem formula_singleton_false_of_pair {n : ℕ} (f : DMFormula n)
    (hf : positiveReadOnce f) (a b : Fin n) (h : f.eval (pairInput a b) = false) :
    f.eval (singletonInput a) = false := by
  cases hsingle : f.eval (singletonInput a) with
  | false => rfl
  | true =>
      have hsubset (i : Fin n) (hi : singletonInput a i = true) : pairInput a b i = true := by
        have he : i = a := of_decide_eq_true hi
        simp [pairInput, he]
      have hpair := formula_mono f hf hsubset hsingle
      exact False.elim (Bool.false_ne_true (h.symm.trans hpair))


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def expand (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) : Finset ℕ :=
  if wire ∈ live then live.erase wire ∪ deps.toFinset else live

theorem expand_le (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2) :
    (expand live wire deps).card ≤ live.card + 1 := by
  by_cases hw : wire ∈ live
  · rw [expand, ite_eq_left hw]
    have hs := Finset.card_erase_add_one hw
    have hu := Finset.card_union_le (live.erase wire) deps.toFinset
    have hdf := List.toFinset_card_le deps
    omega
  · simp [expand, hw]

theorem expand_full (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2)
    (he : (expand live wire deps).card = live.card + 1) :
    wire ∈ live ∧ deps.length = 2 ∧ deps.Nodup ∧ Disjoint (live.erase wire) deps.toFinset := by
  have hw : wire ∈ live := by
    by_contra hn
    simp [expand, hn] at he
  rw [expand, ite_eq_left hw] at he
  have hs := Finset.card_erase_add_one hw
  have hu := Finset.card_union_add_card_inter (live.erase wire) deps.toFinset
  have hdf := List.toFinset_card_le deps
  have hi : ((live.erase wire) ∩ deps.toFinset).card = 0 := by omega
  refine ⟨hw, by omega, ?_, ?_⟩
  · exact Multiset.toFinset_card_eq_card_iff_nodup.mp (by
      change deps.toFinset.card = deps.length
      omega)
  · exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)

def frontier : ℕ → List Gate → Finset ℕ → Finset ℕ
  | _, [], live => live
  | n, g :: gs, live => expand (frontier (n + 1) gs live) n (g.inputs.filter (· < n))

theorem frontier_le (n : ℕ) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (frontier n gs live).card ≤ live.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [frontier]
  | cons g gs ih =>
    have ht := ih (n + 1) (fun a ha => hf a (List.mem_cons_of_mem g ha))
    have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
    simpa [frontier, List.length_cons, Nat.add_assoc] using
      (expand_le (frontier (n + 1) gs live) n _ hg).trans (Nat.add_le_add_right ht 1)

theorem frontier_full (n : ℕ) (g : Gate) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ a ∈ g :: gs, a.inputs.length ≤ 2)
    (h : (frontier n (g :: gs) live).card = live.card + (g :: gs).length) :
    let rest := frontier (n + 1) gs live
    let deps := g.inputs.filter (· < n)
    rest.card = live.card + gs.length ∧ n ∈ rest ∧ deps.length = 2 ∧ deps.Nodup ∧
      Disjoint (rest.erase n) deps.toFinset := by
  dsimp only
  have ht := frontier_le (n + 1) gs live (fun a ha => hf a (List.mem_cons_of_mem g ha))
  have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
  have hb := expand_le (frontier (n + 1) gs live) n _ hg
  rw [frontier, List.length_cons] at h
  refine ⟨by omega, expand_full (frontier (n + 1) gs live) n _ hg ?_⟩
  omega

def Agree (live : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ live, x.getD i false = y.getD i false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst i; simp [step]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem agree_step (n : ℕ) (g : Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (expand live n (g.inputs.filter (· < n))) x y) :
    Agree live (step x g) (step y g) := by
  intro i hi
  rw [getD_step, getD_step, hx, hy]
  by_cases hn : i = n
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    congr 1
    apply List.map_congr_left
    intro j hj
    by_cases hjn : j < n
    · apply ha j
      simp [expand, hi, hj, hjn]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · rw [ite_eq_right hn, ite_eq_right hn]
    apply ha i
    by_cases h : n ∈ live
    · simp [expand, h, hi, hn]
    · simpa [expand, h] using hi

theorem agree_frontier (n : ℕ) (gs : List Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (frontier n gs live) x y) : Agree live (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing n x y with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih (n + 1) (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy]) ?_
    exact agree_step n g (frontier (n + 1) gs live) x y hx hy ha

theorem eval_agree_frontier (n : ℕ) (C : Circuit) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ frontier n C.gates {C.output}, x.getD i false = y.getD i false) :
    C.eval x = C.eval y :=
  agree_frontier n C.gates {C.output} x y hx hy h C.output (by simp)

def plug {m : ℕ} (t : Fin m) (r : DMFormula m) : DMFormula m → DMFormula m
  | .lit i b => if i = t then r else .lit i b
  | .and f g => .and (plug t r f) (plug t r g)
  | .or f g => .or (plug t r f) (plug t r g)

theorem plug_vars {m : ℕ} (t i : Fin m) (r f : DMFormula m) :
    i ∈ formulaVars (plug t r f) ↔
      (i ∈ formulaVars f ∧ i ≠ t) ∨ (t ∈ formulaVars f ∧ i ∈ formulaVars r) := by
  induction f with
  | lit j b =>
    by_cases h : j = t
    · subst j; simp [plug, formulaVars]
    · simp only [plug, h, ite_false, formulaVars, Set.mem_singleton_iff]
      grind
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug,formulaVars,Set.mem_union,ihf,ihg]
    constructor
    · rintro ((⟨h, hne⟩ | ⟨h, hr⟩) | (⟨h, hne⟩ | ⟨h, hr⟩))
      · exact Or.inl ⟨Or.inl h, hne⟩
      · exact Or.inr ⟨Or.inl h, hr⟩
      · exact Or.inl ⟨Or.inr h, hne⟩
      · exact Or.inr ⟨Or.inr h, hr⟩
    · rintro (⟨h | h, hne⟩ | ⟨h | h, hr⟩)
      · exact Or.inl (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inl ⟨h, hne⟩)
      · exact Or.inl (Or.inr ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, hr⟩)

theorem plug_read {m : ℕ} (t : Fin m) (r f : DMFormula m)
    (hr : positiveReadOnce r) (hf : positiveReadOnce f)
    (hs : ∀ i ∈ formulaVars f, i ≠ t → i ∈ formulaVars r → False) :
    positiveReadOnce (plug t r f) := by
  induction f with
  | lit i b =>
    by_cases h : i = t
    · simpa [plug, h] using hr
    · simpa [plug, h] using hf
  | and f g ihf ihg | or f g ihf ihg =>
    refine ⟨ihf hf.1 (fun i hi => hs i (Or.inl hi)),
      ihg hf.2.1 (fun i hi => hs i (Or.inr hi)), ?_⟩
    intro i hiF hiG
    rw [plug_vars] at hiF hiG
    rcases hiF with ⟨hiF, hiT⟩ | ⟨htF, hiR⟩ <;> rcases hiG with ⟨hiG, hiT'⟩ | ⟨htG, hiR'⟩
    · exact hf.2.2 i hiF hiG
    · exact hs i (Or.inl hiF) hiT hiR'
    · exact hs i (Or.inr hiG) hiT' hiR
    · exact hf.2.2 t htF htG

theorem plug_eval {m : ℕ} (t : Fin m) (r f : DMFormula m) (hf : positiveReadOnce f)
    (x : Fin m → Bool) : (plug t r f).eval x = f.eval (fun i => if i = t then r.eval x else x i) := by
  induction f with
  | lit i b =>
    change b = true at hf
    subst b
    by_cases h : i = t <;> simp [plug, DMFormula.eval, h]
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug, DMFormula.eval, ihf hf.1, ihg hf.2.1]

def value {m : ℕ} (w : List Bool) (i : Fin m) : Bool := w.getD i.val false

def supportsFrontier {m : ℕ} (live : Finset ℕ) (f : DMFormula m) : Prop :=
  ∀ i : Fin m, i.val ∈ live ↔ i ∈ formulaVars f

def twoGate {m : ℕ} (o : GateOp) (a b : Fin m) : DMFormula m :=
  match o with
  | .and => .and (.lit a true) (.lit b true)
  | _ => .or (.lit a true) (.lit b true)

theorem twoGate_vars {m : ℕ} (o : GateOp) (a b i : Fin m) :
    i ∈ formulaVars (twoGate o a b) ↔ i = a ∨ i = b := by
  cases o <;> simp only [twoGate, formulaVars, Set.mem_union, Set.mem_singleton_iff]

theorem twoGate_read {m : ℕ} (o : GateOp) (a b : Fin m) (hne : a ≠ b) :
    positiveReadOnce (twoGate o a b) := by
  cases o <;> simp [twoGate, formulaVars, positiveReadOnce, hne]

theorem twoGate_eval {m : ℕ} (g : Gate) (a b : Fin m) (x : List Bool)
    (ho : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hi : g.inputs = [a.val,b.val]) :
    (twoGate g.op a b).eval (value x) = g.op.eval (g.inputs.map fun j => x.getD j false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  rcases ho with h | h <;> simp [twoGate, DMFormula.eval, hi, h, value, GateOp.eval]

theorem frontier_tree {m : ℕ} (n : ℕ) (gs : List Gate) (live : Finset ℕ) (f : DMFormula m)
    (hn : n + gs.length ≤ m) (hr : positiveReadOnce f) (hm : supportsFrontier live f)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier n gs live).card = live.card + gs.length) :
    ∃ F : DMFormula m, positiveReadOnce F ∧ supportsFrontier (frontier n gs live) F ∧
      ∀ w : List Bool, w.length = n → F.eval (value w) = f.eval (value (gs.foldl step w)) := by
  induction gs generalizing n with
  | nil => exact ⟨f, hr, hm, fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ht, hmem, hlen, hnd, hdj⟩ :=
      frontier_full n g gs live (fun a ha => (hf a ha).2) hfull
    obtain ⟨F, hFr, hFm, hFe⟩ := ih (n + 1) (by simp only [List.length_cons] at hn; omega)
      (fun a ha => hf a (List.mem_cons_of_mem g ha)) ht
    have hg := hf g (by simp)
    have he : g.inputs.filter (· < n) = g.inputs :=
      List.filter_sublist.eq_of_length_le (by omega)
    have hb : n < m := by simp only [List.length_cons] at hn; omega
    let t : Fin m := ⟨n, hb⟩
    rw [he] at hlen hnd hdj
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
      cases he' : g.inputs with
      | nil => simp [he'] at hlen
      | cons a rest =>
        cases rest with
        | nil => simp [he'] at hlen
        | cons b tail =>
          have hc : tail = [] := by simpa [he'] using hlen
          exact ⟨a, b, by simp [hc]⟩
    have hn' := List.filter_eq_self.mp he
    have ha : a < n := of_decide_eq_true (hn' a (by simp [hab]))
    have hb' : b < n := of_decide_eq_true (hn' b (by simp [hab]))
    let A : Fin m := ⟨a, ha.trans hb⟩
    let B : Fin m := ⟨b, hb'.trans hb⟩
    have hab' : A ≠ B := by
      intro e
      have ea := congrArg Fin.val e
      simp [hab, show a = b from ea] at hnd
    let r := twoGate g.op A B
    have htv : t ∈ formulaVars F := (hFm t).mp hmem
    have hpd : ∀ i ∈ formulaVars F, i ≠ t → i ∈ formulaVars r → False := by
      intro i hif hit hir
      apply (Finset.disjoint_left.mp hdj) (a := i.val)
      · exact Finset.mem_erase.mpr ⟨fun equ => hit (Fin.ext equ), (hFm i).mpr hif⟩
      · obtain hi | hi := (twoGate_vars g.op A B i).mp hir <;> simp [hi, hab, A, B]
    refine ⟨plug t r F, plug_read t r F (twoGate_read g.op A B hab') hFr hpd, ?_, ?_⟩
    · intro i
      rw [frontier, expand, ite_eq_left hmem, he, Finset.mem_union, Finset.mem_erase,
        List.mem_toFinset, hFm i, plug_vars, twoGate_vars]
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqA : i.val = a ↔ i = A := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqB : i.val = b ↔ i = B := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false, hEqA, hEqB, htv, true_and]
      constructor
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨h2, fun e => h1 (hEq.mpr e)⟩
        · exact Or.inr h
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨fun e => h2 (hEq.mp e), h1⟩
        · exact Or.inr h
    · intro w hw
      rw [plug_eval t r F hFr]
      simp only [List.foldl_cons]
      rw [← hFe (step w g) (by simp [step, hw])]
      congr 1
      funext i
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [value, getD_step, hw, hEq]
      rw [show r.eval (value w) = g.op.eval (g.inputs.map fun j => w.getD j false) from
        twoGate_eval g A B w hg.1 hab]

theorem circuit_tree (n m : ℕ) (C : Circuit) (hn : n + C.gates.length ≤ m) (ho : C.output < m)
    (hf : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier n C.gates {C.output}).card = 1 + C.gates.length) :
    ∃ F : DMFormula m, positiveReadOnce F ∧ supportsFrontier (frontier n C.gates {C.output}) F ∧
      ∀ w : List Bool, w.length = n → F.eval (value w) = C.eval w := by
  let t : Fin m := ⟨C.output, ho⟩
  have hm : supportsFrontier {C.output} (.lit t true) := by
    intro i
    simpa [formulaVars] using (show i.val = C.output ↔ i = t from
      ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩)
  have h : (frontier n C.gates {C.output}).card = ({C.output} : Finset ℕ).card + C.gates.length := by
    simpa using hfull
  obtain ⟨F, fr, fm, fe⟩ := frontier_tree n C.gates {C.output} (.lit t true) hn rfl hm hf h
  refine ⟨F, fr, fm, ?_⟩
  intro w hw
  change F.eval (value w) = (C.gates.foldl step w).getD C.output false
  simpa [DMFormula.eval, value, t] using fe w hw


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ExtendsBits (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (x y : List Bool) (h : ExtendsBits x y) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => h.2 i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h.2 i ht⟩

theorem getD_snoc (x : List Bool) (b : Bool) : (x ++ [b]).getD x.length false = b := by
  simp

theorem gate_step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : ExtendsBits x y) : ExtendsBits (step x g) (step y g) := by
  refine ⟨by simp [step, h.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i x.length with hlt | heq | hgt
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 i hi
  · subst i
    rw [step, getD_snoc] at hi
    rw [h.1, step, getD_snoc]
    exact gate_map_mono g.op hop g.inputs x y h hi
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
    contradiction

theorem gates_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ExtendsBits x y) :
    ExtendsBits (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have ht : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (List.mem_cons_of_mem _ hk)
    exact ih ht _ _ (gate_step_mono g (hgs g (by simp)) x y hxy)

theorem circuit_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hxy : ExtendsBits x y) (hx : C.eval x = true) : C.eval y = true := by
  have hop g (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hC g hg).1
  exact (gates_mono C.gates hop x y hxy).2 C.output hx

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, step, Nat.add_comm, Nat.add_left_comm]

def Essential (C : Circuit) (n i : ℕ) : Prop :=
  ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ C.eval x ≠ C.eval y ∧
    ∀ k : ℕ, k ≠ i → x.getD k false = y.getD k false

def Trace (C : Circuit) (n : ℕ) (x : Fin (2*n) → Bool) (b : Bool) : Prop :=
  ∃ w : List Bool, w.length = n ∧ value w = x ∧ C.eval w = b

theorem corner_price (C : Circuit) (n : ℕ) (hm : Monotone2 C)
    (he : ∀ i < n, Essential C n i) (a b c d : Fin (2*n))
    (hs : ∀ i ∈ cornerIndices a b c d, Trace C n (singletonInput i) false)
    (hac : Trace C n (pairInput a c) true) (had : Trace C n (pairInput a d) true)
    (hbc : Trace C n (pairInput b c) true) (hbd : Trace C n (pairInput b d) false) :
    n ≤ C.size := by
  by_contra hsmall
  have hlen : C.gates.length < n := by change ¬ n ≤ C.gates.length at hsmall; omega
  have used : Finset.range n ⊆ frontier n C.gates {C.output} := by
    intro i hi
    obtain ⟨x, y, hx, hy, hne, hxy⟩ := he i (Finset.mem_range.mp hi)
    by_contra hnot
    apply hne
    apply eval_agree_frontier n C x y hx hy
    intro j hj
    exact hxy j (fun eq => hnot (eq ▸ hj))
  have hmin := Finset.card_le_card used
  rw [Finset.card_range] at hmin
  have bound := frontier_le n C.gates {C.output} (fun g hg => (hm g hg).2)
  rw [Finset.card_singleton] at bound
  have tight : (frontier n C.gates {C.output}).card = 1+C.gates.length := by omega
  have hout : C.output < 2*n := by
    obtain ⟨w, hw, _, val⟩ := hac
    by_contra h
    change (C.gates.foldl step w).getD C.output false = true at val
    rw [List.getD_eq_default _ _ (by rw [run_length, hw]; omega)] at val
    contradiction
  obtain ⟨f, hread, _, eval⟩ := circuit_tree n (2*n) C (by omega) hout hm tight
  have real (x : Fin (2*n) → Bool) (out : Bool) (h : Trace C n x out) : f.eval x = out := by
    obtain ⟨w, hw, rfl, hv⟩ := h
    exact (eval w hw).trans hv
  have htrue := positive_read_once_corners f hread a b c d
    (fun i hi => real _ _ (hs i hi)) (real _ _ hac) (real _ _ had) (real _ _ hbc)
  exact Bool.false_ne_true ((real _ _ hbd).symm.trans htrue)

def table (u : Fin 4) (v : Fin 6) : Bool := (838769 : ℕ).testBit (6 * u.val + v.val)

def oneWire (i : Fin 10) : List Bool := List.ofFn fun j : Fin 10 => decide (j = i)

theorem one_len (i : Fin 10) : (oneWire i).length = 10 := by simp [oneWire]
theorem pair_len (u : Fin 4) (v : Fin 6) : (oneEach u v).length = 10 := by simp [oneEach]

abbrev Witness := Fin 4 × Fin 6 × Fin 4 × Fin 6 × Fin 10

def witness (i : Fin 10) : Witness :=
  ([(0, 0, 2, 0, 4), (1, 0, 2, 0, 4), (2, 2, 0, 2, 6), (3, 0, 2, 0, 4), (0, 0, 0, 1, 0), (3, 1, 3, 2, 3), (2, 2, 2, 0, 2), (2, 3, 2, 0, 2), (0, 4, 0, 1, 0), (0, 5, 0, 1, 0)] : List Witness).getD i.val (0, 0, 2, 0, 4)

def certifies (i : Fin 10) (w : Witness) : Prop :=
  let (u,v,q,p,j) := w
  table u v = true ∧ table q p = false ∧
    (∀ k : Fin 10, (oneWire j).getD k.val false = true → (oneEach q p).getD k.val false = true) ∧
    ∀ k : Fin 10, k ≠ i → (oneWire j).getD k.val false = (oneEach u v).getD k.val false

instance (i : Fin 10) (w : Witness) : Decidable (certifies i w) := by
  rcases w with ⟨u,v,q,p,j⟩
  unfold certifies
  infer_instance

theorem witnesses : ∀ i : Fin 10, certifies i (witness i) := by decide +kernel

theorem one_false (C : Circuit) (hm : Monotone2 C) (hc : Represents table C)
    (j : Fin 10) (q : Fin 4) (p : Fin 6) (ha : table q p = false)
    (hh : ∀ k : Fin 10, (oneWire j).getD k.val false = true → (oneEach q p).getD k.val false = true) :
    C.eval (oneWire j) = false := by
  cases h : C.eval (oneWire j) with
  | false => rfl
  | true =>
    have he : ExtendsBits (oneWire j) (oneEach q p) := by
      refine ⟨(one_len _).trans (pair_len _ _).symm, ?_⟩
      intro k val
      by_cases hk : k < 10
      · exact hh ⟨k,hk⟩ val
      · rw [List.getD_eq_default _ _ (by rw [one_len]; omega)] at val
        contradiction
    have bad := circuit_mono C hm _ _ he h
    rw [hc _ _, ha] at bad
    contradiction

theorem mandatory (C : Circuit) (hm : Monotone2 C) (hc : Represents table C) :
    ∀ i < 10, Essential C 10 i := by
  intro i hi
  obtain ⟨u,v,q,p,j,hp,hn,hle,heq⟩ : ∃ (u : Fin 4) (v : Fin 6) (q : Fin 4) (p : Fin 6) (j : Fin 10),
      certifies ⟨i,hi⟩ (u,v,q,p,j) := by
    have aux (w : Witness) (hw : certifies ⟨i,hi⟩ w) :
        ∃ (u : Fin 4) (v : Fin 6) (q : Fin 4) (p : Fin 6) (j : Fin 10),
          certifies ⟨i,hi⟩ (u,v,q,p,j) := by
      rcases w with ⟨u,v,q,p,j⟩
      exact ⟨u,v,q,p,j,hw⟩
    exact aux _ (witnesses ⟨i,hi⟩)
  refine ⟨oneWire j, oneEach u v, one_len _, pair_len _ _, ?_, ?_⟩
  · rw [one_false C hm hc j q p hn hle, hc _ _, hp]
    decide
  · intro k hk
    by_cases h : k < 10
    · exact heq ⟨k,h⟩ (fun e => hk (congrArg Fin.val e))
    · rw [List.getD_eq_default _ _ (by rw [one_len]; omega),
          List.getD_eq_default _ _ (by rw [pair_len]; omega)]

theorem price (C : Circuit) (hm : Monotone2 C) (hc : Represents table C) : 10 ≤ C.size := by
  apply corner_price C 10 hm (mandatory C hm hc) 0 3 4 8
  · intro i hi
    have hi' : i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 8 := by simpa [cornerIndices] using hi
    rcases hi' with rfl | rfl | rfl | rfl
    · refine ⟨oneWire 0, one_len _, ?_, one_false C hm hc 0 0 1 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 20, value (oneWire 0) k = singletonInput 0 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 3, one_len _, ?_, one_false C hm hc 3 3 2 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 20, value (oneWire 3) k = singletonInput 3 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 4, one_len _, ?_, one_false C hm hc 4 2 0 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 20, value (oneWire 4) k = singletonInput 4 k := by decide +kernel
      exact h k
    · refine ⟨oneWire 8, one_len _, ?_, one_false C hm hc 8 2 4 (by decide) (by decide +kernel)⟩
      funext k
      have h : ∀ k : Fin 20, value (oneWire 8) k = singletonInput 8 k := by decide +kernel
      exact h k
  · refine ⟨oneEach (0 : Fin 4) (0 : Fin 6), pair_len _ _, ?_, (hc 0 0).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 20, value (oneEach (0 : Fin 4) (0 : Fin 6)) k = pairInput 0 4 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (0 : Fin 4) (4 : Fin 6), pair_len _ _, ?_, (hc 0 4).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 20, value (oneEach (0 : Fin 4) (4 : Fin 6)) k = pairInput 0 8 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (3 : Fin 4) (0 : Fin 6), pair_len _ _, ?_, (hc 3 0).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 20, value (oneEach (3 : Fin 4) (0 : Fin 6)) k = pairInput 3 4 k := by decide +kernel
    exact h k
  · refine ⟨oneEach (3 : Fin 4) (4 : Fin 6), pair_len _ _, ?_, (hc 3 4).trans (by decide)⟩
    funext k
    have h : ∀ k : Fin 20, value (oneEach (3 : Fin 4) (4 : Fin 6)) k = pairInput 3 8 k := by decide +kernel
    exact h k

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838769 : ℕ).testBit (6 * u.val + v.val)) 9) := by
  rintro ⟨C, hm, hs, hr⟩
  have hp := price C hm hr
  omega

end PEqualNP.Outside.L_meta_23391

theorem PEqualNP.Outside.L_meta_23391 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838769 : ℕ).testBit (6 * u.val + v.val)) 9) :=
  PEqualNP.Outside.L_meta_23391.result

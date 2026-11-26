import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8323

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pgRel (u v : Fin 42) : Bool :=
  decide (u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))

def adj (u v : Fin 42) : Bool :=
  pgRel u v || pgRel v u

def allEdges : Finset (Fin 42 × Fin 42) :=
  Finset.univ.filter fun e => pgRel e.1 e.2 = true

lemma pgRel_irrefl (u : Fin 42) : pgRel u u = false := by
  revert u; decide

lemma adj_symm (u v : Fin 42) : adj u v = adj v u := by
  simp [adj, Bool.or_comm]

lemma adj_irrefl (u : Fin 42) : adj u u = false := by
  simp [adj, pgRel_irrefl]

lemma diff_set_sidon :
    ∀ d1 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d2 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d3 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    ∀ d4 ∈ ([0, 5, 7, 17, 20] : List ℕ),
    (d1 + d4) % 21 = (d2 + d3) % 21 → d1 = d2 ∨ d1 = d3 := by
  decide

lemma pgRel_c4_aux (p1 p2 l1 l2 : Fin 42) (hp : p1 ≠ p2) (hl : l1 ≠ l2)
    (h11 : pgRel p1 l1 = true) (h12 : pgRel p1 l2 = true)
    (h21 : pgRel p2 l1 = true) (h22 : pgRel p2 l2 = true) : False := by
  unfold pgRel at h11 h12 h21 h22
  simp only [decide_eq_true_eq] at h11 h12 h21 h22
  set d1 := (l1.val + 21 - p1.val) % 21
  set d2 := (l2.val + 21 - p1.val) % 21
  set d3 := (l1.val + 21 - p2.val) % 21
  set d4 := (l2.val + 21 - p2.val) % 21
  have hmod : (d1 + d4) % 21 = (d2 + d3) % 21 := by
    have h1 : (l1.val + 21 - p1.val) + (l2.val + 21 - p2.val) =
              (l2.val + 21 - p1.val) + (l1.val + 21 - p2.val) := by omega
    calc (d1 + d4) % 21
        = ((l1.val + 21 - p1.val) + (l2.val + 21 - p2.val)) % 21 := by
          rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
      _ = ((l2.val + 21 - p1.val) + (l1.val + 21 - p2.val)) % 21 := by rw [h1]
      _ = (d2 + d3) % 21 := by rw [Nat.add_mod]
  have hsid := diff_set_sidon d1 h11.2.2 d2 h12.2.2 d3 h21.2.2 d4 h22.2.2 hmod
  rcases hsid with h12eq | h13eq
  · apply hl
    apply Fin.ext
    have hlt1 : l1.val < 42 := l1.isLt
    have hlt2 : l2.val < 42 := l2.isLt
    omega
  · apply hp
    apply Fin.ext
    omega

lemma pgRel_c4 : ∀ (a b c d : Fin 42), a ≠ b → c ≠ d →
    adj a c = true → adj a d = true → adj b c = true → adj b d = true → False := by
  intro a b c d hab hcd hac had hbc hbd
  unfold adj at hac had hbc hbd
  simp only [Bool.or_eq_true] at hac had hbc hbd
  have hlt : ∀ u v : Fin 42, pgRel u v = true → u.val < 21 ∧ 21 ≤ v.val := by
    intro u v h; unfold pgRel at h; simp only [decide_eq_true_eq] at h; exact ⟨h.1, h.2.1⟩
  rcases hac with hac | hca
  · have ha : a.val < 21 := (hlt a c hac).1
    have hc : 21 ≤ c.val := (hlt a c hac).2
    have had' : pgRel a d = true := had.resolve_right fun h => by have := (hlt d a h).2; omega
    have hd : 21 ≤ d.val := (hlt a d had').2
    have hbc' : pgRel b c = true := hbc.resolve_right fun h => by have := (hlt c b h).1; omega
    have hbd' : pgRel b d = true := hbd.resolve_right fun h => by have := (hlt d b h).1; omega
    exact pgRel_c4_aux a b c d hab hcd hac had' hbc' hbd'
  · have hc : c.val < 21 := (hlt c a hca).1
    have ha : 21 ≤ a.val := (hlt c a hca).2
    have hda' : pgRel d a = true := had.resolve_left fun h => by have := (hlt a d h).1; omega
    have hd : d.val < 21 := (hlt d a hda').1
    have hcb' : pgRel c b = true := hbc.resolve_left fun h => by have := (hlt b c h).2; omega
    have hdb' : pgRel d b = true := hbd.resolve_left fun h => by have := (hlt b d h).2; omega
    exact pgRel_c4_aux c d a b hcd hab hca hcb' hda' hdb'

lemma allEdges_card : allEdges.card = 105 := by
  let f : Fin 21 × Fin 5 → Fin 42 × Fin 42 := fun x =>
    let d : ℕ := ([0, 5, 7, 17, 20] : List ℕ)[x.2.val]'x.2.isLt
    (⟨x.1.val, by omega⟩, ⟨21 + (x.1.val + d) % 21, by omega⟩)
  have hcard : (Finset.univ : Finset (Fin 21 × Fin 5)).card = 105 := by decide
  rw [← hcard]
  symm
  refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
  · intro x _
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, f, pgRel, decide_eq_true_eq]
    refine ⟨by omega, by omega, ?_⟩
    rcases x with ⟨p, idx⟩
    fin_cases idx <;> simp <;> try omega
  · intro x _ y _ hxy
    rcases x with ⟨p1, i1⟩
    rcases y with ⟨p2, i2⟩
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at hxy
    have hp : p1 = p2 := Fin.ext hxy.1
    subst hp
    have h2 : (p1.val + ([0, 5, 7, 17, 20] : List ℕ)[i1.val]'i1.isLt) % 21 =
              (p1.val + ([0, 5, 7, 17, 20] : List ℕ)[i2.val]'i2.isLt) % 21 := by
      omega
    have hi : i1 = i2 := by
      fin_cases i1 <;> fin_cases i2 <;> simp_all <;> try omega
    subst hi; rfl
  · intro e he
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, pgRel, decide_eq_true_eq] at he
    obtain ⟨h1, h2, h3⟩ := he
    set p : Fin 21 := ⟨e.1.val, h1⟩
    set d := (e.2.val + 21 - e.1.val) % 21
    have hl_eq : e.2.val = 21 + (e.1.val + d) % 21 := by
      have hlt2 : e.2.val < 42 := e.2.isLt
      omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with hd | hd | hd | hd | hd
    · refine ⟨(p, 0), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 1), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 2), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 3), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]
    · refine ⟨(p, 4), Finset.mem_univ _, ?_⟩
      ext <;> simp [f, p, hl_eq, hd]

lemma adj_iff_pgRel (u v : Fin 42) :
    adj u v = true ↔ pgRel u v = true ∨ pgRel v u = true := by
  simp [adj]

def isOr (g : Gate) : Bool :=
  GateOp.casesOn g.op false true false (fun _ => false) false

lemma isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  cases h : g.op <;> simp [isOr, h]

def orCount (C : Circuit) : ℕ :=
  C.gates.countP isOr

def computes (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, pgRel u v = true ∧ x u = true ∧ x v = true

def clean (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin 42 → Bool, (C.wires (List.ofFn x)).getD (42 + j) false = true →
      C.eval (List.ofFn x) = true

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma getD_append_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_append_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_append_eq]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def wval (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_input (C : Circuit) (x : Fin 42 → Bool) (i : Fin 42) :
    wval C x i.val = x i := by
  unfold wval
  rw [wires_eq_run, run_input _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

lemma wval_gate (C : Circuit) (x : Fin 42 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (42 + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < 42 + j then wval C x i else false) := by
  unfold wval
  have := run_gate C.gates (List.ofFn x) j hj
  simpa [wires_eq_run] using this

lemma wval_oob (C : Circuit) (x : Fin 42 → Bool) (w : ℕ) (hw : 42 + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [wires_eq_run, List.getD_eq_default]
  rw [run_length]; simp; omega

lemma eval_eq_wval (C : Circuit) (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = wval C x C.output := rfl

lemma mono_wval (C : Circuit) (hM : Monotone2 C) {x y : Fin 42 → Bool}
    (hxy : ∀ i : Fin 42, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < 42
    · have hw' : wval C x (⟨w, h1⟩ : Fin 42).val = true := hw
      rw [wval_input] at hw'
      change wval C y (⟨w, h1⟩ : Fin 42).val = true
      rw [wval_input]
      exact hxy ⟨w, h1⟩ hw'
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hw ⊢
        rw [wval_gate C x j hj] at hw
        rw [wval_gate C y j hj]
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hw ⊢
          intro i hi
          have hwi := hw i hi
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw ⊢
          rcases hw with ⟨i, hi, hwi⟩
          refine ⟨i, hi, ?_⟩
          split_ifs at hwi ⊢ with hilt
          · exact ih i (by omega) hwi
      · rw [wval_oob C x w (by omega)] at hw
        cases hw

def singleIn (v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = v)

def pairIn (u v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = u ∨ i = v)

def supp (C : Circuit) (w : ℕ) : Finset (Fin 42) :=
  Finset.univ.filter fun v => wval C (singleIn v) w = true

lemma mem_supp (C : Circuit) (w : ℕ) (v : Fin 42) :
    v ∈ supp C w ↔ wval C (singleIn v) w = true := by
  simp [supp]

lemma supp_input (C : Circuit) (u : Fin 42) : supp C u.val = {u} := by
  ext v
  simp [mem_supp, wval_input, singleIn, eq_comm]

lemma supp_oob (C : Circuit) (w : ℕ) (hw : 42 + C.gates.length ≤ w) : supp C w = ∅ := by
  ext v
  simp [mem_supp, wval_oob C _ w hw]

lemma computes_single (C : Circuit) (hcomp : computes C) (v : Fin 42) :
    C.eval (List.ofFn (singleIn v)) = false := by
  cases h : C.eval (List.ofFn (singleIn v))
  · rfl
  · obtain ⟨a, b, hab, ha, hb⟩ := (hcomp (singleIn v)).mp h
    simp only [singleIn, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    rw [pgRel_irrefl] at hab
    cases hab

lemma supp_and_empty (C : Circuit) (hcomp : computes C) (hcl : clean C)
    (j : ℕ) (hj : j < C.gates.length) (hand : C.gates[j].op = GateOp.and) :
    supp C (42 + j) = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false, Bool.not_eq_true]
  by_contra h
  simp only [Bool.not_eq_false] at h
  have h1 := hcl j C.gates[j] (List.getElem?_eq_getElem hj) hand (singleIn v) h
  rw [computes_single C hcomp v] at h1
  cases h1

lemma supp_output_empty (C : Circuit) (hcomp : computes C) : supp C C.output = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false, Bool.not_eq_true]
  exact computes_single C hcomp v

def effSupp (C : Circuit) (j i : ℕ) : Finset (Fin 42) :=
  if i < 42 + j then supp C i else ∅

lemma supp_or_gate (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (hor : C.gates[j].op = GateOp.or)
    (v : Fin 42) :
    v ∈ supp C (42 + j) ↔ ∃ i ∈ C.gates[j].inputs, v ∈ effSupp C j i := by
  rw [mem_supp, wval_gate C _ j hj, hor]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq, effSupp]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    split_ifs at h ⊢ with hilt
    · exact (mem_supp C i v).mpr h
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    split_ifs at h ⊢ with hilt
    · exact (mem_supp C i v).mp h
    · simp at h

lemma sound_of_supp_empty (C : Circuit) (hM : Monotone2 C) (hcl : clean C) :
    ∀ w : ℕ, supp C w = ∅ → ∀ x : Fin 42 → Bool, wval C x w = true → C.eval (List.ofFn x) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hsem x hwx
    by_cases h1 : w < 42
    · exfalso
      have hmem : (⟨w, h1⟩ : Fin 42) ∈ supp C (⟨w, h1⟩ : Fin 42).val := by
        rw [supp_input]; simp
      change (⟨w, h1⟩ : Fin 42) ∈ supp C w at hmem
      rw [hsem] at hmem
      exact Finset.notMem_empty _ hmem
    · by_cases h2 : w < 42 + C.gates.length
      · set j := w - 42
        have hwj : w = 42 + j := by omega
        have hj : j < C.gates.length := by omega
        rw [hwj] at hsem hwx
        have hop := (hM C.gates[j] (List.getElem_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · exact hcl j C.gates[j] (List.getElem?_eq_getElem hj) hop x hwx
        · rw [wval_gate C x j hj, hop] at hwx
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwx
          rcases hwx with ⟨i, hi, hwi⟩
          split_ifs at hwi with hilt
          · have his : supp C i = ∅ := by
              ext v
              simp only [Finset.notMem_empty, iff_false]
              intro hv
              have hvj : v ∈ supp C (42 + j) :=
                (supp_or_gate C j hj hop v).mpr ⟨i, hi, by simp [effSupp, hilt, hv]⟩
              rw [hsem] at hvj
              exact Finset.notMem_empty _ hvj
            exact ih i (by omega) his x hwi
      · rw [wval_oob C x w (by omega)] at hwx
        cases hwx

def isMixedOr (C : Circuit) (j : ℕ) : Prop :=
  ∃ (hj : j < C.gates.length), C.gates[j].op = GateOp.or ∧
    (∃ a ∈ C.gates[j].inputs, effSupp C j a = ∅ ∧ a < 42 + j) ∧
    (∃ b ∈ C.gates[j].inputs, (effSupp C j b).Nonempty)

noncomputable def mixedOrCount (C : Circuit) : ℕ :=
  letI := Classical.propDecidable
  ((Finset.range C.gates.length).filter fun j => isMixedOr C j).card

def deadGate (m : ℕ) : Gate :=
  ⟨GateOp.and, [42 + m]⟩

def unmixOne (C : Circuit) (j a b : ℕ) : Circuit :=
  let m := C.gates.length
  let rep := fun w => if w = 42 + j then b else w
  let gs' := C.gates.mapIdx fun k g =>
    if k < j then g else if k = j then deadGate m else ⟨g.op, g.inputs.map rep⟩
  let out' := rep C.output
  { gates := gs' ++ [⟨GateOp.or, [out', a]⟩], output := 42 + m }

lemma unmixOne_length (C : Circuit) (j a b : ℕ) :
    (unmixOne C j a b).gates.length = C.gates.length + 1 := by
  simp [unmixOne]

lemma unmixOne_monotone2 (C : Circuit) (hM : Monotone2 C) (j a b : ℕ) :
    Monotone2 (unmixOne C j a b) := by
  intro g hg
  simp only [unmixOne, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · rw [List.mem_iff_getElem] at hg
    rcases hg with ⟨k, hk, rfl⟩
    simp only [List.length_mapIdx] at hk
    simp only [List.getElem_mapIdx]
    split_ifs
    · exact hM C.gates[k] (List.getElem_mem hk)
    · exact ⟨by simp [deadGate], by simp [deadGate]⟩
    · have hgk := hM C.gates[k] (List.getElem_mem hk)
      exact ⟨hgk.1, by simp [hgk.2]⟩
  · exact ⟨by simp, by simp⟩

lemma countP_mapIdx_replace {α : Type} (p : α → Bool) :
    ∀ (l : List α) (f : ℕ → α → α) (j : ℕ) (hj : j < l.length),
      (∀ k (hk : k < l.length), k ≠ j → p (f k l[k]) = p l[k]) →
      p l[j] = true → p (f j l[j]) = false →
      (l.mapIdx f).countP p + 1 = l.countP p := by
  intro l
  induction l with
  | nil => intro f j hj; simp at hj
  | cons x xs ih =>
    intro f j hj heq hbefore hafter
    simp only [List.mapIdx_cons, List.countP_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hbefore hafter
      have htail : (xs.mapIdx fun k y => f (k + 1) y).countP p = xs.countP p := by
        have hgen : ∀ (ys : List α) (g : ℕ → α → α),
            (∀ k (hk : k < ys.length), p (g k ys[k]) = p ys[k]) →
            (ys.mapIdx g).countP p = ys.countP p := by
          intro ys
          induction ys with
          | nil => intro _ _; simp
          | cons y ys' ihy =>
            intro g hg
            simp only [List.mapIdx_cons, List.countP_cons]
            have h0 := hg 0 (by simp)
            simp only [List.getElem_cons_zero] at h0
            rw [h0, ihy (fun k z => g (k + 1) z) (fun k hk => hg (k + 1) (by simp; omega))]
        exact hgen xs (fun k y => f (k + 1) y) (fun k hk => heq (k + 1) (by simp; omega) (by omega))
      rw [hbefore, hafter, htail]
      simp
    | succ j' =>
      simp only [List.getElem_cons_succ] at hbefore hafter
      have h0 : p (f 0 x) = p x := heq 0 (by simp) (by omega)
      have hrec := ih (fun k => f (k + 1)) j' (by simp at hj; omega)
        (fun k hk hne => heq (k + 1) (by simp; omega) (by omega)) hbefore hafter
      rw [h0]
      split_ifs <;> omega

lemma unmixOne_orCount (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) :
    orCount (unmixOne C j a b) = orCount C := by
  unfold orCount unmixOne
  rw [List.countP_append, List.countP_singleton]
  have htop : isOr ⟨GateOp.or, [if C.output = 42 + j then b else C.output, a]⟩ = true := rfl
  simp only [htop, ↓reduceIte]
  exact countP_mapIdx_replace isOr C.gates
    (fun k g => if k < j then g else if k = j then deadGate C.gates.length
      else ⟨g.op, g.inputs.map (fun w => if w = 42 + j then b else w)⟩)
    j hj
    (fun k _ hne => by split_ifs <;> simp [isOr])
    (by simp [isOr, hor])
    (by simp [deadGate, isOr])

lemma unmixOne_get (C : Circuit) (j a b k : ℕ) (hk : k < C.gates.length) :
    (unmixOne C j a b).gates[k]'(by rw [unmixOne_length]; omega) =
      if k < j then C.gates[k]
      else if k = j then deadGate C.gates.length
      else ⟨C.gates[k].op, C.gates[k].inputs.map fun w => if w = 42 + j then b else w⟩ := by
  unfold unmixOne
  rw [List.getElem_append_left (by simp [hk]), List.getElem_mapIdx]

lemma unmixOne_wval_props (C : Circuit) (hM : Monotone2 C) (j a b : ℕ)
    (hj : j < C.gates.length) (hor : C.gates[j].op = GateOp.or)
    (hinp : C.gates[j].inputs = [a, b] ∨ C.gates[j].inputs = [b, a])
    (ha : a < 42 + j) (hb : b < 42 + j) :
    let D := unmixOne C j a b
    (∀ x : Fin 42 → Bool, ∀ w < 42 + j, wval D x w = wval C x w) ∧
    (∀ x : Fin 42 → Bool, wval D x (42 + j) = false) ∧
    (∀ x : Fin 42 → Bool, ∀ w < 42 + C.gates.length, w ≠ 42 + j →
      (wval D x w = true → wval C x w = true) ∧
      (wval C x w = true → wval D x w = true ∨ wval C x a = true)) := by
  intro D
  have hDlen : D.gates.length = C.gates.length + 1 := unmixOne_length C j a b
  have hlt : ∀ x : Fin 42 → Bool, ∀ w < 42 + j, wval D x w = wval C x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h1 : w < 42
      · change wval D x (⟨w, h1⟩ : Fin 42).val = wval C x (⟨w, h1⟩ : Fin 42).val
        rw [wval_input, wval_input]
      · set k := w - 42
        have hwk : w = 42 + k := by omega
        have hk : k < C.gates.length := by omega
        have hkj : k < j := by omega
        rw [hwk, wval_gate D x k (by omega), wval_gate C x k hk, unmixOne_get C j a b k hk]
        simp only [hkj, ↓reduceIte]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hik
        · exact ih i (by omega) (by omega)
        · rfl
  have hdead : ∀ x : Fin 42 → Bool, wval D x (42 + j) = false := by
    intro x
    rw [wval_gate D x j (by omega), unmixOne_get C j a b j hj]
    simp only [lt_irrefl, ↓reduceIte, deadGate, List.map_cons, List.map_nil, GateOp.eval]
    have hnot : ¬(42 + C.gates.length < 42 + j) := by omega
    simp [hnot]
  have hmain : ∀ x : Fin 42 → Bool, ∀ w < 42 + C.gates.length, w ≠ 42 + j →
      (wval D x w = true → wval C x w = true) ∧
      (wval C x w = true → wval D x w = true ∨ wval C x a = true) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hne
      by_cases hltj : w < 42 + j
      · rw [hlt x w hltj]
        exact ⟨id, Or.inl⟩
      · set k := w - 42
        have hwk : w = 42 + k := by omega
        have hk : k < C.gates.length := by omega
        have hkj_not_lt : ¬(k < j) := by omega
        have hkj_ne : k ≠ j := by omega
        have hrep_prop : ∀ i : ℕ,
            ((if (if i = 42 + j then b else i) < 42 + k then wval D x (if i = 42 + j then b else i) else false) = true →
             (if i < 42 + k then wval C x i else false) = true) ∧
            ((if i < 42 + k then wval C x i else false) = true →
             (if (if i = 42 + j then b else i) < 42 + k then wval D x (if i = 42 + j then b else i) else false) = true ∨
             wval C x a = true) := by
          intro i
          by_cases hij : i = 42 + j
          · subst hij
            simp only [↓reduceIte, show b < 42 + k by omega, show 42 + j < 42 + k by omega,
              hlt x b hb, wval_gate C x j hj, hor]
            rcases hinp with hinp | hinp <;> rw [hinp] <;>
              simp [GateOp.eval, ha, hb] <;> tauto
          · simp only [hij, ↓reduceIte]
            split_ifs with hik
            · exact ih i (by omega) (by omega) hij
            · simp
        rw [hwk, wval_gate D x k (by omega), wval_gate C x k hk, unmixOne_get C j a b k hk]
        simp only [hkj_not_lt, hkj_ne, ↓reduceIte, List.map_map]
        have hop := (hM C.gates[k] (List.getElem_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          constructor
          · intro hDall i hi
            exact (hrep_prop i).1 (hDall i hi)
          · intro hCall
            by_cases hxa : wval C x a = true
            · exact Or.inr hxa
            · left
              intro i hi
              exact ((hrep_prop i).2 (hCall i hi)).resolve_right hxa
        · rw [hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          constructor
          · rintro ⟨i, hi, hDi⟩
            exact ⟨i, hi, (hrep_prop i).1 hDi⟩
          · rintro ⟨i, hi, hCi⟩
            rcases (hrep_prop i).2 hCi with hDi | hxa
            · exact Or.inl ⟨i, hi, hDi⟩
            · exact Or.inr hxa
  exact ⟨hlt, hdead, hmain⟩


def unsafeWire (C : Circuit) (w : Nat) := ∃x : Fin 42 → Bool,
  C.eval (List.ofFn x)=false ∧ wval C x w=true

noncomputable def hazards (C : Circuit) : Finset Nat := by
  classical
  exact (Finset.range C.gates.length).filter (fun j=>unsafeWire C (42+j))

def crossed (C : Circuit) := ∃ (j : Nat) (hj : j<C.gates.length) (a b : Nat),
    C.gates[j].op=.or ∧ (C.gates[j].inputs=[a,b] ∨ C.gates[j].inputs=[b,a]) ∧
    a<42+j ∧ b<42+j ∧ ¬ unsafeWire C a ∧ unsafeWire C b

theorem removeCrossed (C : Circuit) (hM : Monotone2 C) (hcomp : computes C)
    (has : crossed C) :
    ∃ D,Monotone2 D ∧ computes D ∧ orCount D=orCount C ∧ (hazards D).card < (hazards C).card := by
  classical
  obtain ⟨j,hj,a,b,hor,hinp,ha_lt,hb_lt,safe,bad⟩ := has
  have ha_sound (x : Fin 42 → Bool) (v : wval C x a=true) : C.eval (List.ofFn x)=true := by
    cases hv : C.eval (List.ofFn x)
    · exact (safe ⟨x,hv,v⟩).elim
    · rfl
  obtain ⟨z,neg,lit⟩ := bad
  have jlit : wval C z (42+j)=true := by
    rw [wval_gate C z j hj,hor]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    refine ⟨b,?_,by simpa [hb_lt] using lit⟩
    rcases hinp with hp|hp <;> simp [hp]
  have hout_ne : C.output ≠ 42+j := by
    intro eq
    rw [eval_eq_wval,eq,jlit] at neg
    contradiction
  let D := unmixOne C j a b
  have hDlen : D.gates.length = C.gates.length + 1 := unmixOne_length C j a b
  obtain ⟨hlt, hdead, hmain⟩ := unmixOne_wval_props C hM j a b hj hor hinp ha_lt hb_lt
  have hDtop : ∀ x : Fin 42 → Bool,
      D.eval (List.ofFn x) =
        ((if C.output < 42 + C.gates.length then wval D x C.output else false) || wval C x a) := by
    intro x
    rw [eval_eq_wval]
    change wval D x (42 + C.gates.length) = _
    rw [wval_gate D x C.gates.length (by omega)]
    have hlast : D.gates[C.gates.length]'(by omega) = ⟨GateOp.or, [C.output, a]⟩ := by
      simp [D, unmixOne, hout_ne]
    rw [hlast]
    simp only [List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, List.any_nil, Bool.or_false, id_eq, show a < 42 + C.gates.length by omega,
      ↓reduceIte]
    rw [show wval D x a = wval C x a from hlt x a ha_lt]
  have hDeval : ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    rw [hDtop x]
    by_cases hout_lt : C.output < 42 + C.gates.length
    · simp only [hout_lt, ↓reduceIte]
      have ⟨h1, h2⟩ := hmain x C.output hout_lt hout_ne
      cases hCx : C.eval (List.ofFn x)
      · rw [Bool.or_eq_false_iff]
        constructor
        · cases hDx : wval D x C.output
          · rfl
          · have := h1 hDx; rw [← eval_eq_wval, hCx] at this; cases this
        · cases hax : wval C x a
          · rfl
          · have := ha_sound x hax; rw [hCx] at this; cases this
      · rw [Bool.or_eq_true]
        exact h2 hCx
    · simp only [hout_lt, ↓reduceIte, Bool.false_or]
      have hCx : C.eval (List.ofFn x) = false := by
        rw [eval_eq_wval, wval_oob C x C.output (by omega)]
      rw [hCx]
      cases hax : wval C x a
      · rfl
      · have := ha_sound x hax; rw [hCx] at this; cases this
  have hDcomp : computes D := by
    intro x; rw [hDeval x]; exact hcomp x

  refine ⟨D,unmixOne_monotone2 C hM j a b,hDcomp,unmixOne_orCount C j a b hj hor,?_⟩
  apply Finset.card_lt_card
  have sub : hazards D ⊆ hazards C := by
    intro k hk
    obtain ⟨inside,x,xn,xon⟩ := Finset.mem_filter.mp hk
    have old : k<C.gates.length := by
      have sz := Finset.mem_range.mp inside
      by_contra! far
      have eq : k=C.gates.length := by omega
      subst k
      have disagree : D.eval (List.ofFn x)=true := xon
      rw [xn] at disagree
      contradiction
    have ne : k≠j := by
      intro eq
      subst k
      rw [hdead x] at xon
      contradiction
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr old,x, (hDeval x).symm.trans xn,
      (hmain x (42+k) (by omega) (by omega)).1 xon⟩
  apply (Finset.ssubset_iff_of_subset sub).2
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,z,neg,jlit⟩,?_⟩
  intro inside
  obtain ⟨_,x,_,on⟩:=Finset.mem_filter.mp inside
  rw [hdead x] at on
  contradiction

theorem noCrossed (C : Circuit) (hM : Monotone2 C) (hcomp : computes C) :
    ∃ D,Monotone2 D ∧ computes D ∧ orCount D=orCount C ∧ ¬ crossed D := by
  classical
  suffices aux : ∀ n,∀ K : Circuit,(hazards K).card=n → Monotone2 K → computes K →
      ∃ D,Monotone2 D ∧ computes D ∧ orCount D=orCount K ∧ ¬ crossed D by
    exact aux _ C rfl hM hcomp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K num mon comp
    by_cases yes : crossed K
    · obtain ⟨E,me,ec,ce,less⟩ := removeCrossed K mon comp yes
      obtain ⟨D,md,dc,cd,ok⟩ := ih _ (less.trans_le num.le) E rfl me ec
      exact ⟨D,md,dc,cd.trans ce,ok⟩
    · exact ⟨K,mon,comp,rfl,yes⟩

end PEqualNP.Outside.L_meta_8323

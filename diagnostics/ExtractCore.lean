import Mathlib
import PEqualNP.Defs

namespace TerminalExtraction

open PEqualNP.CircuitLowerBounds

def Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def value (w : ℕ → Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map w)

def specialize (r : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => ⟨.and, g.inputs.filterMap r⟩
  | .or =>
      if g.inputs.any (fun i => (r i).isNone) then ⟨.and, []⟩
      else ⟨.or, g.inputs.filterMap r⟩
  | .not =>
      match g.inputs with
      | [] => ⟨.not, []⟩
      | i :: _ =>
          match r i with
          | none => ⟨.or, []⟩
          | some j => ⟨.not, [j]⟩
  | .mod _ | .maj => ⟨.or, []⟩

lemma specialize_legal (r : ℕ → Option ℕ) (g : Gate) (h : Legal g) :
    Legal (specialize r g) := by
  rcases g with ⟨op, l⟩
  change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ l.length ≤ 2 at h
  obtain ⟨hop, hl⟩ := h
  have hlen := (List.length_filterMap_le r l).trans hl
  rcases hop with rfl | rfl | rfl
  · exact ⟨Or.inl rfl, hlen⟩
  · by_cases hit : l.any (fun i => (r i).isNone) = true
    · simp [specialize, hit, Legal]
    · simpa [specialize, hit, Legal] using hlen
  · cases l with
    | nil => simp [specialize, Legal]
    | cons i t => cases hr : r i <;> simp [specialize, hr, Legal]

lemma and_read (r : ℕ → Option ℕ) (w : ℕ → Bool) (l : List ℕ) :
    ((l.filterMap r).map w).all id =
      (l.map fun i => (r i).elim true w).all id := by
  induction l with
  | nil => rfl
  | cons i l ih => cases hr : r i <;> simp [hr, ih]

lemma or_read (r : ℕ → Option ℕ) (w : ℕ → Bool) (l : List ℕ) :
    (l.map fun i => (r i).elim true w).any id =
      (l.any (fun i => (r i).isNone) || ((l.filterMap r).map w).any id) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    cases hr : r i <;> simp [hr, ih, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma specialize_value (r : ℕ → Option ℕ) (g : Gate) (h : Legal g) (w : ℕ → Bool) :
    value w (specialize r g) = value (fun i => (r i).elim true w) g := by
  rcases g with ⟨op,l⟩
  obtain ⟨hop, _⟩ := h
  change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at hop
  rcases hop with rfl | rfl | rfl
  · exact and_read r w l
  · by_cases hit : l.any (fun i => (r i).isNone) = true
    · simp only [specialize, hit, ↓reduceIte]
      change true = (l.map fun i => (r i).elim true w).any id
      rw [or_read r w l, hit, Bool.true_or]
    · have off : l.any (fun i => (r i).isNone) = false := by simpa using hit
      simp only [specialize, hit, ↓reduceIte]
      change ((l.filterMap r).map w).any id = (l.map fun i => (r i).elim true w).any id
      rw [or_read r w l, off, Bool.false_or]
  · cases l with
    | nil => rfl
    | cons i t =>
      cases hr : r i <;> simp [value, specialize, hr, GateOp.eval]

def check (assumeTrue : Bool) (selected : ℕ → Bool) (k : ℕ) (gs : List Gate)
    (z : List Bool) : Bool :=
  match gs with
  | [] => true
  | g :: rest =>
      let v := value (fun i => z.getD i false) g
      let selectedHere := selected k
      (if selectedHere then v else true) &&
        check assumeTrue selected (k + 1) rest
          (z ++ [if assumeTrue && selectedHere then true else v])

lemma check_assume_true (selected : ℕ → Bool) (k : ℕ) (gs : List Gate) (z : List Bool) :
    check true selected k gs z = check false selected k gs z := by
  induction gs generalizing k z with
  | nil => rfl
  | cons g rest ih =>
    cases hs : selected k <;> cases hv : value (fun i => z.getD i false) g <;>
      simp only [check, hs, hv, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, ih]


def build (bound : ℕ) (selected : ℕ → Bool) (gs : List Gate)
    (refs : List (Option ℕ)) (fresh : ℕ) : List Gate × List Gate :=
  match gs with
  | [] => ([], [])
  | g :: rest =>
    let newGate := specialize (fun i => refs.getD i (some bound)) g
    if selected refs.length then
      let tail := build bound selected rest (refs ++ [none]) fresh
      (tail.1, newGate :: tail.2)
    else
      let tail := build bound selected rest (refs ++ [some fresh]) (fresh + 1)
      (newGate :: tail.1, tail.2)

def Fits (v : ℕ → Bool) (fresh : ℕ) (gs : List Gate) : Prop :=
  match gs with
  | [] => True
  | g :: rest => value v g = v fresh ∧ Fits v (fresh + 1) rest

lemma read_map (refs : List (Option ℕ)) (v : ℕ → Bool) (bound : ℕ) (hb : v bound = false)
    (i : ℕ) :
    (refs.map (fun t => t.elim true v)).getD i false = (refs.getD i (some bound)).elim true v := by
  have h := List.getD_map refs (some bound) (n := i) (fun t : Option ℕ => t.elim true v)
  simpa only [Option.elim_some, hb] using h

lemma build_size (bound : ℕ) (s : ℕ → Bool) (gs : List Gate) (refs : List (Option ℕ))
    (fresh : ℕ) :
    (build bound s gs refs fresh).1.length + (build bound s gs refs fresh).2.length = gs.length := by
  induction gs generalizing refs fresh with
  | nil => rfl
  | cons g gs ih =>
    by_cases hs : s refs.length = true
    · have h := ih (refs ++ [none]) fresh
      simp only [build, hs, ↓reduceIte, List.length_cons]
      omega
    · have h := ih (refs ++ [some fresh]) (fresh + 1)
      simp only [build, hs, ↓reduceIte, List.length_cons]
      omega

lemma build_sound (bound : ℕ) (s : ℕ → Bool) (gs : List Gate) (refs : List (Option ℕ))
    (fresh : ℕ) (v : ℕ → Bool) (hb : v bound = false)
    (hg : ∀ g ∈ gs, Legal g) (hf : Fits v fresh (build bound s gs refs fresh).1) :
    (build bound s gs refs fresh).2.all (value v) =
      check true s refs.length gs (refs.map fun t => t.elim true v) := by
  induction gs generalizing refs fresh with
  | nil => rfl
  | cons g gs ih =>
    let r := fun i => refs.getD i (some bound)
    let z := refs.map fun t => t.elim true v
    have val : value v (specialize r g) = value (fun i => z.getD i false) g := by
      rw [specialize_value r g (hg _ List.mem_cons_self)]
      apply congrArg (fun w => value w g)
      funext i
      exact (read_map refs v bound hb i).symm
    have ht (g' : Gate) (hm : g' ∈ gs) : Legal g' := hg g' (List.mem_cons_of_mem g hm)
    by_cases hs : s refs.length = true
    · have hf' : Fits v fresh (build bound s gs (refs ++ [none]) fresh).1 := by
        simpa only [build, hs, ↓reduceIte] using hf
      have hi := ih (refs ++ [none]) fresh ht hf'
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
        List.map_nil, Option.elim_none] at hi
      change (build bound s (g :: gs) refs fresh).2.all (value v) =
        check true s refs.length (g :: gs) z
      simp only [build, hs, ↓reduceIte, List.all_cons, check, Bool.true_and, hi]
      rw [show value v (specialize (fun i => refs.getD i (some bound)) g) =
        value (fun i => z.getD i false) g from val]
    · have hsf : s refs.length = false := by simpa using hs
      have hf' : value v (specialize r g) = v fresh ∧
          Fits v (fresh + 1) (build bound s gs (refs ++ [some fresh]) (fresh + 1)).1 := by
        simpa only [build, hs, ↓reduceIte, Fits, r] using hf
      have hi := ih (refs ++ [some fresh]) (fresh + 1) ht hf'.2
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
        List.map_nil, Option.elim_some] at hi
      change (build bound s (g :: gs) refs fresh).2.all (value v) =
        check true s refs.length (g :: gs) z
      simp only [build, hsf, Bool.false_eq_true, ↓reduceIte, check, Bool.true_and]
      have hv : v fresh = value (fun i => z.getD i false) g := hf'.1.symm.trans val
      simpa only [z, ← hv] using hi


lemma specialize_reads (r : ℕ → Option ℕ) (g : Gate) (j : ℕ)
    (hj : j ∈ (specialize r g).inputs) : ∃ i ∈ g.inputs, r i = some j := by
  rcases g with ⟨op,l⟩
  cases op with
  | and => exact List.mem_filterMap.mp hj
  | or =>
    by_cases hit : l.any (fun i => (r i).isNone) = true
    · simp [specialize, hit] at hj
    · apply List.mem_filterMap.mp
      simpa [specialize, hit] using hj
  | not =>
    cases l with
    | nil => simp [specialize] at hj
    | cons i t =>
      cases hr : r i with
      | none => simp [specialize, hr] at hj
      | some k =>
        have hk : j = k := by simpa [specialize, hr] using hj
        exact ⟨i, List.mem_cons_self, by simpa only [hk] using hr⟩
  | mod => simp [specialize] at hj
  | maj => simp [specialize] at hj

def RefsOK (bound fresh : ℕ) (refs : List (Option ℕ)) : Prop :=
  ∀ j, some j ∈ refs → j < fresh ∨ j = bound

def Ordered (bound fresh : ℕ) (gs : List Gate) : Prop :=
  match gs with
  | [] => True
  | g :: rest =>
      (∀ j ∈ g.inputs, j < fresh ∨ j = bound) ∧ Ordered bound (fresh + 1) rest

lemma build_ordered (bound : ℕ) (s : ℕ → Bool) (gs : List Gate) (refs : List (Option ℕ))
    (fresh : ℕ) (hr : RefsOK bound fresh refs) :
    Ordered bound fresh (build bound s gs refs fresh).1 := by
  induction gs generalizing refs fresh with
  | nil => trivial
  | cons g gs ih =>
    by_cases hs : s refs.length = true
    · simp only [build, hs, ↓reduceIte]
      apply ih
      intro j hj
      apply hr j
      simpa using hj
    · simp only [build, hs, ↓reduceIte, Ordered]
      constructor
      · intro j hj
        obtain ⟨k, _, hk⟩ := specialize_reads _ _ _ hj
        by_cases h : k < refs.length
        · rw [List.getD_eq_getElem _ _ h] at hk
          have hm : refs[k] ∈ refs := List.getElem_mem h
          rw [hk] at hm
          exact hr j hm
        · rw [List.getD_eq_default _ _ (by omega)] at hk
          exact Or.inr (Option.some.inj hk).symm
      · apply ih
        intro j hj
        rcases List.mem_append.mp hj with old | new
        · rcases hr j old with h | h
          · exact Or.inl (by omega)
          · exact Or.inr h
        · have h : j = fresh := by simpa using new
          exact Or.inl (by omega)

def run (gs : List Gate) (z : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value (fun k => w.getD k false) g]) z

lemma run_cons (g : Gate) (gs : List Gate) (z : List Bool) :
    run (g :: gs) z = run gs (z ++ [value (fun k => z.getD k false) g]) := rfl

lemma run_length (gs : List Gate) (z : List Bool) : (run gs z).length = z.length + gs.length := by
  induction gs generalizing z with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_keep (gs : List Gate) (z : List Bool) (k : ℕ) (hk : k < z.length) :
    (run gs z).getD k false = z.getD k false := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hk

lemma snoc_value (z : List Bool) (v : Bool) : (z ++ [v]).getD z.length false = v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

lemma run_head (g : Gate) (gs : List Gate) (z : List Bool) :
    (run (g :: gs) z).getD z.length false = value (fun k => z.getD k false) g := by
  rw [run_cons, run_keep _ _ _ (by simp), snoc_value]

lemma run_fits (bound : ℕ) (gs : List Gate) (z : List Bool)
    (ord : Ordered bound z.length gs) (room : z.length + gs.length ≤ bound) :
    Fits (fun i => (run gs z).getD i false) z.length gs := by
  induction gs generalizing z with
  | nil => trivial
  | cons g gs ih =>
    let read := fun i => (run (g :: gs) z).getD i false
    let next := z ++ [value (fun k => z.getD k false) g]
    have hn : next.length = z.length + 1 := by simp [next]
    change (∀ i ∈ g.inputs, i < z.length ∨ i = bound) ∧ Ordered bound (z.length + 1) gs at ord
    change value read g = read z.length ∧ Fits read (z.length + 1) gs
    constructor
    · change value read g = (run (g :: gs) z).getD z.length false
      rw [run_head]
      unfold value
      congr 1
      apply List.map_congr_left
      intro i hi
      rcases ord.1 i hi with lt | eq
      · exact run_keep _ _ _ lt
      · subst i
        change (run (g :: gs) z).getD bound false = z.getD bound false
        rw [List.getD_eq_default _ _ (by rw [run_length]; exact room),
            List.getD_eq_default _ _ (by omega)]
    · have room' : next.length + gs.length ≤ bound := by
        simp only [List.length_cons] at room
        omega
      have ord' : Ordered bound next.length gs := hn.symm ▸ ord.2
      simpa only [hn] using ih next ord' room'


def both (u v k : ℕ) : Bool := decide (k = u ∨ k = v)

lemma build_count (bound u v : ℕ) (huv : u ≠ v) (gs : List Gate) (refs : List (Option ℕ))
    (fresh : ℕ) :
    (build bound (both u v) gs refs fresh).2.length =
      (if refs.length ≤ u ∧ u < refs.length + gs.length then 1 else 0) +
      (if refs.length ≤ v ∧ v < refs.length + gs.length then 1 else 0) := by
  induction gs generalizing refs fresh with
  | nil => simp [build]
  | cons g gs ih =>
    by_cases h : refs.length = u ∨ refs.length = v
    · have hs : both u v refs.length = true := by simpa [both] using h
      have hi := ih (refs ++ [none]) fresh
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      simp only [build, hs, ↓reduceIte, List.length_cons]
      split_ifs at hi ⊢ <;> omega
    · have hs : both u v refs.length = false := by simp [both, h]
      have hi := ih (refs ++ [some fresh]) (fresh + 1)
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      simp only [build, hs, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      split_ifs at hi ⊢ <;> omega

lemma build_legal (bound : ℕ) (s : ℕ → Bool) (gs : List Gate) (refs : List (Option ℕ))
    (fresh : ℕ) (h : ∀ g ∈ gs, Legal g) :
    ∀ g, g ∈ (build bound s gs refs fresh).1 ∨ g ∈ (build bound s gs refs fresh).2 → Legal g := by
  induction gs generalizing refs fresh with
  | nil => simp [build]
  | cons g gs ih =>
    have hg := specialize_legal (fun i => refs.getD i (some bound)) g (h g List.mem_cons_self)
    have ht (g' : Gate) (hm : g' ∈ gs) : Legal g' := h g' (List.mem_cons_of_mem g hm)
    by_cases hs : s refs.length = true
    · intro g' hm
      simp only [build, hs, ↓reduceIte, List.mem_cons] at hm
      rcases hm with hp | eq | hterm
      · exact ih _ _ ht _ (Or.inl hp)
      · simpa only [eq] using hg
      · exact ih _ _ ht _ (Or.inr hterm)
    · intro g' hm
      simp only [build, hs, ↓reduceIte, List.mem_cons] at hm
      rcases hm with (eq | hp) | hterm
      · simpa only [eq] using hg
      · exact ih _ _ ht _ (Or.inl hp)
      · exact ih _ _ ht _ (Or.inr hterm)

def bitIn (start count k : ℕ) (w : ℕ → Bool) : Bool :=
  if start ≤ k ∧ k < start + count then w k else true

lemma bitIn_succ (start count k : ℕ) (w : ℕ → Bool) :
    bitIn start (count + 1) k w =
      ((if start = k then w k else true) && bitIn (start + 1) count k w) := by
  by_cases h : start = k
  · subst k
    have h₁ : start < start + (count + 1) := by omega
    have h₂ : ¬ start + 1 ≤ start := by omega
    simp [bitIn, h₁, h₂]
  · have equiv : (start ≤ k ∧ k < start + (count + 1)) ↔
        (start + 1 ≤ k ∧ k < start + 1 + count) := by omega
    simp only [bitIn, h, ↓reduceIte, Bool.true_and, equiv]

lemma check_original (u v : ℕ) (distinct : u ≠ v) (gs : List Gate) (z : List Bool) :
    check false (both u v) z.length gs z =
      (bitIn z.length gs.length u (fun i => (run gs z).getD i false) &&
       bitIn z.length gs.length v (fun i => (run gs z).getD i false)) := by
  induction gs generalizing z with
  | nil => simp [check, bitIn]
  | cons g gs ih =>
    let val := value (fun k => z.getD k false) g
    let next := z ++ [val]
    let w := fun i => (run gs next).getD i false
    have hn : next.length = z.length + 1 := by simp [next]
    have head (k : ℕ) (hk : z.length = k) : w k = val := by
      subst k
      exact run_head g gs z
    change ((if both u v z.length then val else true) &&
        check false (both u v) (z.length + 1) gs next) =
      (bitIn z.length (gs.length + 1) u w && bitIn z.length (gs.length + 1) v w)
    have tail := ih next
    change check false (both u v) next.length gs next =
      (bitIn next.length gs.length u w && bitIn next.length gs.length v w) at tail
    rw [hn] at tail
    rw [tail, bitIn_succ z.length gs.length u w, bitIn_succ z.length gs.length v w]
    by_cases hu : z.length = u <;> by_cases hv : z.length = v
    · exact False.elim (distinct (hu.symm.trans hv))
    · simp [both, hu, hv, head u hu, Bool.and_assoc]
    · simp [both, hu, hv, head v hv, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
    · simp [both, hu, hv]

end TerminalExtraction

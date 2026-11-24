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
    · simp [specialize, hit, value, GateOp.eval, or_read, hit]
    · simp [specialize, hit, value, GateOp.eval, or_read]
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
      simp [check, hs, hv, ih]

end TerminalExtraction

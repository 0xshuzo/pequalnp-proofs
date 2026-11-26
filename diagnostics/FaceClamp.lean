import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.FaceClamp
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))


def finish (post : List Gate) (out : Nat) (w : List Bool) (bit : Bool) :=
  (run post (w ++ [bit])).getD out false

theorem finish_order (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (w : List Bool) :
    finish post out w false = true → finish post out w true = true := by
  have same : below w w := ⟨rfl, fun _ h => h⟩
  have ord : below (w ++ [false]) (w ++ [true]) := extend same (by simp)
  exact (run_mono post goodPost ord).2 out

theorem clamp_one {α : Type} (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (bank : α → List Bool) (h f : α → Bool)
    (computes : ∀ x, finish post out (bank x) (!(h x)) = f x)
    (supp : ∀ x, h x = true → f x = true) :
    ∀ x, finish post out (bank x) true = f x := by
  intro x
  cases hh : h x with
  | false => simpa [hh] using computes x
  | true =>
    have hf := supp x hh
    rw [hf]
    apply finish_order post goodPost out (bank x)
    simpa [hh,hf] using computes x

theorem clamp_zero {α : Type} (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (bank : α → List Bool) (h f : α → Bool)
    (computes : ∀ x, finish post out (bank x) (!(h x)) = f x)
    (supp : ∀ x, f x = true → h x = true) :
    ∀ x, finish post out (bank x) false = f x := by
  intro x
  cases hh : h x with
  | true => simpa [hh] using computes x
  | false =>
    cases hf : f x with
    | true => have ht := supp x hf; simp [hh] at ht
    | false =>
      have bound : finish post out (bank x) true = false := by simpa [hh,hf] using computes x
      cases hz : finish post out (bank x) false with
      | false => rfl
      | true =>
        have ht := finish_order post goodPost out (bank x) hz
        simp [bound] at ht

def E : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def target (r : Nat) := E.any fun e => r.testBit e.1 && r.testBit e.2

def signal (r : Nat) := (r.testBit 0 || r.testBit 1) && r.testBit 8

theorem projected_support (r : Nat) (pin : r.testBit 1 = false) (on : signal r = true) :
    target r = true := by
  apply List.any_eq_true.mpr
  refine ⟨(0,8), by decide, ?_⟩
  simpa [signal,pin] using on

theorem projected (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (bank : Nat → List Bool)
    (computes : ∀ r, finish post out (bank r) (!(signal r)) = target r) :
    ∀ r, r.testBit 1 = false → finish post out (bank r) true = target r := by
  intro r pin
  let A := {t : Nat // t.testBit 1 = false}
  exact clamp_one post goodPost out (fun x : A => bank x.val) (fun x => signal x.val)
    (fun x => target x.val) (fun x => computes x.val)
    (fun x => projected_support x.val x.property) ⟨r,pin⟩

theorem genuinely_projected :
    signal 258 = true ∧ target 258 = false ∧
    (257 : Nat).testBit 1 = false ∧ signal 257 = true ∧
    (0 : Nat).testBit 1 = false ∧ signal 0 = false := by decide +kernel
end PEqualNP.Outside.L_meta_9809.FaceClamp

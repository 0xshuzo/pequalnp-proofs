import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9822.Quotient
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
/-- The rows of the second frontier are covered from below on positives and from above
on negatives by rows of the first frontier. All wires use a common order. -/
def covers {A B : Type} (a : A → List Bool) (b : B → List Bool)
    (f : A → Bool) (g : B → Bool) : Prop :=
  (∀ x, g x=true → ∃ y, f y=true ∧ below (a y) (b x)) ∧
  (∀ x, g x=false → ∃ y, f y=false ∧ below (b x) (a y))
theorem monotone_suffix_transfer {A B : Type} (a : A → List Bool) (b : B → List Bool)
    (f : A → Bool) (g : B → Bool) (h : covers a b f g)
    (gs : List Gate) (ok : ∀ t ∈ gs, good t) (out : Nat)
    (hs : ∀ y, (run gs (a y)).getD out false = f y) :
    ∀ x, (run gs (b x)).getD out false = g x := by
  intro x
  cases e : g x with
  | true =>
    obtain ⟨y,hy,hxy⟩ := h.1 x e
    exact (run_mono gs ok hxy).2 out ((hs y).trans hy)
  | false =>
    obtain ⟨y,hy,hxy⟩ := h.2 x e
    cases hv : (run gs (b x)).getD out false with
    | false => rfl
    | true =>
      have hpos := (run_mono gs ok hxy).2 out hv
      rw [hs,hy] at hpos
      contradiction
theorem signed_suffix_transfer {A B : Type} (a : A → List Bool) (b : B → List Bool)
    (f : A → Bool) (g : B → Bool) (h : ∀ x, ∃ y, a y=b x ∧ f y=g x)
    (gs : List Gate) (out : Nat) (hs : ∀ y, (run gs (a y)).getD out false = f y) :
    ∀ x, (run gs (b x)).getD out false = g x := by
  intro x
  obtain ⟨y,he,hf⟩ := h x
  rw [←he,←hf]
  exact hs y
end PEqualNP.Outside.L_meta_9822.Quotient

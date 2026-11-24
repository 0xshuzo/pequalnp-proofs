import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4035_aux

def avoidZero (g : Gate) : Prop :=
  (g.op = .not → g.inputs.head? ≠ some 0) ∧ (g.op ≠ .not → 0 ∉ g.inputs)

def gateVal (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) := w ++ [gateVal w g]

def dominated (a b : List Bool) : Prop :=
  ∀ i : ℕ, i ≠ 0 → a.getD i false = true → b.getD i false = true

lemma binaryDominated (a b : List Bool) (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (avoid : avoidZero g) (h : dominated a b) :
    gateVal a g = true → gateVal b g = true := by
  rcases hg with ha | ho
  · have hz := avoid.2 (by rw [ha]; intro eq; cases eq)
    simp only [gateVal, ha, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro H t ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact h i (fun e => hz (e ▸ hi)) (H _ ⟨i, hi, rfl⟩)
  · have hz := avoid.2 (by rw [ho]; intro eq; cases eq)
    simp only [gateVal, ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨t, ⟨i, hi, rfl⟩, hv⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i (fun e => hz (e ▸ hi)) hv⟩

lemma stepDominated (a b : List Bool) (g : Gate) (len : a.length = b.length)
    (h : dominated a b) (hg : gateVal a g = true → gateVal b g = true) :
    dominated (step a g) (step b g) := by
  intro i hn H
  by_cases small : i < a.length
  · rw [step,List.getD_append _ _ _ _ small] at H
    rw [step,List.getD_append _ _ _ _ (len ▸ small)]
    exact h i hn H
  by_cases eq : i = a.length
  · subst i
    simpa [step, List.getD_eq_getElem?_getD, len] using
      hg (by simpa [step, List.getD_eq_getElem?_getD] using H)
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at H
    contradiction

lemma anyNot (gs : List Gate) (a b : List Bool) (len : a.length = b.length)
    (initial : dominated a b)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp))
    (avoid : ∀ g ∈ gs, avoidZero g)
    (noNot : ∀ g ∈ gs, g.op ≠ .not) :
    dominated (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact initial
  | cons g gs ih =>
    have op := legal g (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    have binary : g.op = .and ∨ g.op = .or := by
      rcases op with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (noNot g (by simp) h)
    apply ih (step a g) (step b g) (by simp [step,len])
      (stepDominated a b g len initial (binaryDominated a b g binary (avoid g (by simp)) initial))
    · exact fun z hz => legal z (by simp [hz])
    · exact fun z hz => avoid z (by simp [hz])
    · exact fun z hz => noNot z (by simp [hz])

def edgeValue (x : Fin 10 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def signed (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]

lemma preservesZero (gs : List Gate) (w : List Bool) (hw : 0 < w.length) :
    (gs.foldl step w).getD 0 false = w.getD 0 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]), step, List.getD_append _ _ _ _ hw]

theorem signedNeedsNot (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x, C.eval (signed x) = edgeValue x)
    (avoid : ∀ g ∈ C.gates, avoidZero g) : ∃ g ∈ C.gates, g.op = .not := by
  by_contra! noNot
  let a : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let b : Fin 10 → Bool := fun i => decide (i = 1)
  have out : C.output ≠ 0 := by
    intro h
    let z : Fin 10 → Bool := fun i => decide (i = 0)
    have e := correct z
    change (C.gates.foldl step (signed z)).getD C.output false = edgeValue z at e
    rw [h,preservesZero _ _ (by decide)] at e
    exact (by decide : (signed z).getD 0 false ≠ edgeValue z) e
  have base : dominated (signed a) (signed b) := by
    intro i hi
    by_cases small : i < 11
    · interval_cases i <;> first | contradiction | decide
    · rw [List.getD_eq_default _ _ (by change 11 ≤ i; omega)]
      intro h
      contradiction
  have rel := anyNot C.gates (signed a) (signed b) (by decide) base
    (fun g hg => (fan g hg).1) avoid noNot
  have ha : C.eval (signed a) = true := (correct a).trans (by decide)
  have hb : C.eval (signed b) = false := (correct b).trans (by decide)
  exact Bool.noConfusion ((rel C.output out ha).symm.trans hb)

theorem signChild : let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
      let read := (fun g : Gate => g.inputs.take (if g.op.eval [false] then 1 else 2))
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = F x) →
        (∀ g ∈ C.gates, 0 ∉ read g) → 0 < C.gates.countP (fun g => g.op.eval [false]) := by
  intro F read C fan h avoid
  have correct (x : Fin 10 → Bool) : C.eval (signed x) = edgeValue x := by
    rw [show C.eval (signed x) = F x from h x]
    simp only [F,edgeValue,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have av (g : Gate) (hg : g ∈ C.gates) : avoidZero g := by
    have hz := avoid g hg
    change 0 ∉ g.inputs.take (if g.op.eval [false] then 1 else 2) at hz
    constructor
    · intro hop bad
      rw [hop] at hz
      cases he : g.inputs with
      | nil => simp [he] at bad
      | cons a rest =>
        rw [he] at bad hz
        simp only [List.head?_cons,Option.some.injEq] at bad
        exact hz (by simp [bad,GateOp.eval])
    · intro hn
      have ops := (fan g hg).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
      rcases ops with hop | hop | hop
      · simpa [hop,GateOp.eval,List.take_of_length_le (fan g hg).2] using hz
      · simpa [hop,GateOp.eval,List.take_of_length_le (fan g hg).2] using hz
      · exact False.elim (hn hop)
  obtain ⟨g,hg,hop⟩ := signedNeedsNot C fan correct av
  rw [List.countP_eq_length_filter]
  apply List.length_pos_iff.mpr
  intro empty
  have mem : g ∈ C.gates.filter (fun q => q.op.eval [false]) :=
    List.mem_filter.mpr ⟨hg, by rw [hop]; rfl⟩
  rw [empty] at mem
  exact List.not_mem_nil mem

end PEqualNP.Outside.L_meta_4035_aux

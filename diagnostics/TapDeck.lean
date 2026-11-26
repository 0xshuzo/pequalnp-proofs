import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Tap
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

theorem belowFin {a b : List Bool} (lengths : a.length = b.length)
    (valid : ∀ i : Fin a.length, a.getD i.val false = true → b.getD i.val false = true) :
    below a b := by
  refine ⟨lengths, ?_⟩
  intro i hi
  by_cases h : i < a.length
  · exact valid ⟨i,h⟩ hi
  · have le : a.length ≤ i := Nat.le_of_not_gt h
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none le] at hi

def E : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def target (r : Nat) := E.any fun e => r.testBit e.1 && r.testBit e.2

def witnesses : List Nat := [0, 8, 10, 8, 8, 8, 10, 8, 10, 8, 8, 8, 8, 8, 7, 0, 7, 13, 7, 7, 7, 13, 7, 7, 7, 7, 7, 7, 12, 8, 0, 8, 8, 8, 12, 8, 12, 8, 8, 8, 8, 8, 7, 11, 7, 0, 7, 7, 7, 11, 7, 7, 7, 7, 7, 7, 11, 10, 10, 10, 0, 11, 10, 10, 10, 10, 11, 10, 10, 10, 9, 9, 9, 9, 9, 0, 10, 9, 9, 10, 9, 9, 9, 9, 9, 8, 9, 8, 8, 8, 0, 8, 9, 8, 8, 8, 8, 8, 1, 3, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 5, 5, 5, 5, 6, 5, 5, 5, 0, 6, 5, 6, 5, 4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3, 3, 0, 4, 3, 2, 2, 3, 2, 2, 2, 2, 2, 3, 2, 2, 2, 0, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 0]

def one (i : Nat) : Nat := 2 ^ i
def q (x a : Fin 14) := witnesses.getD (14*x.val+a.val) 0
def pos (x a : Fin 14) := one x.val ||| one (q x a)
def neg (x a : Fin 14) := one a.val ||| one (q x a)
def raw (x : Fin 14) (r : Nat) := (List.range 14).map fun j => decide (j ≠ x.val) && r.testBit j
def check (x a : Fin 14) : Prop :=
  target (pos x a) = true ∧ target (neg x a) = false ∧
  (pos x a).testBit x.val = true ∧ (neg x a).testBit x.val = false ∧
  (one a.val &&& neg x a) = one a.val ∧
  (∀ i : Fin 14, (raw x (pos x a)).getD i.val false = true →
                 (raw x (neg x a)).getD i.val false = true)
instance (x a : Fin 14) : Decidable (check x a) := by unfold check; infer_instance
theorem deck0 : ∀ a : Fin 14, (0 : Fin 14) ≠ a → check 0 a := by decide +kernel
theorem deck1 : ∀ a : Fin 14, (1 : Fin 14) ≠ a → check 1 a := by decide +kernel
theorem deck2 : ∀ a : Fin 14, (2 : Fin 14) ≠ a → check 2 a := by decide +kernel
theorem deck3 : ∀ a : Fin 14, (3 : Fin 14) ≠ a → check 3 a := by decide +kernel
theorem deck4 : ∀ a : Fin 14, (4 : Fin 14) ≠ a → check 4 a := by decide +kernel
theorem deck5 : ∀ a : Fin 14, (5 : Fin 14) ≠ a → check 5 a := by decide +kernel
theorem deck6 : ∀ a : Fin 14, (6 : Fin 14) ≠ a → check 6 a := by decide +kernel
theorem deck7 : ∀ a : Fin 14, (7 : Fin 14) ≠ a → check 7 a := by decide +kernel
theorem deck8 : ∀ a : Fin 14, (8 : Fin 14) ≠ a → check 8 a := by decide +kernel
theorem deck9 : ∀ a : Fin 14, (9 : Fin 14) ≠ a → check 9 a := by decide +kernel
theorem deck10 : ∀ a : Fin 14, (10 : Fin 14) ≠ a → check 10 a := by decide +kernel
theorem deck11 : ∀ a : Fin 14, (11 : Fin 14) ≠ a → check 11 a := by decide +kernel
theorem deck12 : ∀ a : Fin 14, (12 : Fin 14) ≠ a → check 12 a := by decide +kernel
theorem deck13 : ∀ a : Fin 14, (13 : Fin 14) ≠ a → check 13 a := by decide +kernel
theorem deck (x a : Fin 14) (h : x ≠ a) : check x a := by
  fin_cases x
  · exact deck0 a h
  · exact deck1 a h
  · exact deck2 a h
  · exact deck3 a h
  · exact deck4 a h
  · exact deck5 a h
  · exact deck6 a h
  · exact deck7 a h
  · exact deck8 a h
  · exact deck9 a h
  · exact deck10 a h
  · exact deck11 a h
  · exact deck12 a h
  · exact deck13 a h

def ports (x : Fin 14) (g : Nat → Bool) (r : Nat) :=
  (raw x r ++ [r.testBit x.val || g r]) ++ [!(r.testBit x.val)]

theorem singleton_partner_impossible (x a : Fin 14) (ha : x ≠ a) (g : Nat → Bool)
    (gmono : ∀ u v : Nat, (u &&& v) = u → g u = true → g v = true)
    (singleton : g (one a.val) = true)
    (suffix : List Gate) (goodSuffix : ∀ t ∈ suffix, good t) (out : Nat) :
    ¬∀ r : Nat, (run suffix (ports x g r)).getD out false = target r := by
  intro eqn
  rcases deck x a ha with ⟨pt,nt,px,nx,subset,bits⟩
  have rb : below (raw x (pos x a)) (raw x (neg x a)) := by
    apply belowFin
    · simp [raw]
    · intro i hi
      have bound : i.val < 14 := by simpa [raw] using i.isLt
      exact bits ⟨i.val,bound⟩ hi
  have ng := gmono _ _ subset singleton
  have bp : below (ports x g (pos x a)) (ports x g (neg x a)) := by
    apply extend
    · apply extend rb
      simp [ng]
    · simp [px]
  have falsePositive := (run_mono suffix goodSuffix bp).2 out ((eqn _).trans pt)
  exact Bool.noConfusion (falsePositive.symm.trans ((eqn _).trans nt))

end PEqualNP.Outside.L_meta_9809.Tap

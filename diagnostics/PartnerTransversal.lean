import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9806.Partner
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


abbrev V := Fin 14
def E : List (V × V) := [(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def adjacent (a b : V) : Prop := (a,b) ∈ E ∨ (b,a) ∈ E
instance (a b : V) : Decidable (adjacent a b) := by unfold adjacent; infer_instance
theorem loopless : ∀ a : V, ¬adjacent a a := by decide +kernel
theorem reverseEdge {a b : V} (h : adjacent a b) : adjacent b a := h.elim Or.inr Or.inl

def hits (s : Finset V) : Prop := ∃ a ∈ s, ∃ b ∈ s, adjacent a b
def raw (p : V) (s : Finset V) : List Bool :=
  (List.finRange 14).map (fun a => decide (a ∈ s ∧ a ≠ p))
def ports (p : V) (g : Finset V → Bool) (s : Finset V) : List Bool :=
  (raw p s ++ [decide (p ∈ s) || g s]) ++ [decide (p ∉ s)]
def neighbors (p q : V) : Finset V := Finset.univ.filter (fun v => v ≠ p ∧ adjacent q v)

theorem map_below {α : Type} (f h : α → Bool) (mono : ∀ i, f i = true → h i = true)
    (xs : List α) : below (xs.map f) (xs.map h) := by
  induction xs with
  | nil => exact ⟨rfl, fun _ h => h⟩
  | cons a xs ih =>
    refine ⟨by simp, ?_⟩
    intro i
    cases i with
    | zero => simpa [List.getD] using mono a
    | succ k => simpa [List.getD] using ih.2 k

theorem forced_neighbor
    (p : V) (g : Finset V → Bool)
    (mono : ∀ s t : Finset V, s ⊆ t → g s = true → g t = true)
    (post : List Gate) (goodPost : ∀ k ∈ post, good k) (out : Nat)
    (computes : ∀ s, (run post (ports p g s)).getD out false = true ↔ hits s)
    (s : Finset V) (hp : p ∉ s) (free : ¬hits s) (on : g s = true)
    (q : V) (eq : adjacent p q) : (s ∩ neighbors p q).Nonempty := by
  by_contra none
  have clean : ¬hits (insert q s) := by
    rintro ⟨a,ha,b,hb,he⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact loopless _ he
      · apply none
        exact ⟨b, Finset.mem_inter.mpr ⟨hb, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun h => hp (h ▸ hb), he⟩⟩⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · apply none
        exact ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun h => hp (h ▸ ha), reverseEdge he⟩⟩⟩
      · exact free ⟨a,ha,b,hb,he⟩
  have positive : hits ({p,q} : Finset V) := ⟨p,by simp,q,by simp,eq⟩
  have bank : below (raw p {p,q}) (raw p (insert q s)) := by
    apply map_below
    intro i hi
    simp only [decide_eq_true_eq] at hi ⊢
    rcases hi with ⟨hi,hne⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    exact ⟨Finset.mem_insert.mpr (Or.inl (hi.resolve_left hne)),hne⟩
  have lifted : below (ports p g {p,q}) (ports p g (insert q s)) := by
    apply extend
    · apply extend bank
      have h := mono s (insert q s) (Finset.subset_insert q s) on
      simp [h]
    · simp
  exact clean ((computes _).mp ((run_mono post goodPost lifted).2 out ((computes _).mpr positive)))

private theorem row1_7 : neighbors 1 7 = ({3} : Finset V) := by decide +kernel
private theorem row1_9 : neighbors 1 9 = ({5,6} : Finset V) := by decide +kernel
private theorem row1_13 : neighbors 1 13 = ({2,4} : Finset V) := by decide +kernel
theorem pivot1 (s : Finset V) (all : ∀ q : V, adjacent 1 q → (s ∩ neighbors 1 q).Nonempty) :
    (s ∩ ({3} : Finset V)).Nonempty ∧ (s ∩ ({5,6} : Finset V)).Nonempty ∧ (s ∩ ({2,4} : Finset V)).Nonempty := by
  exact ⟨by simpa only [row1_7] using all 7 (by decide +kernel),
    by simpa only [row1_9] using all 9 (by decide +kernel),
    by simpa only [row1_13] using all 13 (by decide +kernel)⟩

private theorem row4_10 : neighbors 4 10 = ({0,5} : Finset V) := by decide +kernel
private theorem row4_11 : neighbors 4 11 = ({3,6} : Finset V) := by decide +kernel
private theorem row4_13 : neighbors 4 13 = ({1,2} : Finset V) := by decide +kernel
theorem pivot4 (s : Finset V) (all : ∀ q : V, adjacent 4 q → (s ∩ neighbors 4 q).Nonempty) :
    (s ∩ ({0,5} : Finset V)).Nonempty ∧ (s ∩ ({3,6} : Finset V)).Nonempty ∧ (s ∩ ({1,2} : Finset V)).Nonempty := by
  exact ⟨by simpa only [row4_10] using all 10 (by decide +kernel),
    by simpa only [row4_11] using all 11 (by decide +kernel),
    by simpa only [row4_13] using all 13 (by decide +kernel)⟩

private theorem row9_1 : neighbors 9 1 = ({7,13} : Finset V) := by decide +kernel
private theorem row9_5 : neighbors 9 5 = ({10,12} : Finset V) := by decide +kernel
private theorem row9_6 : neighbors 9 6 = ({8,11} : Finset V) := by decide +kernel
theorem pivot9 (s : Finset V) (all : ∀ q : V, adjacent 9 q → (s ∩ neighbors 9 q).Nonempty) :
    (s ∩ ({7,13} : Finset V)).Nonempty ∧ (s ∩ ({10,12} : Finset V)).Nonempty ∧ (s ∩ ({8,11} : Finset V)).Nonempty := by
  exact ⟨by simpa only [row9_1] using all 1 (by decide +kernel),
    by simpa only [row9_5] using all 5 (by decide +kernel),
    by simpa only [row9_6] using all 6 (by decide +kernel)⟩

end PEqualNP.Outside.L_meta_9806.Partner

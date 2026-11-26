import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Chain
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

theorem gate_anti {a b : List Bool} (h : below a b) (g : Gate) (ht : g.op = .not) :
    readGate g b = true → readGate g a = true := by
  intro hb
  cases hi : g.inputs with
  | nil => simp [readGate, ht, hi, GateOp.eval]
  | cons j js =>
    cases e : a.getD j false with
    | false => simp [readGate, ht, hi, GateOp.eval, e]
    | true =>
      have f := h.2 j e
      simp [readGate, ht, hi, GateOp.eval, f] at hb

def response (pre post : List Gate) (g : Gate) (out : Nat) (w : List Bool) :=
  (run post (stage (run pre w) g)).getD out false

theorem no_chain (pre post : List Gate) (g : Gate) (out : Nat)
    (hp : ∀ u ∈ pre, good u) (hq : ∀ u ∈ post, good u) (hn : g.op = .not)
    {a b c d : List Bool} (ab : below a b) (bc : below b c) (cd : below c d) :
    ¬(response pre post g out a = true ∧ response pre post g out b = false ∧
       response pre post g out c = true ∧ response pre post g out d = false) := by
  rintro ⟨av,bv,cv,dv⟩
  have ba := run_mono pre hp ab
  have cb := run_mono pre hp bc
  have dc := run_mono pre hp cd
  by_cases h : readGate g (run pre a) = true → readGate g (run pre b) = true
  · have ord := run_mono post hq (extend ba h)
    have bad := ord.2 out av
    exact Bool.noConfusion (bad.symm.trans bv)
  · have h2 : readGate g (run pre c) = true → readGate g (run pre d) = true := by
      intro hc
      exact False.elim (h (fun _ => gate_anti cb g hn hc))
    have ord := run_mono post hq (extend dc h2)
    have bad := ord.2 out cv
    exact Bool.noConfusion (bad.symm.trans dv)

theorem belowFin {a b : List Bool} (lengths : a.length = b.length)
    (valid : ∀ i : Fin a.length, a.getD i.val false = true → b.getD i.val false = true) :
    below a b := by
  refine ⟨lengths, ?_⟩
  intro i hi
  by_cases h : i < a.length
  · exact valid ⟨i,h⟩ hi
  · have le : a.length ≤ i := Nat.le_of_not_gt h
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none le] at hi

def inputs (r : Nat) : List Bool := (List.range 14).map fun j => r.testBit j
def prefixG : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [15, 20]⟩, ⟨.and, [16, 18]⟩]
def liveIndices : List Nat := [0, 1, 4, 5, 6, 7, 8, 9, 10, 13, 14, 17, 19, 21, 22]
def bank (r : Nat) := liveIndices.map fun j => (run prefixG (inputs r)).getD j false
def E : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def target (r : Nat) := E.any fun e => r.testBit e.1 && r.testBit e.2
theorem comparison0 : below (bank 2112) (bank 68) := belowFin (by rfl) (by decide +kernel)
theorem comparison1 : below (bank 68) (bank 8260) := belowFin (by rfl) (by decide +kernel)
theorem comparison2 : below (bank 8260) (bank 8297) := belowFin (by rfl) (by decide +kernel)

theorem frontier_unreachable (pre post : List Gate) (g : Gate) (out : Nat)
    (hp : ∀ u ∈ pre, good u) (hq : ∀ u ∈ post, good u) (hn : g.op = .not) :
    ¬∀ r : Nat, response pre post g out (bank r) = target r := by
  intro all
  apply no_chain pre post g out hp hq hn comparison0 comparison1 comparison2
  exact ⟨(all 2112).trans (by decide +kernel), (all 68).trans (by decide +kernel), (all 8260).trans (by decide +kernel), (all 8297).trans (by decide +kernel)⟩
end PEqualNP.Outside.L_meta_9809.Chain

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9815.IndependentTaps
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


def value (gs : List Gate) (o : Nat) (b : List Bool) := (run gs b).getD o false

theorem value_mono (gs : List Gate) (ok : ∀ g∈gs,good g) (o : Nat)
    {a b : List Bool} (h : below a b) : value gs o a=true → value gs o b=true :=
  (run_mono gs ok h).2 o

/-- The remaining readers may see the negative pivot rail and the new OR, as well as the entire monotone prefix. -/
theorem forwardReader (pre post : List Gate) (a b : List Bool) (i out : Nat)
    (ord : below a b) (gp : ∀ g ∈ pre, good g) (gs : ∀ g ∈ post, good g)
    (yes : value post out (run pre a ++ [true]) = true)
    (no : value post out (run pre b ++ [(run pre b).getD i false]) = false) :
    (run pre b).getD i false = false := by
  cases h : (run pre b).getD i false with
  | false => rfl
  | true =>
    have m := (value_mono post gs out (extend (v:=true) (w:=true)
      (run_mono pre gp ord) (fun _ => rfl))) yes
    rw [h] at no
    exact Bool.noConfusion (m.symm.trans no)

def edgeValue (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def deck : List Nat := [127, 245, 314, 432, 541, 792, 1102, 1290, 1548, 2087, 2213, 2338, 4183, 4309, 4370, 4757, 5008, 5190, 5316, 6151, 6789, 7174, 7426, 7812, 8297, 8417, 8488, 8713, 9288, 9992, 10401, 10656, 12481, 13504, 14977, 16256]
def base (r : Fin 36) (p : Fin 14) := (deck.getD r.val 0).testBit p.val
def raised (r : Fin 36) (p i : Fin 14) : Bool := decide (i = p) || base r i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem decisive : ∀ r : Fin 36, ∀ p : Fin 14, base r p = false →
    edgeValue (base r) = false ∧ edgeValue (raised r p) = true := by decide +kernel

theorem deckObligation (pre post : List Gate) (p : Fin 14) (partner out : Nat)
    (bank : (Fin 14 → Bool) → List Bool)
    (desc : ∀ r : Fin 36, base r p = false → below (bank (raised r p)) (bank (base r)))
    (gp : ∀ g ∈ pre, good g) (gs : ∀ g ∈ post, good g)
    (computes : ∀ x : Fin 14 → Bool, value post out (run pre (bank x) ++
      [x p || (run pre (bank x)).getD partner false]) = edgeValue x) :
    ∀ r : Fin 36, base r p = false → (run pre (bank (base r))).getD partner false = false := by
  intro r absent
  obtain ⟨lo,hi⟩ := decisive r p absent
  apply forwardReader pre post _ _ partner out (desc r absent) gp gs
  · have yes := (computes (raised r p)).trans hi
    simpa [raised] using yes
  · have no := (computes (base r)).trans lo
    simpa [absent] using no
def tripleDegree (p : Fin 14) : Bool := decide (p.val ≠ 0) && decide (p.val ≠ 2) && decide (p.val ≠ 7) && decide (p.val ≠ 12)
def dyad (a b i : Fin 14) : Bool := decide (i=a ∨ i=b)
def choices0 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 2, 2, 2, 6, 0, 2, 0, 6, 11, 14, 0, 0, 6, 6, 6, 0, 0, 6, 18, 0, 8, 6, 21, 17, 0, 0, 2, 6, 2, 2, 2, 6, 0, 2, 5, 6, 0, 0, 26, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 0, 0, 14, 0, 0, 2, 0, 2, 2, 2, 0, 3, 2, 0, 0, 11, 0, 26, 0, 6, 6, 6, 0, 0, 6, 18, 0, 0, 6, 0, 17, 28, 0, 0, 18, 0, 3, 3, 18, 3, 3, 16, 18, 23, 16, 31, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 11, 14, 26, 0, 0, 8, 5, 5, 0, 0, 16, 5, 5, 8, 23, 16, 29, 0, 6, 6, 6, 0, 0, 6, 18, 7, 8, 6, 21, 17, 28, 0, 11, 21, 0, 0, 11, 0, 23, 11, 23, 21, 11, 21, 31, 0, 14, 17, 0, 14, 0, 17, 16, 14, 16, 17, 21, 14, 33, 0, 0, 0, 26, 0, 26, 28, 31, 26, 29, 28, 31, 33, 26]
def choices1 : Array Nat := #[1, 0, 1, 4, 1, 1, 1, 1, 0, 4, 0, 10, 13, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 4, 1, 1, 1, 1, 0, 4, 8, 10, 13, 0, 4, 0, 4, 4, 4, 24, 24, 0, 5, 4, 8, 0, 0, 24, 1, 0, 1, 4, 1, 1, 1, 1, 3, 4, 0, 0, 13, 0, 1, 0, 1, 24, 1, 1, 1, 1, 3, 0, 0, 10, 0, 24, 1, 0, 1, 24, 1, 1, 1, 1, 0, 0, 18, 0, 13, 24, 1, 0, 1, 0, 1, 1, 1, 1, 3, 15, 18, 10, 13, 25, 0, 0, 0, 5, 3, 3, 0, 3, 3, 5, 29, 31, 16, 26, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 8, 20, 15, 27, 0, 0, 8, 8, 0, 0, 18, 18, 29, 8, 8, 23, 18, 28, 10, 0, 10, 0, 0, 10, 0, 10, 31, 20, 23, 10, 20, 30, 13, 0, 13, 0, 13, 0, 13, 13, 16, 15, 18, 20, 13, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 28, 30, 32, 24]
def choices2 : Array Nat := #[24, 0, 0, 24, 0, 24, 24, 25, 0, 27, 0, 30, 32, 24, 0, 2, 0, 2, 2, 2, 0, 0, 2, 0, 7, 11, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 2, 0, 2, 2, 2, 24, 0, 2, 5, 7, 0, 0, 24, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 0, 0, 14, 0, 24, 2, 0, 2, 2, 2, 24, 3, 2, 0, 0, 11, 0, 24, 24, 0, 0, 24, 0, 24, 24, 25, 0, 0, 28, 0, 32, 24, 25, 0, 0, 0, 3, 3, 25, 3, 3, 16, 33, 30, 16, 25, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 11, 14, 26, 27, 0, 0, 5, 5, 0, 0, 16, 5, 5, 29, 34, 16, 27, 0, 7, 0, 7, 0, 0, 28, 33, 7, 29, 7, 22, 22, 28, 30, 11, 0, 0, 0, 11, 0, 30, 11, 34, 22, 11, 22, 30, 32, 14, 0, 0, 14, 0, 32, 16, 14, 16, 22, 22, 14, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 28, 30, 32, 24]
def choices3 : Array Nat := #[1, 9, 1, 0, 1, 1, 1, 1, 0, 15, 0, 9, 12, 25, 9, 9, 9, 0, 12, 9, 12, 0, 11, 0, 17, 9, 12, 0, 1, 9, 1, 0, 1, 1, 1, 1, 0, 15, 17, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12, 1, 0, 1, 1, 1, 1, 3, 15, 0, 0, 12, 0, 1, 9, 1, 0, 1, 1, 1, 1, 3, 0, 0, 9, 0, 25, 1, 12, 1, 0, 1, 1, 1, 1, 0, 0, 17, 0, 12, 25, 1, 0, 1, 0, 1, 1, 1, 1, 3, 15, 18, 10, 13, 25, 0, 11, 0, 0, 3, 3, 0, 3, 3, 16, 22, 11, 14, 31, 15, 0, 15, 0, 15, 0, 0, 15, 16, 15, 23, 20, 15, 34, 0, 17, 17, 0, 0, 0, 17, 18, 22, 23, 17, 21, 17, 33, 9, 9, 9, 0, 0, 9, 0, 10, 11, 20, 21, 9, 19, 30, 12, 12, 12, 0, 12, 0, 12, 13, 14, 15, 17, 19, 12, 32, 25, 0, 0, 0, 0, 25, 25, 25, 31, 34, 33, 30, 32, 25]
def choices4 : Array Nat := #[9, 9, 9, 24, 0, 9, 24, 10, 0, 20, 0, 9, 19, 24, 9, 6, 6, 6, 0, 9, 6, 0, 7, 0, 6, 9, 17, 0, 9, 6, 6, 6, 0, 9, 6, 10, 0, 8, 6, 9, 17, 0, 24, 6, 6, 6, 0, 24, 6, 0, 7, 8, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 24, 0, 9, 24, 10, 11, 0, 0, 9, 0, 24, 24, 6, 6, 6, 0, 24, 6, 18, 0, 0, 6, 0, 17, 24, 10, 0, 10, 0, 0, 10, 18, 10, 31, 20, 18, 10, 18, 25, 0, 7, 0, 7, 0, 11, 0, 31, 7, 29, 7, 11, 22, 26, 20, 0, 8, 8, 0, 0, 0, 20, 29, 8, 8, 20, 20, 27, 0, 6, 6, 6, 0, 0, 6, 18, 7, 8, 6, 21, 17, 28, 9, 9, 9, 0, 0, 9, 0, 10, 11, 20, 21, 9, 19, 30, 19, 17, 17, 0, 0, 0, 17, 18, 22, 20, 17, 19, 17, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 28, 30, 32, 24]
def choices5 : Array Nat := #[4, 12, 4, 4, 4, 0, 12, 13, 0, 4, 0, 19, 12, 27, 12, 6, 6, 6, 12, 0, 6, 0, 7, 0, 6, 19, 12, 0, 4, 6, 4, 4, 4, 0, 6, 13, 0, 4, 6, 19, 12, 0, 4, 6, 4, 4, 4, 0, 6, 0, 5, 4, 6, 0, 0, 27, 4, 12, 4, 4, 4, 0, 12, 13, 5, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 6, 6, 6, 12, 0, 6, 13, 0, 0, 6, 0, 12, 28, 13, 0, 13, 0, 13, 0, 13, 13, 16, 15, 18, 20, 13, 32, 0, 7, 0, 5, 5, 0, 0, 16, 5, 5, 7, 22, 14, 29, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 8, 20, 15, 27, 0, 6, 6, 6, 0, 0, 6, 18, 7, 8, 6, 21, 17, 28, 19, 19, 19, 0, 0, 0, 0, 20, 22, 20, 21, 19, 19, 34, 12, 12, 12, 0, 12, 0, 12, 13, 14, 15, 17, 19, 12, 32, 27, 0, 0, 27, 0, 0, 28, 32, 29, 27, 28, 34, 32, 27]
def choices6 : Array Nat := #[4, 9, 4, 4, 4, 9, 0, 10, 0, 4, 0, 9, 15, 27, 9, 2, 9, 2, 2, 2, 0, 0, 2, 0, 7, 9, 14, 0, 4, 9, 4, 4, 4, 9, 0, 10, 0, 4, 8, 9, 15, 0, 4, 2, 4, 2, 2, 2, 0, 0, 2, 4, 7, 0, 0, 26, 4, 2, 4, 2, 2, 2, 0, 3, 2, 4, 0, 0, 14, 0, 9, 2, 9, 2, 2, 2, 0, 3, 2, 0, 0, 9, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 10, 0, 3, 3, 0, 3, 3, 15, 23, 10, 15, 30, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 11, 14, 26, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 8, 20, 15, 27, 0, 7, 8, 7, 0, 0, 0, 23, 7, 8, 7, 21, 21, 29, 9, 9, 9, 0, 0, 9, 0, 10, 11, 20, 21, 9, 19, 30, 15, 14, 15, 0, 14, 0, 0, 15, 14, 15, 21, 19, 14, 34, 27, 0, 0, 26, 0, 26, 0, 30, 26, 27, 29, 30, 34, 26]
def choices7 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 9, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 2, 5, 7, 11, 14, 26, 4, 0, 4, 4, 4, 0, 0, 0, 5, 4, 8, 0, 0, 27, 0, 6, 6, 6, 0, 0, 6, 0, 7, 8, 6, 21, 17, 28, 9, 9, 9, 0, 0, 9, 0, 0, 11, 0, 21, 9, 19, 0, 12, 12, 12, 0, 12, 0, 12, 0, 14, 0, 17, 19, 12, 0, 24, 0, 0, 24, 0, 24, 24, 0, 26, 27, 28, 0, 0, 24]
def choices8 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 9, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 12, 24, 1, 0, 1, 0, 1, 1, 1, 1, 0, 15, 18, 10, 13, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 15, 0, 4, 8, 20, 15, 27, 0, 6, 6, 6, 0, 0, 6, 18, 0, 8, 6, 21, 17, 28, 9, 9, 9, 0, 0, 9, 0, 10, 0, 20, 21, 9, 19, 30, 12, 12, 12, 0, 12, 0, 12, 13, 0, 15, 17, 19, 12, 32, 24, 0, 0, 24, 0, 24, 24, 25, 0, 27, 28, 30, 32, 24]
def choices9 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 9, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 12, 24, 1, 0, 1, 0, 1, 1, 1, 1, 3, 0, 18, 10, 13, 25, 0, 2, 0, 2, 2, 2, 0, 3, 2, 0, 7, 11, 14, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 6, 18, 7, 0, 6, 21, 17, 28, 9, 9, 9, 0, 0, 9, 0, 10, 11, 0, 21, 9, 19, 30, 12, 12, 12, 0, 12, 0, 12, 13, 14, 0, 17, 19, 12, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 0, 28, 30, 32, 24]
def choices10 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 9, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 12, 24, 1, 0, 1, 0, 1, 1, 1, 1, 3, 15, 0, 10, 13, 25, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 0, 11, 14, 26, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 0, 20, 15, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 0, 0, 9, 0, 10, 11, 20, 0, 9, 19, 30, 12, 12, 12, 0, 12, 0, 12, 13, 14, 15, 0, 19, 12, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 0, 30, 32, 24]
def choices11 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 12, 24, 1, 0, 1, 0, 1, 1, 1, 1, 3, 15, 18, 0, 13, 25, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 0, 14, 26, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 8, 0, 15, 27, 0, 6, 6, 6, 0, 0, 6, 18, 7, 8, 6, 0, 17, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 0, 12, 0, 12, 13, 14, 15, 17, 0, 12, 32, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 28, 0, 32, 24]
def choices12 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 9, 0, 24, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 24, 1, 0, 1, 0, 1, 1, 1, 1, 3, 0, 0, 10, 0, 25, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 11, 0, 26, 4, 0, 4, 4, 4, 0, 0, 0, 5, 4, 8, 0, 0, 27, 0, 6, 6, 6, 0, 0, 6, 0, 7, 8, 6, 0, 0, 28, 9, 9, 9, 0, 0, 9, 0, 10, 11, 0, 0, 9, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 24, 0, 24, 24, 25, 26, 27, 28, 30, 0, 24]
def choices13 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 6, 9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 12, 0, 1, 0, 1, 0, 1, 1, 1, 1, 3, 15, 18, 10, 13, 0, 0, 2, 0, 2, 2, 2, 0, 3, 2, 5, 7, 11, 14, 0, 4, 0, 4, 4, 4, 0, 0, 15, 5, 4, 8, 20, 15, 0, 0, 6, 6, 6, 0, 0, 6, 18, 7, 8, 6, 21, 17, 0, 9, 9, 9, 0, 0, 9, 0, 10, 11, 20, 21, 9, 19, 0, 12, 12, 12, 0, 12, 0, 12, 13, 14, 15, 17, 19, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def choice (p a b : Fin 14) : Fin 36 :=
  ⟨((#[choices0, choices1, choices2, choices3, choices4, choices5, choices6, choices7, choices8, choices9, choices10, choices11, choices12, choices13][p.val]!)[a.val*14+b.val]!) % 36,Nat.mod_lt _ (by decide)⟩

abbrev dyadCovered (p a b : Fin 14) : Prop :=
  tripleDegree p = true → a ≠ p → b ≠ p → edgeValue (dyad a b) = false →
    base (choice p a b) p = false ∧ base (choice p a b) a = true ∧
      base (choice p a b) b = true
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row0 : ∀ a b, dyadCovered 0 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row1 : ∀ a b, dyadCovered 1 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row2 : ∀ a b, dyadCovered 2 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row3 : ∀ a b, dyadCovered 3 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row4 : ∀ a b, dyadCovered 4 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row5 : ∀ a b, dyadCovered 5 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row6 : ∀ a b, dyadCovered 6 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row7 : ∀ a b, dyadCovered 7 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row8 : ∀ a b, dyadCovered 8 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row9 : ∀ a b, dyadCovered 9 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row10 : ∀ a b, dyadCovered 10 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row11 : ∀ a b, dyadCovered 11 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row12 : ∀ a b, dyadCovered 12 a b := by decide +kernel
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem row13 : ∀ a b, dyadCovered 13 a b := by decide +kernel
theorem allDyads (p a b : Fin 14) : dyadCovered p a b := by
  fin_cases p <;> first | apply row0 | apply row1 | apply row2 | apply row3 | apply row4 | apply row5 | apply row6 | apply row7 | apply row8 | apply row9 | apply row10 | apply row11 | apply row12 | apply row13

theorem tapNoDyad (p a b : Fin 14) (tap : (Fin 14 → Bool) → Bool)
    (tapMono : ∀ x y : Fin 14 → Bool, x p = false → y p = false →
      (∀ i, x i = true → y i = true) → tap x = true → tap y = true)
    (deckLow : ∀ r : Fin 36, base r p = false → tap (base r) = false)
    (degree : tripleDegree p = true) (ap : a ≠ p) (bp : b ≠ p)
    (nonedge : edgeValue (dyad a b) = false) : tap (dyad a b) = false := by
  obtain ⟨zero,ha,hb⟩ := allDyads p a b degree ap bp nonedge
  have power : dyad a b p = false := by simp [dyad,Ne.symm ap,Ne.symm bp]
  have order : ∀ i, dyad a b i = true → base (choice p a b) i = true := by
    intro i h
    have v : i = a ∨ i = b := of_decide_eq_true h
    rcases v with rfl | rfl
    · exact ha
    · exact hb
  cases h : tap (dyad a b) with
  | false => rfl
  | true =>
    have yes := tapMono _ _ power zero order h
    exact Bool.noConfusion (yes.symm.trans (deckLow _ zero))
end PEqualNP.Outside.L_meta_9815.IndependentTaps

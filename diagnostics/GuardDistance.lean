import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.RowCompletion
open Finset

variable {n m k : ℕ}
abbrev Rect (n m : ℕ) := Finset (Fin n) × Finset (Fin m)
def lawful (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m) : Prop :=
  (∀ t, ∀ p ∈ (R t).1, ∀ l ∈ (R t).2, inc p l = false) ∧
  (∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)

def separates (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) : Prop :=
  ∀ p l, inc p l = false → ∃ t, p ∈ S t ∧ ∀ q ∈ S t, inc q l = false

def completed (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) :
    Fin k → Rect n m := fun t =>
  (S t, univ.filter fun l => ∀ q ∈ S t, inc q l = false)

theorem projection (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m)
    (h : lawful inc R) : separates inc (fun t => (R t).1) := by
  intro p l e
  obtain ⟨t, a, b⟩ := h.2 p l e
  exact ⟨t, a, fun q z => h.1 t q z l b⟩

theorem complete_iff (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n)) :
    lawful inc (completed inc S) ↔ separates inc S := by
  constructor
  · exact projection inc (completed inc S)
  · intro h
    constructor
    · intro t p hp l hl
      exact (mem_filter.mp hl).2 p hp
    · intro p l e
      obtain ⟨t, a, b⟩ := h p l e
      exact ⟨t, a, mem_filter.mpr ⟨mem_univ _, b⟩⟩

def unblocked (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n))
    (U : Finset (Fin n)) : Prop :=
  ∀ p l, inc p l = false → p ∈ U ∨
    ∃ t, p ∈ S t ∧ ∀ q ∈ S t, inc q l = true → q ∈ U

theorem candidate_unblocks (inc : Fin n → Fin m → Bool) (R : Fin k → Rect n m)
    (S : Fin k → Finset (Fin n)) (U : Finset (Fin n))
    (h : lawful inc R) (fixedRows : ∀ p ∉ U, ∀ t, p ∈ S t ↔ p ∈ (R t).1) :
    unblocked inc S U := by
  intro p l e
  by_cases f : p ∈ U
  · exact Or.inl f
  · obtain ⟨t, a, b⟩ := h.2 p l e
    refine Or.inr ⟨t, (fixedRows p f t).mpr a, ?_⟩
    intro q qt e'
    by_contra outside
    have v := h.1 t q ((fixedRows q outside t).mp qt) l b
    rw [e'] at v
    contradiction


def guard (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n))
    (p : Fin n) (l : Fin m) (D : Finset (Fin n)) : Prop :=
  inc p l = false ∧ p ∈ D ∧ ∀ t, p ∈ S t → ∃ q ∈ D, q ∈ S t ∧ inc q l = true

theorem guard_hits (inc : Fin n → Fin m → Bool) (S : Fin k → Finset (Fin n))
    (U : Finset (Fin n)) (h : unblocked inc S U)
    {p : Fin n} {l : Fin m} {D : Finset (Fin n)} (g : guard inc S p l D) :
    ∃ q ∈ D, q ∈ U := by
  rcases h p l g.1 with hp | ⟨t, pt, blocked⟩
  · exact ⟨p, g.2.1, hp⟩
  · obtain ⟨q, qd, qt, ql⟩ := g.2.2 t pt
    exact ⟨q, qd, blocked q qt ql⟩

theorem guard_count {s : ℕ} {U : Finset (Fin n)} (D : Fin s → Finset (Fin n))
    (meets : ∀ i, ∃ q ∈ D i, q ∈ U)
    (apart : ∀ i j, ∀ q ∈ D i, q ∈ D j → i = j) : s ≤ U.card := by
  classical
  let z (i : Fin s) : Fin n := (meets i).choose
  have spec (i : Fin s) : z i ∈ D i ∧ z i ∈ U := (meets i).choose_spec
  let f (i : Fin s) : ↥U := ⟨z i, (spec i).2⟩
  have inj : Function.Injective f := by
    intro i j eq
    have same : z i = z j := congrArg Subtype.val eq
    exact apart i j (z i) (spec i).1 (same.symm ▸ (spec j).1)
  simpa using Fintype.card_le_of_injective f inj

def readMask (v : ℕ) : Finset (Fin 31) := univ.filter (fun p => v.testBit p.val)
def incidenceRows : Array ℕ := #[1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def board (p l : Fin 31) : Bool := (incidenceRows[p.val]!).testBit l.val
def pointRows : Array ℕ := #[1619034128, 281608487, 541068162, 205914684, 286791024, 134861416, 269559504, 304532228, 719340640, 2032474113, 76832834, 1077018888, 50364559, 688808961, 101328896, 86064262, 72618629]
def pointGuards : Array ℕ := #[1118208, 20971521, 644, 67118080, 35653640, 1610612992, 655392, 134479936, 8437762]
def pointSeed (t : Fin 17) := readMask (pointRows[t.val]!)
def pointD (i : Fin 9) := readMask (pointGuards[i.val]!)
private def pointP : Fin 9 → Fin 31 := ![12, 0, 7, 13, 25, 30, 19, 27, 23]
private def pointL : Fin 9 → Fin 31 := ![15, 28, 8, 30, 10, 28, 12, 13, 21]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pointValid : ∀ i : Fin 9, guard board pointSeed (pointP i) (pointL i) (pointD i) := by
  intro i
  unfold guard
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pointApart : ∀ i j : Fin 9, ∀ q ∈ pointD i, q ∈ pointD j → i = j := by
  intro i
  fin_cases i <;> decide +kernel

theorem pointDistance (R : Fin 17 → Rect 31 31) (U : Finset (Fin 31))
    (h : lawful board R)
    (fixedRows : ∀ p ∉ U, ∀ t, p ∈ pointSeed t ↔ p ∈ (R t).1) :
    9 ≤ U.card := by
  apply guard_count pointD _ pointApart
  intro i
  exact guard_hits board pointSeed U (candidate_unblocks _ _ _ _ h fixedRows) (pointValid i)

def lineRows : Array ℕ := #[76784259, 17376260, 1121452546, 136069152, 544211012, 1493303360, 304349313, 1140852772, 8946112, 2118400, 276908112, 1078339859, 34050056, 671124482, 406858424, 620757016, 8393769]
def lineGuards : Array ℕ := #[16779280, 1073905664, 671088736, 276824192, 33816578, 4616, 3162113, 4268032]
def lineSeed (t : Fin 17) := readMask (lineRows[t.val]!)
def lineD (i : Fin 8) := readMask (lineGuards[i.val]!)
private def lineP : Fin 8 → Fin 31 := ![4, 17, 27, 7, 25, 12, 21, 13]
private def lineL : Fin 8 → Fin 31 := ![4, 26, 30, 24, 12, 14, 25, 27]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineValid : ∀ i : Fin 8, guard (fun p l => board l p) lineSeed (lineP i) (lineL i) (lineD i) := by
  intro i
  unfold guard
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineApart : ∀ i j : Fin 8, ∀ q ∈ lineD i, q ∈ lineD j → i = j := by
  intro i
  fin_cases i <;> decide +kernel

theorem lineDistance (R : Fin 17 → Rect 31 31) (U : Finset (Fin 31))
    (h : lawful (fun p l => board l p) R)
    (fixedRows : ∀ p ∉ U, ∀ t, p ∈ lineSeed t ↔ p ∈ (R t).1) :
    8 ≤ U.card := by
  apply guard_count lineD _ lineApart
  intro i
  exact guard_hits (fun p l => board l p) lineSeed U (candidate_unblocks _ _ _ _ h fixedRows) (lineValid i)

end PEqualNP.Outside.L_meta_10007.RowCompletion

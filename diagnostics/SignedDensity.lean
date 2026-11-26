import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9768.Density
open PEqualNP.CircuitLowerBounds
abbrev V := Fin 42
abbrev Edge := V × V

def E : List Edge := [(0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]
def board : Finset Edge := E.toFinset
def target (x : V → Bool) := E.any (fun e => x e.1 && x e.2)
def row (e : Edge) (k : V) : Bool := decide (k = e.1 ∨ k = e.2)
def accepts (c : Circuit) : Finset Edge :=
  board.filter (fun e => c.eval (List.ofFn (row e)) = true)

private theorem boardSize : board.card = 104 := by decide +kernel

def charges : List Circuit → Nat
  | [] => 0
  | c :: cs => c.size + 1 + charges cs

def unite (D : Circuit → Finset Edge) : List Circuit → Finset Edge
  | [] => ∅
  | c :: cs => D c ∪ unite D cs

private theorem inUnion (D : Circuit → Finset Edge) (cs : List Circuit)
    (e : Edge) (c : Circuit) (hc : c ∈ cs) (he : e ∈ D c) : e ∈ unite D cs := by
  induction cs with
  | nil => simp at hc
  | cons h t ih =>
    rcases List.mem_cons.mp hc with h | h
    · subst c
      exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (ih h)

theorem boundedDensity (D : Circuit → Finset Edge) (cs : List Circuit)
    (bounds : ∀ c ∈ cs, 6 * (D c).card ≤ 5 * (c.size + 1)) :
    6 * (unite D cs).card ≤ 5 * charges cs := by
  induction cs with
  | nil => simp [unite,charges]
  | cons c cs ih =>
    have h1 := bounds c (by simp)
    have h2 := ih (fun d hd => bounds d (by simp [hd]))
    have hu := Finset.card_union_le (D c) (unite D cs)
    simp only [unite,charges]
    omega

theorem priced (cs : List Circuit) :
    charges cs = (cs.map Circuit.size).sum + cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [charges, ih]; omega

theorem ownerPressure (D : Circuit → Finset Edge) (cs : List Circuit)
    (owns : ∀ e ∈ board, ∃ c ∈ cs, e ∈ D c)
    (size : (cs.map Circuit.size).sum + cs.length - 1 ≤ 123) :
    ∃ c ∈ cs, 5 * (c.size + 1) < 6 * (D c).card := by
  by_contra no
  have dense := boundedDensity D cs (by
    intro c hc
    apply Nat.le_of_not_gt
    intro h
    exact no ⟨c,hc,h⟩)
  have incl : board ⊆ unite D cs := by
    intro e he
    obtain ⟨c,hc,hd⟩ := owns e he
    exact inUnion _ _ _ _ hc hd
  have hu := Finset.card_le_card incl
  rw [boardSize] at hu
  rw [priced] at dense
  omega

theorem signedOrPressure (cs : List Circuit)
    (correct : ∀ x : V → Bool, (cs.any (fun c => c.eval (List.ofFn x))) = target x)
    (size : (cs.map Circuit.size).sum + cs.length - 1 ≤ 123) :
    ∃ c ∈ cs, 5 * (c.size + 1) < 6 * (accepts c).card := by
  apply ownerPressure accepts cs _ size
  intro e he
  have yes : target (row e) = true := by
    apply List.any_eq_true.mpr
    exact ⟨e,by simpa [board] using he,by simp [row]⟩
  obtain ⟨c,hc,ev⟩ := List.any_eq_true.mp ((correct (row e)).trans yes)
  exact ⟨c,hc,Finset.mem_filter.mpr ⟨he,ev⟩⟩

end PEqualNP.Outside.L_meta_9768.Density

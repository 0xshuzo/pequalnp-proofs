import PEqualNP.Defs

namespace PEqualNP.Outside.HeawoodStarRaise
/-- Point 6 is the deleted point. The seven columns, in the posted order, are 7 through 13. -/
def nbr (p j : Nat) : Bool :=
  ([(0,0),(0,1),(0,3),(1,0),(1,2),(1,6),(2,1),(2,5),(2,6),
    (3,0),(3,4),(3,5),(4,3),(4,4),(4,6),(5,2),(5,3),(5,5),
    (6,1),(6,2),(6,4)] : List (Nat × Nat)).contains (p,j)

abbrev X := Fin 7 → Bool
def singleton (j : Fin 7) : X := fun i => decide (i = j)
def wanted (x : X) : Bool := x 1 || x 2 || x 4

/-- The high rail can override any subset of the selected source's users.
In the noncenter case this grammar even allows independent high overrides
at arbitrarily many noncenter wires. Low overrides are always allowed. -/
inductive Mode where
  | center (p : Fin 6)
  | other
  deriving DecidableEq
inductive Near (mode : Mode) (p : Fin 6) where
  | col (j : Fin 7) (ok : nbr p.val j.val = true)
  | low
  | high (ok : mode = .other)
  | join (a b : Near mode p)
def Near.eval {m p} : Near m p → X → Bool
  | .col j _, x => x j
  | .low, _ => false
  | .high _, _ => true
  | .join a b, x => a.eval x || b.eval x

/-- The list of uses may be an unfolding of a DAG. The only positive
center on the test rows is the one supplied by a high rail. -/
inductive Outer (mode : Mode) where
  | spoke (p : Fin 6) (enabled : Bool) (allowed : enabled = true → mode = .center p)
      (field : Near mode p)
  | low
  | high (ok : mode = .other)
  | join (a b : Outer mode)
def Outer.eval {m} : Outer m → X → Bool
  | .spoke _ en _ field, x => en && field.eval x
  | .low, _ => false
  | .high _, _ => true
  | .join a b, x => a.eval x || b.eval x

theorem Near.dies {p : Fin 6} (a : Near (.center p) p) (j : Fin 7)
    (outside : nbr p.val j.val = false) : a.eval (singleton j) = false := by
  induction a with
  | col i ok =>
    have ne : i ≠ j := by rintro rfl; rw [ok] at outside; contradiction
    simp [Near.eval, singleton, ne]
  | low => rfl
  | high bad => contradiction
  | join a b ha hb => simp [Near.eval, ha, hb]

theorem Outer.centerDies {p : Fin 6} (a : Outer (.center p)) (j : Fin 7)
    (outside : nbr p.val j.val = false) : a.eval (singleton j) = false := by
  induction a with
  | spoke q en allowed field =>
    cases en with
    | false => rfl
    | true =>
      have same : p = q := Mode.center.inj (allowed rfl)
      subst q
      simpa [Outer.eval] using field.dies j outside
  | low => rfl
  | high bad => contradiction
  | join a b ha hb => simp [Outer.eval, ha, hb]

theorem Outer.otherConstant (a : Outer .other) (x y : X) : a.eval x = a.eval y := by
  induction a with
  | spoke q en allowed field =>
    cases en with
    | false => rfl
    | true => cases allowed rfl
  | low => rfl
  | high _ => rfl
  | join a b ha hb => simp [Outer.eval, ha, hb]

theorem witness : ∀ p : Fin 6, ∃ j : Fin 7,
    nbr p.val j.val = false ∧ wanted (singleton j) = true := by decide +kernel

/-- On the subcube where exactly the recovered point may be high, no positive/negative
rail splice of this six-star architecture gives the exact Heawood edge function. -/
theorem noRailSplice (m : Mode) (d : Outer m) : ¬ ∀ x : X, d.eval x = wanted x := by
  intro correct
  cases m with
  | center p =>
    obtain ⟨j,outside,isOn⟩ := witness p
    have value := d.centerDies j outside
    rw [correct,isOn] at value
    contradiction
  | other =>
    have e := d.otherConstant (fun _ => false) (singleton 1)
    rw [correct,correct] at e
    exact Bool.noConfusion (show false = true from e)

/-- Arbitrary logic localized to the union of two surviving neighborhoods has
identical observations on an empty test and a suitable required singleton. -/
def observed (p q : Fin 6) (x y : X) : Prop :=
  ∀ j : Fin 7, (nbr p.val j.val = true ∨ nbr q.val j.val = true) → x j = y j

theorem twoMiss : ∀ p q : Fin 6, ∃ j : Fin 7,
    nbr p.val j.val = false ∧ nbr q.val j.val = false ∧ wanted (singleton j) = true := by
  decide +kernel

theorem noTwoBlock (p q : Fin 6) (f : X → Bool)
    (locality : ∀ x y, observed p q x y → f x=f y) : ¬∀ x, f x=wanted x := by
  intro correct
  obtain ⟨j,hp,hq,on⟩ := twoMiss p q
  have same : observed p q (fun _ => false) (singleton j) := by
    intro t known
    have ne : t≠j := by
      rintro rfl
      rcases known with h | h
      · rw [hp] at h; contradiction
      · rw [hq] at h; contradiction
    simp [singleton,ne]
  have e := locality _ _ same
  rw [correct,correct,on] at e
  exact Bool.noConfusion (show false=true from e)

/-- A single unseen line is sufficient regardless of the number of active centers. -/
def coversNew (mask : Fin 64) : Bool :=
  ([1,2,4] : List Nat).all fun j =>
    (List.range 6).any fun i => mask.val.testBit i && nbr i j
theorem threeChoices :
    ((List.finRange 64).filter (fun m => (List.range 6).countP m.val.testBit == 3 && coversNew m)).map Fin.val =
      [11, 14, 19, 22, 41, 44, 49, 52] := by decide +kernel

end PEqualNP.Outside.HeawoodStarRaise

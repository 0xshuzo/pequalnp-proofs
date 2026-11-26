import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4077.Research

abbrev V := Fin 10
abbrev X := V → Bool

def edges : List (V × V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
   (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def pet (x : X) := edges.any fun e => x e.1 && x e.2
def two (a b : V) : X := fun i => decide (i=a ∨ i=b)
def three (a b c : V) : X := fun i => decide (i=a ∨ i=b ∨ i=c)
def four (a b c d : V) : X := fun i => decide (i=a ∨ i=b ∨ i=c ∨ i=d)

theorem pet_mono {x y : X} (on : ∀ i, x i = true → y i = true) (h : pet x = true) :
    pet y = true := by
  obtain ⟨e,he,yes⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  simp only [Bool.and_eq_true] at yes
  exact ⟨e,he,by simp [on _ yes.1, on _ yes.2]⟩

def ignores (A : X → Bool) (v : V) :=
  ∀ x y : X, (∀ i, i ≠ v → x i = y i) → A x = A y

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pair_rows : ∀ i j : V, ∃ a b : V, pet (two a b) = false ∧
    pet (three i a b) = true ∧ pet (three j a b) = true := by decide +kernel

theorem full_factor (A B : X → Bool) (exactPair : ∀ x, (A x && B x) = pet x) :
    (∀ i, ¬ ignores A i) ∨ (∀ i, ¬ ignores B i) := by
  classical
  by_cases all : ∀ i, ¬ ignores A i
  · exact Or.inl all
  push_neg at all
  obtain ⟨i,hi⟩ := all
  refine Or.inr (fun j hj => ?_)
  obtain ⟨a,b,base,l,r⟩ := pair_rows i j
  have posA := (exactPair (three i a b)).trans l
  have posB := (exactPair (three j a b)).trans r
  simp only [Bool.and_eq_true] at posA posB
  have ea := hi (three i a b) (two a b) (fun w hw => by simp [three,two,hw])
  have eb := hj (three j a b) (two a b) (fun w hw => by simp [three,two,hw])
  rw [ea] at posA
  rw [eb] at posB
  have neg := (exactPair (two a b)).trans base
  simp [posA.1,posB.2] at neg

def close (a b c : V) (x : X) : X := fun i =>
  if i=a ∨ i=b ∨ i=c then true else x i

def outside (a b c z : V) (x : X) : Bool :=
  (List.finRange 10).any fun i => decide (i≠a ∧ i≠b ∧ i≠c ∧ i≠z) && x i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem near_maximal : ∀ a b c : V, a < b → b < c → ∃ z : V, ∀ w : V,
    w≠a → w≠b → w≠c → w≠z → pet (four a b c w) = true := by decide +kernel

/-- A factor accepting the whole positive set and ignoring three coordinates is
the OR of the remaining six or seven coordinates with a unary Boolean function. -/
theorem clause_of_three (A : X → Bool) (positive : ∀ x, pet x = true → A x = true)
    (a b c : V) (ab : a<b) (bc : b<c)
    (indep : ∀ x y : X, (∀ i, i≠a → i≠b → i≠c → x i=y i) → A x=A y) :
    ∃ (z : V) (f : Bool → Bool), ∀ x, A x = (outside a b c z x || f (x z)) := by
  obtain ⟨z,hz⟩ := near_maximal a b c ab bc
  let only (t : Bool) : X := fun i => if i=z then t else false
  refine ⟨z,fun t => A (only t), fun x => ?_⟩
  cases ho : outside a b c z x with
  | true =>
    simp only [Bool.true_or]
    obtain ⟨w,_,hw⟩ := List.any_eq_true.mp ho
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hw
    have hleft := hz w hw.1.1 hw.1.2.1 hw.1.2.2.1 hw.1.2.2.2
    have has : pet (close a b c x) = true := by
      apply pet_mono _ hleft
      intro i hi
      change decide (i=a ∨ i=b ∨ i=c ∨ i=w) = true at hi
      rw [decide_eq_true_eq] at hi
      rcases hi with h|h|h|h
      · simp [close,h]
      · simp [close,h]
      · simp [close,h]
      · subst i
        simpa [close,hw.1.1,hw.1.2.1,hw.1.2.2.1] using hw.2
    exact (indep x (close a b c x) (fun i ha hb hc => by simp [close,ha,hb,hc])).trans
      (positive _ has)
  | false =>
    simp only [Bool.false_or]
    apply indep
    intro i ha hb hc
    by_cases iz : i=z
    · simp [only,iz]
    · have hi : x i = false := by
        cases h : x i with
        | false => rfl
        | true =>
          have out : outside a b c z x = true :=
            List.any_eq_true.mpr ⟨i,by simp,by simp [ha,hb,hc,iz,h]⟩
          simp [ho] at out
      simpa [only,iz] using hi

end PEqualNP.Outside.L_meta_4077.Research

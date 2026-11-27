import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19061

open PEqualNP.CircuitLowerBounds
abbrev Bank := Nat → Bool
abbrev Code := Fin 4 → Bool

def flip (x : Bank) (i : Nat) : Bank := fun j => if j = i then !(x j) else x j

def gateValue (g : Gate) (x : Bank) : Bool := g.op.eval (g.inputs.map x)

def step (n : Nat) (g : Gate) (x : Bank) : Bank :=
  fun j => if j = n then gateValue g x else x j

def Supports (S : Finset Nat) (f : Bank → Code) : Prop :=
  ∀ x y : Bank, (∀ i ∈ S, x i = y i) → f x = f y

def Account (f : Bank → Code) (x : Bank) (limit : Nat) : Prop :=
  ∃ (S : Finset Nat) (T : Finset Code), Supports S f ∧ f x ∈ T ∧
    (∀ i, f (flip x i) ∈ T) ∧ S.card + T.card ≤ limit

theorem gateValue_congr (g : Gate) (x y : Bank)
    (h : ∀ i ∈ g.inputs, x i = y i) : gateValue g x = gateValue g y := by
  unfold gateValue
  congr 1
  exact List.map_congr_left h

theorem pullAccount (n : Nat) (g : Gate) (hg : g.inputs.length ≤ 2)
    (f : Bank → Code) (x : Bank) (limit : Nat)
    (h : Account f (step n g x) limit) :
    Account (fun z => f (step n g z)) x (limit + 1) := by
  classical
  obtain ⟨S, T, hs, hbase, hsingle, hcost⟩ := h
  by_cases hn : n ∈ S
  · let A := S.erase n
    let K := g.inputs.toFinset
    let B := A ∩ K
    let U := B.image (fun i => f (step n g (flip x i)))
    have ha : A.card + 1 = S.card := Finset.card_erase_add_one hn
    have hk : K.card ≤ 2 := le_trans List.toFinset_card_le hg
    have hbudget : (A ∪ K).card + B.card = A.card + K.card :=
      Finset.card_union_add_card_inter A K
    have hu : U.card ≤ B.card := Finset.card_image_le
    refine ⟨A ∪ K, T ∪ U, ?_, Finset.mem_union_left _ hbase, ?_, ?_⟩
    · intro y z hy
      apply hs
      intro j hj
      by_cases eq : j = n
      · subst j
        simp only [step, if_pos rfl]
        apply gateValue_congr
        intro i hi
        exact hy i (Finset.mem_union_right A (List.mem_toFinset.mpr hi))
      · simpa [step, eq] using hy j (Finset.mem_union_left K (Finset.mem_erase.mpr ⟨eq, hj⟩))
    · intro i
      by_cases inA : i ∈ A
      · by_cases inK : i ∈ K
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨i, Finset.mem_inter.mpr ⟨inA, inK⟩, rfl⟩)
        · have ine : i ≠ n := (Finset.mem_erase.mp inA).1
          have stable : gateValue g (flip x i) = gateValue g x := by
            apply gateValue_congr
            intro j hj
            have neq : j ≠ i := fun e => inK (e ▸ List.mem_toFinset.mpr hj)
            simp [flip, neq]
          have eq : step n g (flip x i) = flip (step n g x) i := by
            funext j
            by_cases e : j = n
            · subst j
              simp [step, flip, Ne.symm ine, stable]
            · simp [step, flip, e]
          rw [eq]
          exact Finset.mem_union_left _ (hsingle i)
      · have unchanged : ∀ j ∈ S, j ≠ n → flip x i j = x j := by
          intro j hj hne
          have nei : j ≠ i := fun e => inA (e ▸ Finset.mem_erase.mpr ⟨hne, hj⟩)
          simp [flip, nei]
        by_cases val : gateValue g (flip x i) = gateValue g x
        · apply Finset.mem_union_left
          convert hbase using 1
          apply hs
          intro j hj
          by_cases ej : j = n
          · simp [step, ej, val]
          · simp [step, ej, unchanged j hj ej]
        · have val' : gateValue g (flip x i) = !(gateValue g x) := by
            cases h₁ : gateValue g (flip x i) <;> cases h₂ : gateValue g x <;> simp_all
          apply Finset.mem_union_left
          convert hsingle n using 1
          apply hs
          intro j hj
          by_cases ej : j = n
          · simp [step, flip, ej, val']
          · simp only [step, flip, if_neg ej]
            exact unchanged j hj ej
    · have htu := Finset.card_union_le (s := T) (t := U)
      omega
  · refine ⟨S, T, ?_, hbase, ?_, by omega⟩
    · intro a b hab
      apply hs
      intro j hj
      have hne : j ≠ n := fun eq => hn (eq ▸ hj)
      simpa [step, hne] using hab j hj
    · intro i
      convert hsingle i using 1
      apply hs
      intro j hj
      have hne : j ≠ n := fun eq => hn (eq ▸ hj)
      simp [step, flip, hne]

end PEqualNP.Outside.L_meta_19061

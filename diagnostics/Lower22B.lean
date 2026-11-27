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
    have hk : K.card ≤ 2 := le_trans (List.toFinset_card_le _) hg
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
          change f (step n g (flip x i)) ∈ T ∪ U
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
    · have htu := Finset.card_union_le T U
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


def execute : (n : Nat) → List Gate → Bank → Bank
  | _, [], x => x
  | n, g :: gs, x => execute (n+1) gs (step n g x)

def select (w : Fin 4 → Nat) (x : Bank) : Code := fun v => x (w v)

theorem initialAccount (w : Fin 4 → Nat) (x : Bank) : Account (select w) x 9 := by
  classical
  let S := Finset.univ.image w
  let T := insert (select w x) (S.image (fun i => select w (flip x i)))
  have hS : S.card ≤ 4 := by
    simpa [S] using (Finset.card_image_le (f := w) (s := Finset.univ))
  have him : (S.image (fun i => select w (flip x i))).card ≤ S.card := Finset.card_image_le
  have hT : T.card ≤ (S.image (fun i => select w (flip x i))).card + 1 :=
    Finset.card_insert_le _ _
  refine ⟨S, T, ?_, Finset.mem_insert_self _ _, ?_, by omega⟩
  · intro a b hab
    funext v
    exact hab _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  · intro i
    by_cases hi : i ∈ S
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · have eq : select w (flip x i) = select w x := by
        funext v
        have hne : w v ≠ i := fun h => hi (h ▸ Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
        simp [select, flip, hne]
      rw [eq]
      exact Finset.mem_insert_self _ _

theorem executeAccount (gs : List Gate) (w : Fin 4 → Nat) (n : Nat) (x : Bank)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    Account (fun z => select w (execute n gs z)) x (9 + gs.length) := by
  induction gs generalizing n x with
  | nil => exact initialAccount w x
  | cons g gs ih =>
    have hc := ih (n+1) (step n g x) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hn := pullAccount n g (h g List.mem_cons_self)
      (fun z => select w (execute (n+1) gs z)) x _ hc
    simpa only [List.length_cons, Nat.add_assoc, execute] using hn

def pullList (l : List Bool) : Bank := fun i => l.getD i false

def listGate (l : List Bool) (g : Gate) : List Bool :=
  l ++ [gateValue g (pullList l)]

theorem pullStep (l : List Bool) (g : Gate) :
    pullList (listGate l g) = step l.length g (pullList l) := by
  funext i
  by_cases eq : i = l.length
  · subst i
    simp [pullList, listGate, step, List.getD_eq_getElem?_getD]
  · by_cases lt : i < l.length
    · simpa only [pullList, listGate, step, if_neg eq] using
        List.getD_append l [gateValue g (pullList l)] false i lt
    · have hlo : l.length ≤ i := by omega
      have hhi : (listGate l g).length ≤ i := by simp [listGate]; omega
      simp only [pullList, step, if_neg eq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hlo, List.getElem?_eq_none hhi, Option.getD_none]

theorem pullExecute (gs : List Gate) (l : List Bool) :
    pullList (gs.foldl listGate l) = execute l.length gs (pullList l) := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, execute, pullStep]
    simp [listGate]

def probes (p : Fin 16) := List.ofFn (fun q : Fin 16 => decide (q = p))

def zeroBank : Bank := fun _ => false

theorem getOfFn {n : Nat} (x : Fin n → Bool) (i : Nat) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem probePull (p : Fin 16) : pullList (probes p) = flip zeroBank p.val := by
  funext i
  by_cases hi : i < 16
  · change (List.ofFn (fun q : Fin 16 => decide (q = p))).getD i false = _
    rw [getOfFn _ _ hi]
    simp [flip, zeroBank, Fin.ext_iff]
  · have hh : (probes p).length ≤ i := by simp [probes]; omega
    have hne : i ≠ p.val := fun e => hi (e ▸ p.isLt)
    simp [pullList, List.getD_eq_getElem?_getD, List.getElem?_eq_none hh, flip, hne, zeroBank]

def bits (p : Fin 16) : Code := fun v => Nat.testBit p.val v.val

theorem bitsInj : Function.Injective bits := by
  have h : ∀ a b : Fin 16, (∀ v : Fin 4, Nat.testBit a.val v.val = Nat.testBit b.val v.val) → a = b := by decide +kernel
  intro a b eq
  exact h a b (fun v => congrFun eq v)

theorem listObservations (C : Circuit) (w : Fin 4 → Nat)
    (hw : ∀ v : Fin 4, ∀ p : Fin 16, (C.wires (probes p)).getD (w v) false = Nat.testBit p.val v.val)
    (p : Fin 16) :
    select w (execute 16 C.gates (flip zeroBank p.val)) = bits p := by
  have h := pullExecute C.gates (probes p)
  have hlen : (probes p).length = 16 := by simp [probes]
  rw [hlen, probePull] at h
  funext v
  change (execute 16 C.gates (flip zeroBank p.val)) (w v) = _
  rw [← h]
  exact hw v p

theorem codeCard : (Finset.univ.image bits).card = 16 := by
  rw [Finset.card_image_of_injective _ bitsInj]
  decide

theorem forceBudget (f : Bank → Code) (limit : Nat)
    (h : Account f zeroBank limit)
    (full : ∀ p : Fin 16, f (flip zeroBank p.val) = bits p) :
    31 ≤ limit := by
  classical
  obtain ⟨S, T, hsup, hbase, hflip, hcost⟩ := h
  have h1 : Finset.univ.image bits ⊆ T := by
    intro z hz
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
    rw [← full]
    exact hflip p.val
  have h2 : Finset.univ.image bits ⊆
      insert (f zeroBank) (S.image (fun i => f (flip zeroBank i))) := by
    intro z hz
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
    rw [← full]
    by_cases hp : p.val ∈ S
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p.val, hp, rfl⟩)
    · have eq : f (flip zeroBank p.val) = f zeroBank := by
        apply hsup
        intro j hj
        have e : j ≠ p.val := fun eq => hp (eq ▸ hj)
        simp [flip, e]
      exact Finset.mem_insert.mpr (Or.inl eq)
  have hT := Finset.card_le_card h1
  have hS := Finset.card_le_card h2
  rw [codeCard] at hT hS
  have hr := Finset.card_insert_le (f zeroBank) (S.image (fun i => f (flip zeroBank i)))
  have hi : (S.image (fun i => f (flip zeroBank i))).card ≤ S.card := Finset.card_image_le
  omega

theorem encoderLower (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (w : Fin 4 → Nat)
    (hw : ∀ v : Fin 4, ∀ p : Fin 16, (C.wires (probes p)).getD (w v) false = Nat.testBit p.val v.val) :
    22 ≤ C.size := by
  have h := executeAccount C.gates w 16 zeroBank hg
  have force := forceBudget _ _ h (listObservations C w hw)
  change 22 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_19061

open PEqualNP.Outside.L_meta_19061 in
theorem PEqualNP.Outside.L_meta_19061 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 21 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16, (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) := by
  rintro ⟨C, hm, hsize, hrep⟩
  choose w hw using hrep
  have lb := encoderLower C (fun g hg => (hm g hg).2) w hw
  omega

import PEqualNP.Defs

open PEqualNP.GenericRejection PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace SparsePlane

theorem overlap {N : ℕ} (S : Fin N → Finset (Fin N))
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    {l m : Fin N} (hne : l ≠ m) : (S l ∩ S m).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro p hp r hr
  by_contra e
  obtain ⟨u, _, hu⟩ := join p r e
  exact hne ((hu l ⟨(Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hr).1⟩).trans
    (hu m ⟨(Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hr).2⟩).symm)

theorem privateCount {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y : Finset (Fin N)) {l : Fin N} (hl : l ∉ Y) :
    q+1 ≤ Y.card + (S l ∩ zeroSet S Y).card := by
  classical
  let cap := Y.biUnion fun m => S l ∩ S m
  have hc : cap.card ≤ Y.card := by
    simpa [cap] using Finset.card_biUnion_le_card_mul Y (fun m => S l ∩ S m) 1
      (fun m hm => overlap S join (fun h => hl (h ▸ hm)))
  have incl : S l ⊆ cap ∪ (S l ∩ zeroSet S Y) := by
    intro p hp
    by_cases h : ∃ m ∈ Y, p ∈ S m
    · obtain ⟨m, hm, hpm⟩ := h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hp,hpm⟩⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hp' => h ⟨m,hm,hp'⟩⟩
  have hb := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  rw [weight] at hb
  omega

theorem testGeometry {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y Z : Finset (Fin N)) (small : Y.card ≤ q) :
    IsFalseInput S (zeroSet S Y) Z ↔ Z ⊆ Y := by
  constructor
  · intro hf l hl
    by_contra h
    have hc := privateCount S weight join Y h
    have he := Finset.disjoint_iff_inter_eq_empty.mp (hf l hl)
    rw [he] at hc
    simp only [Finset.card_empty, Nat.add_zero] at hc
    omega
  · intro inc l hl
    exact Finset.disjoint_left.mpr fun p hp hpz => (Finset.mem_filter.mp hpz).2 l (inc hl) hp


def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

theorem inputMono {N : ℕ} (C : Circuit) (ao : IsAO2 (N+N) C)
    {X X' Y Y' : Finset (Fin N)} (hx : X ⊆ X') (hy : Y ⊆ Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  refine W_mono C.gates ao.1 (incidenceInput X Y) (incidenceInput X' Y') (by simp [incidenceInput]) ?_ C.output
  intro i
  unfold incidenceInput
  by_cases hi : i < N
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi), ofFn_getD, ofFn_getD]
    simpa [hi] using (show (⟨i,hi⟩ : Fin N) ∈ X → (⟨i,hi⟩ : Fin N) ∈ X' from fun h => hx h)
  · have hle : N ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ (by simpa using hle),
      List.getD_append_right _ _ _ _ (by simpa using hle), ofFn_getD, ofFn_getD]
    by_cases hj : i-N < N
    · simpa [hj] using (show (⟨i-N,hj⟩ : Fin N) ∈ Y → (⟨i-N,hj⟩ : Fin N) ∈ Y' from fun h => hy h)
    · simp [hj]

theorem partitionRows : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (D E : Circuit),
      let row (B : Circuit) (Y : Finset (Fin N)) := ∀ Z : Finset (Fin N),
        B.eval (incidenceInput (zeroSet S Y) Z) = decide (¬ Z ⊆ Y)
      (∀ l, (S l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N+N) D → IsAO2 (N+N) E →
      RightOnIncidentPairs S D → RightOnIncidentPairs S E →
      (∀ Y : Finset (Fin N), Y.card ≤ q →
        D.eval (incidenceInput (zeroSet S Y) Y) = false ∨ E.eval (incidenceInput (zeroSet S Y) Y) = false) →
      ∀ Y : Finset (Fin N), Y.card ≤ q → row D Y ∨ row E Y := by
  intro q N S D E row weight join ad ae fd fe diag Y small
  have fills (B : Circuit) (ab : IsAO2 (N+N) B) (fb : RightOnIncidentPairs S B)
      (hb : B.eval (incidenceInput (zeroSet S Y) Y) = false) :
      ∀ Z : Finset (Fin N), B.eval (incidenceInput (zeroSet S Y) Z) = decide (¬ Z ⊆ Y) := by
    intro Z
    by_cases incl : Z ⊆ Y
    · have hval : B.eval (incidenceInput (zeroSet S Y) Z) = false := by
        cases h : B.eval (incidenceInput (zeroSet S Y) Z) with
        | false => rfl
        | true =>
          have bad := inputMono B ab (Finset.Subset.refl _) incl h
          rw [hb] at bad
          contradiction
      simpa [incl] using hval
    · obtain ⟨l,hl,hy⟩ := Finset.not_subset.mp incl
      have hc := privateCount S weight join Y hy
      have hpos : 0 < (S l ∩ zeroSet S Y).card := by omega
      obtain ⟨p,hp⟩ := Finset.card_pos.mp hpos
      have both := Finset.mem_inter.mp hp
      simpa [incl] using inputMono B ab (Finset.singleton_subset_iff.mpr both.2)
        (Finset.singleton_subset_iff.mpr hl) (fb l p both.1)
  exact (diag Y small).imp (fills D ad fd) (fills E ae fe)

end SparsePlane

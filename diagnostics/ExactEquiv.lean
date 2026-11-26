import PEqualNP.Outside.L_meta_8996
import PEqualNP.Outside.L_meta_2420

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
namespace PEqualNP.Outside.L_meta_8998Research
abbrev plane (l : Fin 13) : Finset (Fin 13) := {l, l+1, l+3, l+9}
abbrev thin (v : Fin 26 → Bool) := ∃ l : Fin 13, ∀ k : Fin 13, v (Fin.natAdd 13 k) = true → k = l
abbrev edgeAt (v : Fin 26 → Bool) := ∃ p l : Fin 13, p ∈ plane l ∧ v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true
abbrev good (C : Circuit) := Monotone2 C ∧ (∀ p l, p ∈ plane l → C.eval (incidenceInput {p} {l}) = true) ∧
  (∀ P L, IsMaximalFalse plane P L → ¬ IsGeneric plane 0 P L → C.eval (incidenceInput P L) = false)

theorem thinCorrect {C : Circuit} (h : good C) : ∀ v, thin v → circuitFun 26 C v = decide (edgeAt v) := by
  classical
  rcases h with ⟨hM, hpos, hdmf⟩
  let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
  let A : (Fin 26 → Bool) → Prop := fun v => ∃ l : Fin 13, ∀ l' : Fin 13, v (Fin.natAdd 13 l') = true → l' = l
  let inc : (Fin 26 → Bool) → Bool := fun v => decide (∃ p l : Fin 13, p ∈ S l ∧ v (Fin.castAdd 13 p) = true ∧ v (Fin.natAdd 13 l) = true)
  have hmono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ k, x.getD k false = true → y.getD k false = true) →
      ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD k false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD k false = true := by
    intro gs
    induction gs with
    | nil =>
      intro _ x y _ hxy k hk
      exact hxy k hk
    | cons g gs ih =>
      intro hgs x y hlen hxy k hk
      have hg := hgs g (by simp)
      have hgs' : ∀ g' ∈ gs, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      refine ih hgs' _ _ (by simp [hlen]) ?_ k hk
      intro j
      rcases lt_trichotomy j x.length with hj | hj | hj
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
          List.getElem?_append_left (by omega : j < y.length)]
        exact hxy j
      · subst hj
        have hxj : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD x.length false =
            g.op.eval (g.inputs.map fun i => x.getD i false) := by simp
        have hyj : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD y.length false =
            g.op.eval (g.inputs.map fun i => y.getD i false) := by simp
        rw [hxj, hlen, hyj]
        have heval_and : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
        have heval_or : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
        rcases Set.mem_insert_iff.mp hg.1 with hop | hop
        · rw [hop, heval_and, heval_and]
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact hxy i (h i hi)
        · rw [Set.mem_singleton_iff.mp hop, heval_or, heval_or]
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i, hi, hxi⟩
          exact ⟨i, hi, hxy i hxi⟩
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        intro h
        cases h
  have hC_mono : ∀ (x y : List Bool), x.length = y.length →
      (∀ k, x.getD k false = true → y.getD k false = true) →
      C.eval x = true → C.eval y = true := by
    intro x y hlen hxy hx
    exact hmono C.gates hM x y hlen hxy C.output hx
  have hinc_def : ∀ (X Y : Finset (Fin 13)),
      PEqualNP.GenericRejection.incidenceInput X Y =
        List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) :=
    fun _ _ => rfl
  have hinc_len : ∀ (X Y : Finset (Fin 13)),
      (PEqualNP.GenericRejection.incidenceInput X Y).length = 26 := by
    intro X Y; rw [hinc_def, List.length_append, List.length_ofFn, List.length_ofFn]
  have hinc_get : ∀ (X Y : Finset (Fin 13)) (k : ℕ),
      (PEqualNP.GenericRejection.incidenceInput X Y).getD k false =
        if hk1 : k < 13 then decide (⟨k, hk1⟩ ∈ X)
        else if hk2 : k < 26 then decide (⟨k - 13, by omega⟩ ∈ Y)
        else false := by
    intro X Y k
    rw [hinc_def]
    simp only [List.getD_eq_getElem?_getD]
    by_cases hk1 : k < 13
    · simp only [hk1, ↓reduceDIte]
      rw [List.getElem?_append_left (by simp; exact hk1), List.getElem?_ofFn]
      simp [hk1]
    · simp only [hk1, ↓reduceDIte]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn]
      by_cases hk2 : k < 26
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_ofFn]
        simp [show k - 13 < 13 by omega]
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  have hofFn_get : ∀ (v : Fin 26 → Bool) (k : ℕ),
      (List.ofFn v).getD k false =
        if hk1 : k < 13 then v (Fin.castAdd 13 ⟨k, hk1⟩)
        else if hk2 : k < 26 then v (Fin.natAdd 13 (⟨k - 13, by omega⟩ : Fin 13))
        else false := by
    intro v k
    simp only [List.getD_eq_getElem?_getD]
    by_cases hk1 : k < 13
    · simp only [hk1, ↓reduceDIte, List.getElem?_ofFn, show k < 26 by omega]
      rfl
    · simp only [hk1, ↓reduceDIte]
      by_cases hk2 : k < 26
      · simp only [hk2, ↓reduceDIte, List.getElem?_ofFn]
        have he : (⟨k, hk2⟩ : Fin 26) = Fin.natAdd 13 (⟨k - 13, by omega⟩ : Fin 13) := Fin.ext (by simp; omega)
        rw [he]
        rfl
      · simp only [hk2, ↓reduceDIte]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  have hmem_self : ∀ l : Fin 13, l ∈ S l := fun l => Finset.mem_insert_self l _
  have hdiff_line : ∀ l l' : Fin 13, l ≠ l' → ∃ p : Fin 13, p ∈ S l' ∧ p ∉ S l := by
    decide
  have hc_agree : ∀ v : Fin 26 → Bool, A v → PEqualNP.MetaComplexity.circuitFun 26 C v = inc v := by
    intro v hv
    obtain ⟨l, hl⟩ := hv
    by_cases hvl : v (Fin.natAdd 13 l) = true
    · by_cases hp : ∃ p : Fin 13, p ∈ S l ∧ v (Fin.castAdd 13 p) = true
      · obtain ⟨p, hpl, hvp⟩ := hp
        have hinc_t : inc v = true := by
          simp only [inc, decide_eq_true_eq]
          exact ⟨p, l, hpl, hvp, hvl⟩
        have hle_sing : ∀ k, (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin 13)) {l}).getD k false = true →
            (List.ofFn v).getD k false = true := by
          intro k hk
          rw [hinc_get] at hk
          rw [hofFn_get]
          by_cases hk1 : k < 13
          · simp only [hk1, ↓reduceDIte] at hk ⊢
            have hpeq : (⟨k, hk1⟩ : Fin 13) = p := by simpa using hk
            rw [hpeq]
            exact hvp
          · by_cases hk2 : k < 26
            · simp only [hk1, hk2, ↓reduceDIte] at hk ⊢
              have hleq : (⟨k - 13, by omega⟩ : Fin 13) = l := by simpa using hk
              rw [hleq]
              exact hvl
            · simp only [hk1, hk2, ↓reduceDIte] at hk
              cases hk
        have hC_t : C.eval (List.ofFn v) = true :=
          hC_mono (PEqualNP.GenericRejection.incidenceInput {p} {l}) (List.ofFn v)
            (by rw [hinc_len, List.length_ofFn]) hle_sing (hpos p l hpl)
        change C.eval (List.ofFn v) = inc v
        rw [hC_t, hinc_t]
      · have hinc_f : inc v = false := by
          simp only [inc, decide_eq_false_iff_not]
          rintro ⟨p, l', hpl', hvp, hvl'⟩
          have heq := hl l' hvl'
          subst heq
          exact hp ⟨p, hpl', hvp⟩
        have hdmf_l : PEqualNP.GenericRejection.IsMaximalFalse S (Finset.univ \ S l) {l} ∧
            ¬PEqualNP.GenericRejection.IsGeneric S 0 (Finset.univ \ S l) {l} := by
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · intro l' hl'
            rw [Finset.mem_singleton.mp hl']
            exact disjoint_sdiff_self_right
          · intro q hq hf
            have hqS : q ∈ S l := by
              by_contra hqn
              exact hq (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqn⟩)
            have hdisj := hf l (Finset.mem_singleton_self l)
            exact Finset.disjoint_right.mp hdisj (Finset.mem_insert_self q _) hqS
          · intro l' hl' hf
            have hne : l' ≠ l := fun h => hl' (Finset.mem_singleton.mpr h)
            obtain ⟨q, hq1, hq2⟩ := hdiff_line l l' hne.symm
            have hdisj := hf l' (Finset.mem_insert_self l' _)
            exact Finset.disjoint_right.mp hdisj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq2⟩) hq1
          · intro hg
            refine hg.2.2.2 l ?_
            intro l' hl'
            rw [Finset.mem_singleton.mp hl']
            exact hmem_self l
        have hC_l : C.eval (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l}) = false :=
          hdmf (Finset.univ \ S l) {l} hdmf_l.1 hdmf_l.2
        have hle_comp : ∀ k, (List.ofFn v).getD k false = true →
            (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l}).getD k false = true := by
          intro k hk
          rw [hofFn_get] at hk
          rw [hinc_get]
          by_cases hk1 : k < 13
          · simp only [hk1, ↓reduceDIte, decide_eq_true_eq, Finset.mem_sdiff, Finset.mem_univ,
              true_and] at hk ⊢
            intro hmem
            exact hp ⟨⟨k, hk1⟩, hmem, hk⟩
          · by_cases hk2 : k < 26
            · simp only [hk1, hk2, ↓reduceDIte, decide_eq_true_eq, Finset.mem_singleton] at hk ⊢
              exact hl ⟨k - 13, by omega⟩ hk
            · simp only [hk1, hk2, ↓reduceDIte] at hk
              cases hk
        have hC_f : C.eval (List.ofFn v) = false := by
          by_contra hnt
          have ht := Bool.eq_true_of_not_eq_false hnt
          have := hC_mono (List.ofFn v) (PEqualNP.GenericRejection.incidenceInput (Finset.univ \ S l) {l})
            (by rw [List.length_ofFn, hinc_len]) hle_comp ht
          rw [hC_l] at this
          cases this
        change C.eval (List.ofFn v) = inc v
        rw [hC_f, hinc_f]
    · have hvl_all : ∀ l' : Fin 13, v (Fin.natAdd 13 l') = false := fun l' => by
        by_contra hnt
        have ht := Bool.eq_true_of_not_eq_false hnt
        have heq := hl l' ht
        subst heq
        exact hvl ht
      have hinc_f : inc v = false := by
        simp only [inc, decide_eq_false_iff_not]
        rintro ⟨p, l', _, _, hvl'⟩
        rw [hvl_all l'] at hvl'
        cases hvl'
      have hdmf_0 : PEqualNP.GenericRejection.IsMaximalFalse S Finset.univ ∅ ∧
          ¬PEqualNP.GenericRejection.IsGeneric S 0 Finset.univ ∅ := by
        refine ⟨⟨fun _ hl0 => by simp at hl0, fun q hq => by simp at hq, fun l0 _ hf => ?_⟩, ?_⟩
        · have hdisj := hf l0 (Finset.mem_insert_self l0 ∅)
          exact Finset.disjoint_right.mp hdisj (Finset.mem_univ l0) (hmem_self l0)
        · intro hg
          exact hg.2.2.2 0 (fun l0 hl0 => by simp at hl0)
      have hC_0 : C.eval (PEqualNP.GenericRejection.incidenceInput Finset.univ ∅) = false :=
        hdmf Finset.univ ∅ hdmf_0.1 hdmf_0.2
      have hle_univ : ∀ k, (List.ofFn v).getD k false = true →
          (PEqualNP.GenericRejection.incidenceInput (Finset.univ : Finset (Fin 13)) (∅ : Finset (Fin 13))).getD k false = true := by
        intro k hk
        rw [hofFn_get] at hk
        rw [hinc_get]
        by_cases hk1 : k < 13
        · simp only [hk1, ↓reduceDIte]; simp
        · by_cases hk2 : k < 26
          · simp only [hk1, hk2, ↓reduceDIte] at hk
            rw [hvl_all ⟨k - 13, by omega⟩] at hk
            cases hk
          · simp only [hk1, hk2, ↓reduceDIte] at hk
            cases hk
      have hC_f : C.eval (List.ofFn v) = false := by
        by_contra hnt
        have ht := Bool.eq_true_of_not_eq_false hnt
        have := hC_mono (List.ofFn v) (PEqualNP.GenericRejection.incidenceInput Finset.univ ∅)
          (by rw [List.length_ofFn, hinc_len]) hle_univ ht
        rw [hC_0] at this
        cases this
      change C.eval (List.ofFn v) = inc v
      rw [hC_f, hinc_f]
  exact hc_agree

theorem exact_iff : (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x1 : Fin (13 : ℕ)) => {x1, x1 + (1 : Fin (13 : ℕ)), x1 + (3 : Fin (13 : ℕ)), x1 + (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)), ∀ (x4 : Fin (13 : ℕ)), x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true → x4 = x3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     x3.size ≤ (63 : ℕ) →       (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ x1 x7 → x3.eval (PEqualNP.GenericRejection.incidenceInput {x6} {x7}) = Bool.true) →         (∀ (x7 x8 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x1 x7 x8 → ¬PEqualNP.GenericRejection.IsGeneric x1 (0 : ℕ) x7 x8 → x3.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) →           ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.Monotone2 x8 ∧               x8.size ≤ x3.size ∧                 (∀ (x9 : Fin (26 : ℕ) → Bool), x2 x9 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 x9) ∧                   ∀ (x9 x10 x11 : ℕ),                     x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } →                       have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.take x9 x8.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };                       have x14 : List ℕ := x13.lineDegrees (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));                       (0 : ℕ) < Min.min (x14.getD x10 (0 : ℕ)) (x14.getD x11 (0 : ℕ)) →                         ∃ (x16 : ℕ) (x17 : ℕ),                           ∀ (x18 : Fin (26 : ℕ) → Bool),                             x2 x18 →                               have x20 : List Bool := x13.wires (List.ofFn x18);                               (x20.getD x10 Bool.false && x20.getD x11 Bool.false) = (x20.getD x16 Bool.false || x20.getD x17 Bool.false)) ↔ (∀ C : Circuit, good C → 64 ≤ C.size) := by
  constructor
  · intro posted C hc
    by_contra! small
    have hs : C.size ≤ 63 := by omega
    obtain ⟨D, dm, dsz, dag, localCover⟩ := posted C hc.1 hs hc.2.1 hc.2.2
    obtain ⟨E, em, esz, edeg, eag⟩ := PEqualNP.Outside.L_meta_8996 26 (Finset.Ico 13 26) {v | thin v} D dm (by
      intro i a b hg ha hb
      obtain ⟨u, w, cover⟩ := localCover i a b hg (lt_min ha hb)
      refine ⟨[u,w], by decide, ?_⟩
      intro v hv
      simpa using cover v hv)
    have lb := PEqualNP.Outside.L_meta_2420 E em edeg (by
      intro v hv
      have eqv : circuitFun 26 E v = decide (edgeAt v) := (eag v hv).trans ((dag v hv).trans (thinCorrect hc v hv))
      rw [eqv, decide_eq_true_eq]
      have index : ∀ p l : Fin 13, p ∈ plane l ↔ ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l+d := by decide +kernel
      exact exists_congr fun p => exists_congr fun l => and_congr_left fun _ => index p l)
    omega
  · intro lower C hm hs hp hn
    have h := lower C ⟨hm, hp, hn⟩
    omega
end PEqualNP.Outside.L_meta_8998Research

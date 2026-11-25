import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2874_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, ∃ b : Bool, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b))

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, b0, hin, ha, hc⟩
      exact ⟨a, c, b0, hin, hSub b0 ha, hSub (!b0) hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {a c : ℕ} (ha : a ∈ S b) (hc : c ∈ S (!b)) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt b a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt (!b) c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, b, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, ∃ b : Bool, (gateAt C j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b)) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end PEqualNP.Outside.L_meta_2874_aux

open PEqualNP.Outside.L_meta_2874_aux in
theorem PEqualNP.Outside.L_meta_2874 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),
      (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →
        ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
          PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
            x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
              (∀ (x9 : Fin (x1 + x2) → Bool),
                PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
                  Decidable.decide
                    (∃ (x10 : Fin x1) (x11 : Fin x2),
                      (x10, x11) ∈ x3 ∧
                        x9 (Fin.castAdd x2 x10) = Bool.true ∧
                          x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
                have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate :=
                  PEqualNP.MetaComplexity.NestedCover.gateAt x7;
                (∀ (x10 : Bool), ∀ x11 ∈ x8 x10,
                  x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
                    ∃ x13 < x7.size,
                      x11 = x1 + x2 + x13 ∧
                        (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                          ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧
                  ∀ x10 < x7.size,
                    (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                      ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
                        (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

namespace PEqualNP.Outside.Star4594
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd
set_option maxHeartbeats 400000
lemma supportStep_length {m : ℕ} (s : List (Finset (Fin m))) (g : Gate) :
    (supportStep s g).length = s.length + 1 := by
  simp [supportStep]

lemma supports_length (m : ℕ) (C : Circuit) :
    (supports m C).length = m + C.gates.length := by
  have h : ∀ (gs : List Gate) (s : List (Finset (Fin m))),
      (gs.foldl supportStep s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp
    | cons g gs ih => intro s; simp [List.foldl_cons, ih, supportStep_length]; omega
  unfold supports
  rw [h, List.length_ofFn]

lemma support_input (m : ℕ) (C : Circuit) (i : ℕ) (hi : i < m) :
    support m C i = ({⟨i, hi⟩} : Finset (Fin m)) := by
  have hfold : ∀ (gs : List Gate) (s : List (Finset (Fin m))), i < s.length →
      (gs.foldl supportStep s).getD i ∅ = s.getD i ∅ := by
    intro gs
    induction gs with
    | nil => intro s _; rfl
    | cons g gs ih =>
      intro s hs
      rw [List.foldl_cons, ih _ (by rw [supportStep_length]; omega), supportStep, List.getD_append _ _ _ _ hs]
  unfold support supports
  rw [hfold _ _ (by simp [hi])]
  have hof : (List.ofFn fun i : Fin m => ({i} : Finset (Fin m)))[i]? = some ({⟨i, hi⟩} : Finset (Fin m)) := by
    simp [List.getElem?_eq_getElem (by simp [hi] : i < (List.ofFn fun i : Fin m => ({i} : Finset (Fin m))).length)]
  rw [List.getD, hof]; rfl

lemma support_gate (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    support m C (m + j) =
      C.gates[j].inputs.foldr (fun w acc => operandSupport m C j w ∪ acc) ∅ := by
  have hfold_getD : ∀ (gs : List Gate) (s : List (Finset (Fin m))) (k : ℕ), k < s.length →
      (gs.foldl supportStep s).getD k ∅ = s.getD k ∅ := by
    intro gs
    induction gs with
    | nil => intro s _ _; rfl
    | cons g gs ih =>
      intro s k hk
      rw [List.foldl_cons, ih _ k (by rw [supportStep_length]; omega), supportStep, List.getD_append _ _ _ _ hk]
  have hfold_len : ∀ (gs : List Gate) (s : List (Finset (Fin m))),
      (gs.foldl supportStep s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp
    | cons g gs ih => intro s; simp [List.foldl_cons, ih, supportStep_length]; omega
  set s0 : List (Finset (Fin m)) := List.ofFn fun i : Fin m => ({i} : Finset (Fin m))
  set s1 : List (Finset (Fin m)) := (C.gates.take j).foldl supportStep s0
  have hs1_len : s1.length = m + j := by
    dsimp only [s1]
    rw [hfold_len, List.length_ofFn, List.length_take]
    omega
  have hsplit : supports m C = (C.gates.drop (j + 1)).foldl supportStep (supportStep s1 C.gates[j]) := by
    unfold supports
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj, List.foldl_append, List.foldl_cons]
  have hget : support m C (m + j) = (supportStep s1 C.gates[j]).getD (m + j) ∅ := by
    unfold support
    rw [hsplit, hfold_getD _ _ _ (by rw [supportStep_length, hs1_len]; omega)]
  rw [hget, supportStep, ← hs1_len, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  congr 1
  ext w acc
  congr 1
  by_cases hw : w < m + j
  · have heq : s1.getD w ∅ = support m C w := by
      unfold support supports
      conv_rhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
      exact (hfold_getD (C.gates.drop j) s1 w (by rw [hs1_len]; exact hw)).symm
    rw [operandSupport, if_pos hw, heq]
  · rw [operandSupport, if_neg hw, List.getD_eq_default s1 _ (by rw [hs1_len]; omega)]

lemma mem_foldr_union {α : Type*} [DecidableEq α] (l : List ℕ) (f : ℕ → Finset α) (x : α) :
    x ∈ l.foldr (fun w acc => f w ∪ acc) ∅ ↔ ∃ w ∈ l, x ∈ f w := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.mem_union, ih]

lemma mem_support_gate {m : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (x : Fin m) :
    x ∈ support m C (m + j) ↔ ∃ w ∈ C.gates[j].inputs, x ∈ operandSupport m C j w := by
  rw [support_gate m C j hj, mem_foldr_union]

/- The support equations used here are from L-meta-4592.
The two-side star construction is the certified theorem L-meta-2874. -/
private theorem marked {n : ℕ} (x : Fin (n+n)) :
    x ∈ Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) ↔ n ≤ x.val := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.natAddEmb_apply, Fin.ext_iff, Fin.val_natAdd]
  constructor
  · rintro ⟨i,hi⟩
    omega
  · intro hx
    exact ⟨⟨x.val-n, by have h := x.isLt; omega⟩,by dsimp; omega⟩

theorem starNetwork (n : ℕ) (F : Finset (Fin n × Fin n)) (P L : Finset (Fin n))
    (cover : ∀ e ∈ F, e.1∈P ∨ e.2∈L) :
    ∃ B : Circuit, IsAO2 (n+n) B ∧
      B.size ≤ F.card+P.card+L.card-1 ∧
      (∀ z : Fin (n+n) → Bool, circuitFun (n+n) B z =
        decide (∃ p l, (p,l) ∈ F ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true)) ∧
      crossCount (n+n) (Finset.map (Fin.natAddEmb n) Finset.univ) B = 0 := by
  classical
  obtain ⟨B,K,hao,sz,sem,typed,ands⟩ := PEqualNP.Outside.L_meta_2874 n n F P L cover
  refine ⟨B,hao,sz,sem,?_⟩
  let M := Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n))
  have color (w : ℕ) (t : Bool) (belongs : w ∈ K t) (x : Fin (n+n))
      (hx : x ∈ support (n+n) B w) : decide (n ≤ x.val) = t := by
    induction w using Nat.strong_induction_on generalizing t x with
    | ind w ih =>
      rcases typed t w belongs with ⟨raw,side⟩ | ⟨j,hj,wire,_,lower⟩
      · rw [support_input (n+n) B w raw,Finset.mem_singleton] at hx
        subst x
        exact side
      · subst w
        obtain ⟨a,ha,hx⟩ := (mem_support_gate (C:=B) hj x).mp hx
        have eqg : gateAt B j = B.gates[j] := List.getD_eq_getElem _ _ hj
        rw [eqg] at lower
        by_cases prev : a < n+n+j
        · rw [operandSupport,if_pos prev] at hx
          exact ih a prev t (lower a ha) x hx
        · simp [operandSupport,prev] at hx
  have operand (j a : ℕ) (t : Bool) (ha : a ∈ K t) (x : Fin (n+n))
      (hx : x ∈ operandSupport (n+n) B j a) : decide (n ≤ x.val) = t := by
    by_cases prev : a<n+n+j
    · rw [operandSupport,if_pos prev] at hx
      exact color a t ha x hx
    · simp [operandSupport,prev] at hx
  have clean (j : ℕ) (hj : j < B.gates.length) : ¬ IsCrossAnd (n+n) M B j := by
    intro h
    obtain ⟨a,b,t,ins,ha,hb⟩ := ands j hj h.1
    have u := h.2.2
    simp only [ins,List.getD_cons_zero,List.getD_cons_succ] at u
    rcases u with ⟨⟨x,hx⟩,⟨y,hy⟩⟩ | ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    · obtain ⟨xs,xm⟩ := Finset.mem_inter.mp hx
      obtain ⟨ys,ym⟩ := Finset.mem_inter.mp hy
      have ax := operand j a t ha x xs
      have by' := operand j b (!t) hb y ys
      have mx := (marked x).mp xm
      have my := (marked y).mp ym
      cases t <;> simp_all
    · obtain ⟨xs,xm⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨ys,ym⟩ := Finset.mem_sdiff.mp hy
      have ax := operand j a t ha x xs
      have by' := operand j b (!t) hb y ys
      have mx : ¬ n ≤ x.val := fun h => xm ((marked x).mpr h)
      have my : ¬ n ≤ y.val := fun h => ym ((marked y).mpr h)
      cases t <;> simp_all <;> omega
  change ((Finset.range B.gates.length).filter (IsCrossAnd (n+n) M B)).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hr,hcross⟩ := Finset.mem_filter.mp hj
  exact clean j (Finset.mem_range.mp hr) hcross

end PEqualNP.Outside.Star4594

namespace PEqualNP.Outside.Frame4594
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd

def shift (n d i : ℕ) : ℕ := if i<n then i else d+i

def move (n d : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (shift n d)⟩

def push {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α) (g : Gate) : List α :=
  xs ++ [ev g.op (g.inputs.map fun i => xs.getD i z)]

lemma frameRead {α : Type} (z : α) (raw mid post : List α) (i : ℕ) :
    ((raw++mid)++post).getD (shift raw.length mid.length i) z = (raw++post).getD i z := by
  by_cases h : i < raw.length
  · simp only [shift,h,if_true,List.append_assoc]
    rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
  · simp only [shift,h,if_false]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega)]
    simp only [List.length_append]
    congr 1 <;> omega

lemma frameRun {α : Type} (z : α) (ev : GateOp → List α → α) (raw mid : List α)
    (gs : List Gate) (post : List α) :
    ∃ more : List α,
      (gs.map (move raw.length mid.length)).foldl (push z ev) ((raw++mid)++post) =
        (raw++mid)++more ∧
      gs.foldl (push z ev) (raw++post) = raw++more := by
  induction gs generalizing post with
  | nil => exact ⟨post,rfl,rfl⟩
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    let v := ev g.op (g.inputs.map fun i => (raw++post).getD i z)
    have he : ev (move raw.length mid.length g).op
        ((move raw.length mid.length g).inputs.map fun i => ((raw++mid)++post).getD i z) = v := by
      simp only [move,List.map_map,Function.comp_def,frameRead,v]
    have big : push z ev ((raw++mid)++post) (move raw.length mid.length g) =
          (raw++mid)++(post++[v]) := by rw [push,he,List.append_assoc]
    have small : push z ev (raw++post) g = raw++(post++[v]) := List.append_assoc .. 
    rw [big,small]
    exact ih (post++[v])

lemma runTail {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α) (gs : List Gate) :
    ∃ mid : List α, gs.foldl (push z ev) xs = xs++mid ∧ mid.length=gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨tail,he,hl⟩ := ih (push z ev xs g)
    refine ⟨ev g.op (g.inputs.map fun i => xs.getD i z)::tail,?_,?_⟩
    · simpa [List.foldl_cons,push,List.append_assoc] using he
    · simp [hl]

def unionValues {n : ℕ} (_ : GateOp) (r : List (Finset (Fin n))) : Finset (Fin n) :=
  r.foldr (· ∪ ·) ∅

lemma support_form {n : ℕ} : @supportStep n = push (∅ : Finset (Fin n)) unionValues := by
  funext xs g
  unfold supportStep push unionValues
  have ef (ws : List ℕ) :
      ws.foldr (fun w acc => xs.getD w ∅ ∪ acc) ∅ =
        (ws.map fun i => xs.getD i ∅).foldr (· ∪ ·) ∅ := by
    induction ws with
    | nil => rfl
    | cons a ws ih => simp only [List.foldr_cons,List.map_cons,ih]
  rw [ef]

def stages (n : ℕ) (D E : Circuit) := D.gates ++ E.gates.map (move n D.size)

def merger (n : ℕ) (D E : Circuit) : Gate :=
  let b := shift n D.size E.output
  ⟨.or,[if D.output<n+D.size then D.output else b,b]⟩

def joined (n : ℕ) (D E : Circuit) : Circuit :=
  ⟨stages n D E ++ [merger n D E],n+D.size+E.size⟩

lemma stageRead {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α)
    (n : ℕ) (hlen : xs.length=n) (D E : Circuit) :
    let st := (stages n D E).foldl (push z ev) xs
    (∀ i < n+D.size, st.getD i z = (D.gates.foldl (push z ev) xs).getD i z) ∧
    (∀ i, st.getD (shift n D.size i) z = (E.gates.foldl (push z ev) xs).getD i z) ∧
    st.length=n+D.size+E.size := by
  dsimp only
  obtain ⟨mid,hD,lD⟩ := runTail z ev xs D.gates
  change mid.length = D.size at lD
  obtain ⟨more,pref,post⟩ := frameRun z ev xs mid E.gates []
  simp only [List.append_nil,hlen,lD] at pref post
  have st : (stages n D E).foldl (push z ev) xs = (xs++mid)++more := by
    rw [stages,List.foldl_append,hD,pref]
  refine ⟨?_,?_,?_⟩
  · intro i bound
    rw [st,hD,List.getD_append _ _ _ _ (by simp [hlen,lD,bound])]
  · intro i
    rw [st,post,← hlen,← lD]
    exact frameRead z xs mid more i
  · obtain ⟨extra,hX,lX⟩ := runTail z ev xs (stages n D E)
    rw [hX,List.length_append,hlen,lX]
    simp [stages,Circuit.size,Nat.add_assoc]

lemma joinSize (n : ℕ) (D E : Circuit) : (joined n D E).size = D.size+E.size+1 := by
  simp [joined,stages,Circuit.size,Nat.add_assoc]

lemma joinMono {n : ℕ} {D E : Circuit} (hD : Monotone2 D) (hE : Monotone2 E) :
    Monotone2 (joined n D E) := by
  intro g hg
  simp only [joined,stages,List.mem_append,List.mem_map,List.mem_singleton] at hg
  rcases hg with (hd|⟨f,hf,rfl⟩)|rfl
  · exact hD _ hd
  · obtain ⟨ops,sz⟩ := hE _ hf
    exact ⟨ops,by simpa [move] using sz⟩
  · exact ⟨Or.inr rfl,by simp [merger]⟩

lemma joinEval {n : ℕ} (D E : Circuit) (xs : List Bool) (hlen : xs.length=n) :
    (joined n D E).eval xs = (D.eval xs || E.eval xs) := by
  obtain ⟨old,ren,len⟩ := stageRead false GateOp.eval xs n hlen D E
  let w := (stages n D E).foldl (push false GateOp.eval) xs
  change w.length=n+D.size+E.size at len
  change ((stages n D E ++ [merger n D E]).foldl (push false GateOp.eval) xs).getD
    (n+D.size+E.size) false = _
  rw [List.foldl_append]
  change (w ++ [(merger n D E).op.eval ((merger n D E).inputs.map fun i => w.getD i false)]).getD
    (n+D.size+E.size) false = _
  rw [List.getD_append_right _ _ _ _ (by omega),← len,Nat.sub_self]
  change (w.getD (if D.output<n+D.size then D.output else shift n D.size E.output) false ||
    (w.getD (shift n D.size E.output) false || false)) = _
  have hr : w.getD (shift n D.size E.output) false = E.eval xs := ren _
  rw [Bool.or_false,hr]
  by_cases valid : D.output < n+D.size
  · rw [if_pos valid,old D.output valid]
    rfl
  · rw [if_neg valid,hr,Bool.or_self]
    have hlenD : (D.wires xs).length=n+D.size := by
      obtain ⟨m,p,h⟩ := runTail false GateOp.eval xs D.gates
      change (D.gates.foldl (push false GateOp.eval) xs).length=n+D.size
      rw [p,List.length_append,hlen,h]
      rfl
    have zero : D.eval xs=false := by
      unfold Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [zero,Bool.false_or]

lemma stageOldGate (n : ℕ) (D E : Circuit) (j : ℕ) (hj : j<D.size) :
    gateAt (joined n D E) j = gateAt D j := by
  unfold gateAt
  change ((D.gates++E.gates.map (move n D.size))++[merger n D E]).getD j _ =
    D.gates.getD j _
  rw [List.append_assoc,List.getD_append _ _ _ _ hj]

lemma stageNewGate (n : ℕ) (D E : Circuit) (j : ℕ) (hj : j<E.size) :
    gateAt (joined n D E) (D.size+j) = move n D.size (gateAt E j) := by
  have hsz : D.size+j < (D.gates ++ E.gates.map (move n D.size)).length := by
    simp only [List.length_append,List.length_map]; change D.size+j<D.size+E.size; omega
  unfold gateAt
  change ((D.gates++E.gates.map (move n D.size))++[merger n D E]).getD (D.size+j) _ = _
  rw [List.getD_append _ _ _ _ hsz,List.getD_append_right _ _ _ _ (by change D.size ≤ D.size+j; omega)]
  change (E.gates.map (move n D.size)).getD (D.size+j-D.size) _ = _
  rw [Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ (by simpa [Circuit.size] using hj),
    List.getElem_map,List.getD_eq_getElem _ _ hj]
  rfl

lemma stageLastGate (n : ℕ) (D E : Circuit) :
    gateAt (joined n D E) (D.size+E.size) = merger n D E := by
  unfold gateAt
  change ((stages n D E)++[merger n D E]).getD (D.size+E.size) _ = _
  have h : (stages n D E).length=D.size+E.size := by simp [stages,Circuit.size]
  rw [List.getD_append_right _ _ _ _ (by omega),h,Nat.sub_self]
  rfl

lemma joinSupport (n : ℕ) (D E : Circuit) :
    (∀ j < D.size, ∀ a, operandSupport n (joined n D E) j a = operandSupport n D j a) ∧
    (∀ j < E.size, ∀ a, operandSupport n (joined n D E) (D.size+j) (shift n D.size a) =
        operandSupport n E j a) := by
  let xs := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))
  have hx : xs.length=n := by simp [xs]
  obtain ⟨old,ren,len⟩ := stageRead ∅ unionValues xs n hx D E
  let w := (stages n D E).foldl (push ∅ unionValues) xs
  change w.length=n+D.size+E.size at len
  have read (i : ℕ) (hi : i < n+D.size+E.size) : support n (joined n D E) i = w.getD i ∅ := by
    unfold support supports
    rw [support_form]
    change ((stages n D E ++ [merger n D E]).foldl (push ∅ unionValues) xs).getD i ∅ = _
    rw [List.foldl_append]
    change (push ∅ unionValues w (merger n D E)).getD i ∅ = _
    rw [push,List.getD_append _ _ _ _ (by omega)]
  constructor
  · intro j hj a
    by_cases a0 : a<n+j
    · rw [operandSupport,operandSupport,if_pos a0,if_pos a0,read a (by omega)]
      unfold support supports
      rw [support_form]
      exact old a (by omega)
    · simp [operandSupport,a0]
  · intro j hj a
    have bound : shift n D.size a < n+(D.size+j) ↔ a<n+j := by dsimp [shift]; split <;> omega
    by_cases a0 : a<n+j
    · have sa := bound.mpr a0
      rw [operandSupport,operandSupport,if_pos a0,if_pos sa,read _ (by omega)]
      unfold support supports
      rw [support_form]
      exact ren a
    · have sa := mt bound.mp a0
      simp [operandSupport,sa,a0]

lemma joinCount (n : ℕ) (M : Finset (Fin n)) (D E : Circuit)
    (clean : crossCount n M E = 0) : crossCount n M (joined n D E) ≤ crossCount n M D := by
  classical
  obtain ⟨o,s⟩ := joinSupport n D E
  have ce (j : ℕ) (hj : j<E.size) : ¬ IsCrossAnd n M E j := by
    intro cross
    let T := (Finset.range E.gates.length).filter (IsCrossAnd n M E)
    have hjt : j∈T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,cross⟩
    have hpos := Finset.card_pos.mpr (show T.Nonempty from ⟨j,hjt⟩)
    change T.card = 0 at clean
    omega
  apply Finset.card_le_card
  intro j hj
  obtain ⟨jl,cross⟩ := Finset.mem_filter.mp hj
  have jl := Finset.mem_range.mp jl
  change j < (joined n D E).size at jl
  rw [joinSize] at jl
  by_cases old : j<D.size
  · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr old,?_⟩
    simpa only [IsCrossAnd,stageOldGate n D E j old,o j old] using cross
  · by_cases endAt : j=D.size+E.size
    · subst j
      have op := cross.1
      rw [stageLastGate] at op
      contradiction
    · let k := j-D.size
      have eqj : j=D.size+k := by dsimp [k]; omega
      have hk : k<E.size := by omega
      exfalso
      apply ce k hk
      rw [eqj] at cross
      unfold IsCrossAnd at cross ⊢
      rw [stageNewGate n D E k hk] at cross
      have le : (gateAt E k).inputs.length=2 := by simpa [move] using cross.2.1
      obtain ⟨a,b,ins⟩ := List.length_eq_two.mp le
      simpa only [move,ins,List.map_cons,List.map_nil,List.length_cons,List.length_nil,
        List.getD_cons_zero,List.getD_cons_succ,s k hk] using cross

end PEqualNP.Outside.Frame4594

namespace PEqualNP.Outside.Repair4594

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.GenericRejection PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {x y : List Bool} (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => intro i hi; exact hxy i hi
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    apply ih hgs' (by simp [step_length, hlen])
    intro i hi
    by_cases hilt : i < x.length
    · rw [step_getD _ _ _ hilt] at hi
      rw [step_getD _ _ _ (by omega)]
      exact hxy i hi
    · have hieq : i = x.length ∨ x.length < i := by omega
      rcases hieq with rfl | hgt
      · rw [step_getD_last] at hi
        rw [hlen, step_getD_last]
        rcases hg.1 with hop | hop
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          intro b hb
          rcases hb with ⟨a, ha, rfl⟩
          exact hxy a (hi (x.getD a false) ⟨a, ha, rfl⟩)
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          rcases hi with ⟨_, ⟨a, ha, rfl⟩, ha_true⟩
          exact ⟨y.getD a false, ⟨a, ha, rfl⟩, hxy a ha_true⟩
      · have h1 : ¬ i < (step x g).length := by rw [step_length]; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h1)] at hi
        cases hi

def wval (n : ℕ) (C : Circuit) (w : ℕ) (X Y : Finset (Fin n)) : Bool :=
  (C.wires (incidenceInput X Y)).getD w false

def pts (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => wval n C w {p} ∅ = true

def lns (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun l => wval n C w ∅ {l} = true

lemma incidenceInput_length {n : ℕ} (X Y : Finset (Fin n)) :
    (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

lemma incidenceInput_getD_left {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  rw [incidenceInput, List.getD_append _ _ _ _ (by simp [hi])]
  have hof : (List.ofFn fun p : Fin n => decide (p ∈ X))[i]? = some (decide (⟨i, hi⟩ ∈ X)) := by
    simp [List.getElem?_eq_getElem (by simp [hi] : i < (List.ofFn fun p : Fin n => decide (p ∈ X)).length)]
  rw [List.getD, hof]; rfl

lemma incidenceInput_getD_right {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + n) :
    (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
  rw [incidenceInput, List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; exact hi1)]
  simp only [List.length_ofFn]
  have hof : (List.ofFn fun l : Fin n => decide (l ∈ Y))[i - n]? = some (decide (⟨i - n, by omega⟩ ∈ Y)) := by
    simp [List.getElem?_eq_getElem (by simp; omega : i - n < (List.ofFn fun l : Fin n => decide (l ∈ Y)).length)]
  rw [List.getD, hof]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hmono : Monotone2 C) {X1 X2 Y1 Y2 : Finset (Fin n)}
    (hX : X1 ⊆ X2) (hY : Y1 ⊆ Y2) (w : ℕ) :
    wval n C w X1 Y1 = true → wval n C w X2 Y2 = true := by
  apply run_mono C.gates hmono (by simp [incidenceInput_length])
  intro i hi
  by_cases hi1 : i < n
  · rw [incidenceInput_getD_left X1 Y1 i hi1] at hi
    rw [incidenceInput_getD_left X2 Y2 i hi1]
    simp only [decide_eq_true_eq] at hi ⊢
    exact hX hi
  · by_cases hi2 : i < n + n
    · rw [incidenceInput_getD_right X1 Y1 i (by omega) hi2] at hi
      rw [incidenceInput_getD_right X2 Y2 i (by omega) hi2]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hY hi
    · rw [List.getD_eq_default _ _ (by simp [incidenceInput_length]; omega)] at hi
      cases hi


theorem repair : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (D : Circuit)
      (F : Finset (Fin n × Fin n)) (P L : Finset (Fin n)),
      let count := crossCount (n+n) (Finset.map (Fin.natAddEmb n) Finset.univ)
      Monotone2 D →
      (∀ X Y : Finset (Fin n), D.eval (incidenceInput X Y) = true → incidenceFun S X Y = true) →
      (∀ l (p : Fin n), p ∈ S l → D.eval (incidenceInput {p} {l}) = true ∨ (p,l) ∈ F) →
      (∀ e ∈ F, e.1 ∈ S e.2) →
      (∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) →
      ∃ B : Circuit, Monotone2 B ∧ ComputesIncidence S B ∧ count B ≤ count D ∧
        B.size ≤ D.size + F.card + P.card + L.card := by
  classical
  intro n S D F P L
  dsimp only
  intro dm under sing good cover
  have witness (X Y : Finset (Fin n)) (p l : Fin n) (hp : p∈X) (hl : l∈Y)
      (h : D.eval (incidenceInput {p} {l})=true) : D.eval (incidenceInput X Y)=true :=
    wval_mono dm (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) D.output h
  by_cases empty : F=∅
  · refine ⟨D,dm,?_,le_rfl,by omega⟩
    intro X Y
    apply Bool.eq_iff_iff.mpr
    refine ⟨under X Y,?_⟩
    intro h
    obtain ⟨p,hp,l,hl,edge⟩ := of_decide_eq_true h
    have h := sing l p edge
    rw [empty] at h
    exact witness X Y p l hp hl (h.resolve_right (Finset.notMem_empty _))
  obtain ⟨E,ao,size,sem,clean⟩ := Star4594.starNetwork n F P L cover
  have em : Monotone2 E := by
    intro g hg
    exact ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  have ce (X Y : Finset (Fin n)) :
      E.eval (incidenceInput X Y) = true ↔ ∃ p l, (p,l)∈F ∧ p∈X ∧ l∈Y := by
    let z : Fin (n+n) → Bool := Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y))
    have inp : List.ofFn z = incidenceInput X Y := by
      rw [List.ofFn_add]
      simp only [z,Fin.addCases_left,Fin.addCases_right,incidenceInput]
    have eq := sem z
    change E.eval (List.ofFn z)=_ at eq
    rw [inp] at eq
    rw [eq]
    simp only [z,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
  have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
  refine ⟨Frame4594.joined (n+n) D E,Frame4594.joinMono dm em,?_,
    Frame4594.joinCount _ _ _ _ clean,?_⟩
  · intro X Y
    rw [Frame4594.joinEval D E _ (incidenceInput_length X Y)]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true,ce]
    constructor
    · rintro (hd | ⟨p,l,hf,hp,hl⟩)
      · exact under X Y hd
      · exact decide_eq_true ⟨p,hp,l,hl,good (p,l) hf⟩
    · intro h
      obtain ⟨p,hp,l,hl,edge⟩ := of_decide_eq_true h
      rcases sing l p edge with hd | hf
      · exact Or.inl (witness X Y p l hp hl hd)
      · exact Or.inr ⟨p,l,hf,hp,hl⟩
  · rw [Frame4594.joinSize]
    omega

end PEqualNP.Outside.Repair4594

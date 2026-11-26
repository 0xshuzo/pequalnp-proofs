import PEqualNP.Defs

namespace Dirty9739.CoverCost

open PEqualNP.BicliqueBlockCost

noncomputable def small {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.1 else p.2

noncomputable def pairs {n : ℕ} (p : Block n) : Finset (Sym2 (Fin n)) :=
  (p.1 ×ˢ p.2).image (fun ab => s(ab.1, ab.2))

lemma small_card {n : ℕ} (p : Block n) (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    (small p).card ≤ 1 := by
  unfold small
  split_ifs with h1
  · exact h1
  · rcases h with h | h
    · exact absurd h h1
    · exact h

lemma pairs_card {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hb : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : (pairs p).card ≤ blockCost p := by
  obtain ⟨_, h1, h2, _⟩ := hb
  have a1 : 1 ≤ p.1.card := Finset.card_pos.mpr h1
  have a2 : 1 ≤ p.2.card := Finset.card_pos.mpr h2
  have hc : (pairs p).card ≤ p.1.card * p.2.card := by
    unfold pairs
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_product _ _))
  unfold blockCost
  rcases h with h | h
  · have e : p.1.card = 1 := le_antisymm h a1
    rw [e] at hc ⊢
    omega
  · have e : p.2.card = 1 := le_antisymm h a2
    rw [e] at hc ⊢
    omega

lemma main {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n))
    (hF : IsBlockCover G F) (hs : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    ∃ X : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G X ∧
      G.edgeSet.ncard + X.card ≤ familyCost F + 1 := by
  classical
  obtain ⟨hblk, hcov⟩ := hF
  refine ⟨F.biUnion small, ?_, ?_⟩
  · intro u v huv
    obtain ⟨p, hp, hc⟩ := hcov u v huv
    have key : ∀ a b : Fin n, a ∈ p.1 → b ∈ p.2 → a ∈ small p ∨ b ∈ small p := by
      intro a b ha hb
      unfold small
      split_ifs
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases key u v h1 h2 with h | h
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
    · rcases key v u h1 h2 with h | h
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  · have hsub : G.edgeSet ⊆ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      have huv : G.Adj u v := he
      obtain ⟨p, hp, hc⟩ := hcov u v huv
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩)
      unfold pairs
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨h1, h2⟩, Sym2.eq_swap⟩
    have hE : G.edgeSet.ncard ≤ ∑ p ∈ F, blockCost p := by
      calc G.edgeSet.ncard
          ≤ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (F.biUnion pairs).card := Set.ncard_coe_finset _
        _ ≤ ∑ p ∈ F, (pairs p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ F, blockCost p :=
            Finset.sum_le_sum (fun p hp => pairs_card G p (hblk p hp) (hs p hp))
    have hX : (F.biUnion small).card ≤ F.card := by
      calc (F.biUnion small).card ≤ ∑ p ∈ F, (small p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ F, 1 := Finset.sum_le_sum (fun p hp => small_card p (hs p hp))
        _ = F.card := by simp
    unfold familyCost
    omega

end Dirty9739.CoverCost

namespace Dirty9739
theorem CoverCost : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (PEqualNP.BicliqueBlockCost.Block x1)), PEqualNP.BicliqueBlockCost.IsBlockCover x2 x3 → (∀ x5 ∈ x3, x5.1.card ≤ (1 : ℕ) ∨ x5.2.card ≤ (1 : ℕ)) → ∃ (x6 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x6 ∧ x2.edgeSet.ncard + x6.card ≤ PEqualNP.BicliqueBlockCost.familyCost x3 + (1 : ℕ) := by
  intro n G F hF hs
  exact Dirty9739.CoverCost.main G F hF hs

end Dirty9739

namespace Dirty9739.CleanGates

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]

def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]

lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

lemma pos_gate_nnil {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (non : ∀ g ∈ gs, g.op=.and → g.inputs≠[])
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    exact non _ (List.getElem_mem hj)
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

theorem star_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → S w = S (a w) ∩ S (b w)) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            rw [hdisj w hkw hr hop] at hx hy
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hx (Finset.mem_inter.mpr ⟨hax,hbx⟩))
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hy (Finset.mem_inter.mpr ⟨hay,hby⟩))
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)


def portSet {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Nat → Finset (Fin n)) (c : Fin n) (w : Nat) :=
  (S w).filter (fun x => G.Adj c x)
def crosses {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Nat → Finset (Fin n)) (a b : Nat → Nat) (w : Nat) (c : Fin n) : Prop :=
  ¬portSet G S c (a w) ⊆ portSet G S c (b w) ∧
  ¬portSet G S c (b w) ⊆ portSet G S c (a w)

theorem trimmed_edges (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → (S w).card ≤ 1)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (huq : ∀ w, k ≤ w → w < N → A w = false → ∀ c d,
      crosses G S a b w c → crosses G S a b w d → c=d)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let F (c : Fin n) (w : Nat) := if w<N then portSet G S c w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v →
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            refine ⟨c,b w,fun _ u hu v hv edge => Or.inl ⟨Finset.card_le_one.mp h u hu c hc,?_⟩⟩
            have eq := Finset.card_le_one.mp h u hu c hc
            simpa [F,show b w<N by omega,portSet,hv,←eq] using edge
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            refine ⟨c,a w,fun _ u hu v hv edge => Or.inr ⟨Finset.card_le_one.mp h v hv c hc,?_⟩⟩
            have eq := Finset.card_le_one.mp h v hv c hc
            simpa [F,show a w<N by omega,portSet,hu,←eq] using edge.symm
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : Nat) := if h : ∃ c, crosses G S a b w c then h.choose else z
    have owner (w : Nat) (hk : k≤w) (hw : w<N) (ht : A w=false) (c : Fin n)
        (hc : crosses G S a b w c) : oc w=c := by
      have ex : ∃ q, crosses G S a b w q := ⟨c,hc⟩
      have hit : crosses G S a b w (oc w) := by simpa [oc,ex] using ex.choose_spec
      exact huq w hk hw ht _ _ hit hc
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hN : i<N
      · have sub : F c i ⊆ S i := by simpa only [F,if_pos hN,portSet] using
            (Finset.filter_subset (fun x => G.Adj c x) (S i))
        have big : 1 < (S i).card := hi.trans_le (Finset.card_le_card sub)
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i=false := by
          cases he : A i with
          | false => rfl
          | true => have := hzero i hk hN he; omega
        obtain ⟨ha,hb⟩ := hparents i hk hN
        have na := ha.trans hN
        have nb := hb.trans hN
        have uni : F c i = F c (a i) ∪ F c (b i) := by
          simp only [F,if_pos hN,if_pos na,if_pos nb,portSet,hunion i hk hN hA,Finset.filter_union]
        by_cases ab : portSet G S c (a i) ⊆ portSet G S c (b i)
        · left; refine ⟨b i,hb,?_⟩
          rw [uni]; apply Finset.union_subset
          · simpa only [F,if_pos na,if_pos nb] using ab
          · exact fun _ h => h
        by_cases ba : portSet G S c (b i) ⊆ portSet G S c (a i)
        · left; refine ⟨a i,ha,?_⟩
          rw [uni]; apply Finset.union_subset
          · exact fun _ h => h
          · simpa only [F,if_pos na,if_pos nb] using ba
        right
        refine ⟨?_,a i,ha,b i,hb,by rw [uni]⟩
        simp [B,OS,hN,hk,hA,big,owner i hk hN hA c ⟨ab,ba⟩]
      · simp [F,hN] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv huv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu huv.symm with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]


theorem sharedPhysical {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : Nat) (ops : binaryOps gs)
    (non : ∀g ∈ gs,g.op=.and → g.inputs ≠ [])
    (he : ∀x : Fin n → Bool, (Circuit.mk gs out).eval (List.ofFn x)=true ↔ edgeTrue G x)
    (small : ∀ w, n+1≤w → w<n+1+gs.length → andPos n gs w=true →
      (supports (n:=n) gs (firstWire n gs w)).card≤1 ∨ (supports (n:=n) gs (secondWire n gs w)).card≤1)
    (unique : ∀ w, n+1≤w → w<n+1+gs.length → andPos n gs w=false → ∀ c d,
      crosses G (supports gs) (firstWire n gs) (secondWire n gs) w c →
      crosses G (supports gs) (firstWire n gs) (secondWire n gs) w d → c=d) :
    ∃ T : Finset (Fin n), (∀u v,G.Adj u v → u∈T ∨ v∈T) ∧ G.edgeFinset.card+T.card≤gs.length+1 := by
  classical
  let S := supports (n:=n) gs
  let a := firstWire n gs
  let b := secondWire n gs
  let A := andPos n gs
  let H := fun (w : Nat) (u v : Fin n) => posRead gs w (pairBits u v) = true
  let r := clampWire (n+gs.length) out
  have ha (w) (lo : n+1≤w) (_hi : w<n+1+gs.length) : a w<w := clamp_lt w _ (by omega)
  have hb (w) (lo : n+1≤w) (_hi : w<n+1+gs.length) : b w<w := clamp_lt w _ (by omega)
  have hU (w) (lo : n+1≤w) (hi : w<n+1+gs.length) (ho : A w=false) : S w = S (a w) ∪ S (b w) := by
    ext i
    simp only [S,a,b,Finset.mem_union,mem_support,pos_gate_nnil G gs ops non w lo hi,show andPos n gs w=false from ho,Bool.false_eq_true,ite_false,Bool.or_eq_true]
  have hM (w) (lo : n+1≤w) (hi : w<n+1+gs.length) (ho : A w=true) : S w = S (a w) ∩ S (b w) := by
    ext i
    simp only [S,a,b,Finset.mem_inter,mem_support,pos_gate_nnil G gs ops non w lo hi,show andPos n gs w=true from ho,ite_true,Bool.and_eq_true]
  have hor (w) (u v : Fin n) (lo : n+1≤w) (hi : w<n+1+gs.length) (ho : A w=false) (hh : H w u v) : H (a w) u v ∨ H (b w) u v := by
    simpa only [H,a,b,pos_gate_nnil G gs ops non w lo hi,show andPos n gs w=false from ho,Bool.false_eq_true,ite_false,Bool.or_eq_true] using hh
  have hand (w) (u v : Fin n) (lo : n+1≤w) (hi : w<n+1+gs.length) (ho : A w=true) (hh : H w u v) : H (a w) u v ∧ H (b w) u v := by
    simpa only [H,a,b,pos_gate_nnil G gs ops non w lo hi,show andPos n gs w=true from ho,ite_true,Bool.and_eq_true] using hh
  have hs (w) (lo : n+1≤w) (hi : w<n+1+gs.length) (ho : A w=true) : (S w).card≤1 := by
    rw [hM w lo hi ho]
    rcases small w lo hi ho with h|h
    · exact (Finset.card_le_card Finset.inter_subset_left).trans h
    · exact (Finset.card_le_card Finset.inter_subset_right).trans h
  have hr := root_bound n gs.length out
  have zero := root_support_empty G gs out he
  have all := root_hits G gs out he
  have births (u v : Fin n) (huv : G.Adj u v) := star_birth n (n+1) (n+1+gs.length) r S H a b A u v hr (all u v huv)
    (by change u∉supports gs (clampWire (n+gs.length) out); simp [zero]) (by change v∉supports gs (clampWire (n+gs.length) out); simp [zero]) (hit_base gs) ha hb hU hor hand hM
  have edges := trimmed_edges n (n+1) (n+1+gs.length) G S a b A (support_base gs)
    (fun w lo hi => ⟨ha w lo hi,hb w lo hi⟩) hs hU unique small births
  obtain ⟨T,hT,card⟩ := cover_half n (n+1) (n+1+gs.length) r G S H a b A hr zero all (hit_base gs) ha hb hU hor small hand (fun f R B step => dag_union_bound f R B step)
  have part := gate_partition_count n gs.length A S
  exact ⟨T,hT,by omega⟩
end Dirty9739.CleanGates
namespace Dirty9739.Plane
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def masks : Array Nat := #[40969, 163878, 327756, 655512, 262448, 524897, 1218, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 199168, 398337, 796674, 544772]
def direction (a b : Fin 40) : Bool := decide (20 ≤ b.val) && (masks[b.val-20]!).testBit a.val
def literal : List (Nat × Nat) := [(0, 20), (0, 25), (0, 27), (0, 37), (1, 21), (1, 26), (1, 28), (1, 38), (2, 21), (2, 22), (2, 27), (2, 29), (2, 39), (3, 20), (3, 22), (3, 23), (3, 28), (3, 30), (4, 23), (4, 24), (4, 29), (4, 31), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 22), (6, 25), (6, 26), (6, 31), (6, 33), (7, 23), (7, 26), (7, 27), (7, 32), (7, 34), (8, 24), (8, 27), (8, 28), (8, 33), (8, 35), (9, 25), (9, 28), (9, 29), (9, 34), (9, 36), (10, 26), (10, 29), (10, 30), (10, 35), (10, 37), (11, 27), (11, 30), (11, 31), (11, 36), (11, 38), (12, 28), (12, 31), (12, 32), (12, 37), (12, 39), (13, 20), (13, 29), (13, 32), (13, 33), (13, 38), (14, 30), (14, 33), (14, 34), (14, 39), (15, 20), (15, 21), (15, 31), (15, 34), (15, 35), (16, 22), (16, 32), (16, 35), (16, 36), (17, 21), (17, 23), (17, 33), (17, 36), (17, 37), (18, 22), (18, 24), (18, 34), (18, 37), (18, 38), (19, 23), (19, 25), (19, 35), (19, 38), (19, 39)]
theorem posted : ∀ a b : Fin 40, direction a b = true ↔ (a.val,b.val)∈literal := by decide +kernel

def G : SimpleGraph (Fin 40) where
  Adj i j := direction i j = true ∨ direction j i = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (direction i j = true ∨ direction j i = true))
abbrev P (i : Fin 20) : Fin 40 := Fin.castAdd 20 i
abbrev L : Fin 20 → Fin 40 := Fin.natAdd 20
def target (x : Fin 40 → Bool) : Prop :=
  ∃ u v : Fin 40, (u.val,v.val) ∈ literal ∧ x u=true ∧ x v=true
theorem graphTarget (x : Fin 40 → Bool) : target x ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨i,j,ij,a,b⟩
    exact ⟨i,j,Or.inl ((posted i j).mpr ij),a,b⟩
  · rintro ⟨i,j,e,hi,hj⟩
    rcases e with e|e
    · exact ⟨i,j,(posted i j).mp e,hi,hj⟩
    · exact ⟨j,i,(posted j i).mp e,hj,hi⟩
set_option maxRecDepth 20000 in
theorem edgeCount : G.edgeSet.ncard = 95 := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem noFour : PEqualNP.TopForm.NoFourCycle G := by
  unfold PEqualNP.TopForm.NoFourCycle
  decide +kernel

theorem coverLower (S : Finset (Fin 40)) (covers : CoverPromise.IsVertexCover G S) : 20 ≤ S.card := by
  classical
  let pick := fun i : Fin 20 => if P i ∈ S then P i else L i
  have edges : ∀ i, G.Adj (P i) (L i) := by decide +kernel
  have pickMem (i) : pick i ∈ S := by
    unfold pick
    split_ifs with h
    · exact h
    · exact (covers _ _ (edges i)).resolve_left h
  have disjoint : ∀ i j : Fin 20, P i ≠ L j := by decide +kernel
  have inj : Function.Injective pick := by
    intro i j eq
    dsimp only [pick] at eq
    split_ifs at eq with hi hj hj
    · exact (show ∀ i j : Fin 20, P i = P j → i=j by decide +kernel) i j eq
    · exact False.elim (disjoint _ _ eq)
    · exact False.elim (disjoint _ _ eq.symm)
    · have facts : ∀ i j : Fin 20, L i = L j → i = j := by decide +kernel
      exact facts i j eq
  have bound := Finset.card_le_card (show Finset.univ.image pick ⊆ S from by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact pickMem j)
  simpa [Finset.card_image_of_injective _ inj] using bound


open Dirty9739.CleanGates
theorem threshold (C : Circuit) (legal : Monotone2 C)
    (non : ∀g∈C.gates,g.op=.and → g.inputs≠[])
    (eval : ∀ x : Fin 40 → Bool, C.eval (List.ofFn x)=true ↔ target x)
    (small : ∀ w, 41≤w → w<41+C.size → andPos 40 C.gates w=true →
      (supports (n:=40) C.gates (firstWire 40 C.gates w)).card≤1 ∨
      (supports (n:=40) C.gates (secondWire 40 C.gates w)).card≤1)
    (unique : ∀ w,41≤w → w<41+C.size → andPos 40 C.gates w=false → ∀ c d,
      crosses G (supports C.gates) (firstWire 40 C.gates) (secondWire 40 C.gates) w c →
      crosses G (supports C.gates) (firstWire 40 C.gates) (secondWire 40 C.gates) w d → c=d) :
    114≤C.size := by
  obtain ⟨T,ct,sz⟩ := sharedPhysical G C.gates C.output (fun g h => ⟨by simpa using (legal g h).1,(legal g h).2⟩)
    non (fun x => (eval x).trans (graphTarget x)) small unique
  have tc := coverLower T ct
  have ec : G.edgeFinset.card=95 := by rw [←Set.ncard_coe_finset,G.coe_edgeFinset]; exact edgeCount
  rw [ec] at sz
  change 114≤C.gates.length
  omega
end Dirty9739.Plane

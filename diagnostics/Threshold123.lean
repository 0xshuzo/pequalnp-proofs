import PEqualNP.Defs

-- The pair-clean circuit argument is adapted from the checked L-meta-1602 proof.
-- Deleting the flag (0,21) leaves 104 edges and a 21-edge matching.
-- We transport independent witnesses under the stabilizer of this deleted flag.
namespace PEqualNP.Outside.L_meta_9769_partial

namespace Clean

-- The general pair-clean bound and its helpers adapt the checked proof of L-meta-1602.

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

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
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
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
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
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
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
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
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
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
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

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)


theorem cleanBound : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro m H _ h4 D hM hfun hclean
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have he : H.edgeFinset = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun e _ => Sym2.inductionOn e (fun a _ => a.elim0))
    simp [he]
  · have hmono : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hM g hg).1
      simpa using this
    refine PEqualNP.Outside.L_meta_9769_partial.Clean.pairCleanBound m H h4 D.gates D.output
      (fun g hg => ⟨hmono g hg, (hM g hg).2⟩) (fun x => ?_) (fun i x hx hop hv => ?_)
    · have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op =
          PEqualNP.CircuitLowerBounds.GateOp.and := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ i.2]
        exact hop
      have hval : ∀ e w : Fin m, ¬ H.Adj e w →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + (i : ℕ)) false = true →
          False := by
        intro e w hew h
        have h2 := hclean i i.2 hop' e w hew
        have h3 : PEqualNP.EdgeOwnership.gateVal m D i (PEqualNP.EdgeOwnership.pairInput e w)
            = true := h
        rw [h2] at h3
        exact Bool.false_ne_true h3
      rcases hx with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · exfalso
        refine hval ⟨0, hm⟩ ⟨0, hm⟩ (H.irrefl) ?_
        refine PEqualNP.Outside.L_meta_9769_partial.Clean.wiresFrom_mono D.gates hmono _ _ (by simp) ?_ _ hv
        intro j h
        by_cases hj : j < m
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h
          exact absurd h Bool.false_ne_true
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          exact absurd h Bool.false_ne_true
      · exfalso
        refine hval u u (H.irrefl) ?_
        have hxe : (fun z : Fin m => decide (z = u)) = PEqualNP.EdgeOwnership.pairInput u u := by
          funext z
          simp [PEqualNP.EdgeOwnership.pairInput]
        rw [← hxe]
        exact hv
      · by_cases hadj : H.Adj u v
        · exact ⟨u, v, hadj, by simp, by simp⟩
        · exact (hval u v hadj hv).elim

end Clean

namespace Dirty

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership

abbrev inc (a b : Fin 42) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val+21-a.val) % 21 ∈ [0,5,7,17,20] ∧ (a.val,b.val) ≠ (0,21)


def yes (x : Fin 42 → Bool) : Prop := ∃ a b, inc a b ∧ x a = true ∧ x b = true

abbrev plane : SimpleGraph (Fin 42) where
  Adj a b := inc a b ∨ inc b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun a ha => by rcases ha with ha|ha <;> have := ha.1 <;> have := ha.2.1 <;> omega⟩


theorem graphEval (x : Fin 42 → Bool) :
    (∃ a b, plane.Adj a b ∧ x a = true ∧ x b = true) ↔ yes x := by
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    rcases ab with ab|ba
    · exact ⟨a,b,ab,ha,hb⟩
    · exact ⟨b,a,ba,hb,ha⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    exact ⟨a,b,Or.inl ab,ha,hb⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 15000000 in
theorem overlap (a c : Fin 42) (ac : a ≠ c) :
    (Finset.univ.filter (fun b => plane.Adj a b ∧ plane.Adj c b)).card ≤ 1 := by
  revert a c; decide +kernel

theorem noFour (a b c d : Fin 42) (ac : a ≠ c) (bd : b ≠ d) :
    ¬ (plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
  rintro ⟨ab,bc,cd,da⟩
  exact bd (Finset.card_le_one.mp (overlap a c ac) b
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ab, bc.symm⟩) d
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, da.symm, cd⟩))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem edges : 104 ≤ plane.edgeFinset.card := by
  let off (i : Fin 5) : ℕ := ![0,5,7,17,20] i
  let e (i : Fin 104) : Sym2 (Fin 42) :=
    s(Fin.ofNat 42 ((i.val+1)/5),
      Fin.ofNat 42 (21 + (((i.val+1)/5 + off (Fin.ofNat 5 (i.val+1))) % 21)))
  have hinj : Function.Injective e := by intro a b; revert a b; decide +kernel
  have hmem (a : Fin 104) : e a ∈ plane.edgeFinset := by
    change s(Fin.ofNat 42 ((a.val+1)/5),
      Fin.ofNat 42 (21 + (((a.val+1)/5 + off (Fin.ofNat 5 (a.val+1))) % 21))) ∈ plane.edgeFinset
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    revert a; decide +kernel
  have sub : Finset.univ.image e ⊆ plane.edgeFinset := by
    intro a ha; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha; exact hmem i
  have card := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin] using card

theorem cover (T : Finset (Fin 42)) (h : ∀ u v : Fin 42, plane.Adj u v → u ∈ T ∨ v ∈ T) :
    21 ≤ T.card := by
  let line (p : Fin 21) := Fin.natAdd 21 (p+5)
  let pick (p : Fin 21) := if Fin.castAdd 21 p ∈ T then Fin.castAdd 21 p else line p
  have matching (p : Fin 21) : plane.Adj (Fin.castAdd 21 p) (line p) := by
    revert p; decide +kernel
  have mem (p) : pick p ∈ T := by
    have pair := h _ _ (matching p)
    dsimp only [pick]; split <;> aesop
  let label (v : Fin 42) := Fin.ofNat 21 (if v.val < 21 then v.val else v.val+16)
  have labels : ∀ p : Fin 21, label (Fin.castAdd 21 p) = p ∧ label (line p) = p := by decide +kernel
  have index (p) : label (pick p) = p := by
    dsimp only [pick]; split
    · exact (labels p).1
    · exact (labels p).2
  have inj : Function.Injective pick := by
    intro p q h; rw [← index p, ← index q, h]
  have sub : Finset.univ.image pick ⊆ T := by
    intro a ha; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha; exact mem i
  have card := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] using card

theorem independent (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 123)
    (good : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ yes x) :
    ∃ a b : Fin 42, ¬ (inc a b ∨ inc b a) ∧ ∃ (k : ℕ) (g : Gate),
      C.gates[k]? = some g ∧ g.op = .and ∧
      (C.wires (List.ofFn (pairInput a b))).getD (42+k) false = true := by
  classical
  by_contra! none
  have exactGraph : circuitFun 42 C = graphFun plane ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [circuitFun,graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
      Bool.false_or,decide_eq_true_eq]
    exact (good x).trans (graphEval x).symm
  have allClean (k : ℕ) (hk : k < C.gates.length) (ha : (gateAt C k).op = .and)
      (a b : Fin 42) (nonedge : ¬plane.Adj a b) : gateVal 42 C k (pairInput a b) = false := by
    apply Bool.eq_false_iff.mpr
    have hg : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
    have ho : C.gates[k].op = .and := by
      change (C.gates.getD k _).op = .and at ha
      rwa [List.getD_eq_getElem _ _ hk] at ha
    exact none a b ⟨fun h => nonedge (Or.inl h),fun h => nonedge (Or.inr h)⟩ k C.gates[k] hg ho
  obtain ⟨T,hcover,bound⟩ := PEqualNP.Outside.L_meta_9769_partial.Clean.cleanBound 42 plane noFour C mono exactGraph allClean
  have ht := cover T hcover
  have he := edges
  omega

end Dirty

namespace Transport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

abbrev V := Fin 42
abbrev inc (a b : V) : Prop := Dirty.inc a b
def adj (a b : V) : Bool := decide (inc a b ∨ inc b a)
def row (k : Fin 3) (i : V) : Bool :=
  decide (i.val ∈ (![[0, 21],[4, 38, 41],[0, 1, 5, 35, 36, 37]] : Fin 3 → List ℕ) k)
theorem rowIndependent : ∀ (k : Fin 3) (a b : V), adj a b = true →
    ¬ (row k a = true ∧ row k b = true) := by decide +kernel

def genData : Array (Array ℕ) := #[#[0,1,11,10,16,13,3,8,7,20,9,2,6,17,4,18,14,19,5,15,12,21,39,31,36,33,41,29,28,27,37,30,23,34,24,25,35,40,26,22,32,38],#[0,1,15,19,4,2,8,3,13,11,12,20,18,6,14,5,16,17,10,7,9,21,22,36,24,30,28,29,41,39,32,40,25,23,34,31,33,37,38,27,35,26],#[0,16,5,10,4,7,11,9,19,8,20,6,15,18,1,12,14,13,3,2,17,21,33,31,30,24,28,37,26,36,25,27,32,35,39,29,40,34,41,23,22,38],#[0,14,8,19,4,13,15,7,2,20,18,11,12,5,1,6,16,17,10,3,9,21,34,36,24,30,41,35,28,40,25,39,32,33,22,27,23,37,38,31,29,26],#[21,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,0,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]]
def gen (g : Fin 5) (i : V) : V := Fin.ofNat 42 ((genData[g.val]!).getD i.val 0)
def chain : List (Fin 5) → V → V
  | [], a => a
  | g::gs, a => chain gs (gen g a)

set_option maxHeartbeats 8000000 in
theorem genSurj : ∀ g : Fin 5, ∀ t : V, ∃ j : V, gen g j=t := by decide +kernel
set_option maxHeartbeats 8000000 in
theorem genAdj : ∀ (g : Fin 5) (a b : V), adj (gen g a) (gen g b)=adj a b := by decide +kernel
theorem chainSurj (gs : List (Fin 5)) : Function.Surjective (chain gs) := by
  induction gs with
  | nil => exact fun a => ⟨a,rfl⟩
  | cons g gs ih => exact ih.comp (genSurj g)

theorem chainAdj (gs : List (Fin 5)) (a b : V) : adj (chain gs a) (chain gs b)=adj a b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih => exact (ih (gen g a) (gen g b)).trans (genAdj g a b)


def wordData : Array (List (Fin 5) × Fin 3) := #[([],0),([],1),([],2),([0],1),([0],2),([0, 0],1),([0, 0],2),([0, 0, 0],2),([0, 0, 0, 0],2),([0, 0, 1],2),([0, 0, 1, 0],2),([0, 0, 2],2),([0, 0, 2, 1],2),([0, 0, 3],2),([0, 0, 3, 0],2),([0, 0, 3, 1],2),([0, 0, 4],2),([0, 0, 4, 0],2),([0, 0, 4, 1],2),([0, 1],2),([0, 1, 0],1),([0, 1, 0],2),([0, 1, 0, 0],2),([0, 1, 0, 2],2),([0, 1, 1],2),([0, 1, 1, 0],2),([0, 1, 2],2),([0, 1, 2, 0],2),([0, 1, 3],2),([0, 1, 4],2),([0, 1, 4, 1],2),([0, 1, 4, 2],2),([0, 2],2),([0, 2, 0],2),([0, 2, 1],2),([0, 2, 2],2),([0, 2, 2, 1],2),([0, 2, 3],2),([0, 2, 4],2),([0, 2, 4, 0],2),([0, 2, 4, 3],2),([0, 3],2),([0, 3, 0],2),([0, 3, 0, 1],2),([0, 3, 1],2),([0, 3, 1, 2],2),([0, 3, 2],2),([0, 3, 2, 0],2),([0, 3, 2, 1],2),([0, 3, 4],2),([0, 3, 4, 0],2),([0, 4],1),([0, 4],2),([0, 4, 0],2),([0, 4, 0, 1],2),([0, 4, 0, 2],2),([0, 4, 0, 3, 0],2),([0, 4, 1],2),([0, 4, 1, 2],2),([0, 4, 2],2),([0, 4, 3],2),([0, 4, 3, 2],2),([1],1),([1],2),([1, 0],1),([1, 0],2),([1, 0, 0],1),([1, 0, 0],2),([1, 0, 0, 0],2),([1, 0, 0, 2],2),([1, 0, 0, 3],2),([1, 0, 1],2),([1, 0, 2],2),([1, 0, 2, 0],2),([1, 0, 2, 1],2),([1, 0, 3],2),([1, 0, 3, 1],2),([1, 0, 4],2),([1, 0, 4, 0],2),([1, 0, 4, 1],2),([1, 1],2),([1, 1, 0],2),([1, 1, 0, 0],2),([1, 1, 0, 2],2),([1, 1, 2],2),([1, 1, 4],2),([1, 2],2),([1, 2, 0],2),([1, 2, 1],2),([1, 2, 1, 1],2),([1, 2, 2],2),([1, 2, 3],2),([1, 2, 4],2),([1, 2, 4, 0],2),([1, 2, 4, 1],2),([1, 3],2),([1, 3, 0],2),([1, 3, 0, 1],2),([1, 3, 0, 2],2),([1, 3, 2],2),([1, 3, 2, 0],2),([1, 3, 4, 1],2),([1, 4],2),([1, 4, 0],2),([1, 4, 0, 0],2),([1, 4, 0, 1],2),([1, 4, 0, 2],2),([1, 4, 1],2),([1, 4, 1, 0],2),([1, 4, 1, 1],2),([1, 4, 2],2),([1, 4, 2, 2],2),([1, 4, 3],2),([2],2),([2, 0],1),([2, 0],2),([2, 0, 0],2),([2, 0, 0, 0],2),([2, 0, 0, 1],2),([2, 0, 0, 2],2),([2, 0, 2],2),([2, 0, 3],2),([2, 0, 4],2),([2, 0, 4, 1],2),([2, 1],2),([2, 1, 0],2),([2, 1, 0, 0],2),([2, 1, 0, 2],2),([2, 1, 1],2),([2, 1, 2],2),([2, 1, 2, 0],2),([2, 1, 3],2),([2, 1, 4],2),([2, 1, 4, 2],2),([2, 2],2),([2, 2, 0],2),([2, 2, 1],2),([2, 2, 2],2),([2, 2, 2, 0],2),([2, 2, 3],2),([2, 2, 3, 0],2),([2, 2, 3, 1],2),([2, 2, 4],2),([2, 2, 4, 0],2),([2, 3],2),([2, 3, 0],2),([2, 3, 1],2),([2, 3, 2],2),([2, 3, 2, 0],2),([2, 3, 4],2),([2, 4],2),([2, 4, 0],2),([2, 4, 0, 1],2),([2, 4, 0, 4],2),([2, 4, 1],2),([2, 4, 1, 0],2),([2, 4, 1, 1],2),([2, 4, 1, 3],2),([2, 4, 2],2),([2, 4, 2, 0],2),([2, 4, 3],2),([2, 4, 3, 0],2),([2, 4, 3, 2],2),([3],1),([3],2),([3, 0],1),([3, 0],2),([3, 0, 0],2),([3, 0, 0, 1],2),([3, 0, 0, 2],2),([3, 0, 0, 4],2),([3, 0, 1],2),([3, 0, 1, 0],2),([3, 0, 1, 1],2),([3, 0, 2],2),([3, 0, 3],2),([3, 0, 4],2),([3, 0, 4, 0],2),([3, 1],2),([3, 1, 2],2),([3, 2],2),([3, 2, 0],2),([3, 2, 1],2),([3, 2, 1, 1],2),([3, 2, 2],2),([3, 2, 4],2),([3, 4],2),([3, 4, 0],1),([3, 4, 0],2),([3, 4, 0, 0],2),([3, 4, 0, 3],2),([3, 4, 1],2),([3, 4, 1, 0],2),([3, 4, 2],2),([3, 4, 3],2),([4],1),([4],2),([4, 0],1),([4, 0],2),([4, 0, 0],2),([4, 0, 0, 0],2),([4, 0, 0, 2],2),([4, 0, 1],2),([4, 0, 1, 0],2),([4, 0, 2],2),([4, 0, 2, 1],2),([4, 0, 2, 3],2),([4, 0, 3],2),([4, 0, 3, 0],2),([4, 0, 4],2),([4, 0, 4, 0],2),([4, 1],1),([4, 1],2),([4, 1, 0],2),([4, 1, 0, 0],2),([4, 1, 0, 1],2),([4, 1, 0, 2],2),([4, 1, 1],2),([4, 1, 1, 0],2),([4, 1, 2],2),([4, 1, 2, 2],2),([4, 1, 2, 3],2),([4, 1, 2, 4],2),([4, 1, 3],2),([4, 1, 3, 2],2),([4, 1, 4, 2],2),([4, 2],2),([4, 2, 0],2),([4, 2, 0, 2],2),([4, 2, 0, 3],2),([4, 2, 1],2),([4, 2, 1, 0],2),([4, 2, 1, 1],2),([4, 2, 1, 2],2),([4, 2, 2],2),([4, 2, 3],2),([4, 2, 4],2),([4, 2, 4, 1],2),([4, 3],1),([4, 3],2),([4, 3, 0],2),([4, 3, 0, 0],2),([4, 3, 0, 1, 0],2),([4, 3, 1],2),([4, 3, 1, 2],2),([4, 3, 2],2),([4, 3, 2, 1],2),([4, 3, 2, 2],2),([4, 3, 2, 4],2)]
def planData : Array ℕ := #[2,2,113,42,11,2,178,46,180,72,166,32,65,164,113,63,32,144,4,19,21,0,134,63,4,32,0,164,0,113,4,80,19,113,6,2,2,2,0,95,63,0,2,2,80,71,195,2,120,46,180,10,81,24,65,179,51,63,197,9,4,19,21,0,0,63,4,65,165,0,197,0,4,80,19,180,6,2,2,2,195,0,63,165,113,80,113,112,11,212,142,245,154,245,176,150,176,18,113,112,129,106,38,212,110,212,0,0,67,176,112,113,0,113,0,80,121,113,67,11,148,80,150,152,0,212,42,71,112,42,222,107,230,221,191,223,192,235,108,191,171,230,42,231,54,50,241,223,90,0,0,145,85,184,223,0,71,0,42,89,184,191,183,71,94,145,90,0,11,195,11,222,1,69,14,248,169,12,23,237,70,37,211,236,238,35,13,36,15,0,37,37,0,0,163,13,62,11,0,236,0,119,12,11,35,236,1,35,13,1,2,2,212,107,69,2,196,196,49,217,202,150,149,243,86,239,41,29,190,212,193,196,0,202,181,0,0,150,239,41,41,0,41,0,33,2,2,2,150,86,181,196,178,120,142,230,14,196,196,196,101,104,77,224,198,243,178,219,43,143,198,142,193,196,167,0,198,77,0,0,230,178,230,120,0,141,0,120,178,196,156,167,194,196,46,46,245,221,248,196,196,196,214,245,229,234,158,186,97,186,28,158,157,244,234,196,28,234,0,46,186,0,0,27,28,16,127,0,245,0,158,196,16,170,201,196,180,180,154,191,169,49,101,214,180,200,203,199,52,191,95,247,210,132,52,154,110,52,117,137,87,0,52,87,0,0,52,154,87,180,0,180,0,95,49,95,180,199,72,10,245,223,12,217,104,245,200,226,133,217,104,226,147,226,72,79,218,200,109,226,147,31,122,98,0,72,226,0,0,130,72,147,245,0,147,0,92,72,226,245,166,81,176,192,23,202,77,229,203,133,166,61,103,207,166,188,76,192,218,59,242,59,203,166,166,166,188,0,59,88,0,0,81,81,78,189,0,59,0,88,23,202,32,24,150,235,237,150,224,234,199,217,61,32,228,151,173,151,32,57,199,246,234,150,225,24,74,32,57,32,0,32,174,0,0,111,22,146,173,0,150,0,217,217,65,65,176,108,70,149,198,158,52,104,103,228,65,103,124,53,44,158,198,58,53,52,177,65,65,65,52,124,103,0,52,182,0,0,53,160,124,116,0,124,0,198,164,179,18,191,37,243,243,186,191,226,207,151,103,164,164,226,175,227,227,102,155,226,37,164,115,115,186,164,226,115,0,204,175,0,0,185,243,164,185,0,226,0,113,51,113,171,211,86,178,97,95,147,166,173,124,164,3,125,187,168,96,128,118,0,147,164,166,115,3,164,64,113,125,0,87,113,0,0,124,164,211,95,0,3,63,63,112,230,236,239,219,186,247,226,188,151,53,226,125,63,136,204,105,239,53,239,0,63,6,125,186,75,239,239,75,6,0,105,6,0,0,63,92,125,63,0,32,197,129,42,238,41,43,28,210,72,76,32,44,175,187,136,5,144,26,134,34,0,134,0,34,32,5,32,114,41,41,144,41,0,184,134,0,0,114,144,175,66,144,9,106,231,35,29,143,158,132,79,192,57,158,227,168,204,144,144,213,60,159,204,0,35,0,135,204,144,29,227,9,144,240,8,0,135,35,0,0,144,9,213,4,4,38,54,13,190,198,157,52,218,218,199,198,227,96,105,26,213,4,213,241,198,26,0,4,0,52,199,240,38,4,13,240,96,140,0,4,47,0,0,13,198,19,19,212,50,36,212,142,244,154,200,59,246,58,102,128,239,134,60,213,19,17,102,134,128,0,126,0,212,102,239,19,134,19,7,7,134,0,19,154,0,0,212,21,21,110,241,15,193,193,234,110,109,242,234,53,155,118,53,34,159,241,17,21,234,34,234,34,0,234,0,193,193,83,110,21,138,21,21,40,0,16,220,0,0,0,0,212,223,0,196,196,196,52,226,59,150,52,226,0,239,0,204,198,102,234,0,203,202,198,151,52,212,226,239,52,154,240,17,53,191,243,196,150,107,226,196,134,0,0,90,37,0,167,28,117,147,203,225,177,37,147,0,134,0,26,134,34,203,134,128,167,28,205,128,30,34,28,134,172,147,131,134,147,117,56,167,90,203,63,63,0,0,37,202,0,234,137,31,166,24,65,164,164,63,0,35,0,128,234,202,128,63,65,65,234,164,232,88,24,182,48,7,139,179,35,63,55,84,63,202,4,4,67,0,0,181,198,0,87,122,166,74,65,115,166,6,34,0,4,0,34,198,167,65,4,65,188,44,103,115,4,6,81,81,6,67,4,153,155,167,181,198,32,65,176,145,0,0,77,46,0,98,166,32,65,115,115,125,32,135,0,126,0,151,28,65,65,32,235,32,108,115,125,100,171,8,25,135,46,116,151,125,175,77,0,165,112,85,163,0,0,186,52,0,188,57,52,186,3,186,5,204,52,0,234,52,205,234,188,235,3,112,20,57,52,204,161,216,53,191,158,186,163,208,233,3,164,0,113,184,13,150,0,0,87,72,0,32,124,164,164,75,32,144,199,212,0,212,128,164,44,32,112,164,60,113,75,144,87,113,184,33,86,164,150,124,13,212,0,197,0,223,62,239,230,0,0,226,59,0,103,226,64,239,114,29,240,102,193,226,30,232,103,108,20,60,62,239,230,109,240,105,223,123,243,102,62,107,226,64,113,0,113,0,11,41,178,27,0,0,88,32,0,115,113,239,41,227,38,239,193,239,34,88,115,115,57,113,239,113,41,129,41,113,136,146,178,178,206,88,27,38,4,4,0,71,0,41,230,28,52,0,0,174,52,0,125,75,41,9,4,19,83,52,28,24,4,125,52,75,230,41,4,120,19,138,209,135,4,19,49,125,181,213,80,80,80,0,236,0,120,16,154,130,0,0,182,204,0,6,144,144,13,134,110,154,134,182,6,100,204,144,109,129,120,80,130,80,6,134,99,80,154,144,9,142,19,19,121,42,0,41,0,127,87,72,81,0,0,175,87,0,41,240,240,19,21,240,172,48,81,171,161,87,240,41,19,130,19,81,21,121,45,19,93,72,175,218,113,180,113,89,119,0,141,0,180,147,81,111,0,0,113,105,0,8,96,7,138,17,147,7,81,8,216,113,105,113,138,80,81,113,7,180,147,80,17,95,180,111,6,6,67,184,12,33,0,245,0,245,78,22,53,0,0,6,184,0,140,7,21,53,131,139,6,25,53,184,223,136,209,6,21,7,6,67,68,47,50,184,82,245,2,2,11,191,11,2,120,0,180,0,189,146,160,185,0,0,134,135,0,134,21,191,134,179,67,135,191,33,123,146,135,134,121,180,67,2,2,2,185,91,180,39,2,2,148,183,35,2,178,158,0,147,0,173,124,243,124,0,0,35,4,0,40,243,147,35,4,46,158,86,243,178,4,99,45,147,68,2,2,2,156,124,99,228,2,2,80,71,236,2,196,196,95,0,59,0,116,164,164,63,0,0,47,19,0,196,117,63,153,116,186,164,102,178,19,80,19,80,47,2,2,2,162,95,63,196,0,195,150,94,1,150,156,16,49,92,0,150,0,185,211,92,114,0,0,154,16,150,56,55,155,151,163,150,62,206,49,154,93,17,50,185,156,162,1,92,201,1,95,0,152,145,35,86,167,170,95,72,88,0,124,0,95,125,144,144,0,0,220,107,167,84,167,125,208,124,107,88,125,144,72,95,184,91,124,95,92,95,73,215,63,63,0,90,13,181,194,201,180,226,23,217,0,226,0,63,175,9,13,0,0,226,90,63,181,175,233,13,226,27,181,9,175,180,82,180,99,63,201,73,63,217,0,165,212,0,1,196,196,196,199,245,202,217,198,0,3,0,66,213,198,212,0,196,203,202,198,77,3,212,64,38,213,142,218,111,245,39,228,196,1,215,217,1]
def plan (a b : V) := wordData[(planData[a.val*42+b.val]!)]!
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem planOK : ∀ a b : V, adj a b=false →
    row (plan a b).2 (chain (plan a b).1 a)=true ∧
    row (plan a b).2 (chain (plan a b).1 b)=true := by decide +kernel

theorem transportPair (a b : V) (missing : adj a b=false) :
    ∃ (k : Fin 3) (e : V → V), Function.Surjective e ∧ (∀ u v, adj (e u) (e v)=adj u v) ∧
      row k (e a)=true ∧ row k (e b)=true := by
  exact ⟨(plan a b).2,chain (plan a b).1,chainSurj _,chainAdj _,planOK a b missing⟩

def yes (x : V → Bool) : Prop := ∃ a b : V, inc a b ∧ x a=true ∧ x b=true
theorem yes_iff (x : V → Bool) : yes x ↔ ∃ a b : V, adj a b=true ∧ x a=true ∧ x b=true := by
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,decide_eq_true (Or.inl h : inc a b ∨ inc b a),ha,hb⟩
  · rintro ⟨a,b,h,ha,hb⟩
    obtain h|h : inc a b ∨ inc b a := of_decide_eq_true h
    · exact ⟨a,b,h,ha,hb⟩
    · exact ⟨b,a,h,hb,ha⟩
theorem yes_move (e : V → V) (onto : Function.Surjective e) (pres : ∀ u v, adj (e u) (e v)=adj u v)
    (x : V → Bool) : yes (x ∘ e) ↔ yes x := by
  rw [yes_iff,yes_iff]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨e a,e b,(pres a b).trans h,ha,hb⟩
  · rintro ⟨p,l,h,hp,hl⟩
    obtain ⟨a,rfl⟩ := onto p
    obtain ⟨b,rfl⟩ := onto l
    exact ⟨a,b,(pres a b).symm.trans h,hp,hl⟩

def idx (e : V → V) (i : ℕ) : ℕ := if hi : i<42 then (e ⟨i,hi⟩).val else i
def changeGate (e : V → V) (g : Gate) : Gate := ⟨g.op,g.inputs.map (idx e)⟩
def changeC (e : V → V) (C : Circuit) : Circuit := ⟨C.gates.map (changeGate e),idx e C.output⟩
def trace (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

theorem read_change (e : V → V) (x : V → Bool) (extra : List Bool) (i : ℕ) :
    (List.ofFn x ++ extra).getD (idx e i) false = (List.ofFn (x ∘ e) ++ extra).getD i false := by
  by_cases hi : i<42
  · rw [List.getD_append _ _ _ _ (by simp [idx,hi]),
        List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simp [idx,hi]),
        List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn,idx,dite_eq_left hi,Function.comp_apply]
  · simp only [idx,dite_eq_right hi]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem trace_change (e : V → V) (x : V → Bool) (gs : List Gate) :
    ∀ extra : List Bool, ∃ rest : List Bool,
      trace (gs.map (changeGate e)) (List.ofFn x ++ extra)=List.ofFn x ++ rest ∧
      trace gs (List.ofFn (x ∘ e) ++ extra)=List.ofFn (x ∘ e) ++ rest := by
  induction gs with
  | nil => exact fun extra => ⟨extra,rfl,rfl⟩
  | cons g gs ih =>
    intro extra
    let old := List.ofFn (x ∘ e) ++ extra
    let y := g.op.eval (g.inputs.map fun i => old.getD i false)
    have he : (changeGate e g).op.eval ((changeGate e g).inputs.map fun i =>
        (List.ofFn x ++ extra).getD i false)=y := by
      simp only [changeGate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _; exact read_change e x extra i
    obtain ⟨rest,hnew,hold⟩ := ih (extra ++ [y])
    refine ⟨rest,?_,?_⟩
    · change trace (gs.map (changeGate e)) ((List.ofFn x ++ extra) ++ [_]) = _
      rw [he,List.append_assoc]; exact hnew
    · change trace gs ((List.ofFn (x ∘ e) ++ extra) ++ [y]) = _
      rw [List.append_assoc]; exact hold

theorem lookup_change (e : V → V) (C : Circuit) (x : V → Bool) (i : ℕ) :
    ((changeC e C).wires (List.ofFn x)).getD (idx e i) false =
    (C.wires (List.ofFn (x ∘ e))).getD i false := by
  obtain ⟨rest,hnew,hold⟩ := trace_change e x C.gates []
  simp only [List.append_nil] at hnew hold
  change (trace (C.gates.map (changeGate e)) (List.ofFn x)).getD _ false =
    (trace C.gates (List.ofFn (x ∘ e))).getD _ false
  rw [hnew,hold]
  exact read_change e x rest i

-- The monotone fold argument is adapted from L-meta-1082.
def m1892_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl m1892_stp x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem m1892_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl m1892_stp W1).getD i false = true → (gs.foldl m1892_stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (m1892_stp W1 g) (m1892_stp W2 g) (by simp [m1892_stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [m1892_stp, m1892_getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [m1892_ev_and g _ ha, m1892_ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [m1892_ev_or g _ ho, m1892_ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem m1892_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi

theorem evalMono1892 {N : ℕ} (gs : List Gate) (u : ℕ)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hle : ∀ p, x p = true → y p = true) :
    (Circuit.mk gs u).eval (List.ofFn x) = true →
      (Circuit.mk gs u).eval (List.ofFn y) = true := by
  rw [m1892_eval_eq, m1892_eval_eq]
  apply m1892_mono gs _ _ (by simp) hop _ u
  apply m1892_all_idx N _ _ (by simp)
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simpa only [List.getElem_ofFn] using hle ⟨i, hi⟩


theorem transport1892 (C : Circuit) (a b : V) (k : ℕ) (g : Gate)
    (model : Monotone2 C) (correct : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ yes x)
    (miss : ¬ (inc a b ∨ inc b a))
    (hk : C.gates[k]?=some g) (hop : g.op=GateOp.and)
    (hot : (C.wires (List.ofFn (pairInput a b))).getD (42+k) false=true) :
    ∃ (r : Fin 3) (D : Circuit), Monotone2 D ∧ D.size=C.size ∧
      (∀ x : V → Bool, D.eval (List.ofFn x)=true ↔ yes x) ∧
      ∃ h : Gate, D.gates[k]?=some h ∧ h.op=GateOp.and ∧
        (D.wires (List.ofFn (row r))).getD (42+k) false=true := by
  have missing : adj a b=false := by simp [adj,miss]
  obtain ⟨r,e,onto,pres,ha,hb⟩ := transportPair a b missing
  let D := changeC e C
  refine ⟨r,D,?_,by simp [D,changeC,Circuit.size],?_,changeGate e g,?_,hop,?_⟩
  · intro q hq
    obtain ⟨t,ht,rfl⟩ := List.mem_map.1 hq
    exact ⟨(model t ht).1,by simpa [changeGate] using (model t ht).2⟩
  · intro x
    have eq : D.eval (List.ofFn x)=C.eval (List.ofFn (x ∘ e)) := lookup_change e C x C.output
    rw [eq,correct,yes_move e onto pres]
  · simp [D,changeC,List.getElem?_map,hk]
  · have ops (q : Gate) (hq : q ∈ C.gates) : q.op=GateOp.and ∨ q.op=GateOp.or :=
      (model q hq).1
    have grows : (⟨C.gates,42+k⟩ : Circuit).eval (List.ofFn (row r ∘ e))=true :=
      evalMono1892 C.gates (42+k) ops (pairInput a b) (row r ∘ e)
        (fun i hi => by
          obtain hi|hi : i=a ∨ i=b := by simpa [pairInput] using hi
          · simpa [hi,Function.comp] using ha
          · simpa [hi,Function.comp] using hb) hot
    have eq := lookup_change e C (row r) (42+k)
    simp only [idx,dite_eq_right (show ¬42+k<42 by omega)] at eq
    exact eq.trans grows

end Transport

namespace Result
open CircuitLowerBounds MetaComplexity EdgeOwnership Transport
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def portEdges : List (Fin 42 × Fin 42) := [(0,26),(0,28),(0,38),(0,41),(1,21),(1,22),(1,27),(1,29),(1,39),(2,22),(2,23),(2,28),(2,30),(2,40),(3,23),(3,24),(3,29),(3,31),(3,41),(4,21),(4,24),(4,25),(4,30),(4,32),(5,22),(5,25),(5,26),(5,31),(5,33),(6,23),(6,26),(6,27),(6,32),(6,34),(7,24),(7,27),(7,28),(7,33),(7,35),(8,25),(8,28),(8,29),(8,34),(8,36),(9,26),(9,29),(9,30),(9,35),(9,37),(10,27),(10,30),(10,31),(10,36),(10,38),(11,28),(11,31),(11,32),(11,37),(11,39),(12,29),(12,32),(12,33),(12,38),(12,40),(13,30),(13,33),(13,34),(13,39),(13,41),(14,21),(14,31),(14,34),(14,35),(14,40),(15,22),(15,32),(15,35),(15,36),(15,41),(16,21),(16,23),(16,33),(16,36),(16,37),(17,22),(17,24),(17,34),(17,37),(17,38),(18,23),(18,25),(18,35),(18,38),(18,39),(19,24),(19,26),(19,36),(19,39),(19,40),(20,25),(20,27),(20,37),(20,40),(20,41)]
def posted (x : Fin 42 → Bool) : Bool := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)
theorem tabulates : ∀ a b : Fin 42, (a,b) ∈ portEdges ↔ inc a b := by decide +kernel
theorem posted_yes (x : Fin 42 → Bool) : posted x = true ↔ yes x := by
  have expansion : posted x = portEdges.any (fun e => x e.1 && x e.2) := by
    dsimp [posted,portEdges,List.any]
    simp only [Bool.or_false,Bool.or_assoc] <;> ac_rfl
  rw [expansion,List.any_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, hm, ht⟩
    have both : x a = true ∧ x b = true := by simpa using ht
    exact ⟨a,b,(tabulates a b).1 hm,both.1,both.2⟩
  · rintro ⟨a,b,hi,hx,hy⟩
    exact ⟨(a,b),(tabulates a b).2 hi,by simp [hx,hy]⟩

theorem necessary (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 123)
    (good : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = posted x) :
    (∃ g ∈ C.gates, g.op=.not) ∨
    ∃ (r : Fin 3) (D : Circuit), Monotone2 D ∧ D.size=C.size ∧
      (∀ x : Fin 42 → Bool, D.eval (List.ofFn x)=posted x) ∧
      ∃ (k : ℕ) (h : Gate), D.gates[k]?=some h ∧ h.op=.and ∧
        (D.wires (List.ofFn (row r))).getD (42+k) false=true := by
  by_cases neg : ∃ g ∈ C.gates, g.op=.not
  · exact Or.inl neg
  right
  have mono : Monotone2 C := by
    intro g hg
    refine ⟨?_,(fan g hg).2⟩
    have room := (fan g hg).1
    have noNot : g.op ≠ .not := fun h => neg ⟨g,hg,h⟩
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff,noNot] using room
  have correct (x) : C.eval (List.ofFn x)=true ↔ yes x := by rw [good]; exact posted_yes x
  obtain ⟨a,b,miss,k,g,hk,hop,hot⟩ := Dirty.independent C mono small correct
  obtain ⟨r,D,monD,sizeD,evD,h,gh,ghop,ghot⟩ :=
    transport1892 C a b k g mono correct miss hk hop hot
  refine ⟨r,D,monD,sizeD,?_,k,h,gh,ghop,ghot⟩
  intro x
  exact Bool.eq_iff_iff.mpr ((evD x).trans (posted_yes x).symm)

end Result
end PEqualNP.Outside.L_meta_9769_partial

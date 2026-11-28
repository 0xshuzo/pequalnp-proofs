import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18670.SafeBank

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

theorem core : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
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
    refine PEqualNP.Outside.L_meta_18670.SafeBank.pairCleanBound m H h4 D.gates D.output
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
        refine PEqualNP.Outside.L_meta_18670.SafeBank.wiresFrom_mono D.gates hmono _ _ (by simp) ?_ _ hv
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

end PEqualNP.Outside.L_meta_18670.SafeBank


namespace PEqualNP.Outside.L_meta_18670.SafeBank

theorem count : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ x8 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 x12 : Fin x1), ¬x2.Adj x11 x12 → PEqualNP.EdgeOwnership.gateVal x1 x4 x8 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ) := by
  intro n G _ C hNo hAO hfun hclean
  have h4 : ∀ p q r s : Fin n, p ≠ r → q ≠ s → ¬ (G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧ G.Adj s p) := by
    intro p q r s hpr hqs ⟨hpq, hqr, hrs, hsp⟩
    have hc := hNo p r hpr
    have hsub : ({q, s} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj r w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨hpq, hqr.symm⟩
      · exact ⟨hsp.symm, hrs⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hqs] at this
    omega
  exact PEqualNP.Outside.L_meta_18670.SafeBank.core n G h4 C hAO hfun hclean


end PEqualNP.Outside.L_meta_18670.SafeBank

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

def PEqualNP.Outside.L_meta_18670.Thin {n : ℕ} (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, ∀ i, x i = true → i=u ∨ i=v

theorem PEqualNP.Outside.L_meta_18670.broadSafe : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → (∀ x10 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin (x1 + x1) → Bool), PEqualNP.Outside.L_meta_18670.Thin x13 → PEqualNP.EdgeOwnership.gateVal (x1 + x1) x4 x10 x13 = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), (x15, x16) ∈ x2 ∧ x13 (Fin.castAdd x1 x15) = Bool.true ∧ x13 (Fin.natAdd x1 x16) = Bool.true) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E p C _ hrect hmatch hC heval safe
  let L (i : Fin n) : Fin (n + n) := Fin.castAdd n i
  let R (i : Fin n) : Fin (n + n) := Fin.natAdd n i

  have L_injective : Function.Injective L := by
    intro i j h
    have hv := congrArg Fin.val h
    exact Fin.ext hv

  have R_injective : Function.Injective R := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    change n + i.val = n + j.val at hval
    omega

  have LR (i j : Fin n) : L i ≠ R j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = n + j.val at hv
    omega

  have parts (w : Fin (n + n)) : (∃ i : Fin n, w = L i) ∨ (∃ j : Fin n, w = R j) :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) w

  let arc (E : Finset (Fin n × Fin n)) (u v : Fin (n + n)) : Prop :=
    ∃ i j : Fin n, (i, j) ∈ E ∧ u = L i ∧ v = R j

  let graph (E : Finset (Fin n × Fin n)) : SimpleGraph (Fin (n + n)) :=
    SimpleGraph.fromRel (arc E)

  have adj (E : Finset (Fin n × Fin n)) (u v : Fin (n + n)) :
      (graph E).Adj u v ↔ arc E u v ∨ arc E v u := by
    change (u ≠ v ∧ (arc E u v ∨ arc E v u)) ↔ _
    refine ⟨And.right, ?_⟩
    intro h
    refine ⟨?_, h⟩
    rcases h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩
    · exact LR i j
    · exact (LR i j).symm

  have adj_left (E : Finset (Fin n × Fin n)) (i : Fin n) (v : Fin (n + n)) :
      (graph E).Adj (L i) v ↔ ∃ j : Fin n, (i, j) ∈ E ∧ v = R j := by
    rw [adj]
    constructor
    · rintro (⟨a, b, hE, hi, hv⟩ | ⟨a, b, _, _, hi⟩)
      · have he := L_injective hi
        subst a
        exact ⟨b, hE, hv⟩
      · exact (LR i b hi).elim
    · rintro ⟨j, hj, rfl⟩
      exact Or.inl ⟨i, j, hj, rfl, rfl⟩

  have adj_right (E : Finset (Fin n × Fin n)) (j : Fin n) (u : Fin (n + n)) :
      (graph E).Adj (R j) u ↔ ∃ i : Fin n, (i, j) ∈ E ∧ u = L i := by
    rw [adj]
    constructor
    · rintro (⟨a, _, _, hj, _⟩ | ⟨a, b, hE, hu, hj⟩)
      · exact (LR a j hj.symm).elim
      · have he := R_injective hj
        subst b
        exact ⟨a, hE, hu⟩
    · rintro ⟨i, hi, rfl⟩
      exact Or.inr ⟨i, j, hi, rfl, rfl⟩

  have connected (E : Finset (Fin n × Fin n)) {i j : Fin n} (h : (i, j) ∈ E) :
      (graph E).Adj (L i) (R j) := (adj_left E i _).mpr ⟨j, h, rfl⟩

  let color (u : Fin (n + n)) : Bool := decide (n ≤ u.val)

  have opposite_colors {E : Finset (Fin n × Fin n)} {u v : Fin (n + n)}
      (h : (graph E).Adj u v) : color u ≠ color v := by
    have hL (i : Fin n) : color (L i) = false := by
      simp [color, L, Nat.not_le_of_lt i.isLt]
    have hR (j : Fin n) : color (R j) = true := by simp [color, R]
    rcases (adj E u v).mp h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩ <;>
      simp [hL, hR]

  have no_four_cycle (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj]
      (hrect : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) :
      PEqualNP.TopForm.NoFourCycle (graph E) := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    by_contra huv
    rcases parts a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨k, hik, rfl⟩ := (adj_left E i u).mp hu'.1
      obtain ⟨l, hil, rfl⟩ := (adj_left E i v).mp hv'.1
      obtain ⟨t, htk, rfl⟩ := (adj_right E k b).mp hu'.2.symm
      obtain ⟨s, hsl, he⟩ := (adj_right E l (L t)).mp hv'.2.symm
      have hts := L_injective he
      subst s
      exact hrect i t k l (fun eq => hab (congrArg L eq))
        (fun eq => huv (congrArg R eq)) ⟨hik, hil, htk, hsl⟩
    · obtain ⟨k, hkj, rfl⟩ := (adj_right E j u).mp hu'.1
      obtain ⟨l, hlj, rfl⟩ := (adj_right E j v).mp hv'.1
      obtain ⟨t, hkt, rfl⟩ := (adj_left E k b).mp hu'.2.symm
      obtain ⟨s, hls, he⟩ := (adj_left E l (R t)).mp hv'.2.symm
      have hts := R_injective he
      subst s
      exact hrect k l j t (fun eq => huv (congrArg L eq))
        (fun eq => hab (congrArg R eq)) ⟨hkj, hkt, hlj, hls⟩

  have incidence_fun (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj]
      (x : Fin (n + n) → Bool) : graphFun (graph E) ∅ x =
        decide (∃ i j : Fin n, (i, j) ∈ E ∧ x (L i) = true ∧ x (R j) = true) := by
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    congr 1
    apply propext
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (adj E u v).mp huv with ⟨i, j, hE, rfl, rfl⟩ | ⟨i, j, hE, rfl, rfl⟩
      · exact ⟨i, j, hE, hu, hv⟩
      · exact ⟨i, j, hE, hv, hu⟩
    · rintro ⟨i, j, hE, hi, hj⟩
      exact ⟨L i, R j, connected E hE, hi, hj⟩

  have card_edges (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj] :
      (graph E).edgeFinset.card = E.card := by
    let f : Fin n × Fin n → Sym2 (Fin (n + n)) := fun e => s(L e.1, R e.2)
    have hf : Function.Injective f := by
      intro u v h
      rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, _⟩
      · exact Prod.ext (L_injective hl) (R_injective hr)
      · exact (LR _ _ hl).elim
    have hEq : (graph E).edgeFinset = E.image f := by
      ext e
      refine Sym2.inductionOn e ?_
      intro a b
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, adj]
      constructor
      · rintro (⟨i, j, hE, rfl, rfl⟩ | ⟨i, j, hE, rfl, rfl⟩)
        · exact ⟨(i, j), hE, rfl⟩
        · exact ⟨(i, j), hE, Sym2.eq_swap⟩
      · rintro ⟨⟨i,j⟩, hE, he⟩
        rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨i, j, hE, ha.symm, hb.symm⟩
        · exact Or.inr ⟨i, j, hE, ha.symm, hb.symm⟩
    rw [hEq, Finset.card_image_of_injective _ hf]

  have matching_cover (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
      (hm : ∀ i, (i, p i) ∈ E) (T : Finset (Fin (n + n)))
      (hT : ∀ u v, (graph E).Adj u v → u ∈ T ∨ v ∈ T) : n ≤ T.card := by
    let f (i : Fin n) := if L i ∈ T then L i else R (p i)
    have hf : Function.Injective f := by
      intro u v h
      by_cases hu : L u ∈ T <;> by_cases hv : L v ∈ T
      · exact L_injective (by simpa [f, hu, hv] using h)
      · exact (LR u (p v) (by simpa [f, hu, hv] using h)).elim
      · exact ((LR v (p u)).symm (by simpa [f, hu, hv] using h)).elim
      · exact p.injective (R_injective (by simpa [f, hu, hv] using h))
    have hin : Finset.univ.image f ⊆ T := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : L i ∈ T
      · simp [f, h]
      · have hr : R (p i) ∈ T := (hT _ _ (connected E (hm i))).resolve_left h
        simpa [f, h] using hr
    have h := Finset.card_le_card hin
    rwa [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at h
  let G := graph E
  have h4 : NoFourCycle G := no_four_cycle E hrect
  have hGraph : circuitFun (n+n) C = graphFun G ∅ := by
    funext x
    rw [heval x, incidence_fun E x]
  have hCard : G.edgeFinset.card = E.card := card_edges E
  have hCover : ∀ T : Finset (Fin (n+n)), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → n ≤ T.card :=
    matching_cover E p hmatch
  have clean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v, ¬G.Adj u v → gateVal (n+n) C j (pairInput u v) = false := by
    intro j hj hop u v absent
    by_contra hfalse
    have hit : gateVal (n+n) C j (pairInput u v) = true := by
      cases he : gateVal (n+n) C j (pairInput u v)
      · exact False.elim (hfalse he)
      · rfl
    obtain ⟨i, k, edge, left, right⟩ := safe j hj hop (pairInput u v) ⟨u,v,fun _ h => of_decide_eq_true h⟩ hit
    change decide (L i = u ∨ L i = v) = true at left
    change decide (R k = u ∨ R k = v) = true at right
    have hL := of_decide_eq_true left
    have hR := of_decide_eq_true right
    rcases hL with a | a <;> rcases hR with b | b
    · exact LR i k (a.trans b.symm)
    · exact absent (a ▸ b ▸ connected E edge)
    · exact absent (b ▸ a ▸ (connected E edge).symm)
    · exact LR i k (a.trans b.symm)
  obtain ⟨T, hT, bound⟩ := PEqualNP.Outside.L_meta_18670.SafeBank.count (n+n) G C h4 hC hGraph clean
  have cover := hCover T hT
  omega

namespace PEqualNP.Outside.L_meta_18670
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def fullBoard : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun e => e.1 + e.2 ∈ ({0,1,3,9} : Finset (Fin 13)))
private def matching : Equiv.Perm (Fin 13) where
  toFun i := -i
  invFun i := -i
  left_inv := neg_neg
  right_inv := neg_neg
def FullEdge (x : Fin 26 → Bool) : Prop := ∃ p l : Fin 13,
  p+l∈({0,1,3,9} : Finset (Fin 13)) ∧ x (p.castAdd 13)=true ∧ x (l.natAdd 13)=true
instance (x : Fin 26 → Bool) : Decidable (FullEdge x) := by unfold FullEdge; infer_instance
def FullSafe (C : Circuit) : Prop := ∀ j<C.size, (NestedCover.gateAt C j).op=.and →
  ∀ x : Fin 26 → Bool, Thin x → PEqualNP.EdgeOwnership.gateVal 26 C j x=true → FullEdge x

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem noRectangle : ∀ i j k l : Fin 13, i≠j → k≠l →
  ¬ ((i,k)∈fullBoard ∧ (i,l)∈fullBoard ∧ (j,k)∈fullBoard ∧ (j,l)∈fullBoard) := by decide +kernel

theorem full_safe_price (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ FullEdge x) (hs : FullSafe C) :
    64≤C.size := by
  have hm' : ∀ i : Fin 13, (i,matching i)∈fullBoard := by decide +kernel
  have hc : fullBoard.card=52 := by decide +kernel
  have h := broadSafe 13 fullBoard matching C (by decide) noRectangle hm' hm
  have he : ∀ x : Fin 26 → Bool, circuitFun 26 C x =
      decide (∃ i j : Fin 13, (i,j)∈fullBoard ∧ x (i.castAdd 13)=true ∧ x (j.natAdd 13)=true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa [FullEdge,fullBoard,circuitFun] using correct x
  apply Nat.le_of_not_gt
  intro no
  have price := h he (by
    intro j hj op x thin v
    simpa [FullEdge,fullBoard] using hs j hj op x thin v)
  omega
end PEqualNP.Outside.L_meta_18670

theorem PEqualNP.Outside.L_meta_18670.cover : ∀ (x1 : Fin (12 : ℕ) → Fin (12 : ℕ) → Prop) [x2 : DecidableRel x1],   have x3 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x3 : Fin (12 : ℕ) → Bool) (x4 : Fin (12 : ℕ)) => Decidable.decide (∀ (x5 : Fin (12 : ℕ)), x1 x5 x4 → x3 x5 = Bool.false);   have x4 : (Fin (12 : ℕ) → Bool) → Fin (12 : ℕ) → Bool := fun (x4 : Fin (12 : ℕ) → Bool) (x5 : Fin (12 : ℕ)) => Decidable.decide (∀ (x6 : Fin (12 : ℕ)), x1 x5 x6 → x4 x6 = Bool.false);   ∀ (x5 : Fin ((12 : ℕ) + (12 : ℕ)) → Bool), (¬∃ (x6 : Fin (12 : ℕ)) (x7 : Fin (12 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (12 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (12 : ℕ) x7) = Bool.true) → ∃ (x7 : Fin (12 : ℕ) → Bool), x4 (x3 x7) = x7 ∧ ∀ (x8 : Fin ((12 : ℕ) + (12 : ℕ))), x5 x8 = Bool.true → Fin.addCases x7 (x3 x7) x8 = Bool.true := by
  intro E inst
  dsimp only
  intro x hn
  let l : Fin 12 → Bool := fun i => x (Fin.castAdd 12 i)
  let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
  let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
  let s := M (N l)
  have leL : ∀ i, l i = true → s i = true := by
    intro i on
    apply decide_eq_true
    intro j e
    cases h : N l j with
    | false => rfl
    | true => exact Bool.noConfusion (on.symm.trans ((of_decide_eq_true h) i e))
  have stable : N s = N l := by
    funext j
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      apply decide_eq_true
      intro i e
      cases a : l i with
      | false => rfl
      | true => exact Bool.noConfusion ((leL i a).symm.trans ((of_decide_eq_true h) i e))
    · intro h
      apply decide_eq_true
      intro i e
      cases a : s i with
      | false => rfl
      | true => exact Bool.noConfusion (h.symm.trans ((of_decide_eq_true a) j e))
  refine ⟨s, ?_, ?_⟩
  · change M (N s) = s
    rw [stable]
  · intro k
    refine Fin.addCases (motive := fun k => x k = true → Fin.addCases s (N s) k = true) ?_ ?_ k
    · intro i hi
      simpa using leL i hi
    · intro j hj
      simp only [Fin.addCases_right, stable]
      apply decide_eq_true
      intro i e
      cases h : l i with
      | false => rfl
      | true => exact (hn ⟨i, j, e, h, hj⟩).elim

namespace PEqualNP.Outside.L_meta_18670.wireMono

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ev_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_eq_true, List.any_eq_true,
    List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩
    subst hx
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem key : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl stp U).getD i false = true → (gs.foldl stp V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stp, hl]
    · intro k hk
      unfold stp at hk ⊢
      rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hk
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h k hk
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact ev_mono g (hgs g (List.mem_cons_self ..)) U V h hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        exact absurd hk (by simp)

end PEqualNP.Outside.L_meta_18670.wireMono

open PEqualNP.Outside.L_meta_18670.wireMono PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18670.wireMono : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (24 : ℕ) → Bool), (∀ (x5 : Fin (24 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C hC x y hxy w hw
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact key C.gates hgs (List.ofFn x) (List.ofFn y) (by simp) (fun i hi => by
    by_cases h : i < 24
    · have e1 : (List.ofFn x).getD i false = x ⟨i, h⟩ := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]; rfl
      have e2 : (List.ofFn y).getD i false = y ⟨i, h⟩ := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]; rfl
      rw [e1] at hi; rw [e2]; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)) w hw

namespace PEqualNP.Outside.L_meta_18670.inject2

open PEqualNP.CircuitLowerBounds

def f (i : ℕ) : ℕ := if i < 9 then i else if i < 12 then i + 1 else i + 2

def rg (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem step (w w' : List Bool) (b : Bool) (hl : 12 ≤ w.length) (hl' : w'.length = w.length + 2)
    (h : ∀ i, w'.getD (f i) false = w.getD i false) (i : ℕ) :
    (w' ++ [b]).getD (f i) false = (w ++ [b]).getD i false := by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  rcases lt_trichotomy i w.length with h1 | h1 | h1
  · have h2 : f i < w'.length := by unfold f; split_ifs <;> omega
    rw [List.getElem?_append_left h2, List.getElem?_append_left h1]
    exact hi
  · have h2 : f i = w'.length := by unfold f; split_ifs <;> omega
    rw [h2, h1]
    simp
  · have h2 : w'.length < f i := by unfold f; split_ifs <;> omega
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem fold (gs : List Gate) :
    ∀ w w' : List Bool, 12 ≤ w.length → w'.length = w.length + 2 →
      (∀ i, w'.getD (f i) false = w.getD i false) →
      ∀ i, ((gs.map rg).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (f i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
          false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hl' h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have e : (rg g).op.eval ((rg g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [e]
    apply ih
    · simp; omega
    · simp; omega
    · exact step w w' _ hl hl' h

theorem base (x6 : Fin 26 → Bool) (i : ℕ) :
    (List.ofFn x6).getD (f i) false
      = (List.ofFn fun x8 : Fin 24 => x6 (Fin.ofNat 26 (f x8))).getD i false := by
  by_cases h : i < 24
  · have h2 : f i < 26 := by unfold f; split_ifs <;> omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h2), List.getElem?_eq_getElem (by simpa using h)]
    simp only [List.getElem_ofFn, Option.getD_some]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h2]
  · have h2 : 26 ≤ f i := by unfold f; split_ifs <;> omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using h2), List.getElem?_eq_none (by simp; omega)]

end PEqualNP.Outside.L_meta_18670.inject2


namespace PEqualNP.Outside.L_meta_18670
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity inject2
def CoreTest (C : Circuit) (a b : ℕ) : Prop :=
    let D : Finset (Fin 13) := {0, 1, 3, 9}
    let E := fun i j : Fin 12 =>
      Fin.succAbove (9 : Fin 13) i + Fin.succAbove (0 : Fin 13) j ∈ D
    let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
    let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
    let Q := fun b : Bool => if b then ({15, 16, 18} : Finset (Fin 24)) else {0, 1, 3}
    Monotone2 C ∧ C.size ≤ 58 ∧
      C.gates.head? = some ⟨.or, [0,1]⟩ ∧ max C.output (max a b) < 24+C.size ∧
      (∀ i j, E i j → C.eval (List.ofFn fun k : Fin 24 =>
        decide (k = Fin.castAdd 12 i ∨ k = Fin.natAdd 12 j)) = true) ∧
      (∀ t i, i ∈ Q t → (C.wires (List.ofFn fun k : Fin 24 => decide (k = i))).getD
        (if t then b else a) false = true) ∧
      ∀ s, M (N s) = s →
        let z : Fin 24 → Bool := Fin.append s (N s)
        C.eval (List.ofFn z) = false ∧
        ∀ t, (C.wires (List.ofFn fun k => if k ∈ Q t then false else z k)).getD
          (if t then b else a) false = false
def CoreFull (D : Circuit) (a b : ℕ) : Prop :=
    let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p l : Fin 13) => p + l ∈ offsets
      let inside := fun (y : Fin 24 → Bool) =>
        ∃ p l : Fin 12, I ((9 : Fin 13).succAbove p) ((0 : Fin 13).succAbove l) ∧
          y (Fin.castAdd 12 p) = true ∧ y (Fin.natAdd 12 l) = true
      Monotone2 D ∧ D.size ≤ 58 ∧
        D.gates.head? = some ⟨.or, [0, 1]⟩ ∧
        D.output < 24 + D.size ∧ a < 24 + D.size ∧ b < 24 + D.size ∧
        (∀ y : Fin 24 → Bool, D.eval (List.ofFn y) = true ↔ inside y) ∧
        ∀ y : Fin 24 → Bool, D.eval (List.ofFn y) = false →
          (D.wires (List.ofFn y)).getD a false = (y 0 || y 1 || y 3) ∧
          (D.wires (List.ofFn y)).getD b false = (y 15 || y 16 || y 18)
theorem testsFull (C : Circuit) (a b : ℕ) (hcert : CoreTest C a b) : CoreFull C a b := by
  let E := fun i j : Fin 12 =>
      Fin.succAbove (9 : Fin 13) i + Fin.succAbove (0 : Fin 13) j ∈
        ({0, 1, 3, 9} : Finset (Fin 13))
  let N := fun (s : Fin 12 → Bool) (j : Fin 12) => decide (∀ i, E i j → s i = false)
  let M := fun (t : Fin 12 → Bool) (i : Fin 12) => decide (∀ j, E i j → t j = false)
  let Q := fun b : Bool => if b then ({15, 16, 18} : Finset (Fin 24)) else {0, 1, 3}
  obtain ⟨hm, hs, hfirst, bounds, hpair, hunit, hmax⟩ := hcert
  obtain ⟨ho, hab⟩ := max_lt_iff.mp bounds
  obtain ⟨ha, hb⟩ := max_lt_iff.mp hab
  let val := fun (k : ℕ) (x : Fin 24 → Bool) => (C.wires (List.ofFn x)).getD k false
  let edge := fun x : Fin 24 → Bool => ∃ i j, E i j ∧
    x (Fin.castAdd 12 i) = true ∧ x (Fin.natAdd 12 j) = true
  have mono (x y : Fin 24 → Bool) (hle : ∀ i, x i = true → y i = true) (k : ℕ) :
      val k x = true → val k y = true := wireMono C hm x y hle k
  have accepts (x : Fin 24 → Bool) (hx : edge x) : C.eval (List.ofFn x) = true := by
    obtain ⟨i, j, he, hi, hj⟩ := hx
    apply mono _ x ?_ C.output (hpair i j he)
    intro k hk
    rcases of_decide_eq_true hk with rfl | rfl <;> assumption
  have rejects (x : Fin 24 → Bool) (hx : ¬ edge x) : C.eval (List.ofFn x) = false := by
    obtain ⟨s, hc, hxz⟩ := cover E x hx
    have hz := (hmax s hc).1
    cases hv : C.eval (List.ofFn x) with
    | false => rfl
    | true => exact Bool.noConfusion ((mono x _ hxz C.output hv).symm.trans hz)
  have tagCorrect (x : Fin 24 → Bool) (hx : ¬ edge x) (t : Bool) :
      val (if t then b else a) x = decide (∃ i ∈ Q t, x i = true) := by
    by_cases hit : ∃ i ∈ Q t, x i = true
    · rw [decide_eq_true hit]
      obtain ⟨i, mem, on⟩ := hit
      apply mono _ x ?_ _ (hunit t i mem)
      intro j hj
      obtain rfl := of_decide_eq_true hj
      exact on
    · rw [decide_eq_false hit]
      obtain ⟨s, hc, hxz⟩ := cover E x hx
      let z : Fin 24 → Bool := Fin.append s (N s)
      have le : ∀ k, x k = true → (if k ∈ Q t then false else z k) = true := by
        intro k on
        by_cases h : k ∈ Q t
        · exact (hit ⟨k, h, on⟩).elim
        · rw [if_neg h]
          exact hxz k on
      have hz := (hmax s hc).2 t
      cases hv : val (if t then b else a) x with
      | false => rfl
      | true => exact Bool.noConfusion ((mono x _ le _ hv).symm.trans hz)
  refine ⟨hm, hs, hfirst, ho, ha, hb, ?_, ?_⟩
  · intro x
    constructor
    · intro yes
      by_contra hx
      exact Bool.noConfusion (yes.symm.trans (rejects x hx))
    · exact accepts x
  · intro x no
    have hx : ¬ edge x := fun e => Bool.noConfusion ((accepts x e).symm.trans no)
    have tags (u v w : Fin 24) : decide (∃ i ∈ ({u,v,w} : Finset (Fin 24)), x i = true) =
        (x u || x v || x w) := by
      apply Bool.eq_iff_iff.mpr
      simp [Finset.mem_insert, or_and_right, exists_or, or_assoc]
    constructor
    · exact (tagCorrect x hx false).trans (tags 0 1 3)
    · exact (tagCorrect x hx true).trans (tags 15 16 18)

def ReducedEdge (x : Fin 24 → Bool) : Prop := ∃ p l : Fin 12,
  (9 : Fin 13).succAbove p+(0 : Fin 13).succAbove l∈({0,1,3,9}:Finset (Fin 13)) ∧
  x (p.castAdd 12)=true ∧ x (l.natAdd 12)=true
def CoreSafe (D : Circuit) : Prop := ∀ j<D.size, (NestedCover.gateAt D j).op=.and →
  ∀ x : Fin 24 → Bool, Thin x → PEqualNP.EdgeOwnership.gateVal 24 D j x=true → ReducedEdge x

theorem core_needs_thin_dirty (D : Circuit) (a b : ℕ) (hcert : CoreTest D a b) : ¬CoreSafe D := by
  classical
  intro safeD
  obtain ⟨okD,sizeD,headD,outD,boundA,boundB,evD,reserves⟩ := testsFull D a b hcert
  let E : Circuit := ⟨D.gates.map rg,D.output⟩
  have okE : Monotone2 E := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using okD g0 hg0
  have sizeE : E.size = D.size := by simp [E,Circuit.size]
  have headE : E.gates.head? = some ⟨.or,[0,1]⟩ := by
    change (D.gates.map rg).head? = _
    rw [List.head?_map,headD]
    rfl
  have transfer (x : Fin 26 → Bool) (i : ℕ) :
      (E.wires (List.ofFn x)).getD (f i) false =
      (D.wires (List.ofFn fun j : Fin 24 => x (Fin.ofNat 26 (f j)))).getD i false := by
    exact fold D.gates _ _ (by simp) (by simp) (base x) i
  let I := fun (p l : Fin 13) => p + l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
  let P := fun (x : Fin 26 → Bool) (p : Fin 13) => x (Fin.castAdd 13 p)
  let L := fun (x : Fin 26 → Bool) (l : Fin 13) => x (Fin.natAdd 13 l)
  let rename := fun i : ℕ => if i < 9 then i else if i < 12 then i + 1 else i + 2
  let restrict := fun (x : Fin 26 → Bool) (j : Fin 24) => x (Fin.ofNat 26 (rename j.val))
  have pointAddress : ∀ p : Fin 12,
      Fin.ofNat 26 (rename (Fin.castAdd 12 p).val) =
        Fin.castAdd 13 ((9 : Fin 13).succAbove p) := by decide +kernel
  have lineAddress : ∀ l : Fin 12,
      Fin.ofNat 26 (rename (Fin.natAdd 12 l).val) =
        Fin.natAdd 13 ((0 : Fin 13).succAbove l) := by decide +kernel
  let n := 26 + E.size
  let suffix : List Gate :=
    [⟨.or, [13, rename b]⟩, ⟨.and, [9, n]⟩, ⟨.and, [13, rename a]⟩,
     ⟨.or, [rename D.output, n + 2]⟩, ⟨.or, [n + 3, n + 1]⟩]
  let C : Circuit := ⟨E.gates ++ suffix, n + 4⟩
  have okC : Monotone2 C := by
    intro g hg
    change g ∈ E.gates ++ suffix at hg
    rcases List.mem_append.mp hg with inside | added
    · exact okE g inside
    · simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at added
      rcases added with rfl | rfl | rfl | rfl | rfl <;> simp
  have sizeC : C.size = D.size + 5 := by
    change (E.gates ++ suffix).length = D.size + 5
    rw [List.length_append]
    change E.size + 5 = D.size + 5
    rw [sizeE]
  have headC : C.gates.head? = some ⟨.or, [0, 1]⟩ := by
    change (E.gates ++ suffix).head? = _
    cases h : E.gates with
    | nil => simp only [h, List.head?_nil, reduceCtorEq] at headE
    | cons g gs =>
      rw [h] at headE
      exact headE
  let run : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl run w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [run, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl run w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (run w g) (by simp [run]; omega)]
      exact List.getD_append _ _ _ _ hi
  have runOr (w : List Bool) (i j : ℕ) :
      run w ⟨.or, [i, j]⟩ = w ++ [w.getD i false || w.getD j false] := by
    change w ++ [w.getD i false || (w.getD j false || false)] = _
    simp only [Bool.or_false]
  have runAnd (w : List Bool) (i j : ℕ) :
      run w ⟨.and, [i, j]⟩ = w ++ [w.getD i false && w.getD j false] := by
    change w ++ [w.getD i false && (w.getD j false && true)] = _
    simp only [Bool.and_true]
  have mappedBound (i : ℕ) (hi : i < 24 + D.size) : rename i < n := by
    dsimp only [rename, n]
    rw [sizeE]
    split
    · omega
    · split <;> omega
  have evC (x : Fin 26 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      C.eval (List.ofFn x) =
        (D.eval (List.ofFn y) || (x 13 && v.getD a false) ||
          (x 9 && (x 13 || v.getD b false))) := by
    let w := E.wires (List.ofFn x)
    let y := restrict x
    have wlen : w.length = n := by
      exact (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn, n]; rfl)
    have old (extra : List Bool) (i : ℕ) (hi : i < n) :
        (w ++ extra).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have new (extra : List Bool) (k : ℕ) :
        (w ++ extra).getD (n + k) false = extra.getD k false := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen, Nat.add_sub_cancel_left]
    have firstNew (extra : List Bool) :
        (w ++ extra).getD n false = extra.getD 0 false := by
      simpa only [Nat.add_zero] using new extra 0
    have raw (i : Fin 26) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have raw9 : w.getD 9 false = x 9 := raw 9
    have raw13 : w.getD 13 false = x 13 := raw 13
    have aSim : w.getD (rename a) false = (D.wires (List.ofFn y)).getD a false :=
      transfer x a
    have bSim : w.getD (rename b) false = (D.wires (List.ofFn y)).getD b false :=
      transfer x b
    have outSim : w.getD (rename D.output) false = D.eval (List.ofFn y) :=
      transfer x D.output
    change ((E.gates ++ suffix).foldl run (List.ofFn x)).getD (n + 4) false = _
    rw [List.foldl_append]
    change (suffix.foldl run w).getD (n + 4) false = _
    simp only [suffix, List.foldl_cons, List.foldl_nil, runOr, runAnd,
      List.append_assoc, List.cons_append, List.nil_append,
      old _ 9 (by dsimp [n]; omega), old _ 13 (by dsimp [n]; omega),
      old _ _ (mappedBound a boundA), old _ _ (mappedBound b boundB),
      old _ _ (mappedBound D.output outD),
      firstNew, new, List.getD_cons_zero, List.getD_cons_succ, raw9, raw13, aSim, bSim, outSim]
    rfl
  have throughLine : ∀ p : Fin 13, I p 0 ↔ p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by
    decide +kernel
  have throughPoint : ∀ l : Fin 13, I 9 l ↔ l = 0 ∨ l = 4 ∨ l = 5 ∨ l = 7 := by
    decide +kernel
  have value (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) =
        (D.eval (List.ofFn (restrict x)) || (L x 0 && (P x 0 || P x 1 || P x 3)) ||
          (P x 9 && (L x 0 || (L x 4 || L x 5 || L x 7)))) := by
    let y := restrict x
    rw [evC x]
    change
      (D.eval (List.ofFn y) || (L x 0 && (D.wires (List.ofFn y)).getD a false) ||
          (P x 9 && (L x 0 || (D.wires (List.ofFn y)).getD b false))) =
        (D.eval (List.ofFn y) || (L x 0 && (P x 0 || P x 1 || P x 3)) ||
          (P x 9 && (L x 0 || (L x 4 || L x 5 || L x 7))))
    cases hd : D.eval (List.ofFn y) with
    | false =>
      obtain ⟨ha, hb⟩ := reserves y hd
      rw [ha, hb]
      rfl
    | true => simp only [Bool.true_or]
  have correct (x : Fin 26 → Bool) :
      C.eval (List.ofFn x) = true ↔
        ∃ (p l : Fin 13), I p l ∧ P x p = true ∧ L x l = true := by
    rw [value]
    simp only [Bool.or_eq_true, Bool.and_eq_true, evD, restrict, pointAddress, lineAddress]
    constructor
    · rintro ((⟨p, l, hI, hp, hl⟩ | ⟨hl, (hp | hp) | hp⟩) |
        ⟨hp, hl | (hl | hl) | hl⟩)
      · exact ⟨_, _, hI, hp, hl⟩
      · exact ⟨0, 0, by decide, hp, hl⟩
      · exact ⟨1, 0, by decide, hp, hl⟩
      · exact ⟨3, 0, by decide, hp, hl⟩
      · exact ⟨9, 0, by decide, hp, hl⟩
      · exact ⟨9, 4, by decide, hp, hl⟩
      · exact ⟨9, 5, by decide, hp, hl⟩
      · exact ⟨9, 7, by decide, hp, hl⟩
    · rintro ⟨p, l, hI, hp, hl⟩
      by_cases p9 : p = 9
      · subst p
        refine Or.inr ⟨hp, ?_⟩
        rcases (throughPoint l).mp hI with rfl | rfl | rfl | rfl
        · exact Or.inl hl
        · exact Or.inr (Or.inl (Or.inl hl))
        · exact Or.inr (Or.inl (Or.inr hl))
        · exact Or.inr (Or.inr hl)
      · by_cases l0 : l = 0
        · subst l
          refine Or.inl (Or.inr ⟨hl, ?_⟩)
          rcases (throughLine p).mp hI with rfl | rfl | rfl | bad
          · exact Or.inl (Or.inl hp)
          · exact Or.inl (Or.inr hp)
          · exact Or.inr hp
          · exact (p9 bad).elim
        · obtain ⟨p', hp'⟩ := Fin.exists_succAbove_eq p9
          obtain ⟨l', hl'⟩ := Fin.exists_succAbove_eq l0
          exact Or.inl (Or.inl ⟨p', l',
            by rw [hp', hl']; exact hI, by rw [hp']; exact hp, by rw [hl']; exact hl⟩)
  have tail1 (x : Fin 26 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      (C.wires (List.ofFn x)).getD (n + 1) false = (x 9 && (x 13 || v.getD b false)) := by
    let w := E.wires (List.ofFn x)
    let y := restrict x
    have wlen : w.length = n := by
      exact (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn, n]; rfl)
    have old (extra : List Bool) (i : ℕ) (hi : i < n) :
        (w ++ extra).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have new (extra : List Bool) (k : ℕ) :
        (w ++ extra).getD (n + k) false = extra.getD k false := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen, Nat.add_sub_cancel_left]
    have firstNew (extra : List Bool) :
        (w ++ extra).getD n false = extra.getD 0 false := by
      simpa only [Nat.add_zero] using new extra 0
    have raw (i : Fin 26) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have raw9 : w.getD 9 false = x 9 := raw 9
    have raw13 : w.getD 13 false = x 13 := raw 13
    have aSim : w.getD (rename a) false = (D.wires (List.ofFn y)).getD a false :=
      transfer x a
    have bSim : w.getD (rename b) false = (D.wires (List.ofFn y)).getD b false :=
      transfer x b
    have outSim : w.getD (rename D.output) false = D.eval (List.ofFn y) :=
      transfer x D.output
    change ((E.gates ++ suffix).foldl run (List.ofFn x)).getD (n + 1) false = _
    rw [List.foldl_append]
    change (suffix.foldl run w).getD (n + 1) false = _
    simp only [suffix, List.foldl_cons, List.foldl_nil, runOr, runAnd,
      List.append_assoc, List.cons_append, List.nil_append,
      old _ 9 (by dsimp [n]; omega), old _ 13 (by dsimp [n]; omega),
      old _ _ (mappedBound a boundA), old _ _ (mappedBound b boundB),
      old _ _ (mappedBound D.output outD),
      firstNew, new, List.getD_cons_zero, List.getD_cons_succ, raw9, raw13, aSim, bSim, outSim]
    all_goals rfl
  have tail2 (x : Fin 26 → Bool) :
      let y := restrict x
      let v := D.wires (List.ofFn y)
      (C.wires (List.ofFn x)).getD (n + 2) false = (x 13 && v.getD a false) := by
    let w := E.wires (List.ofFn x)
    let y := restrict x
    have wlen : w.length = n := by
      exact (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn, n]; rfl)
    have old (extra : List Bool) (i : ℕ) (hi : i < n) :
        (w ++ extra).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (by omega)
    have new (extra : List Bool) (k : ℕ) :
        (w ++ extra).getD (n + k) false = extra.getD k false := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen, Nat.add_sub_cancel_left]
    have firstNew (extra : List Bool) :
        (w ++ extra).getD n false = extra.getD 0 false := by
      simpa only [Nat.add_zero] using new extra 0
    have raw (i : Fin 26) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        keep E.gates (List.ofFn x) i.val (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have raw9 : w.getD 9 false = x 9 := raw 9
    have raw13 : w.getD 13 false = x 13 := raw 13
    have aSim : w.getD (rename a) false = (D.wires (List.ofFn y)).getD a false :=
      transfer x a
    have bSim : w.getD (rename b) false = (D.wires (List.ofFn y)).getD b false :=
      transfer x b
    have outSim : w.getD (rename D.output) false = D.eval (List.ofFn y) :=
      transfer x D.output
    change ((E.gates ++ suffix).foldl run (List.ofFn x)).getD (n + 2) false = _
    rw [List.foldl_append]
    change (suffix.foldl run w).getD (n + 2) false = _
    simp only [suffix, List.foldl_cons, List.foldl_nil, runOr, runAnd,
      List.append_assoc, List.cons_append, List.nil_append,
      old _ 9 (by dsimp [n]; omega), old _ 13 (by dsimp [n]; omega),
      old _ _ (mappedBound a boundA), old _ _ (mappedBound b boundB),
      old _ _ (mappedBound D.output outD),
      firstNew, new, List.getD_cons_zero, List.getD_cons_succ, raw9, raw13, aSim, bSim, outSim]
    all_goals rfl

  have oldVal (x : Fin 26 → Bool) (j : ℕ) (hj : j < E.size) :
      PEqualNP.EdgeOwnership.gateVal 26 C j x =
      PEqualNP.EdgeOwnership.gateVal 24 D j (restrict x) := by
    let w := E.wires (List.ofFn x)
    have wlen : w.length = n := (len E.gates (List.ofFn x)).trans (by simp only [List.length_ofFn,n];rfl)
    change ((E.gates ++ suffix).foldl run (List.ofFn x)).getD (26+j) false = _
    rw [List.foldl_append]
    change (suffix.foldl run w).getD (26+j) false = _
    rw [keep suffix w (26+j) (by dsimp [n] at wlen; omega)]
    have eq : f (24+j) = 26+j := by unfold f;split_ifs <;> omega
    change (E.wires (List.ofFn x)).getD (26+j) false =
      (D.wires (List.ofFn fun i : Fin 24 => x (Fin.ofNat 26 (f i.val)))).getD (24+j) false
    rw [← eq]
    exact transfer x (24+j)
  have appended (t : ℕ) : (NestedCover.gateAt C (E.size+t)).op =
      (suffix.getD t ⟨.or,[]⟩).op := by
    change ((E.gates++suffix).getD (E.gates.length+t) _).op = _
    rw [List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left]
  have safeC : FullSafe C := by
    intro j hj hop x thin on
    have small : Thin (restrict x) := by
      let emb := fun i : Fin 24 => Fin.ofNat 26 (f i.val)
      have inj : Function.Injective emb := by
        change ∀ ⦃a b : Fin 24⦄, Fin.ofNat 26 (f a.val) = Fin.ofNat 26 (f b.val) → a=b
        decide +kernel
      obtain ⟨u,v,huv⟩ := thin
      refine ⟨Function.invFun emb u, Function.invFun emb v,?_⟩
      intro i hi
      rcases huv (emb i) hi with h|h
      · exact Or.inl ((Function.leftInverse_invFun inj i).symm.trans (congrArg (Function.invFun emb) h))
      · exact Or.inr ((Function.leftInverse_invFun inj i).symm.trans (congrArg (Function.invFun emb) h))
    by_cases hold : j < E.size
    · have hd : j < D.gates.length := by change j<D.size; omega
      have he : j < E.gates.length := hold
      have orig : (NestedCover.gateAt D j).op = .and := by
        change ((E.gates++suffix).getD j _).op=.and at hop
        rw [List.getD_append _ _ _ _ he] at hop
        change ((D.gates.map rg).getD j _).op=.and at hop
        simpa only [NestedCover.gateAt,List.getD_eq_getElem?_getD,List.getElem?_map,
          List.getElem?_eq_getElem hd,Option.map_some,Option.getD_some,rg] using hop
      rw [oldVal x j hold] at on
      obtain ⟨p,l,hI,hp,hl⟩ := safeD j hd orig _ small on
      exact ⟨_,_,hI,by simpa only [restrict,pointAddress] using hp,by simpa only [restrict,lineAddress] using hl⟩
    · have casesJ : j=E.size+0 ∨ j=E.size+1 ∨ j=E.size+2 ∨ j=E.size+3 ∨ j=E.size+4 := by omega
      rcases casesJ with rfl|rfl|rfl|rfl|rfl
      · rw [appended 0] at hop; contradiction
      · apply (correct x).mp
        rw [evC x]
        rw [Bool.or_eq_true]
        right
        have eq : 26+(E.size+1)=n+1 := by dsimp [n];omega
        change (C.wires (List.ofFn x)).getD (26+(E.size+1)) false=true at on
        rw [eq,tail1] at on
        exact on
      · apply (correct x).mp
        rw [evC x]
        simp only [Bool.or_eq_true]
        left; right
        have eq : 26+(E.size+2)=n+2 := by dsimp [n];omega
        change (C.wires (List.ofFn x)).getD (26+(E.size+2)) false=true at on
        rw [eq,tail2] at on
        exact on
      · rw [appended 3] at hop; contradiction
      · rw [appended 4] at hop; contradiction
  have lower := full_safe_price C okC correct safeC
  omega

set_option maxRecDepth 9000 in
theorem core_pair_obstruction (D : Circuit) (a b : ℕ) (hcert : CoreTest D a b) :
    ∃ j<D.size, (NestedCover.gateAt D j).op=.and ∧ ∃ u v : Fin 24,
      ¬ReducedEdge (PEqualNP.EdgeOwnership.pairInput u v) ∧
      PEqualNP.EdgeOwnership.gateVal 24 D j (PEqualNP.EdgeOwnership.pairInput u v)=true := by
  classical
  have bad := core_needs_thin_dirty D a b hcert
  unfold CoreSafe at bad
  push_neg at bad
  obtain ⟨j,hj,op,x,⟨u,v,sparse⟩,on,ind⟩ := bad
  have mono (y : Fin 24 → Bool) (le : ∀ i, x i=true → y i=true) :
      PEqualNP.EdgeOwnership.gateVal 24 D j y=true :=
    wireMono D (testsFull D a b hcert).1 x y le (24+j) on
  have witnessed (r t : Fin 24) (embed : ∀ i, x i=true → i=r ∨ i=t)
      (clean : ¬ReducedEdge (PEqualNP.EdgeOwnership.pairInput r t)) :
      ∃ j<D.size, (NestedCover.gateAt D j).op=.and ∧ ∃ u v : Fin 24,
      ¬ReducedEdge (PEqualNP.EdgeOwnership.pairInput u v) ∧
      PEqualNP.EdgeOwnership.gateVal 24 D j (PEqualNP.EdgeOwnership.pairInput u v)=true :=
    ⟨j,hj,op,r,t,clean,mono _ (fun i hi => decide_eq_true (embed i hi))⟩
  have one (r : Fin 24) : ¬ReducedEdge (PEqualNP.EdgeOwnership.pairInput r r) := by
    exact (by decide +kernel : ∀ r : Fin 24, ¬∃ p l : Fin 12,
      (9 : Fin 13).succAbove p + (0 : Fin 13).succAbove l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
      PEqualNP.EdgeOwnership.pairInput r r (p.castAdd 12)=true ∧ PEqualNP.EdgeOwnership.pairInput r r (l.natAdd 12)=true) r
  by_cases hu : x u=true
  · by_cases hv : x v=true
    · apply witnessed u v sparse
      intro edge
      obtain ⟨p,l,inc,hp,hl⟩ := edge
      apply ind
      have lift (i : Fin 24) (hi : PEqualNP.EdgeOwnership.pairInput u v i=true) : x i=true := by
        rcases of_decide_eq_true hi with h|h
        · simpa only [h] using hu
        · simpa only [h] using hv
      exact ⟨p,l,inc,lift _ hp,lift _ hl⟩
    · apply witnessed u u _ (one u)
      intro i hi
      rcases sparse i hi with h|h
      · exact Or.inl h
      · exact (hv (h ▸ hi)).elim
  · apply witnessed v v _ (one v)
    intro i hi
    rcases sparse i hi with h|h
    · exact (hu (h ▸ hi)).elim
    · exact Or.inl h

end PEqualNP.Outside.L_meta_18670

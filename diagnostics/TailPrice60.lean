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


end PEqualNP.Outside.L_meta_18670.SafeBank
namespace PEqualNP.Outside.L_meta_18670
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SafeBank
lemma pos_gate_cond {n : ℕ} (gs : List Gate)
    (ops : binaryOps gs) 
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool)
    (nonempty : (gateAtPos n gs w).op=.and → (gateAtPos n gs w).inputs ≠ []) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have ne : gs[j].op=.and → gs[j].inputs≠[] := by simpa only [hw,gateAt_index gs j hj] using nonempty
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 ne
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)


def Cuts {n k : ℕ} (gs : List Gate) (P N : Fin k → Fin n → Bool) (w : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun z => posRead gs w (P z)=true ∧ posRead gs w (N z)=false

theorem suffixPrice {n k : ℕ} (gs : List Gate) (o : ℕ) (hb : binaryOps gs) (ho : o<n+gs.length)
    (P N : Fin k → Fin n → Bool)
    (bank : ∀ i : Fin n,(Finset.univ.filter fun z : Fin k => P z i=true ∧ N z i=false).card≤1)
    (separate : ∀ z, posRead gs (o+1) (P z)=true ∧ posRead gs (o+1) (N z)=false) :
    k≤gs.length+1 := by
  classical
  let S := Cuts gs P N
  let paid := Finset.Ico (n+1) (n+1+gs.length)
  have step (w : ℕ) (hw : w<n+1+gs.length) (large : 1<(S w).card) :
      ∃ cs : Finset ℕ, cs ⊆ Finset.range w ∧ S w ⊆ cs.biUnion S ∧
        cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    have lo : n+1≤w := by
      by_contra! lt
      cases w with
      | zero => simp [S,Cuts,posRead] at large
      | succ i =>
        have hi : i<n := by omega
        have e : S (i+1)=Finset.univ.filter (fun z : Fin k => P z ⟨i,hi⟩=true ∧ N z ⟨i,hi⟩=false) := by
          ext z
          simp only [S,Cuts,Finset.mem_filter,Finset.mem_univ,true_and,pos_input gs i hi]
        rw [e] at large
        have := bank ⟨i,hi⟩
        omega
    have mem : w∈paid := Finset.mem_Ico.mpr ⟨lo,hw⟩
    let f := firstWire n gs w
    let g := secondWire n gs w
    refine ⟨{f,g},?_,?_,by rw [if_pos mem];exact Finset.card_le_two⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact Finset.mem_range.mpr (clamp_lt _ _ (by omega))
      · obtain rfl := Finset.mem_singleton.mp hi
        exact Finset.mem_range.mpr (clamp_lt _ _ (by omega))
    · intro z hz
      obtain ⟨hp,hn⟩ := (Finset.mem_filter.mp hz).2
      have ne : (gateAtPos n gs w).op=.and → (gateAtPos n gs w).inputs≠[] := by
        intro op he
        let j := w-(n+1)
        have hj : j<gs.length := by dsimp [j];omega
        have eq : w=n+j+1 := by dsimp [j];omega
        rw [eq,gateAt_index gs j hj] at op he
        have h := getD_wiresFrom_gate gs (List.ofFn (N z)) j hj
        simp only [List.length_ofFn,he,List.map_nil,op,GateOp.eval,List.all_nil] at h
        rw [eq] at hn
        exact Bool.noConfusion (h.symm.trans hn)
      rw [pos_gate_cond gs hb w lo hw (P z) ne] at hp
      rw [pos_gate_cond gs hb w lo hw (N z) ne] at hn
      have either : (posRead gs f (P z)=true ∧ posRead gs f (N z)=false) ∨
          (posRead gs g (P z)=true ∧ posRead gs g (N z)=false) := by
        dsimp only [f,g]
        cases h0 : andPos n gs w <;> cases h1 : posRead gs (firstWire n gs w) (P z) <;>
          cases h2 : posRead gs (firstWire n gs w) (N z) <;>
          cases h3 : posRead gs (secondWire n gs w) (P z) <;>
          cases h4 : posRead gs (secondWire n gs w) (N z) <;> simp_all
      rcases either with h|h
      · exact Finset.mem_biUnion.mpr ⟨f,by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨g,by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  have b := countUnion S paid (n+1+gs.length) step {o+1} (by simpa using (show o+1<n+1+gs.length by omega))
  have allS : S (o+1)=Finset.univ := by
    ext z
    simp only [S,Cuts,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact separate z
  have cp : ((Finset.range (n+1+gs.length)) ∩ paid).card≤gs.length := by
    have hh := Finset.card_le_card (Finset.inter_subset_right (s₁:=Finset.range (n+1+gs.length)) (s₂:=paid))
    simpa [paid] using hh
  simp only [Finset.singleton_biUnion,allS,Finset.card_univ,Fintype.card_fin,Finset.card_singleton] at b
  omega

def fixedBank : List Gate := [⟨.or,[0,1]⟩,⟨.or,[24,3]⟩,⟨.or,[15,16]⟩,⟨.or,[26,18]⟩,⟨.or,[12,14]⟩,⟨.or,[20,28]⟩,⟨.or,[13,19]⟩,⟨.or,[30,23]⟩,⟨.or,[22,12]⟩,⟨.or,[18,32]⟩,⟨.or,[33,23]⟩,⟨.or,[21,22]⟩,⟨.or,[17,35]⟩,⟨.or,[21,23]⟩,⟨.or,[20,37]⟩,⟨.or,[38,16]⟩,⟨.or,[20,22]⟩,⟨.or,[19,40]⟩,⟨.or,[41,15]⟩,⟨.or,[14,18]⟩,⟨.or,[21,19]⟩,⟨.or,[43,44]⟩,⟨.or,[18,13]⟩,⟨.or,[17,46]⟩,⟨.or,[47,20]⟩,⟨.or,[19,12]⟩,⟨.or,[17,16]⟩,⟨.or,[49,50]⟩,⟨.or,[15,23]⟩,⟨.or,[52,14]⟩,⟨.or,[17,53]⟩,⟨.or,[16,14]⟩,⟨.or,[55,13]⟩,⟨.or,[56,22]⟩,⟨.or,[13,21]⟩,⟨.or,[15,12]⟩,⟨.or,[59,58]⟩]
def rawP (z : Fin 24) (i : Fin 24) := (([1048577,8388610,8388612,4194312,8388624,4194336,2097216,1048704,524544,8389120,4195328,2099200,131080,32800,1048704,4195328,4097,524290,262148,16448,65792,10240,2097168,8389120] : List ℕ).getD z.val 0).testBit i.val
def bankP (z : Fin 24) (i : Fin 61) := (([289996780077057,31526178850340866,31526178800009220,144123017838985224,31526178800009232,144123017805430816,1441205722470678592,289996729745536,2874126616756480,31526178800009728,144123017805431808,1441205722470680576,21814379448238088,1760911852549734432,289996729745536,144123017805431808,1732197037597790209,2874126667087874,536587578638340,279267158167404608,255579828810481920,1657817247302821888,1441205722470678544,31526178800009728] : List ℕ).getD z.val 0).testBit i.val
def rawN (z : Fin 24) (i : Fin 24) := (([7852034,15704065,16773120,15704065,16773120,16773120,16773120,16773120,16773120,16773120,16773120,16773120,10350600,10973216,15323264,12489728,15704065,7852034,3923972,13873216,16048384,14632960,5173264,8204800] : List ℕ).getD z.val 0).testBit i.val
def bankN (z : Fin 24) (i : Fin 61) := (([2305843005983543298,2305843008407314433,2305843009163358208,2305843008407314433,2305843009163358208,2305843009163358208,2305843009163358208,2305843009163358208,2305843009163358208,2305843009163358208,2305843009163358208,2305843009163358208,2305842906111275016,2305835312576163872,2305350427952664704,2053641430026327040,2305843008407314433,2305843005983543298,2305842979085737988,2305781436509302848,2301902359488684288,288230376099235840,2305842047079084048,2274317811763196416] : List ℕ).getD z.val 0).testBit i.val

def red (x : Fin 24 → Bool) : Prop := ∃ p l : Fin 12,
  (9 : Fin 13).succAbove p+(0 : Fin 13).succAbove l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
  x (p.castAdd 12)=true ∧ x (l.natAdd 12)=true
instance (x : Fin 24 → Bool) : Decidable (red x) := by unfold red;infer_instance
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem fixed_prefix_price (C : Circuit) (tail : List Gate) (split : C.gates=fixedBank++tail)
    (hm : Monotone2 C) (out : C.output<24+C.size)
    (correct : ∀ x : Fin 24 → Bool, C.eval (List.ofFn x)=true ↔ red x) :
    60≤C.size := by
  have len : C.size=37+tail.length := by change C.gates.length=_;rw [split,List.length_append];rfl
  have hb : binaryOps tail := fun g h => hm g (split ▸ List.mem_append_right _ h)
  have non : ∀ i : Fin 61,(Finset.univ.filter fun z : Fin 24 => bankP z i=true ∧ bankN z i=false).card≤1 := by decide +kernel
  have er : ∀ z : Fin 24, red (rawP z) ∧ ¬red (rawN z) := by decide +kernel
  have ep : ∀ z : Fin 24, wiresFrom fixedBank (List.ofFn (rawP z))=List.ofFn (bankP z) := by decide +kernel
  have en : ∀ z : Fin 24, wiresFrom fixedBank (List.ofFn (rawN z))=List.ofFn (bankN z) := by decide +kernel
  have sep (z : Fin 24) : posRead tail (C.output+1) (bankP z)=true ∧
        posRead tail (C.output+1) (bankN z)=false := by
    have hp := (correct (rawP z)).mpr (er z).1
    have hn : C.eval (List.ofFn (rawN z))=false := Bool.eq_false_iff.mpr (fun h => (er z).2 ((correct _).mp h))
    change (wiresFrom C.gates (List.ofFn (rawP z))).getD C.output false=true at hp
    change (wiresFrom C.gates (List.ofFn (rawN z))).getD C.output false=false at hn
    rw [split,wiresFrom_append,ep] at hp
    rw [split,wiresFrom_append,en] at hn
    exact ⟨hp,hn⟩
  have h := suffixPrice tail C.output hb (by omega) bankP bankN non sep
  omega
end PEqualNP.Outside.L_meta_18670

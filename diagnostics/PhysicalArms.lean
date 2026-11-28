import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.FullSupport
abbrev N := Fin 42
abbrev Input := Finset N
abbrev Arm := Input → Bool
def mono (a : Arm) := ∀s t : Input, s ⊆ t → a s=true → a t=true
def changes (a : Arm) (x : N) := ∃s : Input,a (insert x s) ≠ a s
def masks : Array Nat := #[2474236706816,550433193984,1100866387968,2201732775936,5421137920,10842275840,21684551680,43369103360,86738206720,173476413440,346952826880,693905653760,1387811307520,2775622615040,1153200816128,2306401632256,214758850560,429517701120,859035402240,1718070804480,3436141608960,81938,163878,327756,655512,1311024,524897,1049794,2437,4874,9748,19496,38992,77984,155968,311936,623872,1247744,398337,796674,1593348,1089545]
def edge (x y : N) : Bool := masks[x.val]!.testBit y.val
def first : Array N := #[26,21,22,23,21,22,23,24,25,26,27,28,29,30,21,22,21,22,23,24,25,1,1,2,3,4,0,1,0,1,2,3,4,5,6,7,8,9,0,1,2,0]
def second : Array N := #[28,22,23,24,24,25,26,27,28,29,30,31,32,33,31,32,23,24,25,26,27,4,2,3,4,5,5,6,2,3,4,5,6,7,8,9,10,11,10,11,12,3]

def probe (x y : N) : N × N :=
  let p := first[x.val]!
  let q := second[x.val]!
  let u := first[y.val]!
  let v := second[y.val]!
  if !edge p u then (p,u) else if !edge p v then (p,v) else if !edge q u then (q,u) else (q,v)
def checked (x y : N) :=
  let (p,q) := probe x y
  edge x p && edge y q && !edge p q
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem allProbes : ∀x y : N, checked x y=true := by decide +kernel

theorem allInputs (a b : Arm) (ma : mono a) (mb : mono b)
    (onPairs : ∀x y : N, (a {x,y} && b {x,y}) = edge x y) :
    (∀x,changes a x) ∨ (∀y,changes b y) := by
  classical
  by_cases ac : ∀x,changes a x
  · exact Or.inl ac
  right
  intro y
  by_contra hy
  obtain ⟨x,hx⟩ := Classical.not_forall.mp ac
  have xa : ∀s : Input,a (insert x s)=a s := by
    intro s
    by_contra hh
    exact hx ⟨s,hh⟩
  have yb : ∀s : Input,b (insert y s)=b s := by
    intro s
    by_contra hh
    exact hy ⟨s,hh⟩
  obtain ⟨p,q,pq⟩ : ∃p q : N,probe x y=(p,q) := ⟨_,_,rfl⟩
  have chk:=allProbes x y
  simp only [checked,pq] at chk
  have ex : edge x p=true := by
    cases u : edge x p <;> simp_all
  have ey : edge y q=true := by
    cases u : edge y q <;> simp_all
  have ep : edge p q=false := by
    cases u : edge p q <;> simp_all
  have ax := onPairs x p
  have byy := onPairs y q
  rw [ex] at ax
  rw [ey] at byy
  have ap : a {p}=true := by
    rw [←xa {p}]
    cases u : a {x,p} <;> simp_all
  have bq : b {q}=true := by
    rw [←yb {q}]
    cases u : b {y,q} <;> simp_all
  have both := onPairs p q
  rw [ma {p} {p,q} (by simp) ap, mb {q} {p,q} (by simp) bq,ep] at both
  contradiction

end PEqualNP.Outside.L_meta_9743.FullSupport

namespace PEqualNP.Outside.L_meta_9743.FullSupport
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



def listed : List (Nat × Nat) := [(0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def board (s : Input) : Prop := ∃u v : N,(u.val,v.val)∈listed ∧ u∈s ∧ v∈s
def dir (x y : N) := (x.val,y.val)∈listed

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2500000 in
theorem rowData : ∀x y : N, (edge x y=true ↔
      (x.val,x.val)∈listed ∨ (x.val,y.val)∈listed ∨
      (y.val,x.val)∈listed ∨ (y.val,y.val)∈listed) := by decide +kernel

theorem cube (x y : N) : board {x,y} ↔ edge x y=true := by
  rw [rowData]
  constructor
  · rintro ⟨u,v,e,hu,hv⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> tauto
  · rintro (e|e|e|e)
    · exact ⟨x,x,e,by simp,by simp⟩
    · exact ⟨x,y,e,by simp,by simp⟩
    · exact ⟨y,x,e,by simp,by simp⟩
    · exact ⟨y,y,e,by simp,by simp⟩

def wire (gs : List Gate) (i : Nat) (s : Input) : Bool :=
  (wiresFrom gs (List.ofFn (fun x : N => decide (x∈s)))).getD i false

theorem gateMono (gs : List Gate) (hmono : ∀g∈gs,g.op=GateOp.and ∨ g.op=GateOp.or) (i : Nat) :
    mono (wire gs i) := by
  intro s t sub hi
  apply wiresFrom_mono gs hmono _ _ (by simp) _ i hi
  intro j hj
  by_cases hn : j<42
  · rw [List.getD_eq_getElem _ _ (by simpa using hn),List.getElem_ofFn] at hj
    rw [List.getD_eq_getElem _ _ (by simpa using hn),List.getElem_ofFn]
    exact decide_eq_true (sub (of_decide_eq_true hj))
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

theorem physicalPorts (gs : List Gate) (hmono : ∀g∈gs,g.op=GateOp.and ∨ g.op=GateOp.or)
    (i j : Nat) (ok : ∀s, (wire gs i s && wire gs j s)=true ↔ board s) :
    (∀x,changes (wire gs i) x) ∨ (∀x,changes (wire gs j) x) := by
  apply allInputs _ _ (gateMono gs hmono i) (gateMono gs hmono j)
  intro x y
  exact Bool.eq_iff_iff.mpr ((ok {x,y}).trans (cube x y))

end PEqualNP.Outside.L_meta_9743.FullSupport

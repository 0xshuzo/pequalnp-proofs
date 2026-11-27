import PEqualNP.Defs

namespace RawArm18213

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wval C x i.val = x i := by
  change val C (List.ofFn x) i.val = x i
  rw [val_input List.length_ofFn i.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma wval_gate {n : ℕ} {C : Circuit} (h : ReadsBack n C)
    (x : Fin n → Bool) {g : ℕ} (hg : g < C.size) :
    wval C x (n + g) = (gateAt C g).op.eval ((gateAt C g).inputs.map (wval C x)) := by
  change val C (List.ofFn x) (n + g) = _
  rw [val_gate List.length_ofFn hg]
  congr 1
  apply List.map_congr_left
  intro u hu
  exact ite_eq_left (h g hg u hu)

def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega

lemma delDead_wval {n k : ℕ} {C : Circuit} (hk : k < C.size) (h : ReadsBack n C)
    (hno : ∀ j < C.size, n + k ∉ (gateAt C j).inputs) (x : Fin n → Bool) (w : ℕ) :
    wval (delDead n k C) x w = wval C x (unshiftW n k w) := by
  have hback := delDead_readsBack n k C h hk hno
  have hlen := delDead_length n k C hk
  change k < C.gates.length at hk
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · have hu : unshiftW n k w = w := ite_eq_left (by omega)
      rw [hu]
      exact (wval_input _ x ⟨w, hin⟩).trans (wval_input C x ⟨w, hin⟩).symm
    by_cases hout : n + (delDead n k C).gates.length ≤ w
    · have hu : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW
        split_ifs <;> omega
      exact (val_ge List.length_ofFn hout).trans (val_ge List.length_ofFn hu).symm
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < (delDead n k C).gates.length := by omega
    have hj' : unshiftG k j < C.gates.length := by
      unfold unshiftG
      split_ifs <;> omega
    have hu : unshiftW n k (n + j) = n + unshiftG k j := by
      unfold unshiftW unshiftG
      split_ifs <;> omega
    rw [hu, wval_gate hback x hj, wval_gate h x hj', delDead_gateAt n k C hk j hj]
    simp only [shiftGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
      rw [delDead_gateAt n k C hk j hj]
      exact List.mem_map.mpr ⟨u, hu, rfl⟩
    have hne : u ≠ n + k := fun heq => hno (unshiftG k j) hj' (heq ▸ hu)
    simp only [Function.comp_apply]
    rw [ih _ (hback j hj _ hmem), unshiftW_shiftW n k u hne]

private lemma delDead_ao2 {n k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    IsAO2 n (delDead n k C) := by
  have mapped : ∀ g ∈ (delDead n k C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hm := List.mem_of_mem_eraseIdx hg'
    exact ⟨h.1 g' hm, by simp [shiftGate, h.2.2 g' hm]⟩
  exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C h.2.1 hk hno,
    fun g hg => (mapped g hg).2⟩

lemma later_reader {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h : IsLeastAO G C) {k : ℕ} (hk : k < C.size)
    (hout : C.output ≠ n + k) :
    ∃ j, j < C.size ∧ k < j ∧ n + k ∈ (gateAt C j).inputs := by
  by_contra hnone
  have hno : ∀ j < C.size, n + k ∉ (gateAt C j).inputs := by
    intro j hj hmem
    have hlt := h.1.2.1 j hj _ hmem
    exact hnone ⟨j, hj, by omega, hmem⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    change wval (delDead n k C) x (shiftW n k C.output) = wval C x C.output
    rw [delDead_wval hk h.1.2.1 hno, unshiftW_shiftW n k C.output hout]
  have hle := h.2.2 _ (delDead_ao2 h.1 hk hno) (heq.trans h.2.1)
  have hsize := delDead_size n k C hk
  omega

def ZeroOnRestriction {n : ℕ} (C : Circuit) (i : Fin n) (u : ℕ) : Prop :=
  ∀ x : Fin n → Bool, x i = false → wval C x u = false

def Collapses {n : ℕ} (C : Circuit) (i : Fin n) (g : ℕ) : Prop :=
  ∃ u < n + g, ∀ x : Fin n → Bool, x i = false → wval C x (n + g) = wval C x u

lemma input_zero {n : ℕ} (C : Circuit) (i : Fin n) : ZeroOnRestriction C i i.val :=
  fun x hx => (wval_input C x i).trans hx

lemma collapse_from_zero {n : ℕ} {C : Circuit} {i : Fin n} (h : IsAO2 n C)
    {g u : ℕ} (hg : g < C.size) (hu : u ∈ (gateAt C g).inputs)
    (hz : ZeroOnRestriction C i u) :
    Collapses C i g ∧
      ((gateAt C g).op = GateOp.and ∨
        (∃ v ∈ (gateAt C g).inputs, v ≠ u ∧ ZeroOnRestriction C i v) →
        ZeroOnRestriction C i (n + g)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 _ (gateAt_mem hg))
  have hmem : u = a ∨ u = b := by simpa [hab] using hu
  obtain ⟨v, hv, hlist⟩ : ∃ v < n + g,
      (gateAt C g).inputs = [u, v] ∨ (gateAt C g).inputs = [v, u] := by
    rcases hmem with rfl | rfl
    · exact ⟨b, h.2.1 g hg b (by simp [hab]), Or.inl hab⟩
    · exact ⟨a, h.2.1 g hg a (by simp [hab]), Or.inr hab⟩
  have other_zero (hother : ∃ w ∈ (gateAt C g).inputs, w ≠ u ∧ ZeroOnRestriction C i w) :
      ZeroOnRestriction C i v := by
    obtain ⟨w, hw, hne, hwz⟩ := hother
    have hw' : w = v := by
      rcases hlist with hl | hl <;> simpa [hl, hne] using hw
    exact hw' ▸ hwz
  rcases h.1 _ (gateAt_mem hg) with hop | hop
  · have hzero : ZeroOnRestriction C i (n + g) := by
      intro x hx
      rw [wval_gate h.2.1 x hg, hop]
      rcases hlist with hl | hl <;> simp [hl, GateOp.eval, hz x hx]
    exact ⟨⟨i.val, by have := i.isLt; omega,
      fun x hx => (hzero x hx).trans (input_zero C i x hx).symm⟩, fun _ => hzero⟩
  · have heval : ∀ x : Fin n → Bool, x i = false → wval C x (n + g) = wval C x v := by
      intro x hx
      rw [wval_gate h.2.1 x hg, hop]
      rcases hlist with hl | hl <;> simp [hl, GateOp.eval, hz x hx]
    refine ⟨⟨v, hv, heval⟩, ?_⟩
    rintro (hand | hother) x hx
    · cases hop.symm.trans hand
    · exact (heval x hx).trans (other_zero hother x hx)

lemma three_collapses {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {i : Fin n} (h : IsLeastAO G C)
    (htrue : ∃ x : Fin n → Bool, x i = false ∧ graphFun G ∅ x = true)
    (hread :
      (∃ a b c : ℕ, a < b ∧ b < c ∧
        (a < C.size ∧ i.val ∈ (gateAt C a).inputs) ∧
        (b < C.size ∧ i.val ∈ (gateAt C b).inputs) ∧
        (c < C.size ∧ i.val ∈ (gateAt C c).inputs)) ∨
      (∃ a b : ℕ, a ≠ b ∧
        (a < C.size ∧ i.val ∈ (gateAt C a).inputs) ∧
        (b < C.size ∧ i.val ∈ (gateAt C b).inputs) ∧ (gateAt C a).op = GateOp.and)) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ c < C.size ∧
      Collapses C i a ∧ Collapses C i b ∧ Collapses C i c := by
  have hout {w : ℕ} (hz : ZeroOnRestriction C i w) : C.output ≠ w := by
    obtain ⟨x, hx, hf⟩ := htrue
    have heval : wval C x C.output = true := (congrFun h.2.1 x).trans hf
    intro hw
    rw [hw, hz x hx] at heval
    cases heval
  have direct {g : ℕ} (hg : g < C.size ∧ i.val ∈ (gateAt C g).inputs) :=
    collapse_from_zero h.1 hg.1 hg.2 (input_zero C i)
  rcases hread with ⟨a, b, c, hab, hbc, ha, hb, hc⟩ | ⟨a, b, hne, ha, hb, hand⟩
  · exact ⟨a, b, c, hab, hbc, hc.1, (direct ha).1, (direct hb).1, (direct hc).1⟩
  · have hza := (direct ha).2 (Or.inl hand)
    obtain ⟨r, hr, har, hra⟩ := later_reader h ha.1 (hout hza)
    have hcr := collapse_from_zero h.1 hr hra hza
    by_cases heq : r = b
    · subst r
      have hzb := hcr.2 (Or.inr ⟨i.val, hb.2, by have := i.isLt; omega, input_zero C i⟩)
      obtain ⟨s, hs, hbs, hsb⟩ := later_reader h hb.1 (hout hzb)
      exact ⟨a, b, s, har, hbs, hs, (direct ha).1, (direct hb).1,
        (collapse_from_zero h.1 hs hsb hzb).1⟩
    by_cases hbr : b < r
    · by_cases hab : a < b
      · exact ⟨a, b, r, hab, hbr, hr, (direct ha).1, (direct hb).1, hcr.1⟩
      · exact ⟨b, a, r, by omega, har, hr, (direct hb).1, (direct ha).1, hcr.1⟩
    · exact ⟨a, r, b, har, by omega, hb.1, (direct ha).1, hcr.1, (direct hb).1⟩


abbrev G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def seeds : List Nat := [512, 512, 512, 512, 512, 512, 512, 512, 512, 1024, 512, 16, 16, 16, 16, 256, 16, 16, 16, 16, 16, 16, 32, 32, 32, 32, 32, 1024, 32, 32, 32, 32, 32, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 0, 514, 516, 520, 528, 1056, 576, 1152, 1280, 512, 1024, 17, 0, 20, 24, 16, 48, 80, 144, 256, 528, 1280, 33, 34, 0, 40, 48, 32, 96, 160, 1280, 1536, 1024, 65, 66, 68, 0, 80, 96, 64, 128, 320, 576, 1152]
def inputAt (m : Nat) (v : Fin 11) : Bool := m.testBit v.val

def seed (o : Bool) (v q : Fin 11) := seeds.getD ((if o then 44 else 0) + 11*v.val+q.val) 0

set_option maxHeartbeats 2000000 in
theorem probes : ∀ (v q : Fin 11) (o : Bool), v.val < 4 → q ≠ v →
    let m := seed o v q
    let x := inputAt m
    let y := fun j => if j = v then true else x j
    x q = o ∧ x v = false ∧ graphFun G ∅ x = false ∧ graphFun G ∅ y = true := by
  decide +kernel

theorem output_not_raw (C : Circuit) (h : IsLeastAO G C) (i : Fin 11) :
    C.output ≠ i.val := by
  intro he
  let x := pairInput i i
  have lo : graphFun G ∅ x = false := by
    have allsingle : ∀ a : Fin 11, graphFun G ∅ (pairInput a a) = false := by decide +kernel
    exact allsingle i
  have hi : wval C x C.output = true := by rw [he, wval_input]; simp [x,pairInput]
  have hv : wval C x C.output = graphFun G ∅ x := congrFun h.2.1 x
  rw [lo,hi] at hv
  contradiction

theorem differing_reader {n : ℕ} {C : Circuit} (h : IsAO2 n C)
    (v : Fin n) (x y : Fin n → Bool) (same : ∀ j, j ≠ v → x j = y j)
    (out : C.output ≠ v.val) (diff : wval C x C.output ≠ wval C y C.output) :
    ∃ j < C.size, v.val ∈ (gateAt C j).inputs ∧ wval C x (n+j) ≠ wval C y (n+j) := by
  by_contra bad
  apply diff
  have agree : ∀ w : ℕ, w ≠ v.val → wval C x w = wval C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hr : w < n
      · let t : Fin n := ⟨w,hr⟩
        exact (wval_input C x t).trans ((same t (fun e => hw (congrArg Fin.val e))).trans
          (wval_input C y t).symm)
      by_cases valid : w < n+C.size
      · let g := w-n
        have hg : g<C.size := by dsimp [g]; omega
        have he : w=n+g := by dsimp [g]; omega
        by_cases hv : v.val ∈ (gateAt C g).inputs
        · rw [he]
          by_contra ne
          exact bad ⟨g,hg,hv,ne⟩
        · rw [he,wval_gate h.2.1 x hg,wval_gate h.2.1 y hg]
          congr 1
          apply List.map_congr_left
          intro i hi
          apply ih i (by have := h.2.1 g hg i hi; omega)
          exact fun e => hv (e ▸ hi)
      · have bound : n+C.gates.length ≤ w := Nat.le_of_not_gt valid
        exact (val_ge (C := C) (x := List.ofFn x) List.length_ofFn bound).trans
          (val_ge (C := C) (x := List.ofFn y) List.length_ofFn bound).symm
  exact agree C.output out

theorem second_reader {C : Circuit} (h : IsLeastAO G C) {v q : Fin 11}
    (hv : v.val < 4) (hq : q ≠ v) {g : ℕ} (hg : g < C.size)
    (pins : q.val ∈ (gateAt C g).inputs) :
    ∃ j < C.size, j ≠ g ∧ v.val ∈ (gateAt C j).inputs := by
  classical
  let o := decide ((gateAt C g).op = GateOp.or)
  let x := inputAt (seed o v q)
  let y := fun t => if t = v then true else x t
  obtain ⟨xq,_,xlo,yhi⟩ := probes v q o hv hq
  change x q = o at xq
  change graphFun G ∅ x = false at xlo
  change graphFun G ∅ y = true at yhi
  have yq : y q = o := by simpa [y,hq] using xq
  have gx : wval C x C.output = graphFun G ∅ x := congrFun h.2.1 x
  have gy : wval C y C.output = graphFun G ∅ y := congrFun h.2.1 y
  obtain ⟨j,hj,hread,hd⟩ := differing_reader h.1 v x y
    (by intro t ht; simp [y,ht]) (output_not_raw C h v) (by rw [gx,gy,xlo,yhi]; decide)
  refine ⟨j,hj,?_,hread⟩
  intro eqg
  subst j
  apply hd
  rw [wval_gate h.1.2.1 x hg,wval_gate h.1.2.1 y hg]
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (h.1.2.2 _ (gateAt_mem hg))
  have habq : q.val = a ∨ q.val = b := by simpa [hab] using pins
  rcases h.1.1 _ (gateAt_mem hg) with hop | hop
  · have hxq : x q = false := by simpa [o,hop] using xq
    have hyq : y q = false := by simpa [o,hop] using yq
    rcases habq with e | e <;> rw [←e] at hab <;>
      simp [hop,hab,GateOp.eval,wval_input,hxq,hyq]
  · have hxq : x q = true := by simpa [o,hop] using xq
    have hyq : y q = true := by simpa [o,hop] using yq
    rcases habq with e | e <;> rw [←e] at hab <;>
      simp [hop,hab,GateOp.eval,wval_input,hxq,hyq]

theorem raw_and_pays {C : Circuit} (h : IsLeastAO G C) {v q : Fin 11}
    (hv : v.val<4) (hq : q≠v) {g : ℕ} (hg : g<C.size)
    (hand : (gateAt C g).op = GateOp.and)
    (hp : v.val ∈ (gateAt C g).inputs) (hq' : q.val ∈ (gateAt C g).inputs) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ c < C.size ∧
      Collapses C v a ∧ Collapses C v b ∧ Collapses C v c := by
  obtain ⟨j,hj,hne,hv'⟩ := second_reader h hv hq hg hq'
  apply three_collapses h _ (Or.inr ⟨g,j,hne.symm,⟨hg,hp⟩,⟨hj,hv'⟩,hand⟩)
  refine ⟨pairInput 8 9, ?_, by decide⟩
  have h8 : v ≠ (8 : Fin 11) := by
    intro e
    have hh := congrArg Fin.val e
    change v.val = 8 at hh
    omega
  have h9 : v ≠ (9 : Fin 11) := by
    intro e
    have hh := congrArg Fin.val e
    change v.val = 9 at hh
    omega
  simp [pairInput,h8,h9]

theorem missed_edge_pays {C : Circuit} (h : IsLeastAO G C) {v : Fin 11}
    (hv : v.val < 4) {g : ℕ} (hg : g < C.size)
    (hand : (gateAt C g).op = GateOp.and) (hp : v.val ∈ (gateAt C g).inputs)
    {p : Fin 11} (diff : p ≠ v) (edge : graphFun G ∅ (pairInput v p) = true)
    (miss : wval C (pairInput v p) (11+g) = false) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ c < C.size ∧
      Collapses C v a ∧ Collapses C v b ∧ Collapses C v c := by
  let x := pairInput p p
  let y := pairInput v p
  have xs : x v = false := by simp [x,pairInput,Ne.symm diff]
  have allsingle : ∀ a : Fin 11, graphFun G ∅ (pairInput a a) = false := by decide +kernel
  have hx : wval C x C.output = false := (congrFun h.2.1 x).trans (allsingle p)
  have hy : wval C y C.output = true := (congrFun h.2.1 y).trans edge
  have z : wval C x (11+g) = false := (collapse_from_zero h.1 hg hp (input_zero C v)).2 (Or.inl hand) x xs
  obtain ⟨j,hj,hp',hd⟩ := differing_reader h.1 v x y
    (by intro t ht; simp [x,y,pairInput,ht]) (output_not_raw C h v) (by rw [hx,hy]; decide)
  have ne : g ≠ j := by
    rintro rfl
    exact hd (z.trans miss.symm)
  apply three_collapses h _ (Or.inr ⟨g,j,ne,⟨hg,hp⟩,⟨hj,hp'⟩,hand⟩)
  refine ⟨pairInput 8 9, ?_, by decide⟩
  have h8 : v ≠ (8 : Fin 11) := by
    intro e
    have hh := congrArg Fin.val e
    change v.val = 8 at hh
    omega
  have h9 : v ≠ (9 : Fin 11) := by
    intro e
    have hh := congrArg Fin.val e
    change v.val = 9 at hh
    omega
  simp [pairInput,h8,h9]

end RawArm18213

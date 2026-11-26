import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21054

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 200

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 100 := ((x >>> 100) &&& ~~~x).setWidth 100

def cuts (ws : List W) : BitVec 100 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 100) ++ (0 : BitVec 100)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [(BitVec.ofNat 200 (((0xfff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat)), (BitVec.ofNat 200 (((0xfffff000 * 2^64 + 0x380e0380) * 2^64 + 0xe0380e0380e0380e) : Nat)), (BitVec.ofNat 200 (((0xfffff00000000 * 2^64 + 0x1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat)), (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff0000000000000) * 2^64 + 0xe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat)), (BitVec.ofNat 200 (((0x3ff003ff003ff000 * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat)), (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000000) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat)), (BitVec.ofNat 200 (((0xffc0000000003 * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat)), (BitVec.ofNat 200 (((0xffc00000 * 2^64 + 0x485214852) * 2^64 + 0x1485214852148521) : Nat)), (BitVec.ofNat 200 (((0xffc * 2^64 + 0x922489224) * 2^64 + 0x8922489224892248) : Nat))]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 100) (w : W) : Prop :=
  w.getLsbD (100 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 100) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (100 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (100 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 100, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 100) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 200 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 100)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 200 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 200) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 200) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 200, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 200 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 200 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 200 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 200 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 200) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 200 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (103735 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 4 × Fin 5) :=
  [(0, 0), (0, 1), (0, 2), (0, 4), (1, 0), (1, 3), (2, 0), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 5) :=
  [(0, 3), (1, 1), (1, 2), (1, 4), (2, 1), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)]

def samp (k : Fin 200) : Fin 4 × Fin 5 :=
  if k.val < 100 then negL.getD (k.val % 10) (0, 0) else posL.getD ((k.val - 100) / 10) (0, 0)

theorem input_rows : ∀ k : Fin 200,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 200, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 200) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def canon (w : List W) := w.insertionSort (fun x y => x.toNat≤y.toNat)
def beforeL : List W → List W → Bool
  | [], [] => false
  | [], _::_ => true
  | _::_, [] => false
  | a::as',b::bs => decide (a.toNat<b.toNat) || ((a==b) && beforeL as' bs)

inductive BankTree where
  | block (rows : List (List W))
  | fork (pivot : List W) (left right : BankTree)
def BankTree.contains : BankTree → List W → Bool
  | .block rows, s => rows.contains s
  | .fork p l r, s => if beforeL s p then l.contains s else r.contains s
def BankTree.rows : BankTree → List (List W)
  | .block xs => xs
  | .fork _ a b => a.rows ++ b.rows
theorem BankTree.sound (tree : BankTree) (s : List W) (h : tree.contains s=true) : s∈tree.rows := by
  induction tree with
  | block xs => simpa [BankTree.contains,BankTree.rows] using h
  | fork p l r il ir =>
    simp only [BankTree.contains] at h
    simp only [BankTree.rows,List.mem_append]
    split at h
    · exact Or.inl (il h)
    · exact Or.inr (ir h)
def advance (prev : BankTree) (ws : List W) (_ : Nat) : List W → Bool
  | [] => true
  | z::rest => !(ws.contains z) && !(prev.contains (canon (z::rest)))
def refuses (k : Nat) (prev : BankTree) (ws : List W) := !(ws==[goal] ||
  (pairs ws).any (fun (a,b,r) => dispatch (k+2-ws.length) (advance prev ws) a b r))
def Safe (k : Nat) (tree : BankTree) := ∀ ws, tree.contains ws=true → ws.Nodup →
  ¬ live basicOps goal k ws.toFinset
theorem certify (k : Nat) (prev next : BankTree) (old : Safe k prev)
    (verified : next.rows.all (refuses k prev)=true) : Safe (k+1) next := by
  intro ws hw hn h
  have miss := List.all_eq_true.mp verified ws (BankTree.sound next ws hw)
  let extra := k+2-ws.length
  have card := live_card h
  rw [List.toFinset_card_of_nodup hn] at card
  have room : extra+ws.length=k+2 := by dsimp [extra]; omega
  have eqf : (ws==[goal] || (pairs ws).any (fun (a,b,r) =>
      dispatch extra (advance prev ws) a b r))=false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    change (!(ws==[goal] || (pairs ws).any (fun (a,b,r) => dispatch extra (advance prev ws) a b r)))=true at miss
    rw [yes] at miss
    contradiction
  have impossible (yes : (ws==[goal] || (pairs ws).any (fun (a,b,r) =>
      dispatch extra (advance prev ws) a b r))=true) : False := Bool.noConfusion (yes.symm.trans eqf)
  apply impossible
  rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
  · simp [singleton_list hn done]
  · obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a::b::r)) (hset : ws.toFinset=insert a (insert b needed))
        (hop : z∈basicOps a b) : dispatch extra (advance prev ws) a b r=true := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
      have hznew : z∉kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
      have len := perm.length_eq
      simp only [List.length_cons] at len
      apply dispatch_complete (k:=k) (extra:=extra) (advance prev ws) hop hk (by omega) (by omega) (cuts_full hl)
      have pp : (canon (z::kept)).Perm (z::kept) := List.perm_insertionSort _ _
      have eqSet : (canon (z::kept)).toFinset=(z::kept).toFinset := by
        ext v; simpa only [List.mem_toFinset] using (pp.mem_iff (a:=v))
      have no : prev.contains (canon (z::kept))=false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        exact old _ yes (pp.nodup_iff.mpr hnd) (eqSet.symm ▸ hl)
      have noW : z∉ws := fun hz => hout (List.mem_toFinset.mpr hz)
      simp [advance,no,noW]
    simp only [Bool.or_eq_true,List.any_eq_true]
    right
    rcases hm with direct|sw
    · exact ⟨(a,b,r),direct,go hp hs hz⟩
    · exact ⟨(b,a,r),sw,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
def atom0 : W := (BitVec.ofNat 200 (((0xffc * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom1 : W := (BitVec.ofNat 200 (((0xffc * 2^64 + 0x922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom2 : W := (BitVec.ofNat 200 (((0xfff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom3 : W := (BitVec.ofNat 200 (((0xffc00000 * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom4 : W := (BitVec.ofNat 200 (((0xffc00000 * 2^64 + 0x485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom5 : W := (BitVec.ofNat 200 (((0xffc00ffc * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom6 : W := (BitVec.ofNat 200 (((0xffc00ffc * 2^64 + 0x922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom7 : W := (BitVec.ofNat 200 (((0xffc00fff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom8 : W := (BitVec.ofNat 200 (((0xffc00fff * 2^64 + 0xfffffff485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom9 : W := (BitVec.ofNat 200 (((0xfffff000 * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom10 : W := (BitVec.ofNat 200 (((0xfffff000 * 2^64 + 0x380e0380) * 2^64 + 0xe0380e0380e0380e) : Nat))
def atom11 : W := (BitVec.ofNat 200 (((0xfffffffc * 2^64 + 0x380e0380) * 2^64 + 0xe0380e0380e0380e) : Nat))
def atom12 : W := (BitVec.ofNat 200 (((0xfffffffc * 2^64 + 0x93a4e93a4) * 2^64 + 0xe93a4e93a4e93a4e) : Nat))
def atom13 : W := (BitVec.ofNat 200 (((0xffc0000000000 * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom14 : W := (BitVec.ofNat 200 (((0xffc0000000003 * 2^64 + 0xff00000000000000) * 2^64 + 0x0) : Nat))
def atom15 : W := (BitVec.ofNat 200 (((0xffc0000000003 * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom16 : W := (BitVec.ofNat 200 (((0xffc0000000ffc * 2^64 + 0x922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom17 : W := (BitVec.ofNat 200 (((0xffc0000000fff * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom18 : W := (BitVec.ofNat 200 (((0xffc0000000fff * 2^64 + 0xff00000b32ccb32c) * 2^64 + 0xcb32ccb32ccb32cc) : Nat))
def atom19 : W := (BitVec.ofNat 200 (((0xffc0000000fff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom20 : W := (BitVec.ofNat 200 (((0xffc00ffc00000 * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom21 : W := (BitVec.ofNat 200 (((0xffc00ffc00000 * 2^64 + 0x485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom22 : W := (BitVec.ofNat 200 (((0xffc00ffc00003 * 2^64 + 0xff00000000000000) * 2^64 + 0x0) : Nat))
def atom23 : W := (BitVec.ofNat 200 (((0xffc00ffc00003 * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom24 : W := (BitVec.ofNat 200 (((0xffc00ffc00fff * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom25 : W := (BitVec.ofNat 200 (((0xffc00ffc00fff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom26 : W := (BitVec.ofNat 200 (((0xffc00ffc00fff * 2^64 + 0xfffffff485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom27 : W := (BitVec.ofNat 200 (((0xffc00fffff003 * 2^64 + 0xff000002388e2388) * 2^64 + 0xe2388e2388e2388e) : Nat))
def atom28 : W := (BitVec.ofNat 200 (((0xffc00ffffffff * 2^64 + 0xff000002388e2388) * 2^64 + 0xe2388e2388e2388e) : Nat))
def atom29 : W := (BitVec.ofNat 200 (((0xffc00ffffffff * 2^64 + 0xff00000b3aceb3ac) * 2^64 + 0xeb3aceb3aceb3ace) : Nat))
def atom30 : W := (BitVec.ofNat 200 (((0xfffff00000000 * 2^64 + 0x1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat))
def atom31 : W := (BitVec.ofNat 200 (((0xfffff00000ffc * 2^64 + 0x1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat))
def atom32 : W := (BitVec.ofNat 200 (((0xfffff00000ffc * 2^64 + 0x9e2789e27) * 2^64 + 0x89e2789e2789e278) : Nat))
def atom33 : W := (BitVec.ofNat 200 (((0xfffff00000fff * 2^64 + 0xfffffff1c4711c47) * 2^64 + 0x11c4711c4711c471) : Nat))
def atom34 : W := (BitVec.ofNat 200 (((0xfffffffc00000 * 2^64 + 0x1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat))
def atom35 : W := (BitVec.ofNat 200 (((0xfffffffc00000 * 2^64 + 0x5c5715c57) * 2^64 + 0x15c5715c5715c571) : Nat))
def atom36 : W := (BitVec.ofNat 200 (((0xfffffffc00ffc * 2^64 + 0x9e2789e27) * 2^64 + 0x89e2789e2789e278) : Nat))
def atom37 : W := (BitVec.ofNat 200 (((0xfffffffc00fff * 2^64 + 0xfffffff5c5715c57) * 2^64 + 0x15c5715c5715c571) : Nat))
def atom38 : W := (BitVec.ofNat 200 (((0x3ff003ff003ff000 * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom39 : W := (BitVec.ofNat 200 (((0x3ff003ff003ffffc * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom40 : W := (BitVec.ofNat 200 (((0x3ff003ff003ffffc * 2^64 + 0x3ff922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom41 : W := (BitVec.ofNat 200 (((0x3ff003ff003fffff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom42 : W := (BitVec.ofNat 200 (((0x3ff003fffffff000 * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom43 : W := (BitVec.ofNat 200 (((0x3ff003fffffff000 * 2^64 + 0x3ff0380e0380) * 2^64 + 0xe0380e0380e0380e) : Nat))
def atom44 : W := (BitVec.ofNat 200 (((0x3ff003fffffff000 * 2^64 + 0x3ff485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom45 : W := (BitVec.ofNat 200 (((0x3ff003fffffffffc * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom46 : W := (BitVec.ofNat 200 (((0x3ff003fffffffffc * 2^64 + 0x3ff922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom47 : W := (BitVec.ofNat 200 (((0x3ff003fffffffffc * 2^64 + 0x3ff93a4e93a4) * 2^64 + 0xe93a4e93a4e93a4e) : Nat))
def atom48 : W := (BitVec.ofNat 200 (((0x3ff003ffffffffff * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom49 : W := (BitVec.ofNat 200 (((0x3ff003ffffffffff * 2^64 + 0xfffffff485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom50 : W := (BitVec.ofNat 200 (((0x3fffffff003ff000 * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom51 : W := (BitVec.ofNat 200 (((0x3fffffff003ff000 * 2^64 + 0x3ff1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat))
def atom52 : W := (BitVec.ofNat 200 (((0x3fffffff003ff003 * 2^64 + 0xff003ff000000000) * 2^64 + 0x0) : Nat))
def atom53 : W := (BitVec.ofNat 200 (((0x3fffffff003ff003 * 2^64 + 0xff003ff210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom54 : W := (BitVec.ofNat 200 (((0x3fffffff003ffffc * 2^64 + 0x3ff9e2789e27) * 2^64 + 0x89e2789e2789e278) : Nat))
def atom55 : W := (BitVec.ofNat 200 (((0x3ffffffffffff000 * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom56 : W := (BitVec.ofNat 200 (((0x3ffffffffffff000 * 2^64 + 0x3ff1c0701c07) * 2^64 + 0x1c0701c0701c070) : Nat))
def atom57 : W := (BitVec.ofNat 200 (((0x3ffffffffffff000 * 2^64 + 0x3ff5c5715c57) * 2^64 + 0x15c5715c5715c571) : Nat))
def atom58 : W := (BitVec.ofNat 200 (((0x3ffffffffffff003 * 2^64 + 0xff003ff000000000) * 2^64 + 0x0) : Nat))
def atom59 : W := (BitVec.ofNat 200 (((0x3ffffffffffff003 * 2^64 + 0xff003ff210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom60 : W := (BitVec.ofNat 200 (((0x3ffffffffffff003 * 2^64 + 0xff003ff2388e2388) * 2^64 + 0xe2388e2388e2388e) : Nat))
def atom61 : W := (BitVec.ofNat 200 (((0x3ffffffffffffffc * 2^64 + 0x3ff9e2789e27) * 2^64 + 0x89e2789e2789e278) : Nat))
def atom62 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom63 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000000) * 2^64 + 0xffc00000000000) * 2^64 + 0x0) : Nat))
def atom64 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000000) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom65 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000ffc) * 2^64 + 0x922489224) * 2^64 + 0x8922489224892248) : Nat))
def atom66 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000ffc) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom67 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000ffc) * 2^64 + 0xffc0096a5a96a5) * 2^64 + 0xa96a5a96a5a96a5a) : Nat))
def atom68 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc000000000000fff) * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom69 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def atom70 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00000) * 2^64 + 0x485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom71 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00000) * 2^64 + 0xffc00000000000) * 2^64 + 0x0) : Nat))
def atom72 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00000) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom73 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00ffc) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom74 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00fff) * 2^64 + 0xfffffff004010040) * 2^64 + 0x1004010040100401) : Nat))
def atom75 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000ffc00fff) * 2^64 + 0xfffffff485214852) * 2^64 + 0x1485214852148521) : Nat))
def atom76 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000fffff000) * 2^64 + 0xffc000781e0781) * 2^64 + 0xe0781e0781e0781e) : Nat))
def atom77 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000fffffffc) * 2^64 + 0xffc000781e0781) * 2^64 + 0xe0781e0781e0781e) : Nat))
def atom78 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc0000000fffffffc) * 2^64 + 0xffc0097a5e97a5) * 2^64 + 0xe97a5e97a5e97a5e) : Nat))
def atom79 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00ffc0000000000) * 2^64 + 0xffc00048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom80 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00ffc0000000003) * 2^64 + 0xff00000210842108) * 2^64 + 0x4210842108421084) : Nat))
def atom81 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00fffff00000000) * 2^64 + 0xffc001c8721c87) * 2^64 + 0x21c8721c8721c872) : Nat))
def atom82 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00fffff00000ffc) * 2^64 + 0xffc001c8721c87) * 2^64 + 0x21c8721c8721c872) : Nat))
def atom83 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00fffff00000ffc) * 2^64 + 0xffc009ea7a9ea7) * 2^64 + 0xa9ea7a9ea7a9ea7a) : Nat))
def atom84 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xc00fffffffc00000) * 2^64 + 0xffc001c8721c87) * 2^64 + 0x21c8721c8721c872) : Nat))
def atom85 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff0000000000000) * 2^64 + 0xe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat))
def atom86 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff0000000000ffc) * 2^64 + 0xe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat))
def atom87 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff0000000000ffc) * 2^64 + 0xf23c8f23c) * 2^64 + 0x8f23c8f23c8f23c8) : Nat))
def atom88 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff0000000000fff) * 2^64 + 0xfffffffe0781e078) * 2^64 + 0x1e0781e0781e0781) : Nat))
def atom89 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff00000ffc00000) * 2^64 + 0xe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat))
def atom90 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff00000ffc00000) * 2^64 + 0xe87a1e87a) * 2^64 + 0x1e87a1e87a1e87a1) : Nat))
def atom91 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff00000ffc00ffc) * 2^64 + 0xf23c8f23c) * 2^64 + 0x8f23c8f23c8f23c8) : Nat))
def atom92 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff00000ffc00fff) * 2^64 + 0xfffffffe87a1e87a) * 2^64 + 0x1e87a1e87a1e87a1) : Nat))
def atom93 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003ff003ff000) * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom94 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003ff003ff000) * 2^64 + 0x3ffe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat))
def atom95 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003ff003ff000) * 2^64 + 0xfffff000000000) * 2^64 + 0x0) : Nat))
def atom96 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003ff003ff000) * 2^64 + 0xfffff048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom97 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003ff003ffffc) * 2^64 + 0x3fff23c8f23c) * 2^64 + 0x8f23c8f23c8f23c8) : Nat))
def atom98 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0x3ff000000000) * 2^64 + 0x0) : Nat))
def atom99 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0x3ffe0380e038) * 2^64 + 0xe0380e0380e0380) : Nat))
def atom100 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0x3ffe87a1e87a) * 2^64 + 0x1e87a1e87a1e87a1) : Nat))
def atom101 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0xfffff000000000) * 2^64 + 0x0) : Nat))
def atom102 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0xfffff048120481) * 2^64 + 0x2048120481204812) : Nat))
def atom103 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffff000) * 2^64 + 0xfffff0781e0781) * 2^64 + 0xe0781e0781e0781e) : Nat))
def atom104 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfff003fffffffffc) * 2^64 + 0x3fff23c8f23c) * 2^64 + 0x8f23c8f23c8f23c8) : Nat))
def atom105 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffc0000000003) * 2^64 + 0xff00000e1384e138) * 2^64 + 0x4e1384e1384e1384) : Nat))
def atom106 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffc0000000fff) * 2^64 + 0xff00000e1384e138) * 2^64 + 0x4e1384e1384e1384) : Nat))
def atom107 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffc0000000fff) * 2^64 + 0xff00000f33ccf33c) * 2^64 + 0xcf33ccf33ccf33cc) : Nat))
def atom108 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffc00ffc00003) * 2^64 + 0xff00000e1384e138) * 2^64 + 0x4e1384e1384e1384) : Nat))
def atom109 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xffffffff003ff000) * 2^64 + 0xfffff1c8721c87) * 2^64 + 0x21c8721c8721c872) : Nat))
def atom110 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xffffffff003ff003) * 2^64 + 0xff003ffe1384e138) * 2^64 + 0x4e1384e1384e1384) : Nat))
def atom111 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffffffffff000) * 2^64 + 0xfffff1c8721c87) * 2^64 + 0x21c8721c8721c872) : Nat))
def atom112 : W := (BitVec.ofNat 200 ((((0xff * 2^64 + 0xfffffffffffff003) * 2^64 + 0xff003ffe1384e138) * 2^64 + 0x4e1384e1384e1384) : Nat))
noncomputable def t0_0 : BankTree := .block []
theorem safe0 : Safe 0 t0_0 := by intro ws h; simp [t0_0,BankTree.contains] at h
noncomputable def t1_0 : BankTree := .block []
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t1_0 : t1_0.rows.all (refuses 0 t0_0)=true := by decide +kernel
theorem safe1 : Safe 1 t1_0 := certify 0 t0_0 t1_0 safe0 ok_t1_0
noncomputable def t2_0 : BankTree := .block []
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t2_0 : t2_0.rows.all (refuses 1 t1_0)=true := by decide +kernel
theorem safe2 : Safe 2 t2_0 := certify 1 t1_0 t2_0 safe1 ok_t2_0
noncomputable def t3_1 : BankTree := .block [[atom1,atom2,atom111,atom112],[atom1,atom48,atom81,atom112],[atom1,atom48,atom105,atom111],[atom2,atom15,atom32,atom101],[atom2,atom15,atom83,atom98],[atom2,atom42,atom79,atom107],[atom2,atom42,atom80,atom83]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t3_1 : t3_1.rows.all (refuses 2 t2_0)=true := by decide +kernel
noncomputable def t3_2 : BankTree := .block [[atom2,atom42,atom81,atom106],[atom2,atom42,atom82,atom105],[atom2,atom45,atom81,atom105],[atom2,atom55,atom64,atom107],[atom2,atom58,atom64,atom87],[atom15,atom42,atom68,atom83],[atom19,atom42,atom64,atom107],[atom46,atom48,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t3_2 : t3_2.rows.all (refuses 2 t2_0)=true := by decide +kernel
noncomputable def t3_0 : BankTree := .fork [atom2,atom42,atom81,atom106] t3_1 t3_2
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t3_0 : t3_0.rows.all (refuses 2 t2_0)=true := by simp only [t3_0,BankTree.rows,List.all_append,ok_t3_1,ok_t3_2,Bool.true_and]
theorem safe3 : Safe 3 t3_0 := certify 2 t2_0 t3_0 safe2 ok_t3_0
noncomputable def t4_4 : BankTree := .block [[atom0,atom2,atom42,atom81,atom105],[atom1,atom2,atom3,atom109,atom110],[atom1,atom2,atom15,atom30,atom101],[atom1,atom2,atom15,atom81,atom98],[atom1,atom2,atom15,atom99,atom111],[atom1,atom2,atom27,atom35,atom95],[atom1,atom2,atom30,atom102,atom112],[atom1,atom2,atom38,atom84,atom108],[atom1,atom2,atom42,atom79,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_4 : t4_4.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_5 : BankTree := .block [[atom1,atom2,atom42,atom80,atom81],[atom1,atom2,atom42,atom81,atom105],[atom1,atom2,atom42,atom81,atom108],[atom1,atom2,atom42,atom81,atom110],[atom1,atom2,atom42,atom81,atom112],[atom1,atom2,atom42,atom84,atom105],[atom1,atom2,atom42,atom105,atom109],[atom1,atom2,atom42,atom105,atom111],[atom1,atom2,atom52,atom76,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_5 : t4_5.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_3 : BankTree := .fork [atom1,atom2,atom42,atom80,atom81] t4_4 t4_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_3 : t4_3.rows.all (refuses 3 t3_0)=true := by simp only [t4_3,BankTree.rows,List.all_append,ok_t4_4,ok_t4_5,Bool.true_and]
noncomputable def t4_7 : BankTree := .block [[atom1,atom2,atom55,atom64,atom105],[atom1,atom2,atom56,atom64,atom112],[atom1,atom2,atom58,atom64,atom85],[atom1,atom2,atom59,atom85,atom111],[atom1,atom3,atom41,atom81,atom110],[atom1,atom3,atom41,atom105,atom109],[atom1,atom7,atom38,atom81,atom108],[atom1,atom7,atom38,atom84,atom105],[atom1,atom7,atom42,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_7 : t4_7.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_8 : BankTree := .block [[atom1,atom8,atom15,atom30,atom101],[atom1,atom8,atom27,atom30,atom95],[atom1,atom8,atom52,atom76,atom85],[atom1,atom8,atom58,atom64,atom85],[atom1,atom15,atom42,atom68,atom81],[atom1,atom15,atom48,atom81,atom99],[atom1,atom15,atom48,atom85,atom111],[atom1,atom19,atom42,atom64,atom105],[atom1,atom30,atom48,atom64,atom112],[atom1,atom30,atom48,atom102,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_8 : t4_8.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_6 : BankTree := .fork [atom1,atom8,atom15,atom30,atom101] t4_7 t4_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_6 : t4_6.rows.all (refuses 3 t3_0)=true := by simp only [t4_6,BankTree.rows,List.all_append,ok_t4_7,ok_t4_8,Bool.true_and]
noncomputable def t4_2 : BankTree := .fork [atom1,atom2,atom55,atom64,atom105] t4_3 t4_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_2 : t4_2.rows.all (refuses 3 t3_0)=true := by simp only [t4_2,BankTree.rows,List.all_append,ok_t4_3,ok_t4_6,Bool.true_and]
noncomputable def t4_11 : BankTree := .block [[atom1,atom41,atom42,atom81,atom105],[atom1,atom42,atom48,atom81,atom105],[atom1,atom48,atom56,atom64,atom105],[atom1,atom48,atom59,atom81,atom85],[atom2,atom3,atom15,atom32,atom95],[atom2,atom3,atom15,atom83,atom93],[atom2,atom3,atom38,atom79,atom107],[atom2,atom3,atom38,atom80,atom83],[atom2,atom3,atom38,atom81,atom106]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_11 : t4_11.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_12 : BankTree := .block [[atom2,atom3,atom38,atom82,atom105],[atom2,atom3,atom39,atom81,atom105],[atom2,atom3,atom50,atom64,atom107],[atom2,atom3,atom52,atom64,atom87],[atom2,atom4,atom12,atom109,atom110],[atom2,atom5,atom38,atom81,atom105],[atom2,atom6,atom42,atom81,atom105],[atom2,atom12,atom42,atom81,atom105],[atom2,atom13,atom42,atom64,atom107]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_12 : t4_12.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_10 : BankTree := .fork [atom2,atom3,atom38,atom82,atom105] t4_11 t4_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_10 : t4_10.rows.all (refuses 3 t3_0)=true := by simp only [t4_10,BankTree.rows,List.all_append,ok_t4_11,ok_t4_12,Bool.true_and]
noncomputable def t4_14 : BankTree := .block [[atom2,atom14,atom42,atom64,atom87],[atom2,atom15,atom30,atom67,atom98],[atom2,atom15,atom30,atom78,atom98],[atom2,atom15,atom30,atom102,atom104],[atom2,atom15,atom32,atom38,atom71],[atom2,atom15,atom32,atom42,atom63],[atom2,atom15,atom32,atom64,atom98],[atom2,atom15,atom32,atom76,atom98],[atom2,atom15,atom32,atom99,atom102]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_14 : t4_14.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_15 : BankTree := .block [[atom2,atom15,atom32,atom100,atom103],[atom2,atom15,atom38,atom69,atom83],[atom2,atom15,atom42,atom62,atom83],[atom2,atom15,atom42,atom79,atom87],[atom2,atom15,atom42,atom81,atom86],[atom2,atom15,atom42,atom82,atom85],[atom2,atom15,atom45,atom81,atom85],[atom2,atom15,atom55,atom64,atom87],[atom2,atom17,atom42,atom81,atom85],[atom2,atom18,atom42,atom79,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_15 : t4_15.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_13 : BankTree := .fork [atom2,atom15,atom32,atom100,atom103] t4_14 t4_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_13 : t4_13.rows.all (refuses 3 t3_0)=true := by simp only [t4_13,BankTree.rows,List.all_append,ok_t4_14,ok_t4_15,Bool.true_and]
noncomputable def t4_9 : BankTree := .fork [atom2,atom14,atom42,atom64,atom87] t4_10 t4_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_9 : t4_9.rows.all (refuses 3 t3_0)=true := by simp only [t4_9,BankTree.rows,List.all_append,ok_t4_10,ok_t4_13,Bool.true_and]
noncomputable def t4_1 : BankTree := .fork [atom1,atom41,atom42,atom81,atom105] t4_2 t4_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_1 : t4_1.rows.all (refuses 3 t3_0)=true := by simp only [t4_1,BankTree.rows,List.all_append,ok_t4_2,ok_t4_9,Bool.true_and]
noncomputable def t4_19 : BankTree := .block [[atom2,atom18,atom42,atom81,atom105],[atom2,atom18,atom50,atom76,atom90],[atom2,atom18,atom55,atom64,atom85],[atom2,atom20,atom38,atom64,atom107],[atom2,atom22,atom38,atom64,atom87],[atom2,atom27,atom35,atom67,atom93],[atom2,atom27,atom35,atom96,atom97],[atom2,atom27,atom55,atom64,atom87],[atom2,atom29,atom55,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_19 : t4_19.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_20 : BankTree := .block [[atom2,atom30,atom42,atom64,atom106],[atom2,atom30,atom42,atom66,atom105],[atom2,atom30,atom42,atom67,atom80],[atom2,atom30,atom45,atom64,atom105],[atom2,atom30,atom46,atom102,atom105],[atom2,atom30,atom59,atom87,atom102],[atom2,atom31,atom42,atom64,atom105],[atom2,atom32,atom42,atom64,atom80],[atom2,atom32,atom42,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_20 : t4_20.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_18 : BankTree := .fork [atom2,atom30,atom42,atom64,atom106] t4_19 t4_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_18 : t4_18.rows.all (refuses 3 t3_0)=true := by simp only [t4_18,BankTree.rows,List.all_append,ok_t4_19,ok_t4_20,Bool.true_and]
noncomputable def t4_22 : BankTree := .block [[atom2,atom32,atom59,atom85,atom102],[atom2,atom40,atom42,atom81,atom105],[atom2,atom42,atom46,atom81,atom105],[atom2,atom42,atom67,atom81,atom105],[atom2,atom42,atom81,atom83,atom105],[atom2,atom42,atom81,atom87,atom105],[atom2,atom42,atom81,atom105,atom107],[atom2,atom44,atom47,atom81,atom105],[atom2,atom46,atom59,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_22 : t4_22.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_23 : BankTree := .block [[atom2,atom53,atom54,atom76,atom90],[atom2,atom56,atom59,atom64,atom87],[atom2,atom57,atom60,atom64,atom87],[atom2,atom59,atom61,atom64,atom85],[atom3,atom15,atom38,atom68,atom83],[atom3,atom19,atom38,atom64,atom107],[atom3,atom40,atom41,atom81,atom105],[atom4,atom12,atom41,atom81,atom110],[atom4,atom12,atom41,atom105,atom109],[atom4,atom41,atom47,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_23 : t4_23.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_21 : BankTree := .fork [atom2,atom53,atom54,atom76,atom90] t4_22 t4_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_21 : t4_21.rows.all (refuses 3 t3_0)=true := by simp only [t4_21,BankTree.rows,List.all_append,ok_t4_22,ok_t4_23,Bool.true_and]
noncomputable def t4_17 : BankTree := .fork [atom2,atom32,atom59,atom85,atom102] t4_18 t4_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_17 : t4_17.rows.all (refuses 3 t3_0)=true := by simp only [t4_17,BankTree.rows,List.all_append,ok_t4_18,ok_t4_21,Bool.true_and]
noncomputable def t4_26 : BankTree := .block [[atom6,atom7,atom38,atom81,atom105],[atom7,atom12,atom38,atom81,atom105],[atom8,atom12,atom15,atom30,atom95],[atom8,atom12,atom52,atom64,atom85],[atom8,atom15,atom30,atom78,atom93],[atom8,atom18,atom50,atom76,atom85],[atom8,atom27,atom30,atom67,atom93],[atom8,atom29,atom50,atom64,atom85],[atom15,atom19,atom42,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_26 : t4_26.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_27 : BankTree := .block [[atom15,atom30,atom38,atom74,atom78],[atom15,atom30,atom38,atom75,atom78],[atom15,atom30,atom42,atom67,atom68],[atom15,atom30,atom48,atom64,atom104],[atom15,atom30,atom48,atom87,atom102],[atom15,atom32,atom38,atom74,atom76],[atom15,atom32,atom41,atom90,atom103],[atom15,atom32,atom42,atom64,atom68],[atom15,atom32,atom48,atom64,atom99],[atom15,atom32,atom48,atom85,atom102]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_27 : t4_27.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_25 : BankTree := .fork [atom15,atom30,atom38,atom74,atom78] t4_26 t4_27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_25 : t4_25.rows.all (refuses 3 t3_0)=true := by simp only [t4_25,BankTree.rows,List.all_append,ok_t4_26,ok_t4_27,Bool.true_and]
noncomputable def t4_29 : BankTree := .block [[atom15,atom41,atom54,atom76,atom90],[atom15,atom46,atom48,atom81,atom85],[atom15,atom48,atom56,atom64,atom87],[atom15,atom48,atom61,atom64,atom85],[atom18,atom19,atom38,atom76,atom90],[atom18,atom19,atom42,atom64,atom85],[atom18,atom26,atom38,atom76,atom85],[atom25,atom27,atom38,atom64,atom87],[atom25,atom29,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_29 : t4_29.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_30 : BankTree := .block [[atom26,atom29,atom38,atom64,atom85],[atom27,atom30,atom38,atom67,atom75],[atom27,atom35,atom38,atom67,atom68],[atom27,atom35,atom41,atom64,atom97],[atom27,atom35,atom41,atom87,atom96],[atom30,atom46,atom48,atom64,atom105],[atom30,atom48,atom59,atom64,atom87],[atom32,atom41,atom53,atom76,atom90],[atom32,atom48,atom59,atom64,atom85],[atom35,atom41,atom60,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_30 : t4_30.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_28 : BankTree := .fork [atom26,atom29,atom38,atom64,atom85] t4_29 t4_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_28 : t4_28.rows.all (refuses 3 t3_0)=true := by simp only [t4_28,BankTree.rows,List.all_append,ok_t4_29,ok_t4_30,Bool.true_and]
noncomputable def t4_24 : BankTree := .fork [atom15,atom41,atom54,atom76,atom90] t4_25 t4_28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_24 : t4_24.rows.all (refuses 3 t3_0)=true := by simp only [t4_24,BankTree.rows,List.all_append,ok_t4_25,ok_t4_28,Bool.true_and]
noncomputable def t4_16 : BankTree := .fork [atom6,atom7,atom38,atom81,atom105] t4_17 t4_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_16 : t4_16.rows.all (refuses 3 t3_0)=true := by simp only [t4_16,BankTree.rows,List.all_append,ok_t4_17,ok_t4_24,Bool.true_and]
noncomputable def t4_0 : BankTree := .fork [atom2,atom18,atom42,atom81,atom105] t4_1 t4_16
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_0 : t4_0.rows.all (refuses 3 t3_0)=true := by simp only [t4_0,BankTree.rows,List.all_append,ok_t4_1,ok_t4_16,Bool.true_and]
theorem safe4 : Safe 4 t4_0 := certify 3 t3_0 t4_0 safe3 ok_t4_0
noncomputable def t5_6 : BankTree := .block [[atom0,atom2,atom3,atom38,atom81,atom105],[atom0,atom2,atom15,atom42,atom81,atom85],[atom0,atom2,atom30,atom42,atom64,atom105],[atom1,atom2,atom3,atom15,atom30,atom95],[atom1,atom2,atom3,atom15,atom81,atom93],[atom1,atom2,atom3,atom15,atom94,atom109],[atom1,atom2,atom3,atom30,atom96,atom110]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_6 : t5_6.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_7 : BankTree := .block [[atom1,atom2,atom3,atom38,atom79,atom105],[atom1,atom2,atom3,atom38,atom80,atom81],[atom1,atom2,atom3,atom38,atom81,atom105],[atom1,atom2,atom3,atom38,atom81,atom108],[atom1,atom2,atom3,atom38,atom81,atom110],[atom1,atom2,atom3,atom38,atom84,atom105],[atom1,atom2,atom3,atom38,atom105,atom109],[atom1,atom2,atom3,atom42,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_7 : t5_7.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_5 : BankTree := .fork [atom1,atom2,atom3,atom38,atom79,atom105] t5_6 t5_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_5 : t5_5.rows.all (refuses 4 t4_0)=true := by simp only [t5_5,BankTree.rows,List.all_append,ok_t5_6,ok_t5_7,Bool.true_and]
noncomputable def t5_9 : BankTree := .block [[atom1,atom2,atom3,atom50,atom64,atom105],[atom1,atom2,atom3,atom51,atom64,atom110],[atom1,atom2,atom3,atom52,atom64,atom85],[atom1,atom2,atom3,atom53,atom85,atom109],[atom1,atom2,atom4,atom10,atom109,atom110],[atom1,atom2,atom4,atom27,atom30,atom95],[atom1,atom2,atom4,atom42,atom81,atom105],[atom1,atom2,atom4,atom52,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_9 : t5_9.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_10 : BankTree := .block [[atom1,atom2,atom9,atom38,atom81,atom105],[atom1,atom2,atom10,atom15,atom35,atom95],[atom1,atom2,atom10,atom42,atom81,atom105],[atom1,atom2,atom10,atom52,atom64,atom90],[atom1,atom2,atom13,atom42,atom64,atom105],[atom1,atom2,atom14,atom38,atom76,atom90],[atom1,atom2,atom14,atom42,atom64,atom85],[atom1,atom2,atom15,atom30,atom38,atom71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_10 : t5_10.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_8 : BankTree := .fork [atom1,atom2,atom9,atom38,atom81,atom105] t5_9 t5_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_8 : t5_8.rows.all (refuses 4 t4_0)=true := by simp only [t5_8,BankTree.rows,List.all_append,ok_t5_9,ok_t5_10,Bool.true_and]
noncomputable def t5_4 : BankTree := .fork [atom1,atom2,atom3,atom50,atom64,atom105] t5_5 t5_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_4 : t5_4.rows.all (refuses 4 t4_0)=true := by simp only [t5_4,BankTree.rows,List.all_append,ok_t5_5,ok_t5_8,Bool.true_and]
noncomputable def t5_13 : BankTree := .block [[atom1,atom2,atom15,atom30,atom42,atom63],[atom1,atom2,atom15,atom30,atom64,atom98],[atom1,atom2,atom15,atom30,atom76,atom98],[atom1,atom2,atom15,atom30,atom99,atom102],[atom1,atom2,atom15,atom30,atom100,atom103],[atom1,atom2,atom15,atom38,atom69,atom81],[atom1,atom2,atom15,atom38,atom84,atom89]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_13 : t5_13.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_14 : BankTree := .block [[atom1,atom2,atom15,atom42,atom62,atom81],[atom1,atom2,atom15,atom42,atom79,atom85],[atom1,atom2,atom15,atom42,atom81,atom85],[atom1,atom2,atom15,atom42,atom81,atom88],[atom1,atom2,atom15,atom42,atom81,atom89],[atom1,atom2,atom15,atom42,atom81,atom94],[atom1,atom2,atom15,atom42,atom81,atom99],[atom1,atom2,atom15,atom42,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_14 : t5_14.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_12 : BankTree := .fork [atom1,atom2,atom15,atom42,atom62,atom81] t5_13 t5_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_12 : t5_12.rows.all (refuses 4 t4_0)=true := by simp only [t5_12,BankTree.rows,List.all_append,ok_t5_13,ok_t5_14,Bool.true_and]
noncomputable def t5_16 : BankTree := .block [[atom1,atom2,atom15,atom42,atom84,atom85],[atom1,atom2,atom15,atom42,atom85,atom109],[atom1,atom2,atom15,atom42,atom85,atom111],[atom1,atom2,atom15,atom50,atom76,atom90],[atom1,atom2,atom15,atom55,atom64,atom85],[atom1,atom2,atom15,atom56,atom64,atom99],[atom1,atom2,atom20,atom38,atom64,atom105],[atom1,atom2,atom22,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_16 : t5_16.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_17 : BankTree := .block [[atom1,atom2,atom23,atom38,atom84,atom85],[atom1,atom2,atom23,atom42,atom81,atom85],[atom1,atom2,atom27,atom35,atom38,atom63],[atom1,atom2,atom27,atom35,atom64,atom93],[atom1,atom2,atom27,atom35,atom94,atom96],[atom1,atom2,atom27,atom55,atom64,atom85],[atom1,atom2,atom30,atom38,atom72,atom108],[atom1,atom2,atom30,atom42,atom64,atom80]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_17 : t5_17.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_15 : BankTree := .fork [atom1,atom2,atom23,atom38,atom84,atom85] t5_16 t5_17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_15 : t5_15.rows.all (refuses 4 t4_0)=true := by simp only [t5_15,BankTree.rows,List.all_append,ok_t5_16,ok_t5_17,Bool.true_and]
noncomputable def t5_11 : BankTree := .fork [atom1,atom2,atom15,atom42,atom84,atom85] t5_12 t5_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_11 : t5_11.rows.all (refuses 4 t4_0)=true := by simp only [t5_11,BankTree.rows,List.all_append,ok_t5_12,ok_t5_15,Bool.true_and]
noncomputable def t5_3 : BankTree := .fork [atom1,atom2,atom15,atom30,atom42,atom63] t5_4 t5_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_3 : t5_3.rows.all (refuses 4 t4_0)=true := by simp only [t5_3,BankTree.rows,List.all_append,ok_t5_4,ok_t5_11,Bool.true_and]
noncomputable def t5_21 : BankTree := .block [[atom1,atom2,atom30,atom42,atom64,atom105],[atom1,atom2,atom30,atom42,atom64,atom108],[atom1,atom2,atom30,atom42,atom64,atom110],[atom1,atom2,atom30,atom42,atom64,atom112],[atom1,atom2,atom30,atom42,atom72,atom105],[atom1,atom2,atom30,atom42,atom81,atom105],[atom1,atom2,atom30,atom42,atom96,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_21 : t5_21.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_22 : BankTree := .block [[atom1,atom2,atom30,atom42,atom102,atom105],[atom1,atom2,atom30,atom59,atom85,atom102],[atom1,atom2,atom33,atom42,atom64,atom105],[atom1,atom2,atom34,atom38,atom64,atom108],[atom1,atom2,atom34,atom42,atom64,atom105],[atom1,atom2,atom38,atom42,atom81,atom105],[atom1,atom2,atom42,atom51,atom64,atom105],[atom1,atom2,atom42,atom53,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_22 : t5_22.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_20 : BankTree := .fork [atom1,atom2,atom30,atom42,atom102,atom105] t5_21 t5_22
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_20 : t5_20.rows.all (refuses 4 t4_0)=true := by simp only [t5_20,BankTree.rows,List.all_append,ok_t5_21,ok_t5_22,Bool.true_and]
noncomputable def t5_24 : BankTree := .block [[atom1,atom2,atom42,atom56,atom64,atom105],[atom1,atom2,atom42,atom59,atom81,atom85],[atom1,atom2,atom42,atom64,atom81,atom105],[atom1,atom2,atom42,atom81,atom85,atom105],[atom1,atom2,atom42,atom81,atom105],[atom1,atom2,atom43,atom44,atom81,atom105],[atom1,atom2,atom51,atom53,atom76,atom90],[atom1,atom2,atom56,atom59,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_24 : t5_24.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_25 : BankTree := .block [[atom1,atom2,atom57,atom60,atom64,atom85],[atom1,atom3,atom7,atom38,atom81,atom105],[atom1,atom3,atom15,atom38,atom68,atom81],[atom1,atom3,atom15,atom41,atom81,atom94],[atom1,atom3,atom15,atom41,atom85,atom109],[atom1,atom3,atom19,atom38,atom64,atom105],[atom1,atom3,atom30,atom41,atom64,atom110],[atom1,atom3,atom30,atom41,atom96,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_25 : t5_25.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_23 : BankTree := .fork [atom1,atom2,atom57,atom60,atom64,atom85] t5_24 t5_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_23 : t5_23.rows.all (refuses 4 t4_0)=true := by simp only [t5_23,BankTree.rows,List.all_append,ok_t5_24,ok_t5_25,Bool.true_and]
noncomputable def t5_19 : BankTree := .fork [atom1,atom2,atom42,atom56,atom64,atom105] t5_20 t5_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_19 : t5_19.rows.all (refuses 4 t4_0)=true := by simp only [t5_19,BankTree.rows,List.all_append,ok_t5_20,ok_t5_23,Bool.true_and]
noncomputable def t5_28 : BankTree := .block [[atom1,atom3,atom38,atom41,atom81,atom105],[atom1,atom3,atom41,atom51,atom64,atom105],[atom1,atom3,atom41,atom53,atom81,atom85],[atom1,atom4,atom10,atom41,atom81,atom110],[atom1,atom4,atom10,atom41,atom105,atom109],[atom1,atom4,atom41,atom43,atom81,atom105],[atom1,atom7,atom10,atom38,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_28 : t5_28.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_29 : BankTree := .block [[atom1,atom7,atom15,atom38,atom81,atom89],[atom1,atom7,atom15,atom38,atom84,atom85],[atom1,atom7,atom15,atom42,atom81,atom85],[atom1,atom7,atom23,atom38,atom81,atom85],[atom1,atom7,atom30,atom38,atom64,atom108],[atom1,atom7,atom30,atom38,atom72,atom105],[atom1,atom7,atom30,atom42,atom64,atom105],[atom1,atom7,atom34,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_29 : t5_29.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_27 : BankTree := .fork [atom1,atom7,atom15,atom38,atom81,atom89] t5_28 t5_29
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_27 : t5_27.rows.all (refuses 4 t4_0)=true := by simp only [t5_27,BankTree.rows,List.all_append,ok_t5_28,ok_t5_29,Bool.true_and]
noncomputable def t5_31 : BankTree := .block [[atom1,atom8,atom10,atom15,atom30,atom95],[atom1,atom8,atom10,atom52,atom64,atom85],[atom1,atom8,atom14,atom38,atom76,atom85],[atom1,atom8,atom15,atom30,atom38,atom71],[atom1,atom8,atom15,atom30,atom76,atom93],[atom1,atom8,atom15,atom30,atom94,atom103],[atom1,atom8,atom15,atom50,atom76,atom85],[atom1,atom8,atom15,atom51,atom76,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_31 : t5_31.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_32 : BankTree := .block [[atom1,atom8,atom22,atom38,atom64,atom85],[atom1,atom8,atom27,atom30,atom38,atom63],[atom1,atom8,atom27,atom30,atom64,atom93],[atom1,atom8,atom27,atom30,atom94,atom96],[atom1,atom8,atom27,atom50,atom64,atom85],[atom1,atom8,atom27,atom51,atom64,atom94],[atom1,atom8,atom51,atom53,atom76,atom85],[atom1,atom8,atom51,atom60,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_32 : t5_32.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_30 : BankTree := .fork [atom1,atom8,atom22,atom38,atom64,atom85] t5_31 t5_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_30 : t5_30.rows.all (refuses 4 t4_0)=true := by simp only [t5_30,BankTree.rows,List.all_append,ok_t5_31,ok_t5_32,Bool.true_and]
noncomputable def t5_26 : BankTree := .fork [atom1,atom8,atom10,atom15,atom30,atom95] t5_27 t5_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_26 : t5_26.rows.all (refuses 4 t4_0)=true := by simp only [t5_26,BankTree.rows,List.all_append,ok_t5_27,ok_t5_30,Bool.true_and]
noncomputable def t5_18 : BankTree := .fork [atom1,atom3,atom38,atom41,atom81,atom105] t5_19 t5_26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_18 : t5_18.rows.all (refuses 4 t4_0)=true := by simp only [t5_18,BankTree.rows,List.all_append,ok_t5_19,ok_t5_26,Bool.true_and]
noncomputable def t5_2 : BankTree := .fork [atom1,atom2,atom30,atom42,atom64,atom105] t5_3 t5_18
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_2 : t5_2.rows.all (refuses 4 t4_0)=true := by simp only [t5_2,BankTree.rows,List.all_append,ok_t5_3,ok_t5_18,Bool.true_and]
noncomputable def t5_37 : BankTree := .block [[atom1,atom15,atom19,atom38,atom76,atom90],[atom1,atom15,atom19,atom42,atom64,atom85],[atom1,atom15,atom26,atom38,atom76,atom85],[atom1,atom15,atom30,atom38,atom74,atom76],[atom1,atom15,atom30,atom38,atom75,atom76],[atom1,atom15,atom30,atom41,atom90,atom103],[atom1,atom15,atom30,atom42,atom64,atom68]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_37 : t5_37.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_38 : BankTree := .block [[atom1,atom15,atom30,atom48,atom64,atom99],[atom1,atom15,atom30,atom48,atom85,atom102],[atom1,atom15,atom30,atom49,atom85,atom103],[atom1,atom15,atom33,atom38,atom76,atom92],[atom1,atom15,atom33,atom42,atom64,atom88],[atom1,atom15,atom37,atom38,atom76,atom92],[atom1,atom15,atom41,atom42,atom81,atom85],[atom1,atom15,atom41,atom51,atom76,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_38 : t5_38.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_36 : BankTree := .fork [atom1,atom15,atom30,atom48,atom64,atom99] t5_37 t5_38
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_36 : t5_36.rows.all (refuses 4 t4_0)=true := by simp only [t5_36,BankTree.rows,List.all_append,ok_t5_37,ok_t5_38,Bool.true_and]
noncomputable def t5_40 : BankTree := .block [[atom1,atom15,atom42,atom48,atom81,atom85],[atom1,atom15,atom48,atom56,atom64,atom85],[atom1,atom25,atom27,atom38,atom64,atom85],[atom1,atom26,atom27,atom38,atom64,atom85],[atom1,atom27,atom30,atom38,atom64,atom75],[atom1,atom27,atom30,atom49,atom85,atom96],[atom1,atom27,atom35,atom38,atom64,atom68],[atom1,atom27,atom35,atom41,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_40 : t5_40.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_41 : BankTree := .block [[atom1,atom27,atom35,atom41,atom85,atom96],[atom1,atom27,atom37,atom38,atom64,atom88],[atom1,atom27,atom37,atom38,atom64,atom92],[atom1,atom30,atom41,atom42,atom64,atom105],[atom1,atom30,atom41,atom53,atom76,atom90],[atom1,atom30,atom42,atom48,atom64,atom105],[atom1,atom30,atom48,atom59,atom64,atom85],[atom1,atom30,atom49,atom53,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_41 : t5_41.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_39 : BankTree := .fork [atom1,atom27,atom35,atom41,atom85,atom96] t5_40 t5_41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_39 : t5_39.rows.all (refuses 4 t4_0)=true := by simp only [t5_39,BankTree.rows,List.all_append,ok_t5_40,ok_t5_41,Bool.true_and]
noncomputable def t5_35 : BankTree := .fork [atom1,atom15,atom42,atom48,atom81,atom85] t5_36 t5_39
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_35 : t5_35.rows.all (refuses 4 t4_0)=true := by simp only [t5_35,BankTree.rows,List.all_append,ok_t5_36,ok_t5_39,Bool.true_and]
noncomputable def t5_44 : BankTree := .block [[atom1,atom30,atom49,atom60,atom64,atom85],[atom1,atom35,atom41,atom60,atom64,atom85],[atom2,atom3,atom6,atom38,atom81,atom105],[atom2,atom3,atom12,atom38,atom81,atom105],[atom2,atom3,atom13,atom38,atom64,atom107],[atom2,atom3,atom14,atom38,atom64,atom87],[atom2,atom3,atom15,atom30,atom67,atom93]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_44 : t5_44.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_45 : BankTree := .block [[atom2,atom3,atom15,atom30,atom96,atom97],[atom2,atom3,atom15,atom32,atom38,atom63],[atom2,atom3,atom15,atom32,atom64,atom93],[atom2,atom3,atom15,atom32,atom94,atom96],[atom2,atom3,atom15,atom38,atom62,atom83],[atom2,atom3,atom15,atom38,atom79,atom87],[atom2,atom3,atom15,atom38,atom81,atom86],[atom2,atom3,atom15,atom38,atom82,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_45 : t5_45.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_43 : BankTree := .fork [atom2,atom3,atom15,atom30,atom96,atom97] t5_44 t5_45
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_43 : t5_43.rows.all (refuses 4 t4_0)=true := by simp only [t5_43,BankTree.rows,List.all_append,ok_t5_44,ok_t5_45,Bool.true_and]
noncomputable def t5_47 : BankTree := .block [[atom2,atom3,atom15,atom39,atom81,atom85],[atom2,atom3,atom15,atom50,atom64,atom87],[atom2,atom3,atom17,atom38,atom81,atom85],[atom2,atom3,atom18,atom38,atom79,atom85],[atom2,atom3,atom18,atom38,atom81,atom105],[atom2,atom3,atom18,atom50,atom64,atom85],[atom2,atom3,atom30,atom38,atom64,atom106],[atom2,atom3,atom30,atom38,atom66,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_47 : t5_47.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_48 : BankTree := .block [[atom2,atom3,atom30,atom38,atom67,atom80],[atom2,atom3,atom30,atom39,atom64,atom105],[atom2,atom3,atom30,atom40,atom96,atom105],[atom2,atom3,atom30,atom53,atom87,atom96],[atom2,atom3,atom31,atom38,atom64,atom105],[atom2,atom3,atom32,atom38,atom64,atom80],[atom2,atom3,atom32,atom38,atom81,atom105],[atom2,atom3,atom32,atom53,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_48 : t5_48.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_46 : BankTree := .fork [atom2,atom3,atom30,atom38,atom67,atom80] t5_47 t5_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_46 : t5_46.rows.all (refuses 4 t4_0)=true := by simp only [t5_46,BankTree.rows,List.all_append,ok_t5_47,ok_t5_48,Bool.true_and]
noncomputable def t5_42 : BankTree := .fork [atom2,atom3,atom15,atom39,atom81,atom85] t5_43 t5_46
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_42 : t5_42.rows.all (refuses 4 t4_0)=true := by simp only [t5_42,BankTree.rows,List.all_append,ok_t5_43,ok_t5_46,Bool.true_and]
noncomputable def t5_34 : BankTree := .fork [atom1,atom30,atom49,atom60,atom64,atom85] t5_35 t5_42
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_34 : t5_34.rows.all (refuses 4 t4_0)=true := by simp only [t5_34,BankTree.rows,List.all_append,ok_t5_35,ok_t5_42,Bool.true_and]
noncomputable def t5_52 : BankTree := .block [[atom2,atom3,atom38,atom40,atom81,atom105],[atom2,atom3,atom38,atom67,atom81,atom105],[atom2,atom3,atom38,atom81,atom83,atom105],[atom2,atom3,atom38,atom81,atom87,atom105],[atom2,atom3,atom38,atom81,atom105,atom107],[atom2,atom3,atom40,atom53,atom81,atom85],[atom2,atom3,atom51,atom53,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_52 : t5_52.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_53 : BankTree := .block [[atom2,atom3,atom53,atom54,atom64,atom85],[atom2,atom4,atom6,atom38,atom81,atom105],[atom2,atom4,atom10,atom15,atom32,atom95],[atom2,atom4,atom10,atom15,atom83,atom93],[atom2,atom4,atom10,atom38,atom79,atom107],[atom2,atom4,atom10,atom38,atom80,atom83],[atom2,atom4,atom10,atom38,atom81,atom106],[atom2,atom4,atom10,atom38,atom82,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_53 : t5_53.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_51 : BankTree := .fork [atom2,atom3,atom53,atom54,atom64,atom85] t5_52 t5_53
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_51 : t5_51.rows.all (refuses 4 t4_0)=true := by simp only [t5_51,BankTree.rows,List.all_append,ok_t5_52,ok_t5_53,Bool.true_and]
noncomputable def t5_55 : BankTree := .block [[atom2,atom4,atom10,atom39,atom81,atom105],[atom2,atom4,atom10,atom50,atom64,atom107],[atom2,atom4,atom10,atom52,atom64,atom87],[atom2,atom4,atom11,atom38,atom81,atom105],[atom2,atom4,atom12,atom15,atom30,atom95],[atom2,atom4,atom12,atom15,atom81,atom93],[atom2,atom4,atom12,atom15,atom94,atom109],[atom2,atom4,atom12,atom30,atom96,atom110]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_55 : t5_55.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_56 : BankTree := .block [[atom2,atom4,atom12,atom38,atom79,atom105],[atom2,atom4,atom12,atom38,atom80,atom81],[atom2,atom4,atom12,atom38,atom81,atom110],[atom2,atom4,atom12,atom38,atom105,atom109],[atom2,atom4,atom12,atom50,atom64,atom105],[atom2,atom4,atom12,atom51,atom64,atom110],[atom2,atom4,atom12,atom52,atom64,atom85],[atom2,atom4,atom12,atom53,atom85,atom109]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_56 : t5_56.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_54 : BankTree := .fork [atom2,atom4,atom12,atom38,atom79,atom105] t5_55 t5_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_54 : t5_54.rows.all (refuses 4 t4_0)=true := by simp only [t5_54,BankTree.rows,List.all_append,ok_t5_55,ok_t5_56,Bool.true_and]
noncomputable def t5_50 : BankTree := .fork [atom2,atom4,atom10,atom39,atom81,atom105] t5_51 t5_54
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_50 : t5_50.rows.all (refuses 4 t4_0)=true := by simp only [t5_50,BankTree.rows,List.all_append,ok_t5_51,ok_t5_54,Bool.true_and]
noncomputable def t5_59 : BankTree := .block [[atom2,atom4,atom15,atom30,atom78,atom93],[atom2,atom4,atom15,atom32,atom76,atom93],[atom2,atom4,atom15,atom32,atom94,atom103],[atom2,atom4,atom18,atom50,atom76,atom85],[atom2,atom4,atom27,atom30,atom67,atom93],[atom2,atom4,atom27,atom30,atom96,atom97],[atom2,atom4,atom27,atom50,atom64,atom87],[atom2,atom4,atom29,atom38,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_59 : t5_59.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_60 : BankTree := .block [[atom2,atom4,atom29,atom50,atom64,atom85],[atom2,atom4,atom38,atom47,atom81,atom105],[atom2,atom4,atom38,atom78,atom81,atom105],[atom2,atom4,atom51,atom60,atom64,atom87],[atom2,atom4,atom53,atom54,atom76,atom85],[atom2,atom5,atom15,atom38,atom81,atom85],[atom2,atom5,atom30,atom38,atom64,atom105],[atom2,atom6,atom15,atom42,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_60 : t5_60.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_58 : BankTree := .fork [atom2,atom4,atom29,atom50,atom64,atom85] t5_59 t5_60
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_58 : t5_58.rows.all (refuses 4 t4_0)=true := by simp only [t5_58,BankTree.rows,List.all_append,ok_t5_59,ok_t5_60,Bool.true_and]
noncomputable def t5_62 : BankTree := .block [[atom2,atom6,atom23,atom38,atom81,atom85],[atom2,atom6,atom30,atom38,atom72,atom105],[atom2,atom6,atom30,atom42,atom64,atom105],[atom2,atom8,atom12,atom38,atom81,atom105],[atom2,atom10,atom15,atom32,atom96,atom100],[atom2,atom10,atom15,atom35,atom67,atom93],[atom2,atom10,atom15,atom35,atom96,atom97],[atom2,atom10,atom18,atom38,atom79,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_62 : t5_62.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_63 : BankTree := .block [[atom2,atom10,atom18,atom50,atom64,atom90],[atom2,atom10,atom32,atom53,atom90,atom96],[atom2,atom10,atom35,atom38,atom67,atom80],[atom2,atom10,atom35,atom53,atom87,atom96],[atom2,atom10,atom40,atom44,atom81,atom105],[atom2,atom10,atom53,atom54,atom64,atom90],[atom2,atom10,atom53,atom57,atom64,atom87],[atom2,atom12,atom15,atom42,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_63 : t5_63.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_61 : BankTree := .fork [atom2,atom10,atom18,atom50,atom64,atom90] t5_62 t5_63
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_61 : t5_61.rows.all (refuses 4 t4_0)=true := by simp only [t5_61,BankTree.rows,List.all_append,ok_t5_62,ok_t5_63,Bool.true_and]
noncomputable def t5_57 : BankTree := .fork [atom2,atom6,atom23,atom38,atom81,atom85] t5_58 t5_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_57 : t5_57.rows.all (refuses 4 t4_0)=true := by simp only [t5_57,BankTree.rows,List.all_append,ok_t5_58,ok_t5_61,Bool.true_and]
noncomputable def t5_49 : BankTree := .fork [atom2,atom4,atom15,atom30,atom78,atom93] t5_50 t5_57
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_49 : t5_49.rows.all (refuses 4 t4_0)=true := by simp only [t5_49,BankTree.rows,List.all_append,ok_t5_50,ok_t5_57,Bool.true_and]
noncomputable def t5_33 : BankTree := .fork [atom2,atom3,atom38,atom40,atom81,atom105] t5_34 t5_49
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_33 : t5_33.rows.all (refuses 4 t4_0)=true := by simp only [t5_33,BankTree.rows,List.all_append,ok_t5_34,ok_t5_49,Bool.true_and]
noncomputable def t5_1 : BankTree := .fork [atom1,atom15,atom19,atom38,atom76,atom90] t5_2 t5_33
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_1 : t5_1.rows.all (refuses 4 t4_0)=true := by simp only [t5_1,BankTree.rows,List.all_append,ok_t5_2,ok_t5_33,Bool.true_and]
noncomputable def t5_69 : BankTree := .block [[atom2,atom12,atom30,atom42,atom64,atom105],[atom2,atom12,atom30,atom44,atom96,atom105],[atom2,atom12,atom38,atom44,atom81,atom105],[atom2,atom12,atom44,atom53,atom81,atom85],[atom2,atom13,atom15,atom42,atom64,atom87],[atom2,atom13,atom18,atom38,atom76,atom90],[atom2,atom13,atom18,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_69 : t5_69.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_70 : BankTree := .block [[atom2,atom15,atom16,atom38,atom76,atom90],[atom2,atom15,atom16,atom42,atom64,atom85],[atom2,atom15,atom18,atom42,atom81,atom85],[atom2,atom15,atom20,atom38,atom64,atom87],[atom2,atom15,atom30,atom38,atom67,atom69],[atom2,atom15,atom30,atom38,atom69,atom78],[atom2,atom15,atom30,atom38,atom70,atom78],[atom2,atom15,atom30,atom38,atom72,atom91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_70 : t5_70.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_68 : BankTree := .fork [atom2,atom15,atom16,atom38,atom76,atom90] t5_69 t5_70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_68 : t5_68.rows.all (refuses 4 t4_0)=true := by simp only [t5_68,BankTree.rows,List.all_append,ok_t5_69,ok_t5_70,Bool.true_and]
noncomputable def t5_72 : BankTree := .block [[atom2,atom15,atom30,atom38,atom77,atom90],[atom2,atom15,atom30,atom39,atom76,atom90],[atom2,atom15,atom30,atom42,atom62,atom67],[atom2,atom15,atom30,atom42,atom64,atom65],[atom2,atom15,atom30,atom42,atom64,atom86],[atom2,atom15,atom30,atom42,atom64,atom87],[atom2,atom15,atom30,atom42,atom64,atom91],[atom2,atom15,atom30,atom42,atom64,atom97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_72 : t5_72.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_73 : BankTree := .block [[atom2,atom15,atom30,atom42,atom64,atom104],[atom2,atom15,atom30,atom42,atom64,atom107],[atom2,atom15,atom30,atom42,atom66,atom85],[atom2,atom15,atom30,atom42,atom72,atom87],[atom2,atom15,atom30,atom42,atom87,atom96],[atom2,atom15,atom30,atom42,atom87,atom102],[atom2,atom15,atom30,atom45,atom64,atom85],[atom2,atom15,atom30,atom46,atom85,atom102]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_73 : t5_73.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_71 : BankTree := .fork [atom2,atom15,atom30,atom42,atom64,atom104] t5_72 t5_73
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_71 : t5_71.rows.all (refuses 4 t4_0)=true := by simp only [t5_71,BankTree.rows,List.all_append,ok_t5_72,ok_t5_73,Bool.true_and]
noncomputable def t5_67 : BankTree := .fork [atom2,atom15,atom30,atom38,atom77,atom90] t5_68 t5_71
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_67 : t5_67.rows.all (refuses 4 t4_0)=true := by simp only [t5_67,BankTree.rows,List.all_append,ok_t5_68,ok_t5_71,Bool.true_and]
noncomputable def t5_76 : BankTree := .block [[atom2,atom15,atom31,atom38,atom76,atom90],[atom2,atom15,atom31,atom42,atom64,atom85],[atom2,atom15,atom32,atom38,atom64,atom69],[atom2,atom15,atom32,atom38,atom69,atom76],[atom2,atom15,atom32,atom38,atom70,atom76],[atom2,atom15,atom32,atom38,atom72,atom89],[atom2,atom15,atom32,atom38,atom72,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_76 : t5_76.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_77 : BankTree := .block [[atom2,atom15,atom32,atom38,atom76,atom89],[atom2,atom15,atom32,atom38,atom76,atom92],[atom2,atom15,atom32,atom38,atom76,atom100],[atom2,atom15,atom32,atom38,atom90,atom103],[atom2,atom15,atom32,atom42,atom62,atom64],[atom2,atom15,atom32,atom42,atom64,atom85],[atom2,atom15,atom32,atom42,atom64,atom87],[atom2,atom15,atom32,atom42,atom64,atom88]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_77 : t5_77.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_75 : BankTree := .fork [atom2,atom15,atom32,atom38,atom76,atom89] t5_76 t5_77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_75 : t5_75.rows.all (refuses 4 t4_0)=true := by simp only [t5_75,BankTree.rows,List.all_append,ok_t5_76,ok_t5_77,Bool.true_and]
noncomputable def t5_79 : BankTree := .block [[atom2,atom15,atom32,atom42,atom64,atom89],[atom2,atom15,atom32,atom42,atom64,atom90],[atom2,atom15,atom32,atom42,atom64,atom94],[atom2,atom15,atom32,atom42,atom64,atom99],[atom2,atom15,atom32,atom42,atom64,atom105],[atom2,atom15,atom32,atom42,atom72,atom85],[atom2,atom15,atom32,atom42,atom76,atom85],[atom2,atom15,atom32,atom42,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_79 : t5_79.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_80 : BankTree := .block [[atom2,atom15,atom32,atom42,atom85,atom96],[atom2,atom15,atom32,atom42,atom85,atom102],[atom2,atom15,atom32,atom43,atom64,atom100],[atom2,atom15,atom32,atom44,atom85,atom103],[atom2,atom15,atom33,atom42,atom64,atom87],[atom2,atom15,atom34,atom42,atom64,atom87],[atom2,atom15,atom35,atom42,atom64,atom87],[atom2,atom15,atom36,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_80 : t5_80.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_78 : BankTree := .fork [atom2,atom15,atom32,atom42,atom85,atom96] t5_79 t5_80
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_78 : t5_78.rows.all (refuses 4 t4_0)=true := by simp only [t5_78,BankTree.rows,List.all_append,ok_t5_79,ok_t5_80,Bool.true_and]
noncomputable def t5_74 : BankTree := .fork [atom2,atom15,atom32,atom42,atom64,atom89] t5_75 t5_78
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_74 : t5_74.rows.all (refuses 4 t4_0)=true := by simp only [t5_74,BankTree.rows,List.all_append,ok_t5_75,ok_t5_78,Bool.true_and]
noncomputable def t5_66 : BankTree := .fork [atom2,atom15,atom31,atom38,atom76,atom90] t5_67 t5_74
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_66 : t5_66.rows.all (refuses 4 t4_0)=true := by simp only [t5_66,BankTree.rows,List.all_append,ok_t5_67,ok_t5_74,Bool.true_and]
noncomputable def t5_84 : BankTree := .block [[atom2,atom15,atom38,atom54,atom76,atom90],[atom2,atom15,atom38,atom76,atom83,atom90],[atom2,atom15,atom40,atom42,atom81,atom85],[atom2,atom15,atom42,atom46,atom81,atom85],[atom2,atom15,atom42,atom51,atom64,atom87],[atom2,atom15,atom42,atom54,atom64,atom85],[atom2,atom15,atom42,atom56,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_84 : t5_84.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_85 : BankTree := .block [[atom2,atom15,atom42,atom61,atom64,atom85],[atom2,atom15,atom42,atom64,atom81,atom87],[atom2,atom15,atom42,atom64,atom83,atom85],[atom2,atom15,atom42,atom67,atom81,atom85],[atom2,atom15,atom42,atom81,atom83,atom85],[atom2,atom15,atom42,atom81,atom85,atom87],[atom2,atom15,atom43,atom57,atom64,atom87],[atom2,atom15,atom44,atom47,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_85 : t5_85.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_83 : BankTree := .fork [atom2,atom15,atom42,atom61,atom64,atom85] t5_84 t5_85
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_83 : t5_83.rows.all (refuses 4 t4_0)=true := by simp only [t5_83,BankTree.rows,List.all_append,ok_t5_84,ok_t5_85,Bool.true_and]
noncomputable def t5_87 : BankTree := .block [[atom2,atom17,atom30,atom38,atom76,atom90],[atom2,atom17,atom30,atom42,atom64,atom85],[atom2,atom18,atom20,atom38,atom64,atom85],[atom2,atom18,atom21,atom38,atom76,atom85],[atom2,atom18,atom30,atom42,atom64,atom105],[atom2,atom20,atom27,atom38,atom64,atom87],[atom2,atom20,atom29,atom38,atom64,atom85],[atom2,atom21,atom27,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_87 : t5_87.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_88 : BankTree := .block [[atom2,atom21,atom29,atom38,atom64,atom85],[atom2,atom23,atom30,atom38,atom72,atom87],[atom2,atom23,atom30,atom42,atom64,atom87],[atom2,atom23,atom32,atom38,atom72,atom85],[atom2,atom23,atom32,atom42,atom64,atom85],[atom2,atom23,atom34,atom38,atom64,atom87],[atom2,atom23,atom35,atom38,atom64,atom87],[atom2,atom23,atom36,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_88 : t5_88.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_86 : BankTree := .fork [atom2,atom21,atom29,atom38,atom64,atom85] t5_87 t5_88
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_86 : t5_86.rows.all (refuses 4 t4_0)=true := by simp only [t5_86,BankTree.rows,List.all_append,ok_t5_87,ok_t5_88,Bool.true_and]
noncomputable def t5_82 : BankTree := .fork [atom2,atom17,atom30,atom38,atom76,atom90] t5_83 t5_86
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_82 : t5_82.rows.all (refuses 4 t4_0)=true := by simp only [t5_82,BankTree.rows,List.all_append,ok_t5_83,ok_t5_86,Bool.true_and]
noncomputable def t5_91 : BankTree := .block [[atom2,atom27,atom30,atom38,atom67,atom70],[atom2,atom27,atom30,atom42,atom64,atom87],[atom2,atom27,atom30,atom44,atom87,atom96],[atom2,atom27,atom34,atom38,atom64,atom87],[atom2,atom27,atom35,atom38,atom62,atom67],[atom2,atom27,atom35,atom38,atom64,atom65],[atom2,atom27,atom35,atom38,atom64,atom86],[atom2,atom27,atom35,atom38,atom64,atom97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_91 : t5_91.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_92 : BankTree := .block [[atom2,atom27,atom35,atom38,atom64,atom107],[atom2,atom27,atom35,atom38,atom66,atom85],[atom2,atom27,atom35,atom38,atom87,atom96],[atom2,atom27,atom35,atom39,atom64,atom85],[atom2,atom27,atom35,atom40,atom85,atom96],[atom2,atom27,atom37,atom38,atom64,atom87],[atom2,atom27,atom38,atom57,atom64,atom87],[atom2,atom28,atom35,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_92 : t5_92.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_90 : BankTree := .fork [atom2,atom27,atom35,atom38,atom64,atom107] t5_91 t5_92
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_90 : t5_90.rows.all (refuses 4 t4_0)=true := by simp only [t5_90,BankTree.rows,List.all_append,ok_t5_91,ok_t5_92,Bool.true_and]
noncomputable def t5_94 : BankTree := .block [[atom2,atom30,atom32,atom42,atom64,atom105],[atom2,atom30,atom40,atom42,atom64,atom105],[atom2,atom30,atom40,atom53,atom76,atom90],[atom2,atom30,atom42,atom46,atom64,atom105],[atom2,atom30,atom42,atom53,atom64,atom87],[atom2,atom30,atom42,atom59,atom64,atom87],[atom2,atom30,atom42,atom64,atom67,atom105],[atom2,atom30,atom42,atom64,atom87,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_94 : t5_94.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_95 : BankTree := .block [[atom2,atom30,atom42,atom64,atom105,atom107],[atom2,atom30,atom44,atom47,atom64,atom105],[atom2,atom30,atom44,atom60,atom64,atom87],[atom2,atom30,atom46,atom59,atom64,atom85],[atom2,atom32,atom38,atom53,atom76,atom90],[atom2,atom32,atom42,atom53,atom64,atom85],[atom2,atom32,atom42,atom59,atom64,atom85],[atom2,atom32,atom44,atom53,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_95 : t5_95.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_93 : BankTree := .fork [atom2,atom30,atom42,atom64,atom105,atom107] t5_94 t5_95
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_93 : t5_93.rows.all (refuses 4 t4_0)=true := by simp only [t5_93,BankTree.rows,List.all_append,ok_t5_94,ok_t5_95,Bool.true_and]
noncomputable def t5_89 : BankTree := .fork [atom2,atom30,atom32,atom42,atom64,atom105] t5_90 t5_93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_89 : t5_89.rows.all (refuses 4 t4_0)=true := by simp only [t5_89,BankTree.rows,List.all_append,ok_t5_90,ok_t5_93,Bool.true_and]
noncomputable def t5_81 : BankTree := .fork [atom2,atom27,atom30,atom38,atom67,atom70] t5_82 t5_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_81 : t5_81.rows.all (refuses 4 t4_0)=true := by simp only [t5_81,BankTree.rows,List.all_append,ok_t5_82,ok_t5_89,Bool.true_and]
noncomputable def t5_65 : BankTree := .fork [atom2,atom15,atom38,atom54,atom76,atom90] t5_66 t5_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_65 : t5_65.rows.all (refuses 4 t4_0)=true := by simp only [t5_65,BankTree.rows,List.all_append,ok_t5_66,ok_t5_81,Bool.true_and]
noncomputable def t5_100 : BankTree := .block [[atom2,atom35,atom38,atom60,atom64,atom87],[atom3,atom15,atom19,atom38,atom64,atom87],[atom3,atom15,atom30,atom38,atom67,atom68],[atom3,atom15,atom30,atom41,atom64,atom97],[atom3,atom15,atom30,atom41,atom87,atom96],[atom3,atom15,atom32,atom38,atom64,atom68],[atom3,atom15,atom32,atom41,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_100 : t5_100.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_101 : BankTree := .block [[atom3,atom15,atom32,atom41,atom85,atom96],[atom3,atom15,atom40,atom41,atom81,atom85],[atom3,atom15,atom41,atom51,atom64,atom87],[atom3,atom15,atom41,atom54,atom64,atom85],[atom3,atom18,atom19,atom38,atom64,atom85],[atom3,atom30,atom40,atom41,atom64,atom105],[atom3,atom30,atom41,atom53,atom64,atom87],[atom3,atom32,atom41,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_101 : t5_101.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_99 : BankTree := .fork [atom3,atom15,atom32,atom41,atom85,atom96] t5_100 t5_101
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_99 : t5_99.rows.all (refuses 4 t4_0)=true := by simp only [t5_99,BankTree.rows,List.all_append,ok_t5_100,ok_t5_101,Bool.true_and]
noncomputable def t5_103 : BankTree := .block [[atom4,atom10,atom15,atom38,atom68,atom83],[atom4,atom10,atom19,atom38,atom64,atom107],[atom4,atom10,atom40,atom41,atom81,atom105],[atom4,atom12,atom15,atom38,atom68,atom81],[atom4,atom12,atom15,atom41,atom81,atom94],[atom4,atom12,atom15,atom41,atom85,atom109],[atom4,atom12,atom19,atom38,atom64,atom105],[atom4,atom12,atom30,atom41,atom64,atom110]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_103 : t5_103.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_104 : BankTree := .block [[atom4,atom12,atom30,atom41,atom96,atom105],[atom4,atom12,atom38,atom41,atom81,atom105],[atom4,atom12,atom41,atom51,atom64,atom105],[atom4,atom12,atom41,atom53,atom81,atom85],[atom4,atom15,atom30,atom38,atom68,atom78],[atom4,atom15,atom32,atom38,atom68,atom76],[atom4,atom15,atom32,atom41,atom76,atom94],[atom4,atom15,atom32,atom41,atom85,atom103]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_104 : t5_104.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_102 : BankTree := .fork [atom4,atom12,atom30,atom41,atom96,atom105] t5_103 t5_104
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_102 : t5_102.rows.all (refuses 4 t4_0)=true := by simp only [t5_102,BankTree.rows,List.all_append,ok_t5_103,ok_t5_104,Bool.true_and]
noncomputable def t5_98 : BankTree := .fork [atom4,atom10,atom15,atom38,atom68,atom83] t5_99 t5_102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_98 : t5_98.rows.all (refuses 4 t4_0)=true := by simp only [t5_98,BankTree.rows,List.all_append,ok_t5_99,ok_t5_102,Bool.true_and]
noncomputable def t5_107 : BankTree := .block [[atom4,atom15,atom41,atom47,atom81,atom85],[atom4,atom15,atom41,atom54,atom76,atom85],[atom4,atom18,atom19,atom38,atom76,atom85],[atom4,atom19,atom27,atom38,atom64,atom87],[atom4,atom19,atom29,atom38,atom64,atom85],[atom4,atom27,atom30,atom38,atom67,atom68],[atom4,atom27,atom30,atom41,atom64,atom97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_107 : t5_107.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_108 : BankTree := .block [[atom4,atom27,atom30,atom41,atom87,atom96],[atom4,atom27,atom41,atom51,atom64,atom87],[atom4,atom30,atom41,atom47,atom64,atom105],[atom4,atom30,atom41,atom60,atom64,atom87],[atom4,atom32,atom41,atom53,atom76,atom85],[atom6,atom7,atom15,atom38,atom81,atom85],[atom6,atom7,atom30,atom38,atom64,atom105],[atom7,atom12,atom15,atom38,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_108 : t5_108.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_106 : BankTree := .fork [atom4,atom27,atom30,atom41,atom87,atom96] t5_107 t5_108
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_106 : t5_106.rows.all (refuses 4 t4_0)=true := by simp only [t5_106,BankTree.rows,List.all_append,ok_t5_107,ok_t5_108,Bool.true_and]
noncomputable def t5_110 : BankTree := .block [[atom7,atom12,atom30,atom38,atom64,atom105],[atom7,atom15,atom30,atom38,atom64,atom91],[atom7,atom15,atom30,atom38,atom72,atom87],[atom7,atom15,atom30,atom42,atom64,atom87],[atom7,atom15,atom32,atom38,atom64,atom89],[atom7,atom15,atom32,atom38,atom72,atom85],[atom7,atom15,atom32,atom38,atom76,atom85],[atom7,atom15,atom32,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_110 : t5_110.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_111 : BankTree := .block [[atom7,atom15,atom34,atom38,atom64,atom87],[atom7,atom15,atom36,atom38,atom64,atom85],[atom7,atom23,atom30,atom38,atom64,atom87],[atom7,atom23,atom32,atom38,atom64,atom85],[atom7,atom27,atom30,atom38,atom64,atom87],[atom8,atom10,atom15,atom30,atom67,atom93],[atom8,atom10,atom18,atom38,atom79,atom85],[atom8,atom10,atom18,atom50,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_111 : t5_111.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_109 : BankTree := .fork [atom7,atom15,atom34,atom38,atom64,atom87] t5_110 t5_111
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_109 : t5_109.rows.all (refuses 4 t4_0)=true := by simp only [t5_109,BankTree.rows,List.all_append,ok_t5_110,ok_t5_111,Bool.true_and]
noncomputable def t5_105 : BankTree := .fork [atom7,atom12,atom30,atom38,atom64,atom105] t5_106 t5_109
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_105 : t5_105.rows.all (refuses 4 t4_0)=true := by simp only [t5_105,BankTree.rows,List.all_append,ok_t5_106,ok_t5_109,Bool.true_and]
noncomputable def t5_97 : BankTree := .fork [atom4,atom15,atom41,atom47,atom81,atom85] t5_98 t5_105
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_97 : t5_97.rows.all (refuses 4 t4_0)=true := by simp only [t5_97,BankTree.rows,List.all_append,ok_t5_98,ok_t5_105,Bool.true_and]
noncomputable def t5_115 : BankTree := .block [[atom8,atom10,atom30,atom38,atom67,atom80],[atom8,atom12,atom14,atom38,atom64,atom85],[atom8,atom12,atom15,atom30,atom38,atom63],[atom8,atom12,atom15,atom30,atom64,atom93],[atom8,atom12,atom15,atom30,atom94,atom96],[atom8,atom12,atom15,atom38,atom79,atom85],[atom8,atom12,atom15,atom38,atom81,atom88]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_115 : t5_115.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_116 : BankTree := .block [[atom8,atom12,atom15,atom50,atom64,atom85],[atom8,atom12,atom15,atom51,atom64,atom94],[atom8,atom12,atom30,atom38,atom64,atom80],[atom8,atom12,atom30,atom53,atom85,atom96],[atom8,atom12,atom33,atom38,atom64,atom105],[atom8,atom12,atom51,atom53,atom64,atom85],[atom8,atom13,atom18,atom38,atom76,atom85],[atom8,atom13,atom29,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_116 : t5_116.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_114 : BankTree := .fork [atom8,atom12,atom15,atom50,atom64,atom85] t5_115 t5_116
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_114 : t5_114.rows.all (refuses 4 t4_0)=true := by simp only [t5_114,BankTree.rows,List.all_append,ok_t5_115,ok_t5_116,Bool.true_and]
noncomputable def t5_118 : BankTree := .block [[atom8,atom15,atom16,atom38,atom76,atom85],[atom8,atom15,atom30,atom38,atom62,atom78],[atom8,atom15,atom30,atom38,atom73,atom85],[atom8,atom15,atom30,atom38,atom77,atom85],[atom8,atom15,atom30,atom39,atom76,atom85],[atom8,atom15,atom30,atom45,atom64,atom85],[atom8,atom15,atom32,atom38,atom76,atom88],[atom8,atom15,atom38,atom78,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_118 : t5_118.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_119 : BankTree := .block [[atom8,atom17,atom30,atom38,atom76,atom85],[atom8,atom24,atom30,atom38,atom64,atom85],[atom8,atom27,atom30,atom38,atom62,atom67],[atom8,atom27,atom30,atom38,atom64,atom65],[atom8,atom27,atom30,atom38,atom66,atom85],[atom8,atom27,atom30,atom39,atom64,atom85],[atom8,atom27,atom30,atom40,atom85,atom96],[atom8,atom27,atom33,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_119 : t5_119.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_117 : BankTree := .fork [atom8,atom17,atom30,atom38,atom76,atom85] t5_118 t5_119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_117 : t5_117.rows.all (refuses 4 t4_0)=true := by simp only [t5_117,BankTree.rows,List.all_append,ok_t5_118,ok_t5_119,Bool.true_and]
noncomputable def t5_113 : BankTree := .fork [atom8,atom15,atom16,atom38,atom76,atom85] t5_114 t5_117
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_113 : t5_113.rows.all (refuses 4 t4_0)=true := by simp only [t5_113,BankTree.rows,List.all_append,ok_t5_114,ok_t5_117,Bool.true_and]
noncomputable def t5_122 : BankTree := .block [[atom8,atom28,atom30,atom38,atom64,atom85],[atom8,atom29,atom30,atom38,atom64,atom105],[atom8,atom30,atom40,atom53,atom76,atom85],[atom10,atom15,atom30,atom38,atom67,atom75],[atom10,atom15,atom32,atom41,atom90,atom96],[atom10,atom15,atom35,atom38,atom67,atom68],[atom10,atom15,atom35,atom41,atom64,atom97],[atom10,atom15,atom35,atom41,atom87,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_122 : t5_122.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_123 : BankTree := .block [[atom10,atom15,atom41,atom54,atom64,atom90],[atom10,atom18,atom19,atom38,atom64,atom90],[atom10,atom18,atom26,atom38,atom64,atom85],[atom10,atom32,atom41,atom53,atom64,atom90],[atom10,atom35,atom41,atom53,atom64,atom87],[atom12,atom15,atom26,atom38,atom64,atom85],[atom12,atom15,atom30,atom38,atom64,atom75],[atom12,atom15,atom30,atom49,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_123 : t5_123.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_121 : BankTree := .fork [atom10,atom15,atom41,atom54,atom64,atom90] t5_122 t5_123
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_121 : t5_121.rows.all (refuses 4 t4_0)=true := by simp only [t5_121,BankTree.rows,List.all_append,ok_t5_122,ok_t5_123,Bool.true_and]
noncomputable def t5_125 : BankTree := .block [[atom12,atom15,atom37,atom38,atom64,atom92],[atom12,atom30,atom49,atom53,atom64,atom85],[atom15,atom30,atom40,atom41,atom76,atom90],[atom15,atom30,atom40,atom49,atom76,atom85],[atom15,atom30,atom41,atom42,atom64,atom87],[atom15,atom30,atom42,atom48,atom64,atom87],[atom15,atom30,atom46,atom48,atom64,atom85],[atom15,atom30,atom47,atom49,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_125 : t5_125.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_126 : BankTree := .block [[atom15,atom32,atom38,atom41,atom76,atom90],[atom15,atom32,atom41,atom42,atom64,atom85],[atom15,atom32,atom41,atom43,atom64,atom90],[atom15,atom32,atom42,atom48,atom64,atom85],[atom15,atom35,atom41,atom43,atom64,atom87],[atom27,atom30,atom40,atom49,atom64,atom85],[atom27,atom35,atom38,atom41,atom64,atom87],[atom27,atom35,atom40,atom41,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_126 : t5_126.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_124 : BankTree := .fork [atom15,atom32,atom38,atom41,atom76,atom90] t5_125 t5_126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_124 : t5_124.rows.all (refuses 4 t4_0)=true := by simp only [t5_124,BankTree.rows,List.all_append,ok_t5_125,ok_t5_126,Bool.true_and]
noncomputable def t5_120 : BankTree := .fork [atom12,atom15,atom37,atom38,atom64,atom92] t5_121 t5_124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_120 : t5_120.rows.all (refuses 4 t4_0)=true := by simp only [t5_120,BankTree.rows,List.all_append,ok_t5_121,ok_t5_124,Bool.true_and]
noncomputable def t5_112 : BankTree := .fork [atom8,atom28,atom30,atom38,atom64,atom85] t5_113 t5_120
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_112 : t5_112.rows.all (refuses 4 t4_0)=true := by simp only [t5_112,BankTree.rows,List.all_append,ok_t5_113,ok_t5_120,Bool.true_and]
noncomputable def t5_96 : BankTree := .fork [atom8,atom10,atom30,atom38,atom67,atom80] t5_97 t5_112
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_96 : t5_96.rows.all (refuses 4 t4_0)=true := by simp only [t5_96,BankTree.rows,List.all_append,ok_t5_97,ok_t5_112,Bool.true_and]
noncomputable def t5_64 : BankTree := .fork [atom2,atom35,atom38,atom60,atom64,atom87] t5_65 t5_96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_64 : t5_64.rows.all (refuses 4 t4_0)=true := by simp only [t5_64,BankTree.rows,List.all_append,ok_t5_65,ok_t5_96,Bool.true_and]
noncomputable def t5_0 : BankTree := .fork [atom2,atom12,atom30,atom42,atom64,atom105] t5_1 t5_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_0 : t5_0.rows.all (refuses 4 t4_0)=true := by simp only [t5_0,BankTree.rows,List.all_append,ok_t5_1,ok_t5_64,Bool.true_and]
theorem safe5 : Safe 5 t5_0 := certify 4 t4_0 t5_0 safe4 ok_t5_0
noncomputable def t6_6 : BankTree := .block [[atom0,atom2,atom3,atom15,atom38,atom81,atom85],[atom0,atom2,atom3,atom30,atom38,atom64,atom105],[atom0,atom2,atom4,atom10,atom38,atom81,atom105],[atom0,atom2,atom15,atom30,atom38,atom76,atom90],[atom0,atom2,atom15,atom30,atom42,atom64,atom85],[atom0,atom2,atom27,atom35,atom38,atom64,atom85],[atom0,atom8,atom15,atom30,atom38,atom76,atom85],[atom0,atom8,atom27,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom4,atom38,atom81,atom105],[atom1,atom2,atom3,atom10,atom38,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_6 : t6_6.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_8 : BankTree := .block [[atom1,atom2,atom3,atom13,atom38,atom64,atom105],[atom1,atom2,atom3,atom14,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom63],[atom1,atom2,atom3,atom15,atom30,atom64,atom93],[atom1,atom2,atom3,atom15,atom30,atom94,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_8 : t6_8.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_9 : BankTree := .block [[atom1,atom2,atom3,atom15,atom38,atom62,atom81],[atom1,atom2,atom3,atom15,atom38,atom79,atom85],[atom1,atom2,atom3,atom15,atom38,atom81,atom85],[atom1,atom2,atom3,atom15,atom38,atom81,atom88],[atom1,atom2,atom3,atom15,atom38,atom81,atom89],[atom1,atom2,atom3,atom15,atom38,atom81,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_9 : t6_9.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_7 : BankTree := .fork [atom1,atom2,atom3,atom15,atom38,atom62,atom81] t6_8 t6_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_7 : t6_7.rows.all (refuses 5 t5_0)=true := by simp only [t6_7,BankTree.rows,List.all_append,ok_t6_8,ok_t6_9,Bool.true_and]
noncomputable def t6_5 : BankTree := .fork [atom1,atom2,atom3,atom13,atom38,atom64,atom105] t6_6 t6_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_5 : t6_5.rows.all (refuses 5 t5_0)=true := by simp only [t6_5,BankTree.rows,List.all_append,ok_t6_6,ok_t6_7,Bool.true_and]
noncomputable def t6_11 : BankTree := .block [[atom1,atom2,atom3,atom15,atom38,atom81,atom105],[atom1,atom2,atom3,atom15,atom38,atom84,atom85],[atom1,atom2,atom3,atom15,atom38,atom85,atom109],[atom1,atom2,atom3,atom15,atom42,atom81,atom85],[atom1,atom2,atom3,atom15,atom50,atom64,atom85],[atom1,atom2,atom3,atom15,atom51,atom64,atom94],[atom1,atom2,atom3,atom23,atom38,atom81,atom85],[atom1,atom2,atom3,atom30,atom38,atom64,atom80],[atom1,atom2,atom3,atom30,atom38,atom64,atom105],[atom1,atom2,atom3,atom30,atom38,atom64,atom108]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_11 : t6_11.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_13 : BankTree := .block [[atom1,atom2,atom3,atom30,atom38,atom64,atom110],[atom1,atom2,atom3,atom30,atom38,atom72,atom105],[atom1,atom2,atom3,atom30,atom38,atom81,atom105],[atom1,atom2,atom3,atom30,atom38,atom96,atom105],[atom1,atom2,atom3,atom30,atom42,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_13 : t6_13.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_14 : BankTree := .block [[atom1,atom2,atom3,atom30,atom53,atom85,atom96],[atom1,atom2,atom3,atom33,atom38,atom64,atom105],[atom1,atom2,atom3,atom34,atom38,atom64,atom105],[atom1,atom2,atom3,atom38,atom51,atom64,atom105],[atom1,atom2,atom3,atom38,atom53,atom81,atom85],[atom1,atom2,atom3,atom38,atom64,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_14 : t6_14.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_12 : BankTree := .fork [atom1,atom2,atom3,atom30,atom53,atom85,atom96] t6_13 t6_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_12 : t6_12.rows.all (refuses 5 t5_0)=true := by simp only [t6_12,BankTree.rows,List.all_append,ok_t6_13,ok_t6_14,Bool.true_and]
noncomputable def t6_10 : BankTree := .fork [atom1,atom2,atom3,atom30,atom38,atom64,atom110] t6_11 t6_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_10 : t6_10.rows.all (refuses 5 t5_0)=true := by simp only [t6_10,BankTree.rows,List.all_append,ok_t6_11,ok_t6_12,Bool.true_and]
noncomputable def t6_4 : BankTree := .fork [atom1,atom2,atom3,atom15,atom38,atom81,atom105] t6_5 t6_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_4 : t6_4.rows.all (refuses 5 t5_0)=true := by simp only [t6_4,BankTree.rows,List.all_append,ok_t6_5,ok_t6_10,Bool.true_and]
noncomputable def t6_17 : BankTree := .block [[atom1,atom2,atom3,atom38,atom81,atom85,atom105],[atom1,atom2,atom3,atom38,atom81,atom105],[atom1,atom2,atom3,atom51,atom53,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom30,atom95],[atom1,atom2,atom4,atom10,atom15,atom81,atom93],[atom1,atom2,atom4,atom10,atom15,atom94,atom109],[atom1,atom2,atom4,atom10,atom30,atom96,atom110],[atom1,atom2,atom4,atom10,atom38,atom79,atom105],[atom1,atom2,atom4,atom10,atom38,atom80,atom81],[atom1,atom2,atom4,atom10,atom38,atom81,atom110]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_17 : t6_17.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_19 : BankTree := .block [[atom1,atom2,atom4,atom10,atom38,atom105,atom109],[atom1,atom2,atom4,atom10,atom50,atom64,atom105],[atom1,atom2,atom4,atom10,atom51,atom64,atom110],[atom1,atom2,atom4,atom10,atom52,atom64,atom85],[atom1,atom2,atom4,atom10,atom53,atom85,atom109]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_19 : t6_19.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_20 : BankTree := .block [[atom1,atom2,atom4,atom12,atom38,atom81,atom105],[atom1,atom2,atom4,atom14,atom38,atom76,atom85],[atom1,atom2,atom4,atom15,atom30,atom76,atom93],[atom1,atom2,atom4,atom15,atom30,atom94,atom103],[atom1,atom2,atom4,atom15,atom42,atom81,atom85],[atom1,atom2,atom4,atom15,atom43,atom81,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_20 : t6_20.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_18 : BankTree := .fork [atom1,atom2,atom4,atom12,atom38,atom81,atom105] t6_19 t6_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_18 : t6_18.rows.all (refuses 5 t5_0)=true := by simp only [t6_18,BankTree.rows,List.all_append,ok_t6_19,ok_t6_20,Bool.true_and]
noncomputable def t6_16 : BankTree := .fork [atom1,atom2,atom4,atom10,atom38,atom105,atom109] t6_17 t6_18
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_16 : t6_16.rows.all (refuses 5 t5_0)=true := by simp only [t6_16,BankTree.rows,List.all_append,ok_t6_17,ok_t6_18,Bool.true_and]
noncomputable def t6_22 : BankTree := .block [[atom1,atom2,atom4,atom15,atom50,atom76,atom85],[atom1,atom2,atom4,atom15,atom51,atom76,atom94],[atom1,atom2,atom4,atom23,atom38,atom81,atom85],[atom1,atom2,atom4,atom27,atom30,atom38,atom63],[atom1,atom2,atom4,atom27,atom30,atom64,atom93],[atom1,atom2,atom4,atom27,atom30,atom94,atom96],[atom1,atom2,atom4,atom27,atom38,atom81,atom105],[atom1,atom2,atom4,atom27,atom50,atom64,atom85],[atom1,atom2,atom4,atom27,atom51,atom64,atom94],[atom1,atom2,atom4,atom30,atom38,atom72,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_22 : t6_22.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_24 : BankTree := .block [[atom1,atom2,atom4,atom30,atom42,atom64,atom105],[atom1,atom2,atom4,atom38,atom43,atom81,atom105],[atom1,atom2,atom4,atom38,atom76,atom81,atom105],[atom1,atom2,atom4,atom43,atom51,atom64,atom105],[atom1,atom2,atom4,atom51,atom53,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_24 : t6_24.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_25 : BankTree := .block [[atom1,atom2,atom4,atom51,atom60,atom64,atom85],[atom1,atom2,atom8,atom10,atom38,atom81,atom105],[atom1,atom2,atom9,atom15,atom38,atom81,atom85],[atom1,atom2,atom9,atom30,atom38,atom64,atom105],[atom1,atom2,atom10,atom14,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom30,atom96,atom100]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_25 : t6_25.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_23 : BankTree := .fork [atom1,atom2,atom4,atom51,atom60,atom64,atom85] t6_24 t6_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_23 : t6_23.rows.all (refuses 5 t5_0)=true := by simp only [t6_23,BankTree.rows,List.all_append,ok_t6_24,ok_t6_25,Bool.true_and]
noncomputable def t6_21 : BankTree := .fork [atom1,atom2,atom4,atom30,atom42,atom64,atom105] t6_22 t6_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_21 : t6_21.rows.all (refuses 5 t5_0)=true := by simp only [t6_21,BankTree.rows,List.all_append,ok_t6_22,ok_t6_23,Bool.true_and]
noncomputable def t6_15 : BankTree := .fork [atom1,atom2,atom4,atom15,atom50,atom76,atom85] t6_16 t6_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_15 : t6_15.rows.all (refuses 5 t5_0)=true := by simp only [t6_15,BankTree.rows,List.all_append,ok_t6_16,ok_t6_21,Bool.true_and]
noncomputable def t6_3 : BankTree := .fork [atom1,atom2,atom3,atom38,atom81,atom85,atom105] t6_4 t6_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_3 : t6_3.rows.all (refuses 5 t5_0)=true := by simp only [t6_3,BankTree.rows,List.all_append,ok_t6_4,ok_t6_15,Bool.true_and]
noncomputable def t6_29 : BankTree := .block [[atom1,atom2,atom10,atom15,atom35,atom38,atom63],[atom1,atom2,atom10,atom15,atom35,atom64,atom93],[atom1,atom2,atom10,atom15,atom35,atom94,atom96],[atom1,atom2,atom10,atom15,atom38,atom79,atom90],[atom1,atom2,atom10,atom15,atom38,atom81,atom89],[atom1,atom2,atom10,atom15,atom42,atom81,atom85],[atom1,atom2,atom10,atom15,atom50,atom64,atom90],[atom1,atom2,atom10,atom30,atom42,atom64,atom105],[atom1,atom2,atom10,atom30,atom44,atom96,atom105],[atom1,atom2,atom10,atom30,atom53,atom90,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_29 : t6_29.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_31 : BankTree := .block [[atom1,atom2,atom10,atom34,atom38,atom64,atom105],[atom1,atom2,atom10,atom35,atom38,atom64,atom80],[atom1,atom2,atom10,atom35,atom38,atom81,atom105],[atom1,atom2,atom10,atom35,atom53,atom85,atom96],[atom1,atom2,atom10,atom38,atom44,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_31 : t6_31.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_32 : BankTree := .block [[atom1,atom2,atom10,atom38,atom81,atom90,atom105],[atom1,atom2,atom10,atom44,atom53,atom81,atom85],[atom1,atom2,atom10,atom51,atom53,atom64,atom90],[atom1,atom2,atom10,atom53,atom57,atom64,atom85],[atom1,atom2,atom13,atom15,atom38,atom76,atom90],[atom1,atom2,atom13,atom15,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_32 : t6_32.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_30 : BankTree := .fork [atom1,atom2,atom10,atom38,atom81,atom90,atom105] t6_31 t6_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_30 : t6_30.rows.all (refuses 5 t5_0)=true := by simp only [t6_30,BankTree.rows,List.all_append,ok_t6_31,ok_t6_32,Bool.true_and]
noncomputable def t6_28 : BankTree := .fork [atom1,atom2,atom10,atom34,atom38,atom64,atom105] t6_29 t6_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_28 : t6_28.rows.all (refuses 5 t5_0)=true := by simp only [t6_28,BankTree.rows,List.all_append,ok_t6_29,ok_t6_30,Bool.true_and]
noncomputable def t6_34 : BankTree := .block [[atom1,atom2,atom15,atom20,atom38,atom64,atom85],[atom1,atom2,atom15,atom21,atom38,atom76,atom85],[atom1,atom2,atom15,atom30,atom38,atom64,atom69],[atom1,atom2,atom15,atom30,atom38,atom69,atom76],[atom1,atom2,atom15,atom30,atom38,atom70,atom76],[atom1,atom2,atom15,atom30,atom38,atom72,atom89],[atom1,atom2,atom15,atom30,atom38,atom72,atom90],[atom1,atom2,atom15,atom30,atom38,atom76,atom89],[atom1,atom2,atom15,atom30,atom38,atom76,atom92],[atom1,atom2,atom15,atom30,atom38,atom76,atom100]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_34 : t6_34.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_36 : BankTree := .block [[atom1,atom2,atom15,atom30,atom38,atom90,atom103],[atom1,atom2,atom15,atom30,atom42,atom62,atom64],[atom1,atom2,atom15,atom30,atom42,atom64,atom85],[atom1,atom2,atom15,atom30,atom42,atom64,atom87],[atom1,atom2,atom15,atom30,atom42,atom64,atom88]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_36 : t6_36.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_37 : BankTree := .block [[atom1,atom2,atom15,atom30,atom42,atom64,atom89],[atom1,atom2,atom15,atom30,atom42,atom64,atom90],[atom1,atom2,atom15,atom30,atom42,atom64,atom94],[atom1,atom2,atom15,atom30,atom42,atom64,atom99],[atom1,atom2,atom15,atom30,atom42,atom64,atom105],[atom1,atom2,atom15,atom30,atom42,atom72,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_37 : t6_37.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_35 : BankTree := .fork [atom1,atom2,atom15,atom30,atom42,atom64,atom89] t6_36 t6_37
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_35 : t6_35.rows.all (refuses 5 t5_0)=true := by simp only [t6_35,BankTree.rows,List.all_append,ok_t6_36,ok_t6_37,Bool.true_and]
noncomputable def t6_33 : BankTree := .fork [atom1,atom2,atom15,atom30,atom38,atom90,atom103] t6_34 t6_35
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_33 : t6_33.rows.all (refuses 5 t5_0)=true := by simp only [t6_33,BankTree.rows,List.all_append,ok_t6_34,ok_t6_35,Bool.true_and]
noncomputable def t6_27 : BankTree := .fork [atom1,atom2,atom15,atom20,atom38,atom64,atom85] t6_28 t6_33
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_27 : t6_27.rows.all (refuses 5 t5_0)=true := by simp only [t6_27,BankTree.rows,List.all_append,ok_t6_28,ok_t6_33,Bool.true_and]
noncomputable def t6_40 : BankTree := .block [[atom1,atom2,atom15,atom30,atom42,atom76,atom85],[atom1,atom2,atom15,atom30,atom42,atom81,atom85],[atom1,atom2,atom15,atom30,atom42,atom85,atom96],[atom1,atom2,atom15,atom30,atom42,atom85,atom102],[atom1,atom2,atom15,atom30,atom43,atom64,atom100],[atom1,atom2,atom15,atom30,atom44,atom85,atom103],[atom1,atom2,atom15,atom32,atom38,atom76,atom90],[atom1,atom2,atom15,atom32,atom42,atom64,atom85],[atom1,atom2,atom15,atom33,atom38,atom76,atom90],[atom1,atom2,atom15,atom33,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_40 : t6_40.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_42 : BankTree := .block [[atom1,atom2,atom15,atom34,atom38,atom64,atom89],[atom1,atom2,atom15,atom34,atom42,atom64,atom85],[atom1,atom2,atom15,atom35,atom38,atom76,atom90],[atom1,atom2,atom15,atom35,atom42,atom64,atom85],[atom1,atom2,atom15,atom35,atom43,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_42 : t6_42.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_43 : BankTree := .block [[atom1,atom2,atom15,atom38,atom42,atom81,atom85],[atom1,atom2,atom15,atom38,atom51,atom76,atom90],[atom1,atom2,atom15,atom38,atom76,atom81,atom90],[atom1,atom2,atom15,atom42,atom51,atom64,atom85],[atom1,atom2,atom15,atom42,atom56,atom64,atom85],[atom1,atom2,atom15,atom42,atom64,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_43 : t6_43.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_41 : BankTree := .fork [atom1,atom2,atom15,atom38,atom42,atom81,atom85] t6_42 t6_43
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_41 : t6_41.rows.all (refuses 5 t5_0)=true := by simp only [t6_41,BankTree.rows,List.all_append,ok_t6_42,ok_t6_43,Bool.true_and]
noncomputable def t6_39 : BankTree := .fork [atom1,atom2,atom15,atom34,atom38,atom64,atom89] t6_40 t6_41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_39 : t6_39.rows.all (refuses 5 t5_0)=true := by simp only [t6_39,BankTree.rows,List.all_append,ok_t6_40,ok_t6_41,Bool.true_and]
noncomputable def t6_46 : BankTree := .block [[atom1,atom2,atom15,atom42,atom81,atom85],[atom1,atom2,atom15,atom43,atom44,atom81,atom85],[atom1,atom2,atom15,atom43,atom51,atom64,atom90],[atom1,atom2,atom15,atom43,atom57,atom64,atom85],[atom1,atom2,atom20,atom27,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_46 : t6_46.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_47 : BankTree := .block [[atom1,atom2,atom21,atom27,atom38,atom64,atom85],[atom1,atom2,atom23,atom30,atom38,atom72,atom85],[atom1,atom2,atom23,atom30,atom42,atom64,atom85],[atom1,atom2,atom23,atom34,atom38,atom64,atom85],[atom1,atom2,atom23,atom35,atom38,atom64,atom85],[atom1,atom2,atom27,atom30,atom38,atom64,atom70]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_47 : t6_47.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_45 : BankTree := .fork [atom1,atom2,atom21,atom27,atom38,atom64,atom85] t6_46 t6_47
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_45 : t6_45.rows.all (refuses 5 t5_0)=true := by simp only [t6_45,BankTree.rows,List.all_append,ok_t6_46,ok_t6_47,Bool.true_and]
noncomputable def t6_49 : BankTree := .block [[atom1,atom2,atom27,atom30,atom38,atom76,atom90],[atom1,atom2,atom27,atom30,atom42,atom64,atom85],[atom1,atom2,atom27,atom30,atom44,atom85,atom96],[atom1,atom2,atom27,atom34,atom38,atom64,atom85],[atom1,atom2,atom27,atom35,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_49 : t6_49.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_50 : BankTree := .block [[atom1,atom2,atom27,atom35,atom38,atom64,atom87],[atom1,atom2,atom27,atom35,atom38,atom64,atom88],[atom1,atom2,atom27,atom35,atom38,atom64,atom90],[atom1,atom2,atom27,atom35,atom38,atom64,atom94],[atom1,atom2,atom27,atom35,atom38,atom64,atom105],[atom1,atom2,atom27,atom35,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_50 : t6_50.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_48 : BankTree := .fork [atom1,atom2,atom27,atom35,atom38,atom64,atom87] t6_49 t6_50
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_48 : t6_48.rows.all (refuses 5 t5_0)=true := by simp only [t6_48,BankTree.rows,List.all_append,ok_t6_49,ok_t6_50,Bool.true_and]
noncomputable def t6_44 : BankTree := .fork [atom1,atom2,atom27,atom30,atom38,atom76,atom90] t6_45 t6_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_44 : t6_44.rows.all (refuses 5 t5_0)=true := by simp only [t6_44,BankTree.rows,List.all_append,ok_t6_45,ok_t6_48,Bool.true_and]
noncomputable def t6_38 : BankTree := .fork [atom1,atom2,atom15,atom42,atom81,atom85] t6_39 t6_44
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_38 : t6_38.rows.all (refuses 5 t5_0)=true := by simp only [t6_38,BankTree.rows,List.all_append,ok_t6_39,ok_t6_44,Bool.true_and]
noncomputable def t6_26 : BankTree := .fork [atom1,atom2,atom15,atom30,atom42,atom76,atom85] t6_27 t6_38
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_26 : t6_26.rows.all (refuses 5 t5_0)=true := by simp only [t6_26,BankTree.rows,List.all_append,ok_t6_27,ok_t6_38,Bool.true_and]
noncomputable def t6_2 : BankTree := .fork [atom1,atom2,atom10,atom15,atom35,atom38,atom63] t6_3 t6_26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_2 : t6_2.rows.all (refuses 5 t5_0)=true := by simp only [t6_2,BankTree.rows,List.all_append,ok_t6_3,ok_t6_26,Bool.true_and]
noncomputable def t6_55 : BankTree := .block [[atom1,atom2,atom27,atom35,atom38,atom81,atom85],[atom1,atom2,atom27,atom35,atom38,atom85,atom96],[atom1,atom2,atom27,atom37,atom38,atom64,atom85],[atom1,atom2,atom27,atom38,atom57,atom64,atom85],[atom1,atom2,atom30,atom38,atom42,atom64,atom105],[atom1,atom2,atom30,atom38,atom53,atom76,atom90],[atom1,atom2,atom30,atom38,atom76,atom90,atom105],[atom1,atom2,atom30,atom42,atom53,atom64,atom85],[atom1,atom2,atom30,atom42,atom59,atom64,atom85],[atom1,atom2,atom30,atom42,atom64,atom85,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_55 : t6_55.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_57 : BankTree := .block [[atom1,atom2,atom30,atom42,atom64,atom105],[atom1,atom2,atom30,atom43,atom44,atom64,atom105],[atom1,atom2,atom30,atom44,atom53,atom76,atom85],[atom1,atom2,atom30,atom44,atom60,atom64,atom85],[atom1,atom2,atom35,atom38,atom60,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_57 : t6_57.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_58 : BankTree := .block [[atom1,atom3,atom7,atom15,atom38,atom81,atom85],[atom1,atom3,atom7,atom30,atom38,atom64,atom105],[atom1,atom3,atom15,atom19,atom38,atom64,atom85],[atom1,atom3,atom15,atom30,atom38,atom64,atom68],[atom1,atom3,atom15,atom30,atom41,atom64,atom94],[atom1,atom3,atom15,atom30,atom41,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_58 : t6_58.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_56 : BankTree := .fork [atom1,atom3,atom7,atom15,atom38,atom81,atom85] t6_57 t6_58
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_56 : t6_56.rows.all (refuses 5 t5_0)=true := by simp only [t6_56,BankTree.rows,List.all_append,ok_t6_57,ok_t6_58,Bool.true_and]
noncomputable def t6_54 : BankTree := .fork [atom1,atom2,atom30,atom42,atom64,atom105] t6_55 t6_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_54 : t6_54.rows.all (refuses 5 t5_0)=true := by simp only [t6_54,BankTree.rows,List.all_append,ok_t6_55,ok_t6_56,Bool.true_and]
noncomputable def t6_60 : BankTree := .block [[atom1,atom3,atom15,atom33,atom38,atom64,atom88],[atom1,atom3,atom15,atom38,atom41,atom81,atom85],[atom1,atom3,atom15,atom41,atom51,atom64,atom85],[atom1,atom3,atom30,atom38,atom41,atom64,atom105],[atom1,atom3,atom30,atom41,atom53,atom64,atom85],[atom1,atom4,atom10,atom15,atom38,atom68,atom81],[atom1,atom4,atom10,atom15,atom41,atom81,atom94],[atom1,atom4,atom10,atom15,atom41,atom85,atom109],[atom1,atom4,atom10,atom19,atom38,atom64,atom105],[atom1,atom4,atom10,atom30,atom41,atom64,atom110]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_60 : t6_60.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_62 : BankTree := .block [[atom1,atom4,atom10,atom30,atom41,atom96,atom105],[atom1,atom4,atom10,atom38,atom41,atom81,atom105],[atom1,atom4,atom10,atom41,atom51,atom64,atom105],[atom1,atom4,atom10,atom41,atom53,atom81,atom85],[atom1,atom4,atom15,atom19,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_62 : t6_62.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_63 : BankTree := .block [[atom1,atom4,atom15,atom30,atom38,atom68,atom76],[atom1,atom4,atom15,atom30,atom41,atom76,atom94],[atom1,atom4,atom15,atom30,atom41,atom85,atom103],[atom1,atom4,atom15,atom33,atom38,atom76,atom88],[atom1,atom4,atom15,atom41,atom43,atom81,atom85],[atom1,atom4,atom15,atom41,atom51,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_63 : t6_63.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_61 : BankTree := .fork [atom1,atom4,atom15,atom30,atom38,atom68,atom76] t6_62 t6_63
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_61 : t6_61.rows.all (refuses 5 t5_0)=true := by simp only [t6_61,BankTree.rows,List.all_append,ok_t6_62,ok_t6_63,Bool.true_and]
noncomputable def t6_59 : BankTree := .fork [atom1,atom4,atom10,atom30,atom41,atom96,atom105] t6_60 t6_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_59 : t6_59.rows.all (refuses 5 t5_0)=true := by simp only [t6_59,BankTree.rows,List.all_append,ok_t6_60,ok_t6_61,Bool.true_and]
noncomputable def t6_53 : BankTree := .fork [atom1,atom3,atom15,atom33,atom38,atom64,atom88] t6_54 t6_59
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_53 : t6_53.rows.all (refuses 5 t5_0)=true := by simp only [t6_53,BankTree.rows,List.all_append,ok_t6_54,ok_t6_59,Bool.true_and]
noncomputable def t6_66 : BankTree := .block [[atom1,atom4,atom19,atom27,atom38,atom64,atom85],[atom1,atom4,atom27,atom30,atom38,atom64,atom68],[atom1,atom4,atom27,atom30,atom41,atom64,atom94],[atom1,atom4,atom27,atom30,atom41,atom85,atom96],[atom1,atom4,atom27,atom33,atom38,atom64,atom88],[atom1,atom4,atom27,atom41,atom51,atom64,atom85],[atom1,atom4,atom30,atom41,atom43,atom64,atom105],[atom1,atom4,atom30,atom41,atom53,atom76,atom85],[atom1,atom4,atom30,atom41,atom60,atom64,atom85],[atom1,atom7,atom10,atom15,atom38,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_66 : t6_66.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_68 : BankTree := .block [[atom1,atom7,atom10,atom30,atom38,atom64,atom105],[atom1,atom7,atom15,atom30,atom38,atom64,atom89],[atom1,atom7,atom15,atom30,atom38,atom72,atom85],[atom1,atom7,atom15,atom30,atom38,atom76,atom85],[atom1,atom7,atom15,atom30,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_68 : t6_68.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_69 : BankTree := .block [[atom1,atom7,atom15,atom34,atom38,atom64,atom85],[atom1,atom7,atom23,atom30,atom38,atom64,atom85],[atom1,atom7,atom27,atom30,atom38,atom64,atom85],[atom1,atom8,atom10,atom14,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom30,atom38,atom63],[atom1,atom8,atom10,atom15,atom30,atom64,atom93]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_69 : t6_69.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_67 : BankTree := .fork [atom1,atom7,atom15,atom34,atom38,atom64,atom85] t6_68 t6_69
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_67 : t6_67.rows.all (refuses 5 t5_0)=true := by simp only [t6_67,BankTree.rows,List.all_append,ok_t6_68,ok_t6_69,Bool.true_and]
noncomputable def t6_65 : BankTree := .fork [atom1,atom7,atom10,atom30,atom38,atom64,atom105] t6_66 t6_67
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_65 : t6_65.rows.all (refuses 5 t5_0)=true := by simp only [t6_65,BankTree.rows,List.all_append,ok_t6_66,ok_t6_67,Bool.true_and]
noncomputable def t6_72 : BankTree := .block [[atom1,atom8,atom10,atom15,atom30,atom94,atom96],[atom1,atom8,atom10,atom15,atom38,atom79,atom85],[atom1,atom8,atom10,atom15,atom38,atom81,atom88],[atom1,atom8,atom10,atom15,atom50,atom64,atom85],[atom1,atom8,atom10,atom15,atom51,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_72 : t6_72.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_73 : BankTree := .block [[atom1,atom8,atom10,atom30,atom38,atom64,atom80],[atom1,atom8,atom10,atom30,atom53,atom85,atom96],[atom1,atom8,atom10,atom33,atom38,atom64,atom105],[atom1,atom8,atom10,atom51,atom53,atom64,atom85],[atom1,atom8,atom13,atom15,atom38,atom76,atom85],[atom1,atom8,atom13,atom27,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_73 : t6_73.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_71 : BankTree := .fork [atom1,atom8,atom10,atom30,atom38,atom64,atom80] t6_72 t6_73
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_71 : t6_71.rows.all (refuses 5 t5_0)=true := by simp only [t6_71,BankTree.rows,List.all_append,ok_t6_72,ok_t6_73,Bool.true_and]
noncomputable def t6_75 : BankTree := .block [[atom1,atom8,atom15,atom30,atom38,atom62,atom76],[atom1,atom8,atom15,atom30,atom38,atom72,atom85],[atom1,atom8,atom15,atom30,atom38,atom76,atom88],[atom1,atom8,atom15,atom30,atom38,atom76,atom90],[atom1,atom8,atom15,atom30,atom38,atom76,atom92]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_75 : t6_75.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_76 : BankTree := .block [[atom1,atom8,atom15,atom30,atom38,atom76,atom94],[atom1,atom8,atom15,atom30,atom38,atom85,atom103],[atom1,atom8,atom15,atom30,atom42,atom64,atom85],[atom1,atom8,atom15,atom30,atom43,atom64,atom94],[atom1,atom8,atom15,atom32,atom38,atom76,atom85],[atom1,atom8,atom15,atom33,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_76 : t6_76.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_74 : BankTree := .fork [atom1,atom8,atom15,atom30,atom38,atom76,atom94] t6_75 t6_76
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_74 : t6_74.rows.all (refuses 5 t5_0)=true := by simp only [t6_74,BankTree.rows,List.all_append,ok_t6_75,ok_t6_76,Bool.true_and]
noncomputable def t6_70 : BankTree := .fork [atom1,atom8,atom15,atom30,atom38,atom62,atom76] t6_71 t6_74
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_70 : t6_70.rows.all (refuses 5 t5_0)=true := by simp only [t6_70,BankTree.rows,List.all_append,ok_t6_71,ok_t6_74,Bool.true_and]
noncomputable def t6_64 : BankTree := .fork [atom1,atom8,atom10,atom15,atom30,atom94,atom96] t6_65 t6_70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_64 : t6_64.rows.all (refuses 5 t5_0)=true := by simp only [t6_64,BankTree.rows,List.all_append,ok_t6_65,ok_t6_70,Bool.true_and]
noncomputable def t6_52 : BankTree := .fork [atom1,atom4,atom19,atom27,atom38,atom64,atom85] t6_53 t6_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_52 : t6_52.rows.all (refuses 5 t5_0)=true := by simp only [t6_52,BankTree.rows,List.all_append,ok_t6_53,ok_t6_64,Bool.true_and]
noncomputable def t6_80 : BankTree := .block [[atom1,atom8,atom15,atom35,atom38,atom76,atom85],[atom1,atom8,atom15,atom37,atom38,atom76,atom85],[atom1,atom8,atom15,atom38,atom51,atom76,atom85],[atom1,atom8,atom15,atom38,atom76,atom81,atom85],[atom1,atom8,atom15,atom43,atom51,atom64,atom85],[atom1,atom8,atom23,atom30,atom38,atom64,atom85],[atom1,atom8,atom27,atom30,atom38,atom62,atom64],[atom1,atom8,atom27,atom30,atom38,atom64,atom87],[atom1,atom8,atom27,atom30,atom38,atom64,atom88],[atom1,atom8,atom27,atom30,atom38,atom64,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_80 : t6_80.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_82 : BankTree := .block [[atom1,atom8,atom27,atom30,atom38,atom64,atom92],[atom1,atom8,atom27,atom30,atom38,atom64,atom94],[atom1,atom8,atom27,atom30,atom38,atom64,atom105],[atom1,atom8,atom27,atom30,atom38,atom76,atom85],[atom1,atom8,atom27,atom30,atom38,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_82 : t6_82.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_83 : BankTree := .block [[atom1,atom8,atom27,atom33,atom38,atom64,atom85],[atom1,atom8,atom27,atom35,atom38,atom64,atom85],[atom1,atom8,atom27,atom37,atom38,atom64,atom85],[atom1,atom8,atom27,atom38,atom51,atom64,atom85],[atom1,atom8,atom30,atom38,atom53,atom76,atom85],[atom1,atom8,atom30,atom38,atom60,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_83 : t6_83.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_81 : BankTree := .fork [atom1,atom8,atom27,atom33,atom38,atom64,atom85] t6_82 t6_83
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_81 : t6_81.rows.all (refuses 5 t5_0)=true := by simp only [t6_81,BankTree.rows,List.all_append,ok_t6_82,ok_t6_83,Bool.true_and]
noncomputable def t6_79 : BankTree := .fork [atom1,atom8,atom27,atom30,atom38,atom64,atom92] t6_80 t6_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_79 : t6_79.rows.all (refuses 5 t5_0)=true := by simp only [t6_79,BankTree.rows,List.all_append,ok_t6_80,ok_t6_81,Bool.true_and]
noncomputable def t6_85 : BankTree := .block [[atom1,atom10,atom15,atom19,atom38,atom64,atom90],[atom1,atom10,atom15,atom26,atom38,atom64,atom85],[atom1,atom10,atom15,atom30,atom38,atom64,atom75],[atom1,atom10,atom15,atom30,atom41,atom90,atom96],[atom1,atom10,atom15,atom30,atom49,atom85,atom96],[atom1,atom10,atom15,atom33,atom38,atom64,atom92],[atom1,atom10,atom15,atom35,atom38,atom64,atom68],[atom1,atom10,atom15,atom35,atom41,atom64,atom94],[atom1,atom10,atom15,atom35,atom41,atom85,atom96],[atom1,atom10,atom15,atom37,atom38,atom64,atom88]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_85 : t6_85.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_87 : BankTree := .block [[atom1,atom10,atom15,atom37,atom38,atom64,atom92],[atom1,atom10,atom15,atom41,atom51,atom64,atom90],[atom1,atom10,atom30,atom41,atom53,atom64,atom90],[atom1,atom10,atom30,atom49,atom53,atom64,atom85],[atom1,atom10,atom35,atom41,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_87 : t6_87.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_88 : BankTree := .block [[atom1,atom15,atom30,atom38,atom41,atom76,atom90],[atom1,atom15,atom30,atom38,atom49,atom76,atom85],[atom1,atom15,atom30,atom41,atom42,atom64,atom85],[atom1,atom15,atom30,atom41,atom43,atom64,atom90],[atom1,atom15,atom30,atom42,atom48,atom64,atom85],[atom1,atom15,atom30,atom43,atom49,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_88 : t6_88.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_86 : BankTree := .fork [atom1,atom15,atom30,atom38,atom41,atom76,atom90] t6_87 t6_88
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_86 : t6_86.rows.all (refuses 5 t5_0)=true := by simp only [t6_86,BankTree.rows,List.all_append,ok_t6_87,ok_t6_88,Bool.true_and]
noncomputable def t6_84 : BankTree := .fork [atom1,atom10,atom15,atom37,atom38,atom64,atom92] t6_85 t6_86
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_84 : t6_84.rows.all (refuses 5 t5_0)=true := by simp only [t6_84,BankTree.rows,List.all_append,ok_t6_85,ok_t6_86,Bool.true_and]
noncomputable def t6_78 : BankTree := .fork [atom1,atom10,atom15,atom19,atom38,atom64,atom90] t6_79 t6_84
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_78 : t6_78.rows.all (refuses 5 t5_0)=true := by simp only [t6_78,BankTree.rows,List.all_append,ok_t6_79,ok_t6_84,Bool.true_and]
noncomputable def t6_91 : BankTree := .block [[atom1,atom15,atom35,atom41,atom43,atom64,atom85],[atom1,atom27,atom30,atom38,atom49,atom64,atom85],[atom1,atom27,atom35,atom38,atom41,atom64,atom85],[atom2,atom3,atom6,atom15,atom38,atom81,atom85],[atom2,atom3,atom6,atom30,atom38,atom64,atom105],[atom2,atom3,atom12,atom15,atom38,atom81,atom85],[atom2,atom3,atom12,atom30,atom38,atom64,atom105],[atom2,atom3,atom13,atom15,atom38,atom64,atom87],[atom2,atom3,atom13,atom18,atom38,atom64,atom85],[atom2,atom3,atom15,atom16,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_91 : t6_91.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_93 : BankTree := .block [[atom2,atom3,atom15,atom18,atom38,atom81,atom85],[atom2,atom3,atom15,atom30,atom38,atom62,atom67],[atom2,atom3,atom15,atom30,atom38,atom64,atom65],[atom2,atom3,atom15,atom30,atom38,atom64,atom86],[atom2,atom3,atom15,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_93 : t6_93.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_94 : BankTree := .block [[atom2,atom3,atom15,atom30,atom38,atom64,atom91],[atom2,atom3,atom15,atom30,atom38,atom64,atom97],[atom2,atom3,atom15,atom30,atom38,atom64,atom107],[atom2,atom3,atom15,atom30,atom38,atom66,atom85],[atom2,atom3,atom15,atom30,atom38,atom72,atom87],[atom2,atom3,atom15,atom30,atom38,atom87,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_94 : t6_94.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_92 : BankTree := .fork [atom2,atom3,atom15,atom30,atom38,atom64,atom91] t6_93 t6_94
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_92 : t6_92.rows.all (refuses 5 t5_0)=true := by simp only [t6_92,BankTree.rows,List.all_append,ok_t6_93,ok_t6_94,Bool.true_and]
noncomputable def t6_90 : BankTree := .fork [atom2,atom3,atom15,atom18,atom38,atom81,atom85] t6_91 t6_92
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_90 : t6_90.rows.all (refuses 5 t5_0)=true := by simp only [t6_90,BankTree.rows,List.all_append,ok_t6_91,ok_t6_92,Bool.true_and]
noncomputable def t6_97 : BankTree := .block [[atom2,atom3,atom15,atom30,atom39,atom64,atom85],[atom2,atom3,atom15,atom30,atom40,atom85,atom96],[atom2,atom3,atom15,atom30,atom42,atom64,atom87],[atom2,atom3,atom15,atom31,atom38,atom64,atom85],[atom2,atom3,atom15,atom32,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_97 : t6_97.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_98 : BankTree := .block [[atom2,atom3,atom15,atom32,atom38,atom64,atom85],[atom2,atom3,atom15,atom32,atom38,atom64,atom87],[atom2,atom3,atom15,atom32,atom38,atom64,atom88],[atom2,atom3,atom15,atom32,atom38,atom64,atom89],[atom2,atom3,atom15,atom32,atom38,atom64,atom90],[atom2,atom3,atom15,atom32,atom38,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_98 : t6_98.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_96 : BankTree := .fork [atom2,atom3,atom15,atom32,atom38,atom64,atom85] t6_97 t6_98
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_96 : t6_96.rows.all (refuses 5 t5_0)=true := by simp only [t6_96,BankTree.rows,List.all_append,ok_t6_97,ok_t6_98,Bool.true_and]
noncomputable def t6_100 : BankTree := .block [[atom2,atom3,atom15,atom32,atom38,atom64,atom105],[atom2,atom3,atom15,atom32,atom38,atom72,atom85],[atom2,atom3,atom15,atom32,atom38,atom76,atom85],[atom2,atom3,atom15,atom32,atom38,atom81,atom85],[atom2,atom3,atom15,atom32,atom38,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_100 : t6_100.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_101 : BankTree := .block [[atom2,atom3,atom15,atom32,atom42,atom64,atom85],[atom2,atom3,atom15,atom33,atom38,atom64,atom87],[atom2,atom3,atom15,atom34,atom38,atom64,atom87],[atom2,atom3,atom15,atom35,atom38,atom64,atom87],[atom2,atom3,atom15,atom36,atom38,atom64,atom85],[atom2,atom3,atom15,atom38,atom40,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_101 : t6_101.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_99 : BankTree := .fork [atom2,atom3,atom15,atom32,atom42,atom64,atom85] t6_100 t6_101
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_99 : t6_99.rows.all (refuses 5 t5_0)=true := by simp only [t6_99,BankTree.rows,List.all_append,ok_t6_100,ok_t6_101,Bool.true_and]
noncomputable def t6_95 : BankTree := .fork [atom2,atom3,atom15,atom32,atom38,atom64,atom105] t6_96 t6_99
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_95 : t6_95.rows.all (refuses 5 t5_0)=true := by simp only [t6_95,BankTree.rows,List.all_append,ok_t6_96,ok_t6_99,Bool.true_and]
noncomputable def t6_89 : BankTree := .fork [atom2,atom3,atom15,atom30,atom39,atom64,atom85] t6_90 t6_95
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_89 : t6_89.rows.all (refuses 5 t5_0)=true := by simp only [t6_89,BankTree.rows,List.all_append,ok_t6_90,ok_t6_95,Bool.true_and]
noncomputable def t6_77 : BankTree := .fork [atom1,atom15,atom35,atom41,atom43,atom64,atom85] t6_78 t6_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_77 : t6_77.rows.all (refuses 5 t5_0)=true := by simp only [t6_77,BankTree.rows,List.all_append,ok_t6_78,ok_t6_89,Bool.true_and]
noncomputable def t6_51 : BankTree := .fork [atom1,atom8,atom15,atom35,atom38,atom76,atom85] t6_52 t6_77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_51 : t6_51.rows.all (refuses 5 t5_0)=true := by simp only [t6_51,BankTree.rows,List.all_append,ok_t6_52,ok_t6_77,Bool.true_and]
noncomputable def t6_1 : BankTree := .fork [atom1,atom2,atom27,atom35,atom38,atom81,atom85] t6_2 t6_51
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_1 : t6_1.rows.all (refuses 5 t5_0)=true := by simp only [t6_1,BankTree.rows,List.all_append,ok_t6_2,ok_t6_51,Bool.true_and]
noncomputable def t6_107 : BankTree := .block [[atom2,atom3,atom15,atom38,atom51,atom64,atom87],[atom2,atom3,atom15,atom38,atom54,atom64,atom85],[atom2,atom3,atom15,atom38,atom64,atom81,atom87],[atom2,atom3,atom15,atom38,atom64,atom83,atom85],[atom2,atom3,atom15,atom38,atom67,atom81,atom85],[atom2,atom3,atom15,atom38,atom81,atom83,atom85],[atom2,atom3,atom15,atom38,atom81,atom85,atom87],[atom2,atom3,atom17,atom30,atom38,atom64,atom85],[atom2,atom3,atom18,atom30,atom38,atom64,atom105],[atom2,atom3,atom23,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_107 : t6_107.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_109 : BankTree := .block [[atom2,atom3,atom23,atom32,atom38,atom64,atom85],[atom2,atom3,atom27,atom30,atom38,atom64,atom87],[atom2,atom3,atom30,atom32,atom38,atom64,atom105],[atom2,atom3,atom30,atom38,atom40,atom64,atom105],[atom2,atom3,atom30,atom38,atom53,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_109 : t6_109.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_110 : BankTree := .block [[atom2,atom3,atom30,atom38,atom64,atom67,atom105],[atom2,atom3,atom30,atom38,atom64,atom87,atom105],[atom2,atom3,atom30,atom38,atom64,atom105,atom107],[atom2,atom3,atom30,atom40,atom53,atom64,atom85],[atom2,atom3,atom32,atom38,atom53,atom64,atom85],[atom2,atom4,atom6,atom15,atom38,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_110 : t6_110.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_108 : BankTree := .fork [atom2,atom3,atom30,atom38,atom64,atom67,atom105] t6_109 t6_110
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_108 : t6_108.rows.all (refuses 5 t5_0)=true := by simp only [t6_108,BankTree.rows,List.all_append,ok_t6_109,ok_t6_110,Bool.true_and]
noncomputable def t6_106 : BankTree := .fork [atom2,atom3,atom23,atom32,atom38,atom64,atom85] t6_107 t6_108
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_106 : t6_106.rows.all (refuses 5 t5_0)=true := by simp only [t6_106,BankTree.rows,List.all_append,ok_t6_107,ok_t6_108,Bool.true_and]
noncomputable def t6_112 : BankTree := .block [[atom2,atom4,atom6,atom30,atom38,atom64,atom105],[atom2,atom4,atom10,atom12,atom38,atom81,atom105],[atom2,atom4,atom10,atom13,atom38,atom64,atom107],[atom2,atom4,atom10,atom14,atom38,atom64,atom87],[atom2,atom4,atom10,atom15,atom30,atom67,atom93],[atom2,atom4,atom10,atom15,atom30,atom96,atom97],[atom2,atom4,atom10,atom15,atom32,atom38,atom63],[atom2,atom4,atom10,atom15,atom32,atom64,atom93],[atom2,atom4,atom10,atom15,atom32,atom94,atom96],[atom2,atom4,atom10,atom15,atom38,atom62,atom83]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_112 : t6_112.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_114 : BankTree := .block [[atom2,atom4,atom10,atom15,atom38,atom79,atom87],[atom2,atom4,atom10,atom15,atom38,atom81,atom86],[atom2,atom4,atom10,atom15,atom38,atom82,atom85],[atom2,atom4,atom10,atom15,atom39,atom81,atom85],[atom2,atom4,atom10,atom15,atom50,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_114 : t6_114.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_115 : BankTree := .block [[atom2,atom4,atom10,atom17,atom38,atom81,atom85],[atom2,atom4,atom10,atom18,atom38,atom79,atom85],[atom2,atom4,atom10,atom18,atom38,atom81,atom105],[atom2,atom4,atom10,atom18,atom50,atom64,atom85],[atom2,atom4,atom10,atom30,atom38,atom64,atom106],[atom2,atom4,atom10,atom30,atom38,atom66,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_115 : t6_115.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_113 : BankTree := .fork [atom2,atom4,atom10,atom17,atom38,atom81,atom85] t6_114 t6_115
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_113 : t6_113.rows.all (refuses 5 t5_0)=true := by simp only [t6_113,BankTree.rows,List.all_append,ok_t6_114,ok_t6_115,Bool.true_and]
noncomputable def t6_111 : BankTree := .fork [atom2,atom4,atom10,atom15,atom38,atom79,atom87] t6_112 t6_113
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_111 : t6_111.rows.all (refuses 5 t5_0)=true := by simp only [t6_111,BankTree.rows,List.all_append,ok_t6_112,ok_t6_113,Bool.true_and]
noncomputable def t6_105 : BankTree := .fork [atom2,atom4,atom6,atom30,atom38,atom64,atom105] t6_106 t6_111
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_105 : t6_105.rows.all (refuses 5 t5_0)=true := by simp only [t6_105,BankTree.rows,List.all_append,ok_t6_106,ok_t6_111,Bool.true_and]
noncomputable def t6_118 : BankTree := .block [[atom2,atom4,atom10,atom30,atom38,atom67,atom80],[atom2,atom4,atom10,atom30,atom39,atom64,atom105],[atom2,atom4,atom10,atom30,atom40,atom96,atom105],[atom2,atom4,atom10,atom30,atom53,atom87,atom96],[atom2,atom4,atom10,atom31,atom38,atom64,atom105],[atom2,atom4,atom10,atom32,atom38,atom64,atom80],[atom2,atom4,atom10,atom32,atom38,atom81,atom105],[atom2,atom4,atom10,atom32,atom53,atom85,atom96],[atom2,atom4,atom10,atom38,atom40,atom81,atom105],[atom2,atom4,atom10,atom38,atom67,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_118 : t6_118.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_120 : BankTree := .block [[atom2,atom4,atom10,atom38,atom81,atom83,atom105],[atom2,atom4,atom10,atom38,atom81,atom87,atom105],[atom2,atom4,atom10,atom38,atom81,atom105,atom107],[atom2,atom4,atom10,atom40,atom53,atom81,atom85],[atom2,atom4,atom10,atom51,atom53,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_120 : t6_120.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_121 : BankTree := .block [[atom2,atom4,atom10,atom53,atom54,atom64,atom85],[atom2,atom4,atom11,atom15,atom38,atom81,atom85],[atom2,atom4,atom11,atom30,atom38,atom64,atom105],[atom2,atom4,atom12,atom13,atom38,atom64,atom105],[atom2,atom4,atom12,atom14,atom38,atom64,atom85],[atom2,atom4,atom12,atom15,atom30,atom38,atom63]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_121 : t6_121.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_119 : BankTree := .fork [atom2,atom4,atom10,atom53,atom54,atom64,atom85] t6_120 t6_121
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_119 : t6_119.rows.all (refuses 5 t5_0)=true := by simp only [t6_119,BankTree.rows,List.all_append,ok_t6_120,ok_t6_121,Bool.true_and]
noncomputable def t6_117 : BankTree := .fork [atom2,atom4,atom10,atom38,atom81,atom83,atom105] t6_118 t6_119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_117 : t6_117.rows.all (refuses 5 t5_0)=true := by simp only [t6_117,BankTree.rows,List.all_append,ok_t6_118,ok_t6_119,Bool.true_and]
noncomputable def t6_123 : BankTree := .block [[atom2,atom4,atom12,atom15,atom30,atom64,atom93],[atom2,atom4,atom12,atom15,atom30,atom94,atom96],[atom2,atom4,atom12,atom15,atom38,atom62,atom81],[atom2,atom4,atom12,atom15,atom38,atom79,atom85],[atom2,atom4,atom12,atom15,atom38,atom81,atom88],[atom2,atom4,atom12,atom15,atom38,atom81,atom94],[atom2,atom4,atom12,atom15,atom38,atom81,atom105],[atom2,atom4,atom12,atom15,atom38,atom85,atom109],[atom2,atom4,atom12,atom15,atom50,atom64,atom85],[atom2,atom4,atom12,atom15,atom51,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_123 : t6_123.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_125 : BankTree := .block [[atom2,atom4,atom12,atom30,atom38,atom64,atom80],[atom2,atom4,atom12,atom30,atom38,atom64,atom110],[atom2,atom4,atom12,atom30,atom38,atom81,atom105],[atom2,atom4,atom12,atom30,atom38,atom96,atom105],[atom2,atom4,atom12,atom30,atom53,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_125 : t6_125.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_126 : BankTree := .block [[atom2,atom4,atom12,atom33,atom38,atom64,atom105],[atom2,atom4,atom12,atom38,atom51,atom64,atom105],[atom2,atom4,atom12,atom38,atom53,atom81,atom85],[atom2,atom4,atom12,atom38,atom64,atom81,atom105],[atom2,atom4,atom12,atom38,atom81,atom85,atom105],[atom2,atom4,atom12,atom38,atom81,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_126 : t6_126.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_124 : BankTree := .fork [atom2,atom4,atom12,atom33,atom38,atom64,atom105] t6_125 t6_126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_124 : t6_124.rows.all (refuses 5 t5_0)=true := by simp only [t6_124,BankTree.rows,List.all_append,ok_t6_125,ok_t6_126,Bool.true_and]
noncomputable def t6_122 : BankTree := .fork [atom2,atom4,atom12,atom30,atom38,atom64,atom80] t6_123 t6_124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_122 : t6_122.rows.all (refuses 5 t5_0)=true := by simp only [t6_122,BankTree.rows,List.all_append,ok_t6_123,ok_t6_124,Bool.true_and]
noncomputable def t6_116 : BankTree := .fork [atom2,atom4,atom12,atom15,atom30,atom64,atom93] t6_117 t6_122
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_116 : t6_116.rows.all (refuses 5 t5_0)=true := by simp only [t6_116,BankTree.rows,List.all_append,ok_t6_117,ok_t6_122,Bool.true_and]
noncomputable def t6_104 : BankTree := .fork [atom2,atom4,atom10,atom30,atom38,atom67,atom80] t6_105 t6_116
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_104 : t6_104.rows.all (refuses 5 t5_0)=true := by simp only [t6_104,BankTree.rows,List.all_append,ok_t6_105,ok_t6_116,Bool.true_and]
noncomputable def t6_130 : BankTree := .block [[atom2,atom4,atom12,atom51,atom53,atom64,atom85],[atom2,atom4,atom13,atom18,atom38,atom76,atom85],[atom2,atom4,atom13,atom27,atom38,atom64,atom87],[atom2,atom4,atom13,atom29,atom38,atom64,atom85],[atom2,atom4,atom15,atom16,atom38,atom76,atom85],[atom2,atom4,atom15,atom29,atom38,atom81,atom85],[atom2,atom4,atom15,atom30,atom38,atom62,atom78],[atom2,atom4,atom15,atom30,atom38,atom72,atom87],[atom2,atom4,atom15,atom30,atom38,atom76,atom86],[atom2,atom4,atom15,atom30,atom38,atom77,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_130 : t6_130.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_132 : BankTree := .block [[atom2,atom4,atom15,atom30,atom39,atom76,atom85],[atom2,atom4,atom15,atom30,atom42,atom64,atom87],[atom2,atom4,atom15,atom31,atom38,atom76,atom85],[atom2,atom4,atom15,atom32,atom38,atom62,atom76],[atom2,atom4,atom15,atom32,atom38,atom72,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_132 : t6_132.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_133 : BankTree := .block [[atom2,atom4,atom15,atom32,atom38,atom76,atom88],[atom2,atom4,atom15,atom32,atom38,atom76,atom90],[atom2,atom4,atom15,atom32,atom38,atom76,atom94],[atom2,atom4,atom15,atom32,atom38,atom85,atom103],[atom2,atom4,atom15,atom32,atom42,atom64,atom85],[atom2,atom4,atom15,atom32,atom43,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_133 : t6_133.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_131 : BankTree := .fork [atom2,atom4,atom15,atom32,atom38,atom76,atom88] t6_132 t6_133
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_131 : t6_131.rows.all (refuses 5 t5_0)=true := by simp only [t6_131,BankTree.rows,List.all_append,ok_t6_132,ok_t6_133,Bool.true_and]
noncomputable def t6_129 : BankTree := .fork [atom2,atom4,atom15,atom30,atom39,atom76,atom85] t6_130 t6_131
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_129 : t6_129.rows.all (refuses 5 t5_0)=true := by simp only [t6_129,BankTree.rows,List.all_append,ok_t6_130,ok_t6_131,Bool.true_and]
noncomputable def t6_135 : BankTree := .block [[atom2,atom4,atom15,atom38,atom47,atom81,atom85],[atom2,atom4,atom15,atom38,atom54,atom76,atom85],[atom2,atom4,atom15,atom38,atom76,atom81,atom87],[atom2,atom4,atom15,atom38,atom76,atom83,atom85],[atom2,atom4,atom15,atom38,atom78,atom81,atom85],[atom2,atom4,atom15,atom43,atom51,atom64,atom87],[atom2,atom4,atom17,atom30,atom38,atom76,atom85],[atom2,atom4,atom18,atom27,atom38,atom81,atom85],[atom2,atom4,atom23,atom30,atom38,atom64,atom87],[atom2,atom4,atom23,atom32,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_135 : t6_135.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_137 : BankTree := .block [[atom2,atom4,atom27,atom30,atom38,atom62,atom67],[atom2,atom4,atom27,atom30,atom38,atom64,atom65],[atom2,atom4,atom27,atom30,atom38,atom64,atom86],[atom2,atom4,atom27,atom30,atom38,atom64,atom97],[atom2,atom4,atom27,atom30,atom38,atom64,atom107]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_137 : t6_137.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_138 : BankTree := .block [[atom2,atom4,atom27,atom30,atom38,atom66,atom85],[atom2,atom4,atom27,atom30,atom38,atom87,atom96],[atom2,atom4,atom27,atom30,atom39,atom64,atom85],[atom2,atom4,atom27,atom30,atom40,atom85,atom96],[atom2,atom4,atom27,atom31,atom38,atom64,atom85],[atom2,atom4,atom27,atom32,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_138 : t6_138.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_136 : BankTree := .fork [atom2,atom4,atom27,atom30,atom38,atom66,atom85] t6_137 t6_138
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_136 : t6_136.rows.all (refuses 5 t5_0)=true := by simp only [t6_136,BankTree.rows,List.all_append,ok_t6_137,ok_t6_138,Bool.true_and]
noncomputable def t6_134 : BankTree := .fork [atom2,atom4,atom27,atom30,atom38,atom62,atom67] t6_135 t6_136
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_134 : t6_134.rows.all (refuses 5 t5_0)=true := by simp only [t6_134,BankTree.rows,List.all_append,ok_t6_135,ok_t6_136,Bool.true_and]
noncomputable def t6_128 : BankTree := .fork [atom2,atom4,atom15,atom38,atom47,atom81,atom85] t6_129 t6_134
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_128 : t6_128.rows.all (refuses 5 t5_0)=true := by simp only [t6_128,BankTree.rows,List.all_append,ok_t6_129,ok_t6_134,Bool.true_and]
noncomputable def t6_141 : BankTree := .block [[atom2,atom4,atom27,atom32,atom38,atom81,atom85],[atom2,atom4,atom27,atom33,atom38,atom64,atom87],[atom2,atom4,atom27,atom35,atom38,atom64,atom87],[atom2,atom4,atom27,atom38,atom51,atom64,atom87],[atom2,atom4,atom28,atom30,atom38,atom64,atom85],[atom2,atom4,atom29,atom30,atom38,atom64,atom105],[atom2,atom4,atom30,atom38,atom47,atom64,atom105],[atom2,atom4,atom30,atom38,atom60,atom64,atom87],[atom2,atom4,atom30,atom38,atom64,atom78,atom105],[atom2,atom4,atom30,atom38,atom67,atom76,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_141 : t6_141.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_143 : BankTree := .block [[atom2,atom4,atom30,atom38,atom76,atom87,atom105],[atom2,atom4,atom30,atom40,atom53,atom76,atom85],[atom2,atom4,atom32,atom38,atom53,atom76,atom85],[atom2,atom5,atom15,atom30,atom38,atom64,atom85],[atom2,atom6,atom15,atom30,atom38,atom72,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_143 : t6_143.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_144 : BankTree := .block [[atom2,atom6,atom15,atom30,atom42,atom64,atom85],[atom2,atom6,atom23,atom30,atom38,atom64,atom85],[atom2,atom8,atom12,atom15,atom38,atom81,atom85],[atom2,atom8,atom12,atom30,atom38,atom64,atom105],[atom2,atom8,atom15,atom32,atom38,atom76,atom85],[atom2,atom8,atom27,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_144 : t6_144.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_142 : BankTree := .fork [atom2,atom6,atom15,atom30,atom42,atom64,atom85] t6_143 t6_144
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_142 : t6_142.rows.all (refuses 5 t5_0)=true := by simp only [t6_142,BankTree.rows,List.all_append,ok_t6_143,ok_t6_144,Bool.true_and]
noncomputable def t6_140 : BankTree := .fork [atom2,atom4,atom30,atom38,atom76,atom87,atom105] t6_141 t6_142
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_140 : t6_140.rows.all (refuses 5 t5_0)=true := by simp only [t6_140,BankTree.rows,List.all_append,ok_t6_141,ok_t6_142,Bool.true_and]
noncomputable def t6_147 : BankTree := .block [[atom2,atom9,atom15,atom30,atom38,atom64,atom87],[atom2,atom9,atom15,atom32,atom38,atom64,atom85],[atom2,atom10,atom13,atom18,atom38,atom64,atom90],[atom2,atom10,atom15,atom16,atom38,atom64,atom90],[atom2,atom10,atom15,atom21,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_147 : t6_147.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_148 : BankTree := .block [[atom2,atom10,atom15,atom30,atom38,atom66,atom90],[atom2,atom10,atom15,atom30,atom38,atom67,atom70],[atom2,atom10,atom15,atom30,atom39,atom64,atom90],[atom2,atom10,atom15,atom30,atom40,atom90,atom96],[atom2,atom10,atom15,atom30,atom42,atom64,atom87],[atom2,atom10,atom15,atom30,atom44,atom87,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_148 : t6_148.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_146 : BankTree := .fork [atom2,atom10,atom15,atom30,atom38,atom66,atom90] t6_147 t6_148
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_146 : t6_146.rows.all (refuses 5 t5_0)=true := by simp only [t6_146,BankTree.rows,List.all_append,ok_t6_147,ok_t6_148,Bool.true_and]
noncomputable def t6_150 : BankTree := .block [[atom2,atom10,atom15,atom31,atom38,atom64,atom90],[atom2,atom10,atom15,atom32,atom38,atom64,atom70],[atom2,atom10,atom15,atom32,atom38,atom64,atom89],[atom2,atom10,atom15,atom32,atom38,atom64,atom92],[atom2,atom10,atom15,atom32,atom38,atom64,atom100]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_150 : t6_150.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_151 : BankTree := .block [[atom2,atom10,atom15,atom32,atom38,atom76,atom90],[atom2,atom10,atom15,atom32,atom38,atom90,atom96],[atom2,atom10,atom15,atom32,atom42,atom64,atom85],[atom2,atom10,atom15,atom32,atom44,atom85,atom96],[atom2,atom10,atom15,atom34,atom38,atom64,atom87],[atom2,atom10,atom15,atom35,atom38,atom62,atom67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_151 : t6_151.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_149 : BankTree := .fork [atom2,atom10,atom15,atom32,atom38,atom76,atom90] t6_150 t6_151
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_149 : t6_149.rows.all (refuses 5 t5_0)=true := by simp only [t6_149,BankTree.rows,List.all_append,ok_t6_150,ok_t6_151,Bool.true_and]
noncomputable def t6_145 : BankTree := .fork [atom2,atom10,atom15,atom31,atom38,atom64,atom90] t6_146 t6_149
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_145 : t6_145.rows.all (refuses 5 t5_0)=true := by simp only [t6_145,BankTree.rows,List.all_append,ok_t6_146,ok_t6_149,Bool.true_and]
noncomputable def t6_139 : BankTree := .fork [atom2,atom9,atom15,atom30,atom38,atom64,atom87] t6_140 t6_145
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_139 : t6_139.rows.all (refuses 5 t5_0)=true := by simp only [t6_139,BankTree.rows,List.all_append,ok_t6_140,ok_t6_145,Bool.true_and]
noncomputable def t6_127 : BankTree := .fork [atom2,atom4,atom27,atom32,atom38,atom81,atom85] t6_128 t6_139
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_127 : t6_127.rows.all (refuses 5 t5_0)=true := by simp only [t6_127,BankTree.rows,List.all_append,ok_t6_128,ok_t6_139,Bool.true_and]
noncomputable def t6_103 : BankTree := .fork [atom2,atom4,atom12,atom51,atom53,atom64,atom85] t6_104 t6_127
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_103 : t6_103.rows.all (refuses 5 t5_0)=true := by simp only [t6_103,BankTree.rows,List.all_append,ok_t6_104,ok_t6_127,Bool.true_and]
noncomputable def t6_156 : BankTree := .block [[atom2,atom10,atom15,atom35,atom38,atom64,atom65],[atom2,atom10,atom15,atom35,atom38,atom64,atom86],[atom2,atom10,atom15,atom35,atom38,atom64,atom97],[atom2,atom10,atom15,atom35,atom38,atom64,atom107],[atom2,atom10,atom15,atom35,atom38,atom66,atom85],[atom2,atom10,atom15,atom35,atom38,atom87,atom96],[atom2,atom10,atom15,atom35,atom39,atom64,atom85],[atom2,atom10,atom15,atom35,atom40,atom85,atom96],[atom2,atom10,atom15,atom37,atom38,atom64,atom87],[atom2,atom10,atom15,atom38,atom54,atom64,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_156 : t6_156.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_158 : BankTree := .block [[atom2,atom10,atom15,atom38,atom57,atom64,atom87],[atom2,atom10,atom15,atom38,atom64,atom83,atom90],[atom2,atom10,atom15,atom38,atom67,atom81,atom90],[atom2,atom10,atom15,atom38,atom81,atom87,atom90],[atom2,atom10,atom15,atom40,atom44,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_158 : t6_158.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_159 : BankTree := .block [[atom2,atom10,atom17,atom30,atom38,atom64,atom90],[atom2,atom10,atom17,atom35,atom38,atom64,atom85],[atom2,atom10,atom18,atom21,atom38,atom64,atom85],[atom2,atom10,atom18,atom35,atom38,atom64,atom105],[atom2,atom10,atom27,atom35,atom38,atom64,atom87],[atom2,atom10,atom30,atom40,atom44,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_159 : t6_159.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_157 : BankTree := .fork [atom2,atom10,atom17,atom30,atom38,atom64,atom90] t6_158 t6_159
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_157 : t6_157.rows.all (refuses 5 t5_0)=true := by simp only [t6_157,BankTree.rows,List.all_append,ok_t6_158,ok_t6_159,Bool.true_and]
noncomputable def t6_155 : BankTree := .fork [atom2,atom10,atom15,atom38,atom57,atom64,atom87] t6_156 t6_157
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_155 : t6_155.rows.all (refuses 5 t5_0)=true := by simp only [t6_155,BankTree.rows,List.all_append,ok_t6_156,ok_t6_157,Bool.true_and]
noncomputable def t6_161 : BankTree := .block [[atom2,atom10,atom30,atom40,atom53,atom64,atom90],[atom2,atom10,atom30,atom44,atom53,atom64,atom87],[atom2,atom10,atom32,atom35,atom38,atom64,atom105],[atom2,atom10,atom32,atom38,atom53,atom64,atom90],[atom2,atom10,atom32,atom44,atom53,atom64,atom85],[atom2,atom10,atom35,atom38,atom53,atom64,atom87],[atom2,atom10,atom35,atom40,atom53,atom64,atom85],[atom2,atom11,atom15,atom30,atom38,atom64,atom90],[atom2,atom11,atom15,atom35,atom38,atom64,atom85],[atom2,atom12,atom15,atom21,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_161 : t6_161.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_163 : BankTree := .block [[atom2,atom12,atom15,atom30,atom38,atom64,atom70],[atom2,atom12,atom15,atom30,atom38,atom76,atom90],[atom2,atom12,atom15,atom30,atom42,atom64,atom85],[atom2,atom12,atom15,atom30,atom44,atom85,atom96],[atom2,atom12,atom15,atom35,atom38,atom64,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_163 : t6_163.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_164 : BankTree := .block [[atom2,atom12,atom15,atom35,atom38,atom76,atom85],[atom2,atom12,atom15,atom38,atom44,atom81,atom85],[atom2,atom12,atom27,atom30,atom38,atom64,atom90],[atom2,atom12,atom27,atom35,atom38,atom64,atom85],[atom2,atom12,atom30,atom38,atom44,atom64,atom105],[atom2,atom12,atom30,atom44,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_164 : t6_164.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_162 : BankTree := .fork [atom2,atom12,atom15,atom35,atom38,atom76,atom85] t6_163 t6_164
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_162 : t6_162.rows.all (refuses 5 t5_0)=true := by simp only [t6_162,BankTree.rows,List.all_append,ok_t6_163,ok_t6_164,Bool.true_and]
noncomputable def t6_160 : BankTree := .fork [atom2,atom12,atom15,atom30,atom38,atom64,atom70] t6_161 t6_162
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_160 : t6_160.rows.all (refuses 5 t5_0)=true := by simp only [t6_160,BankTree.rows,List.all_append,ok_t6_161,ok_t6_162,Bool.true_and]
noncomputable def t6_154 : BankTree := .fork [atom2,atom10,atom30,atom40,atom53,atom64,atom90] t6_155 t6_160
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_154 : t6_154.rows.all (refuses 5 t5_0)=true := by simp only [t6_154,BankTree.rows,List.all_append,ok_t6_155,ok_t6_160,Bool.true_and]
noncomputable def t6_167 : BankTree := .block [[atom2,atom15,atom18,atom30,atom38,atom76,atom90],[atom2,atom15,atom18,atom30,atom42,atom64,atom85],[atom2,atom15,atom27,atom35,atom38,atom64,atom87],[atom2,atom15,atom30,atom32,atom38,atom76,atom90],[atom2,atom15,atom30,atom32,atom42,atom64,atom85],[atom2,atom15,atom30,atom38,atom40,atom76,atom90],[atom2,atom15,atom30,atom38,atom42,atom64,atom87],[atom2,atom15,atom30,atom38,atom67,atom76,atom90],[atom2,atom15,atom30,atom38,atom76,atom78,atom90],[atom2,atom15,atom30,atom38,atom76,atom87,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_167 : t6_167.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_169 : BankTree := .block [[atom2,atom15,atom30,atom40,atom42,atom64,atom85],[atom2,atom15,atom30,atom40,atom44,atom76,atom85],[atom2,atom15,atom30,atom42,atom46,atom64,atom85],[atom2,atom15,atom30,atom42,atom64,atom67,atom85],[atom2,atom15,atom30,atom42,atom64,atom85,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_169 : t6_169.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_170 : BankTree := .block [[atom2,atom15,atom30,atom42,atom64,atom87],[atom2,atom15,atom30,atom43,atom44,atom64,atom87],[atom2,atom15,atom30,atom44,atom47,atom64,atom85],[atom2,atom15,atom32,atom38,atom42,atom64,atom85],[atom2,atom15,atom32,atom38,atom43,atom64,atom90],[atom2,atom15,atom32,atom38,atom44,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_170 : t6_170.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_168 : BankTree := .fork [atom2,atom15,atom30,atom42,atom64,atom87] t6_169 t6_170
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_168 : t6_168.rows.all (refuses 5 t5_0)=true := by simp only [t6_168,BankTree.rows,List.all_append,ok_t6_169,ok_t6_170,Bool.true_and]
noncomputable def t6_166 : BankTree := .fork [atom2,atom15,atom30,atom40,atom42,atom64,atom85] t6_167 t6_168
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_166 : t6_166.rows.all (refuses 5 t5_0)=true := by simp only [t6_166,BankTree.rows,List.all_append,ok_t6_167,ok_t6_168,Bool.true_and]
noncomputable def t6_173 : BankTree := .block [[atom2,atom15,atom32,atom38,atom64,atom76,atom90],[atom2,atom15,atom32,atom38,atom76,atom85,atom90],[atom2,atom15,atom32,atom38,atom76,atom90],[atom2,atom15,atom32,atom42,atom64,atom85],[atom2,atom15,atom32,atom43,atom44,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_173 : t6_173.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_174 : BankTree := .block [[atom2,atom15,atom35,atom38,atom43,atom64,atom87],[atom2,atom18,atom27,atom35,atom38,atom64,atom85],[atom2,atom27,atom29,atom35,atom38,atom64,atom85],[atom2,atom27,atom30,atom35,atom38,atom64,atom87],[atom2,atom27,atom30,atom38,atom44,atom64,atom87],[atom2,atom27,atom30,atom40,atom44,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_174 : t6_174.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_172 : BankTree := .fork [atom2,atom15,atom35,atom38,atom43,atom64,atom87] t6_173 t6_174
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_172 : t6_172.rows.all (refuses 5 t5_0)=true := by simp only [t6_172,BankTree.rows,List.all_append,ok_t6_173,ok_t6_174,Bool.true_and]
noncomputable def t6_176 : BankTree := .block [[atom2,atom27,atom32,atom35,atom38,atom64,atom85],[atom2,atom27,atom35,atom38,atom40,atom64,atom85],[atom2,atom27,atom35,atom38,atom64,atom67,atom85],[atom2,atom27,atom35,atom38,atom64,atom85,atom87],[atom2,atom27,atom35,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_176 : t6_176.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_177 : BankTree := .block [[atom3,atom7,atom15,atom30,atom38,atom64,atom87],[atom3,atom7,atom15,atom32,atom38,atom64,atom85],[atom3,atom15,atom30,atom38,atom41,atom64,atom87],[atom3,atom15,atom30,atom40,atom41,atom64,atom85],[atom3,atom15,atom32,atom38,atom41,atom64,atom85],[atom4,atom10,atom15,atom19,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_177 : t6_177.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_175 : BankTree := .fork [atom3,atom7,atom15,atom30,atom38,atom64,atom87] t6_176 t6_177
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_175 : t6_175.rows.all (refuses 5 t5_0)=true := by simp only [t6_175,BankTree.rows,List.all_append,ok_t6_176,ok_t6_177,Bool.true_and]
noncomputable def t6_171 : BankTree := .fork [atom2,atom27,atom32,atom35,atom38,atom64,atom85] t6_172 t6_175
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_171 : t6_171.rows.all (refuses 5 t5_0)=true := by simp only [t6_171,BankTree.rows,List.all_append,ok_t6_172,ok_t6_175,Bool.true_and]
noncomputable def t6_165 : BankTree := .fork [atom2,atom15,atom32,atom38,atom64,atom76,atom90] t6_166 t6_171
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_165 : t6_165.rows.all (refuses 5 t5_0)=true := by simp only [t6_165,BankTree.rows,List.all_append,ok_t6_166,ok_t6_171,Bool.true_and]
noncomputable def t6_153 : BankTree := .fork [atom2,atom15,atom18,atom30,atom38,atom76,atom90] t6_154 t6_165
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_153 : t6_153.rows.all (refuses 5 t5_0)=true := by simp only [t6_153,BankTree.rows,List.all_append,ok_t6_154,ok_t6_165,Bool.true_and]
noncomputable def t6_181 : BankTree := .block [[atom4,atom10,atom15,atom30,atom38,atom67,atom68],[atom4,atom10,atom15,atom30,atom41,atom64,atom97],[atom4,atom10,atom15,atom30,atom41,atom87,atom96],[atom4,atom10,atom15,atom32,atom38,atom64,atom68],[atom4,atom10,atom15,atom32,atom41,atom64,atom94],[atom4,atom10,atom15,atom32,atom41,atom85,atom96],[atom4,atom10,atom15,atom40,atom41,atom81,atom85],[atom4,atom10,atom15,atom41,atom51,atom64,atom87],[atom4,atom10,atom15,atom41,atom54,atom64,atom85],[atom4,atom10,atom18,atom19,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_181 : t6_181.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_183 : BankTree := .block [[atom4,atom10,atom30,atom40,atom41,atom64,atom105],[atom4,atom10,atom30,atom41,atom53,atom64,atom87],[atom4,atom10,atom32,atom41,atom53,atom64,atom85],[atom4,atom12,atom15,atom19,atom38,atom64,atom85],[atom4,atom12,atom15,atom30,atom38,atom64,atom68]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_183 : t6_183.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_184 : BankTree := .block [[atom4,atom12,atom15,atom30,atom41,atom64,atom94],[atom4,atom12,atom15,atom30,atom41,atom85,atom96],[atom4,atom12,atom15,atom33,atom38,atom64,atom88],[atom4,atom12,atom15,atom38,atom41,atom81,atom85],[atom4,atom12,atom15,atom41,atom51,atom64,atom85],[atom4,atom12,atom30,atom38,atom41,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_184 : t6_184.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_182 : BankTree := .fork [atom4,atom12,atom15,atom30,atom41,atom64,atom94] t6_183 t6_184
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_182 : t6_182.rows.all (refuses 5 t5_0)=true := by simp only [t6_182,BankTree.rows,List.all_append,ok_t6_183,ok_t6_184,Bool.true_and]
noncomputable def t6_180 : BankTree := .fork [atom4,atom10,atom30,atom40,atom41,atom64,atom105] t6_181 t6_182
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_180 : t6_180.rows.all (refuses 5 t5_0)=true := by simp only [t6_180,BankTree.rows,List.all_append,ok_t6_181,ok_t6_182,Bool.true_and]
noncomputable def t6_186 : BankTree := .block [[atom4,atom12,atom30,atom41,atom53,atom64,atom85],[atom4,atom15,atom30,atom40,atom41,atom76,atom85],[atom4,atom15,atom30,atom41,atom43,atom64,atom87],[atom4,atom15,atom30,atom41,atom47,atom64,atom85],[atom4,atom15,atom32,atom38,atom41,atom76,atom85],[atom4,atom15,atom32,atom41,atom43,atom64,atom85],[atom4,atom27,atom30,atom38,atom41,atom64,atom87],[atom4,atom27,atom30,atom40,atom41,atom64,atom85],[atom5,atom8,atom15,atom30,atom38,atom64,atom85],[atom6,atom7,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_186 : t6_186.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_188 : BankTree := .block [[atom6,atom8,atom15,atom30,atom38,atom64,atom85],[atom7,atom10,atom15,atom30,atom38,atom64,atom87],[atom7,atom10,atom15,atom32,atom38,atom64,atom85],[atom7,atom12,atom15,atom30,atom38,atom64,atom85],[atom8,atom10,atom13,atom18,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_188 : t6_188.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_189 : BankTree := .block [[atom8,atom10,atom15,atom16,atom38,atom64,atom85],[atom8,atom10,atom15,atom30,atom38,atom62,atom67],[atom8,atom10,atom15,atom30,atom38,atom64,atom65],[atom8,atom10,atom15,atom30,atom38,atom66,atom85],[atom8,atom10,atom15,atom30,atom39,atom64,atom85],[atom8,atom10,atom15,atom30,atom40,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_189 : t6_189.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_187 : BankTree := .fork [atom8,atom10,atom15,atom16,atom38,atom64,atom85] t6_188 t6_189
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_187 : t6_187.rows.all (refuses 5 t5_0)=true := by simp only [t6_187,BankTree.rows,List.all_append,ok_t6_188,ok_t6_189,Bool.true_and]
noncomputable def t6_185 : BankTree := .fork [atom6,atom8,atom15,atom30,atom38,atom64,atom85] t6_186 t6_187
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_185 : t6_185.rows.all (refuses 5 t5_0)=true := by simp only [t6_185,BankTree.rows,List.all_append,ok_t6_186,ok_t6_187,Bool.true_and]
noncomputable def t6_179 : BankTree := .fork [atom4,atom12,atom30,atom41,atom53,atom64,atom85] t6_180 t6_185
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_179 : t6_179.rows.all (refuses 5 t5_0)=true := by simp only [t6_179,BankTree.rows,List.all_append,ok_t6_180,ok_t6_185,Bool.true_and]
noncomputable def t6_192 : BankTree := .block [[atom8,atom10,atom15,atom32,atom38,atom64,atom87],[atom8,atom10,atom15,atom32,atom38,atom64,atom88],[atom8,atom10,atom15,atom33,atom38,atom64,atom87],[atom8,atom10,atom15,atom38,atom67,atom81,atom85],[atom8,atom10,atom17,atom30,atom38,atom64,atom85],[atom8,atom10,atom18,atom30,atom38,atom64,atom105],[atom8,atom10,atom30,atom40,atom53,atom64,atom85],[atom8,atom11,atom15,atom30,atom38,atom64,atom85],[atom8,atom12,atom13,atom15,atom38,atom64,atom85],[atom8,atom12,atom15,atom30,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_192 : t6_192.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_194 : BankTree := .block [[atom8,atom12,atom15,atom30,atom38,atom64,atom87],[atom8,atom12,atom15,atom30,atom38,atom64,atom88],[atom8,atom12,atom15,atom30,atom38,atom64,atom90],[atom8,atom12,atom15,atom30,atom38,atom64,atom92],[atom8,atom12,atom15,atom30,atom38,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_194 : t6_194.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_195 : BankTree := .block [[atom8,atom12,atom15,atom30,atom38,atom64,atom105],[atom8,atom12,atom15,atom30,atom38,atom76,atom85],[atom8,atom12,atom15,atom30,atom38,atom85,atom96],[atom8,atom12,atom15,atom32,atom38,atom64,atom85],[atom8,atom12,atom15,atom33,atom38,atom64,atom85],[atom8,atom12,atom15,atom35,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_195 : t6_195.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_193 : BankTree := .fork [atom8,atom12,atom15,atom30,atom38,atom64,atom105] t6_194 t6_195
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_193 : t6_193.rows.all (refuses 5 t5_0)=true := by simp only [t6_193,BankTree.rows,List.all_append,ok_t6_194,ok_t6_195,Bool.true_and]
noncomputable def t6_191 : BankTree := .fork [atom8,atom12,atom15,atom30,atom38,atom64,atom87] t6_192 t6_193
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_191 : t6_191.rows.all (refuses 5 t5_0)=true := by simp only [t6_191,BankTree.rows,List.all_append,ok_t6_192,ok_t6_193,Bool.true_and]
noncomputable def t6_198 : BankTree := .block [[atom8,atom12,atom15,atom37,atom38,atom64,atom85],[atom8,atom12,atom15,atom38,atom51,atom64,atom85],[atom8,atom12,atom15,atom38,atom64,atom81,atom85],[atom8,atom12,atom27,atom30,atom38,atom64,atom85],[atom8,atom12,atom30,atom38,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_198 : t6_198.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_199 : BankTree := .block [[atom8,atom15,atom18,atom30,atom38,atom76,atom85],[atom8,atom15,atom29,atom30,atom38,atom64,atom85],[atom8,atom15,atom30,atom38,atom40,atom76,atom85],[atom8,atom15,atom30,atom38,atom47,atom64,atom85],[atom8,atom15,atom30,atom38,atom64,atom78,atom85],[atom8,atom15,atom30,atom38,atom67,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_199 : t6_199.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_197 : BankTree := .fork [atom8,atom15,atom18,atom30,atom38,atom76,atom85] t6_198 t6_199
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_197 : t6_197.rows.all (refuses 5 t5_0)=true := by simp only [t6_197,BankTree.rows,List.all_append,ok_t6_198,ok_t6_199,Bool.true_and]
noncomputable def t6_201 : BankTree := .block [[atom8,atom15,atom30,atom38,atom76,atom78,atom85],[atom8,atom18,atom27,atom30,atom38,atom64,atom85],[atom8,atom27,atom29,atom30,atom38,atom64,atom85],[atom8,atom27,atom30,atom38,atom40,atom64,atom85],[atom8,atom27,atom30,atom38,atom64,atom67,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_201 : t6_201.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_202 : BankTree := .block [[atom10,atom15,atom30,atom40,atom41,atom64,atom90],[atom10,atom15,atom30,atom40,atom49,atom64,atom85],[atom10,atom15,atom32,atom38,atom41,atom64,atom90],[atom10,atom15,atom35,atom38,atom41,atom64,atom87],[atom10,atom15,atom35,atom40,atom41,atom64,atom85],[atom12,atom15,atom30,atom38,atom49,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_202 : t6_202.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_200 : BankTree := .fork [atom10,atom15,atom30,atom40,atom41,atom64,atom90] t6_201 t6_202
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_200 : t6_200.rows.all (refuses 5 t5_0)=true := by simp only [t6_200,BankTree.rows,List.all_append,ok_t6_201,ok_t6_202,Bool.true_and]
noncomputable def t6_196 : BankTree := .fork [atom8,atom15,atom30,atom38,atom76,atom78,atom85] t6_197 t6_200
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_196 : t6_196.rows.all (refuses 5 t5_0)=true := by simp only [t6_196,BankTree.rows,List.all_append,ok_t6_197,ok_t6_200,Bool.true_and]
noncomputable def t6_190 : BankTree := .fork [atom8,atom12,atom15,atom37,atom38,atom64,atom85] t6_191 t6_196
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_190 : t6_190.rows.all (refuses 5 t5_0)=true := by simp only [t6_190,BankTree.rows,List.all_append,ok_t6_191,ok_t6_196,Bool.true_and]
noncomputable def t6_178 : BankTree := .fork [atom8,atom10,atom15,atom32,atom38,atom64,atom87] t6_179 t6_190
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_178 : t6_178.rows.all (refuses 5 t5_0)=true := by simp only [t6_178,BankTree.rows,List.all_append,ok_t6_179,ok_t6_190,Bool.true_and]
noncomputable def t6_152 : BankTree := .fork [atom4,atom10,atom15,atom30,atom38,atom67,atom68] t6_153 t6_178
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_152 : t6_152.rows.all (refuses 5 t5_0)=true := by simp only [t6_152,BankTree.rows,List.all_append,ok_t6_153,ok_t6_178,Bool.true_and]
noncomputable def t6_102 : BankTree := .fork [atom2,atom10,atom15,atom35,atom38,atom64,atom65] t6_103 t6_152
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_102 : t6_102.rows.all (refuses 5 t5_0)=true := by simp only [t6_102,BankTree.rows,List.all_append,ok_t6_103,ok_t6_152,Bool.true_and]
noncomputable def t6_0 : BankTree := .fork [atom2,atom3,atom15,atom38,atom51,atom64,atom87] t6_1 t6_102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_0 : t6_0.rows.all (refuses 5 t5_0)=true := by simp only [t6_0,BankTree.rows,List.all_append,ok_t6_1,ok_t6_102,Bool.true_and]
theorem safe6 : Safe 6 t6_0 := certify 5 t5_0 t6_0 safe5 ok_t6_0
noncomputable def t7_5 : BankTree := .block [[atom0,atom2,atom3,atom15,atom30,atom38,atom64,atom85],[atom0,atom2,atom4,atom10,atom15,atom38,atom81,atom85],[atom0,atom2,atom4,atom10,atom30,atom38,atom64,atom105],[atom0,atom2,atom4,atom15,atom30,atom38,atom76,atom85],[atom0,atom2,atom4,atom27,atom30,atom38,atom64,atom85],[atom0,atom2,atom10,atom15,atom30,atom38,atom64,atom90],[atom0,atom2,atom10,atom15,atom35,atom38,atom64,atom85],[atom0,atom8,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom4,atom15,atom38,atom81,atom85],[atom1,atom2,atom3,atom4,atom30,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_5 : t7_5.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_7 : BankTree := .block [[atom1,atom2,atom3,atom10,atom15,atom38,atom81,atom85],[atom1,atom2,atom3,atom10,atom30,atom38,atom64,atom105],[atom1,atom2,atom3,atom13,atom15,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom62,atom64],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_7 : t7_7.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_8 : BankTree := .block [[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom87],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom88],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom89],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom90],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom94],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_8 : t7_8.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_6 : BankTree := .fork [atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom87] t7_7 t7_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_6 : t7_6.rows.all (refuses 6 t6_0)=true := by simp only [t7_6,BankTree.rows,List.all_append,ok_t7_7,ok_t7_8,Bool.true_and]
noncomputable def t7_4 : BankTree := .fork [atom1,atom2,atom3,atom10,atom15,atom38,atom81,atom85] t7_5 t7_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_4 : t7_4.rows.all (refuses 6 t6_0)=true := by simp only [t7_4,BankTree.rows,List.all_append,ok_t7_5,ok_t7_6,Bool.true_and]
noncomputable def t7_10 : BankTree := .block [[atom1,atom2,atom3,atom15,atom30,atom38,atom72,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom76,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom81,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom85,atom96],[atom1,atom2,atom3,atom15,atom30,atom42,atom64,atom85],[atom1,atom2,atom3,atom15,atom32,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom33,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom34,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom35,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom38,atom51,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_10 : t7_10.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_12 : BankTree := .block [[atom1,atom2,atom3,atom15,atom38,atom64,atom81,atom85],[atom1,atom2,atom3,atom15,atom38,atom81,atom85],[atom1,atom2,atom3,atom23,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom27,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom30,atom38,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_12 : t7_12.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_13 : BankTree := .block [[atom1,atom2,atom3,atom30,atom38,atom64,atom85,atom105],[atom1,atom2,atom3,atom30,atom38,atom64,atom105],[atom1,atom2,atom4,atom10,atom13,atom38,atom64,atom105],[atom1,atom2,atom4,atom10,atom14,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom63],[atom1,atom2,atom4,atom10,atom15,atom30,atom64,atom93]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_13 : t7_13.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_11 : BankTree := .fork [atom1,atom2,atom3,atom30,atom38,atom64,atom85,atom105] t7_12 t7_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_11 : t7_11.rows.all (refuses 6 t6_0)=true := by simp only [t7_11,BankTree.rows,List.all_append,ok_t7_12,ok_t7_13,Bool.true_and]
noncomputable def t7_9 : BankTree := .fork [atom1,atom2,atom3,atom15,atom38,atom64,atom81,atom85] t7_10 t7_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_9 : t7_9.rows.all (refuses 6 t6_0)=true := by simp only [t7_9,BankTree.rows,List.all_append,ok_t7_10,ok_t7_11,Bool.true_and]
noncomputable def t7_3 : BankTree := .fork [atom1,atom2,atom3,atom15,atom30,atom38,atom72,atom85] t7_4 t7_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_3 : t7_3.rows.all (refuses 6 t6_0)=true := by simp only [t7_3,BankTree.rows,List.all_append,ok_t7_4,ok_t7_9,Bool.true_and]
noncomputable def t7_16 : BankTree := .block [[atom1,atom2,atom4,atom10,atom15,atom30,atom94,atom96],[atom1,atom2,atom4,atom10,atom15,atom38,atom62,atom81],[atom1,atom2,atom4,atom10,atom15,atom38,atom79,atom85],[atom1,atom2,atom4,atom10,atom15,atom38,atom81,atom88],[atom1,atom2,atom4,atom10,atom15,atom38,atom81,atom94],[atom1,atom2,atom4,atom10,atom15,atom38,atom81,atom105],[atom1,atom2,atom4,atom10,atom15,atom38,atom85,atom109],[atom1,atom2,atom4,atom10,atom15,atom50,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom51,atom64,atom94],[atom1,atom2,atom4,atom10,atom30,atom38,atom64,atom80]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_16 : t7_16.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_18 : BankTree := .block [[atom1,atom2,atom4,atom10,atom30,atom38,atom64,atom110],[atom1,atom2,atom4,atom10,atom30,atom38,atom81,atom105],[atom1,atom2,atom4,atom10,atom30,atom38,atom96,atom105],[atom1,atom2,atom4,atom10,atom30,atom53,atom85,atom96],[atom1,atom2,atom4,atom10,atom33,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_18 : t7_18.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_19 : BankTree := .block [[atom1,atom2,atom4,atom10,atom38,atom51,atom64,atom105],[atom1,atom2,atom4,atom10,atom38,atom53,atom81,atom85],[atom1,atom2,atom4,atom10,atom38,atom64,atom81,atom105],[atom1,atom2,atom4,atom10,atom38,atom81,atom85,atom105],[atom1,atom2,atom4,atom10,atom38,atom81,atom105],[atom1,atom2,atom4,atom10,atom51,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_19 : t7_19.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_17 : BankTree := .fork [atom1,atom2,atom4,atom10,atom38,atom51,atom64,atom105] t7_18 t7_19
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_17 : t7_17.rows.all (refuses 6 t6_0)=true := by simp only [t7_17,BankTree.rows,List.all_append,ok_t7_18,ok_t7_19,Bool.true_and]
noncomputable def t7_15 : BankTree := .fork [atom1,atom2,atom4,atom10,atom30,atom38,atom64,atom110] t7_16 t7_17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_15 : t7_15.rows.all (refuses 6 t6_0)=true := by simp only [t7_15,BankTree.rows,List.all_append,ok_t7_16,ok_t7_17,Bool.true_and]
noncomputable def t7_21 : BankTree := .block [[atom1,atom2,atom4,atom12,atom15,atom38,atom81,atom85],[atom1,atom2,atom4,atom12,atom30,atom38,atom64,atom105],[atom1,atom2,atom4,atom13,atom15,atom38,atom76,atom85],[atom1,atom2,atom4,atom13,atom27,atom38,atom64,atom85],[atom1,atom2,atom4,atom15,atom27,atom38,atom81,atom85],[atom1,atom2,atom4,atom15,atom30,atom38,atom62,atom76],[atom1,atom2,atom4,atom15,atom30,atom38,atom72,atom85],[atom1,atom2,atom4,atom15,atom30,atom38,atom76,atom88],[atom1,atom2,atom4,atom15,atom30,atom38,atom76,atom90],[atom1,atom2,atom4,atom15,atom30,atom38,atom76,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_21 : t7_21.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_23 : BankTree := .block [[atom1,atom2,atom4,atom15,atom30,atom38,atom85,atom103],[atom1,atom2,atom4,atom15,atom30,atom42,atom64,atom85],[atom1,atom2,atom4,atom15,atom30,atom43,atom64,atom94],[atom1,atom2,atom4,atom15,atom32,atom38,atom76,atom85],[atom1,atom2,atom4,atom15,atom33,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_23 : t7_23.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_24 : BankTree := .block [[atom1,atom2,atom4,atom15,atom35,atom38,atom76,atom85],[atom1,atom2,atom4,atom15,atom38,atom43,atom81,atom85],[atom1,atom2,atom4,atom15,atom38,atom51,atom76,atom85],[atom1,atom2,atom4,atom15,atom38,atom76,atom81,atom85],[atom1,atom2,atom4,atom15,atom43,atom51,atom64,atom85],[atom1,atom2,atom4,atom23,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_24 : t7_24.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_22 : BankTree := .fork [atom1,atom2,atom4,atom15,atom35,atom38,atom76,atom85] t7_23 t7_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_22 : t7_22.rows.all (refuses 6 t6_0)=true := by simp only [t7_22,BankTree.rows,List.all_append,ok_t7_23,ok_t7_24,Bool.true_and]
noncomputable def t7_20 : BankTree := .fork [atom1,atom2,atom4,atom15,atom30,atom38,atom85,atom103] t7_21 t7_22
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_20 : t7_20.rows.all (refuses 6 t6_0)=true := by simp only [t7_20,BankTree.rows,List.all_append,ok_t7_21,ok_t7_22,Bool.true_and]
noncomputable def t7_14 : BankTree := .fork [atom1,atom2,atom4,atom12,atom15,atom38,atom81,atom85] t7_15 t7_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_14 : t7_14.rows.all (refuses 6 t6_0)=true := by simp only [t7_14,BankTree.rows,List.all_append,ok_t7_15,ok_t7_20,Bool.true_and]
noncomputable def t7_2 : BankTree := .fork [atom1,atom2,atom4,atom10,atom15,atom30,atom94,atom96] t7_3 t7_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_2 : t7_2.rows.all (refuses 6 t6_0)=true := by simp only [t7_2,BankTree.rows,List.all_append,ok_t7_3,ok_t7_14,Bool.true_and]
noncomputable def t7_28 : BankTree := .block [[atom1,atom2,atom4,atom27,atom30,atom38,atom62,atom64],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom87],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom88],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom90],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom94],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom105],[atom1,atom2,atom4,atom27,atom30,atom38,atom76,atom85],[atom1,atom2,atom4,atom27,atom30,atom38,atom81,atom85],[atom1,atom2,atom4,atom27,atom30,atom38,atom85,atom96],[atom1,atom2,atom4,atom27,atom33,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_28 : t7_28.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_30 : BankTree := .block [[atom1,atom2,atom4,atom27,atom35,atom38,atom64,atom85],[atom1,atom2,atom4,atom27,atom38,atom51,atom64,atom85],[atom1,atom2,atom4,atom30,atom38,atom43,atom64,atom105],[atom1,atom2,atom4,atom30,atom38,atom53,atom76,atom85],[atom1,atom2,atom4,atom30,atom38,atom60,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_30 : t7_30.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_31 : BankTree := .block [[atom1,atom2,atom4,atom30,atom38,atom64,atom76,atom105],[atom1,atom2,atom4,atom30,atom38,atom76,atom85,atom105],[atom1,atom2,atom8,atom10,atom15,atom38,atom81,atom85],[atom1,atom2,atom8,atom10,atom30,atom38,atom64,atom105],[atom1,atom2,atom8,atom15,atom30,atom38,atom76,atom85],[atom1,atom2,atom8,atom27,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_31 : t7_31.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_29 : BankTree := .fork [atom1,atom2,atom4,atom30,atom38,atom64,atom76,atom105] t7_30 t7_31
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_29 : t7_29.rows.all (refuses 6 t6_0)=true := by simp only [t7_29,BankTree.rows,List.all_append,ok_t7_30,ok_t7_31,Bool.true_and]
noncomputable def t7_27 : BankTree := .fork [atom1,atom2,atom4,atom27,atom35,atom38,atom64,atom85] t7_28 t7_29
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_27 : t7_27.rows.all (refuses 6 t6_0)=true := by simp only [t7_27,BankTree.rows,List.all_append,ok_t7_28,ok_t7_29,Bool.true_and]
noncomputable def t7_33 : BankTree := .block [[atom1,atom2,atom9,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom10,atom13,atom15,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom21,atom38,atom64,atom85],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom70],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom89],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom92],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom100],[atom1,atom2,atom10,atom15,atom30,atom38,atom76,atom90],[atom1,atom2,atom10,atom15,atom30,atom38,atom90,atom96],[atom1,atom2,atom10,atom15,atom30,atom42,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_33 : t7_33.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_35 : BankTree := .block [[atom1,atom2,atom10,atom15,atom30,atom44,atom85,atom96],[atom1,atom2,atom10,atom15,atom32,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom33,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom34,atom38,atom64,atom85],[atom1,atom2,atom10,atom15,atom35,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_35 : t7_35.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_36 : BankTree := .block [[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom87],[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom88],[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom94],[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom105],[atom1,atom2,atom10,atom15,atom35,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_36 : t7_36.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_34 : BankTree := .fork [atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom87] t7_35 t7_36
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_34 : t7_34.rows.all (refuses 6 t6_0)=true := by simp only [t7_34,BankTree.rows,List.all_append,ok_t7_35,ok_t7_36,Bool.true_and]
noncomputable def t7_32 : BankTree := .fork [atom1,atom2,atom10,atom15,atom30,atom44,atom85,atom96] t7_33 t7_34
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_32 : t7_32.rows.all (refuses 6 t6_0)=true := by simp only [t7_32,BankTree.rows,List.all_append,ok_t7_33,ok_t7_34,Bool.true_and]
noncomputable def t7_26 : BankTree := .fork [atom1,atom2,atom9,atom15,atom30,atom38,atom64,atom85] t7_27 t7_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_26 : t7_26.rows.all (refuses 6 t6_0)=true := by simp only [t7_26,BankTree.rows,List.all_append,ok_t7_27,ok_t7_32,Bool.true_and]
noncomputable def t7_39 : BankTree := .block [[atom1,atom2,atom10,atom15,atom35,atom38,atom81,atom85],[atom1,atom2,atom10,atom15,atom35,atom38,atom85,atom96],[atom1,atom2,atom10,atom15,atom37,atom38,atom64,atom85],[atom1,atom2,atom10,atom15,atom38,atom44,atom81,atom85],[atom1,atom2,atom10,atom15,atom38,atom51,atom64,atom90],[atom1,atom2,atom10,atom15,atom38,atom57,atom64,atom85],[atom1,atom2,atom10,atom15,atom38,atom64,atom81,atom90],[atom1,atom2,atom10,atom15,atom38,atom81,atom85,atom90],[atom1,atom2,atom10,atom27,atom30,atom38,atom64,atom90],[atom1,atom2,atom10,atom27,atom35,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_39 : t7_39.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_41 : BankTree := .block [[atom1,atom2,atom10,atom30,atom35,atom38,atom64,atom105],[atom1,atom2,atom10,atom30,atom38,atom44,atom64,atom105],[atom1,atom2,atom10,atom30,atom38,atom53,atom64,atom90],[atom1,atom2,atom10,atom30,atom38,atom64,atom90,atom105],[atom1,atom2,atom10,atom30,atom44,atom53,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_41 : t7_41.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_42 : BankTree := .block [[atom1,atom2,atom10,atom35,atom38,atom53,atom64,atom85],[atom1,atom2,atom15,atom27,atom35,atom38,atom64,atom85],[atom1,atom2,atom15,atom30,atom38,atom42,atom64,atom85],[atom1,atom2,atom15,atom30,atom38,atom43,atom64,atom90],[atom1,atom2,atom15,atom30,atom38,atom44,atom76,atom85],[atom1,atom2,atom15,atom30,atom38,atom64,atom76,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_42 : t7_42.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_40 : BankTree := .fork [atom1,atom2,atom10,atom35,atom38,atom53,atom64,atom85] t7_41 t7_42
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_40 : t7_40.rows.all (refuses 6 t6_0)=true := by simp only [t7_40,BankTree.rows,List.all_append,ok_t7_41,ok_t7_42,Bool.true_and]
noncomputable def t7_38 : BankTree := .fork [atom1,atom2,atom10,atom30,atom35,atom38,atom64,atom105] t7_39 t7_40
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_38 : t7_38.rows.all (refuses 6 t6_0)=true := by simp only [t7_38,BankTree.rows,List.all_append,ok_t7_39,ok_t7_40,Bool.true_and]
noncomputable def t7_44 : BankTree := .block [[atom1,atom2,atom15,atom30,atom38,atom76,atom85,atom90],[atom1,atom2,atom15,atom30,atom38,atom76,atom90],[atom1,atom2,atom15,atom30,atom42,atom64,atom85],[atom1,atom2,atom15,atom30,atom43,atom44,atom64,atom85],[atom1,atom2,atom15,atom35,atom38,atom43,atom64,atom85],[atom1,atom2,atom27,atom30,atom35,atom38,atom64,atom85],[atom1,atom2,atom27,atom30,atom38,atom44,atom64,atom85],[atom1,atom2,atom27,atom35,atom38,atom64,atom85],[atom1,atom3,atom7,atom15,atom30,atom38,atom64,atom85],[atom1,atom3,atom8,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_44 : t7_44.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_46 : BankTree := .block [[atom1,atom3,atom15,atom30,atom38,atom41,atom64,atom85],[atom1,atom4,atom8,atom15,atom30,atom38,atom76,atom85],[atom1,atom4,atom8,atom27,atom30,atom38,atom64,atom85],[atom1,atom4,atom10,atom15,atom19,atom38,atom64,atom85],[atom1,atom4,atom10,atom15,atom30,atom38,atom64,atom68]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_46 : t7_46.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_47 : BankTree := .block [[atom1,atom4,atom10,atom15,atom30,atom41,atom64,atom94],[atom1,atom4,atom10,atom15,atom30,atom41,atom85,atom96],[atom1,atom4,atom10,atom15,atom33,atom38,atom64,atom88],[atom1,atom4,atom10,atom15,atom38,atom41,atom81,atom85],[atom1,atom4,atom10,atom15,atom41,atom51,atom64,atom85],[atom1,atom4,atom10,atom30,atom38,atom41,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_47 : t7_47.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_45 : BankTree := .fork [atom1,atom4,atom10,atom15,atom30,atom41,atom64,atom94] t7_46 t7_47
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_45 : t7_45.rows.all (refuses 6 t6_0)=true := by simp only [t7_45,BankTree.rows,List.all_append,ok_t7_46,ok_t7_47,Bool.true_and]
noncomputable def t7_43 : BankTree := .fork [atom1,atom3,atom15,atom30,atom38,atom41,atom64,atom85] t7_44 t7_45
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_43 : t7_43.rows.all (refuses 6 t6_0)=true := by simp only [t7_43,BankTree.rows,List.all_append,ok_t7_44,ok_t7_45,Bool.true_and]
noncomputable def t7_37 : BankTree := .fork [atom1,atom2,atom15,atom30,atom38,atom76,atom85,atom90] t7_38 t7_43
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_37 : t7_37.rows.all (refuses 6 t6_0)=true := by simp only [t7_37,BankTree.rows,List.all_append,ok_t7_38,ok_t7_43,Bool.true_and]
noncomputable def t7_25 : BankTree := .fork [atom1,atom2,atom10,atom15,atom35,atom38,atom81,atom85] t7_26 t7_37
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_25 : t7_25.rows.all (refuses 6 t6_0)=true := by simp only [t7_25,BankTree.rows,List.all_append,ok_t7_26,ok_t7_37,Bool.true_and]
noncomputable def t7_1 : BankTree := .fork [atom1,atom2,atom4,atom27,atom30,atom38,atom62,atom64] t7_2 t7_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_1 : t7_1.rows.all (refuses 6 t6_0)=true := by simp only [t7_1,BankTree.rows,List.all_append,ok_t7_2,ok_t7_25,Bool.true_and]
noncomputable def t7_52 : BankTree := .block [[atom1,atom4,atom10,atom30,atom41,atom53,atom64,atom85],[atom1,atom4,atom15,atom30,atom38,atom41,atom76,atom85],[atom1,atom4,atom15,atom30,atom41,atom43,atom64,atom85],[atom1,atom4,atom27,atom30,atom38,atom41,atom64,atom85],[atom1,atom7,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom8,atom10,atom13,atom15,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom30,atom38,atom62,atom64],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom87],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom88],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom90]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_52 : t7_52.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_54 : BankTree := .block [[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom92],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom94],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom105],[atom1,atom8,atom10,atom15,atom30,atom38,atom76,atom85],[atom1,atom8,atom10,atom15,atom30,atom38,atom85,atom96]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_54 : t7_54.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_55 : BankTree := .block [[atom1,atom8,atom10,atom15,atom32,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom33,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom35,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom37,atom38,atom64,atom85],[atom1,atom8,atom10,atom15,atom38,atom51,atom64,atom85],[atom1,atom8,atom10,atom15,atom38,atom64,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_55 : t7_55.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_53 : BankTree := .fork [atom1,atom8,atom10,atom15,atom32,atom38,atom64,atom85] t7_54 t7_55
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_53 : t7_53.rows.all (refuses 6 t6_0)=true := by simp only [t7_53,BankTree.rows,List.all_append,ok_t7_54,ok_t7_55,Bool.true_and]
noncomputable def t7_51 : BankTree := .fork [atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom92] t7_52 t7_53
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_51 : t7_51.rows.all (refuses 6 t6_0)=true := by simp only [t7_51,BankTree.rows,List.all_append,ok_t7_52,ok_t7_53,Bool.true_and]
noncomputable def t7_57 : BankTree := .block [[atom1,atom8,atom10,atom27,atom30,atom38,atom64,atom85],[atom1,atom8,atom10,atom30,atom38,atom53,atom64,atom85],[atom1,atom8,atom12,atom15,atom30,atom38,atom64,atom85],[atom1,atom8,atom15,atom27,atom30,atom38,atom64,atom85],[atom1,atom8,atom15,atom30,atom38,atom43,atom64,atom85],[atom1,atom8,atom15,atom30,atom38,atom64,atom76,atom85],[atom1,atom8,atom15,atom30,atom38,atom76,atom85],[atom1,atom8,atom27,atom30,atom38,atom64,atom85],[atom1,atom10,atom15,atom30,atom38,atom41,atom64,atom90],[atom1,atom10,atom15,atom30,atom38,atom49,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_57 : t7_57.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_59 : BankTree := .block [[atom1,atom10,atom15,atom35,atom38,atom41,atom64,atom85],[atom2,atom3,atom4,atom15,atom30,atom38,atom64,atom87],[atom2,atom3,atom4,atom15,atom32,atom38,atom64,atom85],[atom2,atom3,atom6,atom15,atom30,atom38,atom64,atom85],[atom2,atom3,atom10,atom15,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_59 : t7_59.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_60 : BankTree := .block [[atom2,atom3,atom10,atom15,atom32,atom38,atom64,atom85],[atom2,atom3,atom12,atom15,atom30,atom38,atom64,atom85],[atom2,atom3,atom15,atom18,atom30,atom38,atom64,atom85],[atom2,atom3,atom15,atom30,atom32,atom38,atom64,atom85],[atom2,atom3,atom15,atom30,atom38,atom40,atom64,atom85],[atom2,atom3,atom15,atom30,atom38,atom64,atom67,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_60 : t7_60.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_58 : BankTree := .fork [atom2,atom3,atom10,atom15,atom32,atom38,atom64,atom85] t7_59 t7_60
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_58 : t7_58.rows.all (refuses 6 t6_0)=true := by simp only [t7_58,BankTree.rows,List.all_append,ok_t7_59,ok_t7_60,Bool.true_and]
noncomputable def t7_56 : BankTree := .fork [atom1,atom10,atom15,atom35,atom38,atom41,atom64,atom85] t7_57 t7_58
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_56 : t7_56.rows.all (refuses 6 t6_0)=true := by simp only [t7_56,BankTree.rows,List.all_append,ok_t7_57,ok_t7_58,Bool.true_and]
noncomputable def t7_50 : BankTree := .fork [atom1,atom8,atom10,atom27,atom30,atom38,atom64,atom85] t7_51 t7_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_50 : t7_50.rows.all (refuses 6 t6_0)=true := by simp only [t7_50,BankTree.rows,List.all_append,ok_t7_51,ok_t7_56,Bool.true_and]
noncomputable def t7_63 : BankTree := .block [[atom2,atom3,atom15,atom30,atom38,atom64,atom85,atom87],[atom2,atom3,atom15,atom30,atom38,atom64,atom87],[atom2,atom3,atom15,atom32,atom38,atom64,atom85],[atom2,atom4,atom6,atom15,atom30,atom38,atom64,atom85],[atom2,atom4,atom10,atom12,atom15,atom38,atom81,atom85],[atom2,atom4,atom10,atom12,atom30,atom38,atom64,atom105],[atom2,atom4,atom10,atom13,atom15,atom38,atom64,atom87],[atom2,atom4,atom10,atom13,atom18,atom38,atom64,atom85],[atom2,atom4,atom10,atom15,atom16,atom38,atom64,atom85],[atom2,atom4,atom10,atom15,atom18,atom38,atom81,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_63 : t7_63.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_65 : BankTree := .block [[atom2,atom4,atom10,atom15,atom30,atom38,atom62,atom67],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom65],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom86],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom97],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom107]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_65 : t7_65.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_66 : BankTree := .block [[atom2,atom4,atom10,atom15,atom30,atom38,atom66,atom85],[atom2,atom4,atom10,atom15,atom30,atom38,atom87,atom96],[atom2,atom4,atom10,atom15,atom30,atom39,atom64,atom85],[atom2,atom4,atom10,atom15,atom30,atom40,atom85,atom96],[atom2,atom4,atom10,atom15,atom31,atom38,atom64,atom85],[atom2,atom4,atom10,atom15,atom32,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_66 : t7_66.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_64 : BankTree := .fork [atom2,atom4,atom10,atom15,atom30,atom38,atom66,atom85] t7_65 t7_66
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_64 : t7_64.rows.all (refuses 6 t6_0)=true := by simp only [t7_64,BankTree.rows,List.all_append,ok_t7_65,ok_t7_66,Bool.true_and]
noncomputable def t7_62 : BankTree := .fork [atom2,atom4,atom10,atom15,atom30,atom38,atom62,atom67] t7_63 t7_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_62 : t7_62.rows.all (refuses 6 t6_0)=true := by simp only [t7_62,BankTree.rows,List.all_append,ok_t7_63,ok_t7_64,Bool.true_and]
noncomputable def t7_68 : BankTree := .block [[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom87],[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom88],[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom90],[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom94],[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom105],[atom2,atom4,atom10,atom15,atom32,atom38,atom76,atom85],[atom2,atom4,atom10,atom15,atom32,atom38,atom81,atom85],[atom2,atom4,atom10,atom15,atom32,atom38,atom85,atom96],[atom2,atom4,atom10,atom15,atom33,atom38,atom64,atom87],[atom2,atom4,atom10,atom15,atom35,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_68 : t7_68.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_70 : BankTree := .block [[atom2,atom4,atom10,atom15,atom38,atom40,atom81,atom85],[atom2,atom4,atom10,atom15,atom38,atom51,atom64,atom87],[atom2,atom4,atom10,atom15,atom38,atom54,atom64,atom85],[atom2,atom4,atom10,atom15,atom38,atom64,atom81,atom87],[atom2,atom4,atom10,atom15,atom38,atom64,atom83,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_70 : t7_70.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_71 : BankTree := .block [[atom2,atom4,atom10,atom15,atom38,atom67,atom81,atom85],[atom2,atom4,atom10,atom15,atom38,atom81,atom83,atom85],[atom2,atom4,atom10,atom15,atom38,atom81,atom85,atom87],[atom2,atom4,atom10,atom17,atom30,atom38,atom64,atom85],[atom2,atom4,atom10,atom18,atom30,atom38,atom64,atom105],[atom2,atom4,atom10,atom27,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_71 : t7_71.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_69 : BankTree := .fork [atom2,atom4,atom10,atom15,atom38,atom67,atom81,atom85] t7_70 t7_71
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_69 : t7_69.rows.all (refuses 6 t6_0)=true := by simp only [t7_69,BankTree.rows,List.all_append,ok_t7_70,ok_t7_71,Bool.true_and]
noncomputable def t7_67 : BankTree := .fork [atom2,atom4,atom10,atom15,atom38,atom40,atom81,atom85] t7_68 t7_69
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_67 : t7_67.rows.all (refuses 6 t6_0)=true := by simp only [t7_67,BankTree.rows,List.all_append,ok_t7_68,ok_t7_69,Bool.true_and]
noncomputable def t7_61 : BankTree := .fork [atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom87] t7_62 t7_67
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_61 : t7_61.rows.all (refuses 6 t6_0)=true := by simp only [t7_61,BankTree.rows,List.all_append,ok_t7_62,ok_t7_67,Bool.true_and]
noncomputable def t7_49 : BankTree := .fork [atom2,atom3,atom15,atom30,atom38,atom64,atom85,atom87] t7_50 t7_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_49 : t7_49.rows.all (refuses 6 t6_0)=true := by simp only [t7_49,BankTree.rows,List.all_append,ok_t7_50,ok_t7_61,Bool.true_and]
noncomputable def t7_75 : BankTree := .block [[atom2,atom4,atom10,atom30,atom32,atom38,atom64,atom105],[atom2,atom4,atom10,atom30,atom38,atom40,atom64,atom105],[atom2,atom4,atom10,atom30,atom38,atom53,atom64,atom87],[atom2,atom4,atom10,atom30,atom38,atom64,atom67,atom105],[atom2,atom4,atom10,atom30,atom38,atom64,atom87,atom105],[atom2,atom4,atom10,atom30,atom38,atom64,atom105,atom107],[atom2,atom4,atom10,atom30,atom40,atom53,atom64,atom85],[atom2,atom4,atom10,atom32,atom38,atom53,atom64,atom85],[atom2,atom4,atom11,atom15,atom30,atom38,atom64,atom85],[atom2,atom4,atom12,atom13,atom15,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_75 : t7_75.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_77 : BankTree := .block [[atom2,atom4,atom12,atom15,atom30,atom38,atom62,atom64],[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom87],[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom88],[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom90],[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_77 : t7_77.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_78 : BankTree := .block [[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom105],[atom2,atom4,atom12,atom15,atom30,atom38,atom76,atom85],[atom2,atom4,atom12,atom15,atom30,atom38,atom81,atom85],[atom2,atom4,atom12,atom15,atom30,atom38,atom85,atom96],[atom2,atom4,atom12,atom15,atom32,atom38,atom64,atom85],[atom2,atom4,atom12,atom15,atom33,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_78 : t7_78.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_76 : BankTree := .fork [atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom105] t7_77 t7_78
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_76 : t7_76.rows.all (refuses 6 t6_0)=true := by simp only [t7_76,BankTree.rows,List.all_append,ok_t7_77,ok_t7_78,Bool.true_and]
noncomputable def t7_74 : BankTree := .fork [atom2,atom4,atom12,atom15,atom30,atom38,atom62,atom64] t7_75 t7_76
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_74 : t7_74.rows.all (refuses 6 t6_0)=true := by simp only [t7_74,BankTree.rows,List.all_append,ok_t7_75,ok_t7_76,Bool.true_and]
noncomputable def t7_80 : BankTree := .block [[atom2,atom4,atom12,atom15,atom35,atom38,atom64,atom85],[atom2,atom4,atom12,atom15,atom38,atom51,atom64,atom85],[atom2,atom4,atom12,atom15,atom38,atom64,atom81,atom85],[atom2,atom4,atom12,atom15,atom38,atom81,atom85],[atom2,atom4,atom12,atom27,atom30,atom38,atom64,atom85],[atom2,atom4,atom12,atom30,atom38,atom53,atom64,atom85],[atom2,atom4,atom12,atom30,atom38,atom64,atom85,atom105],[atom2,atom4,atom12,atom30,atom38,atom64,atom105],[atom2,atom4,atom15,atom18,atom30,atom38,atom76,atom85],[atom2,atom4,atom15,atom27,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_80 : t7_80.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_82 : BankTree := .block [[atom2,atom4,atom15,atom27,atom32,atom38,atom64,atom85],[atom2,atom4,atom15,atom29,atom30,atom38,atom64,atom85],[atom2,atom4,atom15,atom30,atom32,atom38,atom76,atom85],[atom2,atom4,atom15,atom30,atom38,atom40,atom76,atom85],[atom2,atom4,atom15,atom30,atom38,atom43,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_82 : t7_82.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_83 : BankTree := .block [[atom2,atom4,atom15,atom30,atom38,atom47,atom64,atom85],[atom2,atom4,atom15,atom30,atom38,atom64,atom76,atom87],[atom2,atom4,atom15,atom30,atom38,atom64,atom78,atom85],[atom2,atom4,atom15,atom30,atom38,atom67,atom76,atom85],[atom2,atom4,atom15,atom30,atom38,atom76,atom78,atom85],[atom2,atom4,atom15,atom30,atom38,atom76,atom85,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_83 : t7_83.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_81 : BankTree := .fork [atom2,atom4,atom15,atom30,atom38,atom47,atom64,atom85] t7_82 t7_83
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_81 : t7_81.rows.all (refuses 6 t6_0)=true := by simp only [t7_81,BankTree.rows,List.all_append,ok_t7_82,ok_t7_83,Bool.true_and]
noncomputable def t7_79 : BankTree := .fork [atom2,atom4,atom15,atom27,atom32,atom38,atom64,atom85] t7_80 t7_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_79 : t7_79.rows.all (refuses 6 t6_0)=true := by simp only [t7_79,BankTree.rows,List.all_append,ok_t7_80,ok_t7_81,Bool.true_and]
noncomputable def t7_73 : BankTree := .fork [atom2,atom4,atom12,atom15,atom35,atom38,atom64,atom85] t7_74 t7_79
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_73 : t7_73.rows.all (refuses 6 t6_0)=true := by simp only [t7_73,BankTree.rows,List.all_append,ok_t7_74,ok_t7_79,Bool.true_and]
noncomputable def t7_86 : BankTree := .block [[atom2,atom4,atom15,atom32,atom38,atom43,atom64,atom85],[atom2,atom4,atom15,atom32,atom38,atom64,atom76,atom85],[atom2,atom4,atom15,atom32,atom38,atom76,atom85],[atom2,atom4,atom18,atom27,atom30,atom38,atom64,atom85],[atom2,atom4,atom27,atom29,atom30,atom38,atom64,atom85],[atom2,atom4,atom27,atom30,atom32,atom38,atom64,atom85],[atom2,atom4,atom27,atom30,atom38,atom40,atom64,atom85],[atom2,atom4,atom27,atom30,atom38,atom64,atom67,atom85],[atom2,atom4,atom27,atom30,atom38,atom64,atom85,atom87],[atom2,atom4,atom27,atom30,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_86 : t7_86.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_88 : BankTree := .block [[atom2,atom8,atom10,atom15,atom30,atom38,atom64,atom87],[atom2,atom8,atom10,atom15,atom32,atom38,atom64,atom85],[atom2,atom8,atom12,atom15,atom30,atom38,atom64,atom85],[atom2,atom10,atom12,atom15,atom30,atom38,atom64,atom90],[atom2,atom10,atom12,atom15,atom35,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_88 : t7_88.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_89 : BankTree := .block [[atom2,atom10,atom15,atom18,atom30,atom38,atom64,atom90],[atom2,atom10,atom15,atom18,atom35,atom38,atom64,atom85],[atom2,atom10,atom15,atom30,atom32,atom38,atom64,atom90],[atom2,atom10,atom15,atom30,atom35,atom38,atom64,atom87],[atom2,atom10,atom15,atom30,atom38,atom40,atom64,atom90],[atom2,atom10,atom15,atom30,atom38,atom44,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_89 : t7_89.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_87 : BankTree := .fork [atom2,atom10,atom15,atom18,atom30,atom38,atom64,atom90] t7_88 t7_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_87 : t7_87.rows.all (refuses 6 t6_0)=true := by simp only [t7_87,BankTree.rows,List.all_append,ok_t7_88,ok_t7_89,Bool.true_and]
noncomputable def t7_85 : BankTree := .fork [atom2,atom8,atom10,atom15,atom30,atom38,atom64,atom87] t7_86 t7_87
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_85 : t7_85.rows.all (refuses 6 t6_0)=true := by simp only [t7_85,BankTree.rows,List.all_append,ok_t7_86,ok_t7_87,Bool.true_and]
noncomputable def t7_92 : BankTree := .block [[atom2,atom10,atom15,atom30,atom38,atom64,atom67,atom90],[atom2,atom10,atom15,atom30,atom38,atom64,atom87,atom90],[atom2,atom10,atom15,atom30,atom40,atom44,atom64,atom85],[atom2,atom10,atom15,atom32,atom35,atom38,atom64,atom85],[atom2,atom10,atom15,atom32,atom38,atom44,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_92 : t7_92.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_93 : BankTree := .block [[atom2,atom10,atom15,atom32,atom38,atom64,atom85,atom90],[atom2,atom10,atom15,atom32,atom38,atom64,atom90],[atom2,atom10,atom15,atom35,atom38,atom40,atom64,atom85],[atom2,atom10,atom15,atom35,atom38,atom64,atom67,atom85],[atom2,atom10,atom15,atom35,atom38,atom64,atom85,atom87],[atom2,atom10,atom15,atom35,atom38,atom64,atom87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_93 : t7_93.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_91 : BankTree := .fork [atom2,atom10,atom15,atom32,atom38,atom64,atom85,atom90] t7_92 t7_93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_91 : t7_91.rows.all (refuses 6 t6_0)=true := by simp only [t7_91,BankTree.rows,List.all_append,ok_t7_92,ok_t7_93,Bool.true_and]
noncomputable def t7_95 : BankTree := .block [[atom2,atom12,atom15,atom30,atom38,atom44,atom64,atom85],[atom4,atom8,atom12,atom15,atom30,atom38,atom64,atom85],[atom4,atom10,atom15,atom30,atom38,atom41,atom64,atom87],[atom4,atom10,atom15,atom30,atom40,atom41,atom64,atom85],[atom4,atom10,atom15,atom32,atom38,atom41,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_95 : t7_95.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_96 : BankTree := .block [[atom4,atom12,atom15,atom30,atom38,atom41,atom64,atom85],[atom8,atom10,atom12,atom15,atom30,atom38,atom64,atom85],[atom8,atom10,atom15,atom18,atom30,atom38,atom64,atom85],[atom8,atom10,atom15,atom30,atom38,atom40,atom64,atom85],[atom8,atom10,atom15,atom30,atom38,atom64,atom67,atom85],[atom8,atom12,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_96 : t7_96.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_94 : BankTree := .fork [atom4,atom12,atom15,atom30,atom38,atom41,atom64,atom85] t7_95 t7_96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_94 : t7_94.rows.all (refuses 6 t6_0)=true := by simp only [t7_94,BankTree.rows,List.all_append,ok_t7_95,ok_t7_96,Bool.true_and]
noncomputable def t7_90 : BankTree := .fork [atom2,atom12,atom15,atom30,atom38,atom44,atom64,atom85] t7_91 t7_94
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_90 : t7_90.rows.all (refuses 6 t6_0)=true := by simp only [t7_90,BankTree.rows,List.all_append,ok_t7_91,ok_t7_94,Bool.true_and]
noncomputable def t7_84 : BankTree := .fork [atom2,atom10,atom15,atom30,atom38,atom64,atom67,atom90] t7_85 t7_90
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_84 : t7_84.rows.all (refuses 6 t6_0)=true := by simp only [t7_84,BankTree.rows,List.all_append,ok_t7_85,ok_t7_90,Bool.true_and]
noncomputable def t7_72 : BankTree := .fork [atom2,atom4,atom15,atom32,atom38,atom43,atom64,atom85] t7_73 t7_84
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_72 : t7_72.rows.all (refuses 6 t6_0)=true := by simp only [t7_72,BankTree.rows,List.all_append,ok_t7_73,ok_t7_84,Bool.true_and]
noncomputable def t7_48 : BankTree := .fork [atom2,atom4,atom10,atom30,atom32,atom38,atom64,atom105] t7_49 t7_72
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_48 : t7_48.rows.all (refuses 6 t6_0)=true := by simp only [t7_48,BankTree.rows,List.all_append,ok_t7_49,ok_t7_72,Bool.true_and]
noncomputable def t7_0 : BankTree := .fork [atom1,atom4,atom10,atom30,atom41,atom53,atom64,atom85] t7_1 t7_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_0 : t7_0.rows.all (refuses 6 t6_0)=true := by simp only [t7_0,BankTree.rows,List.all_append,ok_t7_1,ok_t7_48,Bool.true_and]
theorem safe7 : Safe 7 t7_0 := certify 6 t6_0 t7_0 safe6 ok_t7_0
noncomputable def t8_3 : BankTree := .block [[atom0,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom4,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom3,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom13,atom15,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom62,atom64]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_3 : t8_3.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_4 : BankTree := .block [[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom87],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom88],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom90],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom94],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom105],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom76,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_4 : t8_4.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_2 : BankTree := .fork [atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom87] t8_3 t8_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_2 : t8_2.rows.all (refuses 7 t7_0)=true := by simp only [t8_2,BankTree.rows,List.all_append,ok_t8_3,ok_t8_4,Bool.true_and]
noncomputable def t8_6 : BankTree := .block [[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom81,atom85],[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom85,atom96],[atom1,atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom33,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom35,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom15,atom38,atom51,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_6 : t8_6.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_7 : BankTree := .block [[atom1,atom2,atom4,atom10,atom15,atom38,atom64,atom81,atom85],[atom1,atom2,atom4,atom10,atom15,atom38,atom81,atom85],[atom1,atom2,atom4,atom10,atom27,atom30,atom38,atom64,atom85],[atom1,atom2,atom4,atom10,atom30,atom38,atom53,atom64,atom85],[atom1,atom2,atom4,atom10,atom30,atom38,atom64,atom85,atom105],[atom1,atom2,atom4,atom10,atom30,atom38,atom64,atom105]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_7 : t8_7.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_5 : BankTree := .fork [atom1,atom2,atom4,atom10,atom15,atom38,atom64,atom81,atom85] t8_6 t8_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_5 : t8_5.rows.all (refuses 7 t7_0)=true := by simp only [t8_5,BankTree.rows,List.all_append,ok_t8_6,ok_t8_7,Bool.true_and]
noncomputable def t8_1 : BankTree := .fork [atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom81,atom85] t8_2 t8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_1 : t8_1.rows.all (refuses 7 t7_0)=true := by simp only [t8_1,BankTree.rows,List.all_append,ok_t8_2,ok_t8_5,Bool.true_and]
noncomputable def t8_10 : BankTree := .block [[atom1,atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom4,atom15,atom27,atom30,atom38,atom64,atom85],[atom1,atom2,atom4,atom15,atom30,atom38,atom43,atom64,atom85],[atom1,atom2,atom4,atom15,atom30,atom38,atom64,atom76,atom85],[atom1,atom2,atom4,atom15,atom30,atom38,atom76,atom85],[atom1,atom2,atom4,atom27,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_10 : t8_10.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_11 : BankTree := .block [[atom1,atom2,atom8,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom2,atom10,atom15,atom30,atom35,atom38,atom64,atom85],[atom1,atom2,atom10,atom15,atom30,atom38,atom44,atom64,atom85],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom85,atom90],[atom1,atom2,atom10,atom15,atom30,atom38,atom64,atom90],[atom1,atom2,atom10,atom15,atom35,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_11 : t8_11.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_9 : BankTree := .fork [atom1,atom2,atom8,atom10,atom15,atom30,atom38,atom64,atom85] t8_10 t8_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_9 : t8_9.rows.all (refuses 7 t7_0)=true := by simp only [t8_9,BankTree.rows,List.all_append,ok_t8_10,ok_t8_11,Bool.true_and]
noncomputable def t8_13 : BankTree := .block [[atom1,atom4,atom8,atom10,atom15,atom30,atom38,atom64,atom85],[atom1,atom4,atom10,atom15,atom30,atom38,atom41,atom64,atom85],[atom1,atom8,atom10,atom15,atom30,atom38,atom64,atom85],[atom2,atom4,atom10,atom12,atom15,atom30,atom38,atom64,atom85],[atom2,atom4,atom10,atom15,atom18,atom30,atom38,atom64,atom85],[atom2,atom4,atom10,atom15,atom30,atom32,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_13 : t8_13.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_14 : BankTree := .block [[atom2,atom4,atom10,atom15,atom30,atom38,atom40,atom64,atom85],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom67,atom85],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom85,atom87],[atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom87],[atom2,atom4,atom10,atom15,atom32,atom38,atom64,atom85],[atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_14 : t8_14.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_12 : BankTree := .fork [atom2,atom4,atom10,atom15,atom30,atom38,atom40,atom64,atom85] t8_13 t8_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_12 : t8_12.rows.all (refuses 7 t7_0)=true := by simp only [t8_12,BankTree.rows,List.all_append,ok_t8_13,ok_t8_14,Bool.true_and]
noncomputable def t8_8 : BankTree := .fork [atom1,atom4,atom8,atom10,atom15,atom30,atom38,atom64,atom85] t8_9 t8_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_8 : t8_8.rows.all (refuses 7 t7_0)=true := by simp only [t8_8,BankTree.rows,List.all_append,ok_t8_9,ok_t8_12,Bool.true_and]
noncomputable def t8_0 : BankTree := .fork [atom1,atom2,atom4,atom12,atom15,atom30,atom38,atom64,atom85] t8_1 t8_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_0 : t8_0.rows.all (refuses 7 t7_0)=true := by simp only [t8_0,BankTree.rows,List.all_append,ok_t8_1,ok_t8_8,Bool.true_and]
theorem safe8 : Safe 8 t8_0 := certify 7 t7_0 t8_0 safe7 ok_t8_0
noncomputable def t9_0 : BankTree := .block [[atom1,atom2,atom4,atom10,atom15,atom30,atom38,atom64,atom85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t9_0 : t9_0.rows.all (refuses 8 t8_0)=true := by decide +kernel
theorem safe9 : Safe 9 t9_0 := certify 8 t8_0 t9_0 safe8 ok_t9_0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem knownRoots : inputs.sublists.all (fun l =>
    decide (10 < l.length) || (!(cuts l == -1) || t9_0.contains (canon l))) = true := by decide +kernel
theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hmem : l∈inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have row := List.all_eq_true.mp knownRoots l hmem
  have hc := cuts_full (hlS ▸ hl3)
  have room : ¬(10<l.length) := by omega
  have yy : t9_0.contains (canon l)=true := by simpa [room,hc] using row
  have pp : (canon l).Perm l := List.perm_insertionSort _ _
  have ez : (canon l).toFinset=l.toFinset := by
    ext v; simpa only [List.mem_toFinset] using (pp.mem_iff (a:=v))
  exact safe9 _ yy (pp.nodup_iff.mpr hnd) (ez.symm ▸ (hlS ▸ hl3))

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103735 : ℕ).testBit (5 * u.val + v.val)) 9) := by
  rintro ⟨C, hm, hs, hr⟩
  exact no_small C hm hs hr

end PEqualNP.Outside.L_meta_21054

theorem PEqualNP.Outside.L_meta_21054 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103735 : ℕ).testBit (5 * u.val + v.val)) 9) :=
  PEqualNP.Outside.L_meta_21054.result

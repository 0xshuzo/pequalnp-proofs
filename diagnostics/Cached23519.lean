import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23519

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 128 := ((x >>> 128) &&& ~~~x).setWidth 128

def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [(BitVec.ofNat 256 (((0xffffffffffff * 2^64 + 0x0) * 2^64 + 0x0) : Nat)), (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffff000000000000) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat)), (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0x0) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat)), (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0x0) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat)), (BitVec.ofNat 256 ((((0xff000000ff00 * 2^64 + 0xff) * 2^64 + 0x101010101010101) * 2^64 + 0x101010101010101) : Nat)), (BitVec.ofNat 256 ((((0xff000000ff0000 * 2^64 + 0xff00) * 2^64 + 0x202020202020202) * 2^64 + 0x202020202020202) : Nat)), (BitVec.ofNat 256 ((((0xff000000ff000000 * 2^64 + 0xff0000) * 2^64 + 0x404040404040404) * 2^64 + 0x404040404040404) : Nat)), (BitVec.ofNat 256 ((((0xff00000000 * 2^64 + 0xff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat)), (BitVec.ofNat 256 (((0xff0000ff00000000 * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat)), (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff0000000000) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))]

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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (128 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (128 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 128, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 256 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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
  z == 0 || z == BitVec.allOnes 256 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
    · exact ⟨BitVec.allOnes 256, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 256 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 256 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 256 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 256 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 256) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 256 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)

def posL : List (Fin 4 × Fin 6) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2)]

def negL : List (Fin 4 × Fin 6) :=
  [(1, 0), (1, 1), (1, 2), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5)]

def samp (k : Fin 256) : Fin 4 × Fin 6 :=
  if k.val < 128 then negL.getD (k.val % 8) (0, 0) else posL.getD ((k.val - 128) / 8) (0, 0)

theorem input_rows : ∀ k : Fin 256,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 256, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 256) :
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
def w0 : W := (BitVec.ofNat 256 (((0xffffffffffff * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w1 : W := (BitVec.ofNat 256 (((0xff00000000000000 * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w2 : W := (BitVec.ofNat 256 (((0xff0000ff00000000 * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat))
def w3 : W := (BitVec.ofNat 256 (((0xff00ffffffffffff * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w4 : W := (BitVec.ofNat 256 (((0xff00ffffffffffff * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat))
def w5 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0x0) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w6 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff0000000000) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))
def w7 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w8 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffffffffffff) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))
def w9 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff00000000000000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w10 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff0000ff00000000) * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat))
def w11 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff00ff0000000000) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))
def w12 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w13 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff00ffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w14 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xff00ffffffffffff) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w15 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffff000000000000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w16 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffff000000000000) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w17 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w18 : W := (BitVec.ofNat 256 ((((0xff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w19 : W := (BitVec.ofNat 256 ((((0xff00000000 * 2^64 + 0xff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w20 : W := (BitVec.ofNat 256 ((((0xff00000000 * 2^64 + 0xffffffffffffff) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w21 : W := (BitVec.ofNat 256 ((((0xff00000000 * 2^64 + 0xffff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w22 : W := (BitVec.ofNat 256 ((((0xff00000000 * 2^64 + 0xffff00ffff000000) * 2^64 + 0x6868686868686868) * 2^64 + 0x6868686868686868) : Nat))
def w23 : W := (BitVec.ofNat 256 ((((0xff000000ff * 2^64 + 0xff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w24 : W := (BitVec.ofNat 256 ((((0xff000000ff * 2^64 + 0xffff00ff000000) * 2^64 + 0xb0b0b0b0b0b0b0b0) * 2^64 + 0xb0b0b0b0b0b0b0b0) : Nat))
def w25 : W := (BitVec.ofNat 256 ((((0xff000000ff * 2^64 + 0xffff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w26 : W := (BitVec.ofNat 256 ((((0xff000000ff * 2^64 + 0xffffffffff000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w27 : W := (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0x0) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w28 : W := (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w29 : W := (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0xff00000000000000) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w30 : W := (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0xff0000ff00000000) * 2^64 + 0x5858585858585858) * 2^64 + 0x5858585858585858) : Nat))
def w31 : W := (BitVec.ofNat 256 ((((0xffffffff00 * 2^64 + 0xff00ffffffffffff) * 2^64 + 0x5858585858585858) * 2^64 + 0x5858585858585858) : Nat))
def w32 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0x0) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w33 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff0000000000) * 2^64 + 0x9898989898989898) * 2^64 + 0x9898989898989898) : Nat))
def w34 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xffffffffffff) * 2^64 + 0x9898989898989898) * 2^64 + 0x9898989898989898) : Nat))
def w35 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff00000000000000) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w36 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff0000ff00000000) * 2^64 + 0x5858585858585858) * 2^64 + 0x5858585858585858) : Nat))
def w37 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff00ff0000000000) * 2^64 + 0x9898989898989898) * 2^64 + 0x9898989898989898) : Nat))
def w38 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w39 : W := (BitVec.ofNat 256 ((((0xffffffffff * 2^64 + 0xff00ffffffffffff) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w40 : W := (BitVec.ofNat 256 ((((0xff000000ff00 * 2^64 + 0xff) * 2^64 + 0x101010101010101) * 2^64 + 0x101010101010101) : Nat))
def w41 : W := (BitVec.ofNat 256 ((((0xff000000ff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x101010101010101) * 2^64 + 0x101010101010101) : Nat))
def w42 : W := (BitVec.ofNat 256 ((((0xff000000ffff * 2^64 + 0xffff0000000000ff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w43 : W := (BitVec.ofNat 256 ((((0xff000000ffff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w44 : W := (BitVec.ofNat 256 ((((0xff000000ff0000 * 2^64 + 0xff00) * 2^64 + 0x202020202020202) * 2^64 + 0x202020202020202) : Nat))
def w45 : W := (BitVec.ofNat 256 ((((0xff000000ff0000 * 2^64 + 0xffffffffffff) * 2^64 + 0x202020202020202) * 2^64 + 0x202020202020202) : Nat))
def w46 : W := (BitVec.ofNat 256 ((((0xff000000ff00ff * 2^64 + 0xffff00000000ff00) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w47 : W := (BitVec.ofNat 256 ((((0xff000000ff00ff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w48 : W := (BitVec.ofNat 256 ((((0xffff0000ffff00 * 2^64 + 0xffff) * 2^64 + 0x303030303030303) * 2^64 + 0x303030303030303) : Nat))
def w49 : W := (BitVec.ofNat 256 ((((0xffff0000ffff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x303030303030303) * 2^64 + 0x303030303030303) : Nat))
def w50 : W := (BitVec.ofNat 256 ((((0xffff0000ffffff * 2^64 + 0xffff00000000ffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w51 : W := (BitVec.ofNat 256 ((((0xffff0000ffffff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w52 : W := (BitVec.ofNat 256 ((((0xff000000ff000000 * 2^64 + 0xff0000) * 2^64 + 0x404040404040404) * 2^64 + 0x404040404040404) : Nat))
def w53 : W := (BitVec.ofNat 256 ((((0xff000000ff000000 * 2^64 + 0xffffffffffff) * 2^64 + 0x404040404040404) * 2^64 + 0x404040404040404) : Nat))
def w54 : W := (BitVec.ofNat 256 ((((0xff000000ff0000ff * 2^64 + 0xffff000000ff0000) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w55 : W := (BitVec.ofNat 256 ((((0xff000000ff0000ff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w56 : W := (BitVec.ofNat 256 ((((0xff00ff00ff00ff00 * 2^64 + 0xff00ff) * 2^64 + 0x505050505050505) * 2^64 + 0x505050505050505) : Nat))
def w57 : W := (BitVec.ofNat 256 ((((0xff00ff00ff00ff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x505050505050505) * 2^64 + 0x505050505050505) : Nat))
def w58 : W := (BitVec.ofNat 256 ((((0xff00ff00ff00ffff * 2^64 + 0xffff000000ff00ff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w59 : W := (BitVec.ofNat 256 ((((0xff00ff00ff00ffff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w60 : W := (BitVec.ofNat 256 ((((0xffff0000ffff0000 * 2^64 + 0xffff00) * 2^64 + 0x606060606060606) * 2^64 + 0x606060606060606) : Nat))
def w61 : W := (BitVec.ofNat 256 ((((0xffff0000ffff0000 * 2^64 + 0xffffffffffff) * 2^64 + 0x606060606060606) * 2^64 + 0x606060606060606) : Nat))
def w62 : W := (BitVec.ofNat 256 ((((0xffff0000ffff00ff * 2^64 + 0xffff000000ffff00) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w63 : W := (BitVec.ofNat 256 ((((0xffff0000ffff00ff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w64 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0x0) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w65 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0x0) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w66 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w67 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xffffffffffff) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w68 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff00000000000000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w69 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff00000000000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w70 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff0000ff00000000) * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat))
def w71 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff0000ff00000000) * 2^64 + 0xe8e8e8e8e8e8e8e8) * 2^64 + 0xe8e8e8e8e8e8e8e8) : Nat))
def w72 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff00ffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w73 : W := (BitVec.ofNat 256 ((((0xffffff0000000000 * 2^64 + 0xff00ffffffffffff) * 2^64 + 0xe8e8e8e8e8e8e8e8) * 2^64 + 0xe8e8e8e8e8e8e8e8) : Nat))
def w74 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0x0) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w75 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0x0) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w76 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff0000000000) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))
def w77 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff0000000000) * 2^64 + 0xf0f0f0f0f0f0f0f0) * 2^64 + 0xf0f0f0f0f0f0f0f0) : Nat))
def w78 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w79 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xffffffffffff) * 2^64 + 0xf0f0f0f0f0f0f0f0) * 2^64 + 0xf0f0f0f0f0f0f0f0) : Nat))
def w80 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00000000000000) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w81 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00000000000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w82 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff0000ff00000000) * 2^64 + 0x4848484848484848) * 2^64 + 0x4848484848484848) : Nat))
def w83 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff0000ff00000000) * 2^64 + 0xe8e8e8e8e8e8e8e8) * 2^64 + 0xe8e8e8e8e8e8e8e8) : Nat))
def w84 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ff0000000000) * 2^64 + 0x9090909090909090) * 2^64 + 0x9090909090909090) : Nat))
def w85 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ff0000000000) * 2^64 + 0xf0f0f0f0f0f0f0f0) * 2^64 + 0xf0f0f0f0f0f0f0f0) : Nat))
def w86 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w87 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w88 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w89 : W := (BitVec.ofNat 256 ((((0xffffff00000000ff * 2^64 + 0xff00ffffffffffff) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w90 : W := (BitVec.ofNat 256 ((((0xffffff00ffffff00 * 2^64 + 0x0) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w91 : W := (BitVec.ofNat 256 ((((0xffffff00ffffff00 * 2^64 + 0xffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w92 : W := (BitVec.ofNat 256 ((((0xffffff00ffffff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x0) * 2^64 + 0x0) : Nat))
def w93 : W := (BitVec.ofNat 256 ((((0xffffff00ffffff00 * 2^64 + 0xffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w94 : W := (BitVec.ofNat 256 ((((0xffffff00ffffffff * 2^64 + 0xffff000000ffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w95 : W := (BitVec.ofNat 256 ((((0xffffff00ffffffff * 2^64 + 0xffffffffffffffff) * 2^64 + 0x707070707070707) * 2^64 + 0x707070707070707) : Nat))
def w96 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w97 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xff0000ff000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w98 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xffffffffffffff) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w99 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xffff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w100 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xffff0000ff000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w101 : W := (BitVec.ofNat 256 ((((0xffffffff00000000 * 2^64 + 0xffff00ffff000000) * 2^64 + 0xe8e8e8e8e8e8e8e8) * 2^64 + 0xe8e8e8e8e8e8e8e8) : Nat))
def w102 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w103 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xff0000ff000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w104 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xffff00ff000000) * 2^64 + 0xf0f0f0f0f0f0f0f0) * 2^64 + 0xf0f0f0f0f0f0f0f0) : Nat))
def w105 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xffff0000ff000000) * 2^64 + 0x2020202020202020) * 2^64 + 0x2020202020202020) : Nat))
def w106 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xffff0000ff000000) * 2^64 + 0xe0e0e0e0e0e0e0e0) * 2^64 + 0xe0e0e0e0e0e0e0e0) : Nat))
def w107 : W := (BitVec.ofNat 256 ((((0xffffffff000000ff * 2^64 + 0xffffffffff000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w108 : W := (BitVec.ofNat 256 ((((0xffffffffffffff00 * 2^64 + 0x0) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w109 : W := (BitVec.ofNat 256 ((((0xffffffffffffff00 * 2^64 + 0x0) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w110 : W := (BitVec.ofNat 256 ((((0xffffffffffffff00 * 2^64 + 0xff00000000000000) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w111 : W := (BitVec.ofNat 256 ((((0xffffffffffffff00 * 2^64 + 0xff0000ff00000000) * 2^64 + 0x5858585858585858) * 2^64 + 0x5858585858585858) : Nat))
def w112 : W := (BitVec.ofNat 256 ((((0xffffffffffffff00 * 2^64 + 0xff0000ff00000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w113 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0x0) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w114 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff0000000000) * 2^64 + 0x9898989898989898) * 2^64 + 0x9898989898989898) : Nat))
def w115 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff0000000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
def w116 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff00000000000000) * 2^64 + 0x1818181818181818) * 2^64 + 0x1818181818181818) : Nat))
def w117 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff0000ff00000000) * 2^64 + 0x5858585858585858) * 2^64 + 0x5858585858585858) : Nat))
def w118 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff00ff0000000000) * 2^64 + 0x9898989898989898) * 2^64 + 0x9898989898989898) : Nat))
def w119 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xd8d8d8d8d8d8d8d8) * 2^64 + 0xd8d8d8d8d8d8d8d8) : Nat))
def w120 : W := (BitVec.ofNat 256 ((((0xffffffffffffffff * 2^64 + 0xff00ffff00000000) * 2^64 + 0xf8f8f8f8f8f8f8f8) * 2^64 + 0xf8f8f8f8f8f8f8f8) : Nat))
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
noncomputable def t3_0 : BankTree := .block [[w0,w19,w94,w116],[w0,w19,w94,w117],[w0,w19,w94,w118],[w0,w19,w94,w119],[w0,w27,w94,w105],[w0,w27,w94,w106],[w0,w30,w94,w102],[w0,w33,w94,w99],[w0,w35,w94,w97],[w0,w38,w94,w96],[w12,w27,w95,w98],[w12,w28,w94,w98],[w12,w28,w95,w97],[w13,w27,w94,w97],[w14,w27,w95,w97],[w16,w19,w38,w92],[w17,w27,w91,w97],[w19,w27,w88,w94],[w19,w27,w89,w95],[w19,w28,w87,w95],[w19,w30,w78,w94],[w19,w30,w79,w95],[w19,w31,w77,w95],[w19,w33,w72,w94],[w19,w33,w73,w95],[w19,w34,w71,w95],[w19,w38,w66,w94],[w19,w38,w67,w95],[w19,w39,w65,w95],[w20,w27,w87,w95],[w20,w28,w87,w94],[w20,w30,w77,w95],[w20,w31,w77,w94],[w20,w33,w71,w95],[w20,w34,w71,w94],[w20,w38,w65,w95],[w20,w39,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t3_0 : t3_0.rows.all (refuses 2 t2_0)=true := by decide +kernel
theorem safe3 : Safe 3 t3_0 := certify 2 t2_0 t3_0 safe2 ok_t3_0
noncomputable def t4_4 : BankTree := .block [[w0,w2,w19,w94,w113],[w0,w2,w19,w94,w114],[w0,w2,w27,w94,w102],[w0,w2,w27,w94,w103],[w0,w2,w32,w94,w97],[w0,w2,w33,w94,w96],[w0,w6,w19,w94,w110],[w0,w6,w19,w94,w111],[w0,w6,w27,w94,w99],[w0,w6,w27,w94,w100],[w0,w6,w29,w94,w97],[w0,w6,w30,w94,w96],[w0,w9,w27,w94,w97],[w0,w10,w27,w94,w97],[w0,w11,w27,w94,w97],[w0,w12,w19,w94,w108],[w0,w12,w27,w94,w96],[w0,w12,w27,w94,w97],[w0,w12,w27,w94,w98],[w0,w12,w27,w95,w97],[w0,w12,w28,w94,w97],[w0,w14,w27,w94,w97],[w0,w15,w27,w91,w97],[w0,w16,w19,w38,w90],[w0,w16,w19,w91,w119],[w0,w16,w27,w91,w106]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_4 : t4_4.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_5 : BankTree := .block [[w0,w16,w35,w91,w97],[w0,w16,w38,w91,w96],[w0,w19,w27,w80,w94],[w0,w19,w27,w81,w94],[w0,w19,w27,w82,w94],[w0,w19,w27,w83,w94],[w0,w19,w27,w84,w94],[w0,w19,w27,w85,w94],[w0,w19,w27,w86,w94],[w0,w19,w27,w87,w94],[w0,w19,w27,w87,w95],[w0,w19,w27,w89,w94],[w0,w19,w27,w94,w107],[w0,w19,w27,w94,w120],[w0,w19,w28,w87,w94],[w0,w19,w29,w77,w94],[w0,w19,w30,w74,w94],[w0,w19,w30,w75,w94],[w0,w19,w30,w76,w94],[w0,w19,w30,w77,w94],[w0,w19,w30,w77,w95],[w0,w19,w30,w79,w94],[w0,w19,w30,w87,w94],[w0,w19,w30,w94,w104],[w0,w19,w30,w94,w115],[w0,w19,w30,w94,w120]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_5 : t4_5.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_3 : BankTree := .fork [w0,w16,w35,w91,w97] t4_4 t4_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_3 : t4_3.rows.all (refuses 3 t3_0)=true := by simp only [t4_3,BankTree.rows,List.all_append,ok_t4_4,ok_t4_5,Bool.true_and]
noncomputable def t4_7 : BankTree := .block [[w0,w19,w31,w77,w94],[w0,w19,w32,w71,w94],[w0,w19,w33,w68,w94],[w0,w19,w33,w69,w94],[w0,w19,w33,w70,w94],[w0,w19,w33,w71,w94],[w0,w19,w33,w71,w95],[w0,w19,w33,w73,w94],[w0,w19,w33,w87,w94],[w0,w19,w33,w94,w101],[w0,w19,w33,w94,w112],[w0,w19,w33,w94,w120],[w0,w19,w34,w71,w94],[w0,w19,w35,w65,w94],[w0,w19,w36,w65,w94],[w0,w19,w37,w65,w94],[w0,w19,w38,w64,w94],[w0,w19,w38,w65,w94],[w0,w19,w38,w65,w95],[w0,w19,w38,w67,w94],[w0,w19,w38,w71,w94],[w0,w19,w38,w77,w94],[w0,w19,w38,w87,w94],[w0,w19,w38,w94,w97],[w0,w19,w38,w94,w109],[w0,w19,w38,w94,w112]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_7 : t4_7.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_8 : BankTree := .block [[w0,w19,w38,w94,w115],[w0,w19,w38,w94,w120],[w0,w19,w39,w65,w94],[w0,w20,w27,w87,w94],[w0,w20,w30,w77,w94],[w0,w20,w33,w71,w94],[w0,w20,w38,w65,w94],[w0,w21,w27,w77,w94],[w0,w21,w33,w65,w94],[w0,w22,w27,w94,w104],[w0,w22,w33,w94,w97],[w0,w23,w27,w71,w94],[w0,w23,w30,w65,w94],[w0,w24,w27,w94,w101],[w0,w24,w30,w94,w97],[w0,w25,w27,w65,w94],[w0,w26,w27,w94,w97],[w0,w27,w38,w94,w97],[w0,w27,w40,w62,w106],[w0,w27,w42,w60,w106],[w0,w27,w44,w58,w106],[w0,w27,w46,w56,w106],[w0,w27,w48,w54,w106],[w0,w27,w50,w52,w106],[w0,w27,w87,w94,w97],[w0,w27,w94,w97,w107],[w0,w27,w94,w101,w104]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_8 : t4_8.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_6 : BankTree := .fork [w0,w19,w38,w94,w115] t4_7 t4_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_6 : t4_6.rows.all (refuses 3 t3_0)=true := by simp only [t4_6,BankTree.rows,List.all_append,ok_t4_7,ok_t4_8,Bool.true_and]
noncomputable def t4_2 : BankTree := .fork [w0,w19,w31,w77,w94] t4_3 t4_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_2 : t4_2.rows.all (refuses 3 t3_0)=true := by simp only [t4_2,BankTree.rows,List.all_append,ok_t4_3,ok_t4_6,Bool.true_and]
noncomputable def t4_11 : BankTree := .block [[w0,w30,w33,w94,w97],[w0,w35,w40,w62,w97],[w0,w35,w42,w60,w97],[w0,w35,w44,w58,w97],[w0,w35,w46,w56,w97],[w0,w35,w48,w54,w97],[w0,w35,w50,w52,w97],[w2,w6,w27,w95,w98],[w2,w6,w28,w94,w98],[w2,w6,w28,w95,w97],[w2,w7,w27,w94,w97],[w2,w8,w27,w95,w97],[w2,w16,w19,w33,w92],[w2,w19,w27,w78,w94],[w2,w19,w27,w79,w95],[w2,w19,w28,w77,w95],[w2,w19,w33,w66,w94],[w2,w19,w33,w67,w95],[w2,w19,w34,w65,w95],[w2,w20,w27,w77,w95],[w2,w20,w28,w77,w94],[w2,w20,w33,w65,w95],[w2,w20,w34,w65,w94],[w3,w6,w27,w94,w97],[w3,w19,w27,w77,w94],[w3,w19,w33,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_11 : t4_11.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_12 : BankTree := .block [[w4,w6,w27,w95,w97],[w4,w8,w27,w94,w97],[w4,w19,w27,w77,w95],[w4,w19,w33,w65,w95],[w4,w20,w27,w77,w94],[w4,w20,w33,w65,w94],[w6,w16,w19,w30,w92],[w6,w19,w27,w72,w94],[w6,w19,w27,w73,w95],[w6,w19,w28,w71,w95],[w6,w19,w30,w66,w94],[w6,w19,w30,w67,w95],[w6,w19,w31,w65,w95],[w6,w20,w27,w71,w95],[w6,w20,w28,w71,w94],[w6,w20,w30,w65,w95],[w6,w20,w31,w65,w94],[w7,w19,w27,w71,w94],[w7,w19,w30,w65,w94],[w8,w19,w27,w71,w95],[w8,w19,w30,w65,w95],[w8,w20,w27,w71,w94],[w8,w20,w30,w65,w94],[w12,w16,w19,w27,w92],[w12,w16,w27,w93,w98],[w12,w16,w28,w91,w98]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_12 : t4_12.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_10 : BankTree := .fork [w4,w6,w27,w95,w97] t4_11 t4_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_10 : t4_10.rows.all (refuses 3 t3_0)=true := by simp only [t4_10,BankTree.rows,List.all_append,ok_t4_11,ok_t4_12,Bool.true_and]
noncomputable def t4_14 : BankTree := .block [[w12,w16,w28,w93,w97],[w12,w18,w27,w91,w98],[w12,w18,w28,w91,w97],[w12,w19,w27,w66,w94],[w12,w19,w27,w67,w95],[w12,w19,w28,w65,w95],[w12,w19,w28,w67,w94],[w12,w20,w27,w65,w95],[w12,w20,w28,w65,w94],[w12,w27,w40,w63,w98],[w12,w27,w41,w62,w98],[w12,w27,w42,w61,w98],[w12,w27,w43,w60,w98],[w12,w27,w44,w59,w98],[w12,w27,w45,w58,w98],[w12,w27,w46,w57,w98],[w12,w27,w47,w56,w98],[w12,w27,w48,w55,w98],[w12,w27,w49,w54,w98],[w12,w27,w50,w53,w98],[w12,w27,w51,w52,w98],[w12,w28,w40,w62,w98],[w12,w28,w40,w63,w97],[w12,w28,w41,w62,w97],[w12,w28,w42,w60,w98],[w12,w28,w42,w61,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_14 : t4_14.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_15 : BankTree := .block [[w12,w28,w43,w60,w97],[w12,w28,w44,w58,w98],[w12,w28,w44,w59,w97],[w12,w28,w45,w58,w97],[w12,w28,w46,w56,w98],[w12,w28,w46,w57,w97],[w12,w28,w47,w56,w97],[w12,w28,w48,w54,w98],[w12,w28,w48,w55,w97],[w12,w28,w49,w54,w97],[w12,w28,w50,w52,w98],[w12,w28,w50,w53,w97],[w12,w28,w51,w52,w97],[w13,w16,w27,w91,w97],[w13,w19,w27,w65,w94],[w13,w27,w40,w62,w97],[w13,w27,w42,w60,w97],[w13,w27,w44,w58,w97],[w13,w27,w46,w56,w97],[w13,w27,w48,w54,w97],[w13,w27,w50,w52,w97],[w14,w16,w27,w93,w97],[w14,w18,w27,w91,w97],[w14,w19,w27,w65,w95],[w14,w20,w27,w65,w94],[w14,w27,w40,w63,w97],[w14,w27,w41,w62,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_15 : t4_15.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_13 : BankTree := .fork [w12,w28,w43,w60,w97] t4_14 t4_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_13 : t4_13.rows.all (refuses 3 t3_0)=true := by simp only [t4_13,BankTree.rows,List.all_append,ok_t4_14,ok_t4_15,Bool.true_and]
noncomputable def t4_9 : BankTree := .fork [w12,w16,w28,w93,w97] t4_10 t4_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_9 : t4_9.rows.all (refuses 3 t3_0)=true := by simp only [t4_9,BankTree.rows,List.all_append,ok_t4_10,ok_t4_13,Bool.true_and]
noncomputable def t4_1 : BankTree := .fork [w0,w30,w33,w94,w97] t4_2 t4_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_1 : t4_1.rows.all (refuses 3 t3_0)=true := by simp only [t4_1,BankTree.rows,List.all_append,ok_t4_2,ok_t4_9,Bool.true_and]
noncomputable def t4_19 : BankTree := .block [[w14,w27,w42,w61,w97],[w14,w27,w43,w60,w97],[w14,w27,w44,w59,w97],[w14,w27,w45,w58,w97],[w14,w27,w46,w57,w97],[w14,w27,w47,w56,w97],[w14,w27,w48,w55,w97],[w14,w27,w49,w54,w97],[w14,w27,w50,w53,w97],[w14,w27,w51,w52,w97],[w16,w19,w27,w89,w93],[w16,w19,w28,w87,w93],[w16,w19,w30,w79,w93],[w16,w19,w31,w77,w93],[w16,w19,w33,w73,w93],[w16,w19,w34,w71,w93],[w16,w19,w38,w66,w91],[w16,w19,w38,w67,w93],[w16,w19,w39,w65,w93],[w16,w20,w27,w87,w93],[w16,w20,w28,w87,w91],[w16,w20,w30,w77,w93],[w16,w20,w31,w77,w91],[w16,w20,w33,w71,w93],[w16,w20,w34,w71,w91],[w16,w20,w38,w65,w93]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_19 : t4_19.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_20 : BankTree := .block [[w16,w20,w39,w65,w91],[w17,w19,w27,w65,w91],[w17,w27,w40,w60,w97],[w17,w27,w44,w56,w97],[w17,w27,w48,w52,w97],[w18,w19,w27,w89,w91],[w18,w19,w28,w87,w91],[w18,w19,w30,w79,w91],[w18,w19,w31,w77,w91],[w18,w19,w33,w73,w91],[w18,w19,w34,w71,w91],[w18,w19,w38,w67,w91],[w18,w19,w39,w65,w91],[w18,w20,w27,w87,w91],[w18,w20,w30,w77,w91],[w18,w20,w33,w71,w91],[w18,w20,w38,w65,w91],[w19,w27,w40,w63,w89],[w19,w27,w41,w62,w89],[w19,w27,w42,w61,w89],[w19,w27,w43,w60,w89],[w19,w27,w44,w59,w89],[w19,w27,w45,w58,w89],[w19,w27,w46,w57,w89],[w19,w27,w47,w56,w89],[w19,w27,w48,w55,w89]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_20 : t4_20.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_18 : BankTree := .fork [w16,w20,w39,w65,w91] t4_19 t4_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_18 : t4_18.rows.all (refuses 3 t3_0)=true := by simp only [t4_18,BankTree.rows,List.all_append,ok_t4_19,ok_t4_20,Bool.true_and]
noncomputable def t4_22 : BankTree := .block [[w19,w27,w49,w54,w89],[w19,w27,w50,w53,w89],[w19,w27,w51,w52,w89],[w19,w28,w40,w63,w87],[w19,w28,w41,w62,w87],[w19,w28,w42,w61,w87],[w19,w28,w43,w60,w87],[w19,w28,w44,w59,w87],[w19,w28,w45,w58,w87],[w19,w28,w46,w57,w87],[w19,w28,w47,w56,w87],[w19,w28,w48,w55,w87],[w19,w28,w49,w54,w87],[w19,w28,w50,w53,w87],[w19,w28,w51,w52,w87],[w19,w30,w40,w63,w79],[w19,w30,w41,w62,w79],[w19,w30,w42,w61,w79],[w19,w30,w43,w60,w79],[w19,w30,w44,w59,w79],[w19,w30,w45,w58,w79],[w19,w30,w46,w57,w79],[w19,w30,w47,w56,w79],[w19,w30,w48,w55,w79],[w19,w30,w49,w54,w79],[w19,w30,w50,w53,w79]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_22 : t4_22.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_23 : BankTree := .block [[w19,w30,w51,w52,w79],[w19,w31,w40,w63,w77],[w19,w31,w41,w62,w77],[w19,w31,w42,w61,w77],[w19,w31,w43,w60,w77],[w19,w31,w44,w59,w77],[w19,w31,w45,w58,w77],[w19,w31,w46,w57,w77],[w19,w31,w47,w56,w77],[w19,w31,w48,w55,w77],[w19,w31,w49,w54,w77],[w19,w31,w50,w53,w77],[w19,w31,w51,w52,w77],[w19,w33,w40,w63,w73],[w19,w33,w41,w62,w73],[w19,w33,w42,w61,w73],[w19,w33,w43,w60,w73],[w19,w33,w44,w59,w73],[w19,w33,w45,w58,w73],[w19,w33,w46,w57,w73],[w19,w33,w47,w56,w73],[w19,w33,w48,w55,w73],[w19,w33,w49,w54,w73],[w19,w33,w50,w53,w73],[w19,w33,w51,w52,w73],[w19,w34,w40,w63,w71],[w19,w34,w41,w62,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_23 : t4_23.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_21 : BankTree := .fork [w19,w30,w51,w52,w79] t4_22 t4_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_21 : t4_21.rows.all (refuses 3 t3_0)=true := by simp only [t4_21,BankTree.rows,List.all_append,ok_t4_22,ok_t4_23,Bool.true_and]
noncomputable def t4_17 : BankTree := .fork [w19,w27,w49,w54,w89] t4_18 t4_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_17 : t4_17.rows.all (refuses 3 t3_0)=true := by simp only [t4_17,BankTree.rows,List.all_append,ok_t4_18,ok_t4_21,Bool.true_and]
noncomputable def t4_26 : BankTree := .block [[w19,w34,w42,w61,w71],[w19,w34,w43,w60,w71],[w19,w34,w44,w59,w71],[w19,w34,w45,w58,w71],[w19,w34,w46,w57,w71],[w19,w34,w47,w56,w71],[w19,w34,w48,w55,w71],[w19,w34,w49,w54,w71],[w19,w34,w50,w53,w71],[w19,w34,w51,w52,w71],[w19,w38,w40,w63,w67],[w19,w38,w41,w62,w67],[w19,w38,w42,w61,w67],[w19,w38,w43,w60,w67],[w19,w38,w44,w59,w67],[w19,w38,w45,w58,w67],[w19,w38,w46,w57,w67],[w19,w38,w47,w56,w67],[w19,w38,w48,w55,w67],[w19,w38,w49,w54,w67],[w19,w38,w50,w53,w67],[w19,w38,w51,w52,w67],[w19,w39,w40,w63,w65],[w19,w39,w41,w62,w65],[w19,w39,w42,w61,w65],[w19,w39,w43,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_26 : t4_26.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_27 : BankTree := .block [[w19,w39,w44,w59,w65],[w19,w39,w45,w58,w65],[w19,w39,w46,w57,w65],[w19,w39,w47,w56,w65],[w19,w39,w48,w55,w65],[w19,w39,w49,w54,w65],[w19,w39,w50,w53,w65],[w19,w39,w51,w52,w65],[w20,w27,w40,w63,w87],[w20,w27,w41,w62,w87],[w20,w27,w42,w61,w87],[w20,w27,w43,w60,w87],[w20,w27,w44,w59,w87],[w20,w27,w45,w58,w87],[w20,w27,w46,w57,w87],[w20,w27,w47,w56,w87],[w20,w27,w48,w55,w87],[w20,w27,w49,w54,w87],[w20,w27,w50,w53,w87],[w20,w27,w51,w52,w87],[w20,w28,w40,w62,w87],[w20,w28,w42,w60,w87],[w20,w28,w44,w58,w87],[w20,w28,w46,w56,w87],[w20,w28,w48,w54,w87],[w20,w28,w50,w52,w87],[w20,w30,w40,w63,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_27 : t4_27.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_25 : BankTree := .fork [w19,w39,w44,w59,w65] t4_26 t4_27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_25 : t4_25.rows.all (refuses 3 t3_0)=true := by simp only [t4_25,BankTree.rows,List.all_append,ok_t4_26,ok_t4_27,Bool.true_and]
noncomputable def t4_29 : BankTree := .block [[w20,w30,w41,w62,w77],[w20,w30,w42,w61,w77],[w20,w30,w43,w60,w77],[w20,w30,w44,w59,w77],[w20,w30,w45,w58,w77],[w20,w30,w46,w57,w77],[w20,w30,w47,w56,w77],[w20,w30,w48,w55,w77],[w20,w30,w49,w54,w77],[w20,w30,w50,w53,w77],[w20,w30,w51,w52,w77],[w20,w31,w40,w62,w77],[w20,w31,w42,w60,w77],[w20,w31,w44,w58,w77],[w20,w31,w46,w56,w77],[w20,w31,w48,w54,w77],[w20,w31,w50,w52,w77],[w20,w33,w40,w63,w71],[w20,w33,w41,w62,w71],[w20,w33,w42,w61,w71],[w20,w33,w43,w60,w71],[w20,w33,w44,w59,w71],[w20,w33,w45,w58,w71],[w20,w33,w46,w57,w71],[w20,w33,w47,w56,w71],[w20,w33,w48,w55,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_29 : t4_29.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_30 : BankTree := .block [[w20,w33,w49,w54,w71],[w20,w33,w50,w53,w71],[w20,w33,w51,w52,w71],[w20,w34,w40,w62,w71],[w20,w34,w42,w60,w71],[w20,w34,w44,w58,w71],[w20,w34,w46,w56,w71],[w20,w34,w48,w54,w71],[w20,w34,w50,w52,w71],[w20,w38,w40,w63,w65],[w20,w38,w41,w62,w65],[w20,w38,w42,w61,w65],[w20,w38,w43,w60,w65],[w20,w38,w44,w59,w65],[w20,w38,w45,w58,w65],[w20,w38,w46,w57,w65],[w20,w38,w47,w56,w65],[w20,w38,w48,w55,w65],[w20,w38,w49,w54,w65],[w20,w38,w50,w53,w65],[w20,w38,w51,w52,w65],[w20,w39,w40,w62,w65],[w20,w39,w42,w60,w65],[w20,w39,w44,w58,w65],[w20,w39,w46,w56,w65],[w20,w39,w48,w54,w65],[w20,w39,w50,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_30 : t4_30.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_28 : BankTree := .fork [w20,w33,w49,w54,w71] t4_29 t4_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_28 : t4_28.rows.all (refuses 3 t3_0)=true := by simp only [t4_28,BankTree.rows,List.all_append,ok_t4_29,ok_t4_30,Bool.true_and]
noncomputable def t4_24 : BankTree := .fork [w20,w30,w41,w62,w77] t4_25 t4_28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_24 : t4_24.rows.all (refuses 3 t3_0)=true := by simp only [t4_24,BankTree.rows,List.all_append,ok_t4_25,ok_t4_28,Bool.true_and]
noncomputable def t4_16 : BankTree := .fork [w19,w34,w42,w61,w71] t4_17 t4_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_16 : t4_16.rows.all (refuses 3 t3_0)=true := by simp only [t4_16,BankTree.rows,List.all_append,ok_t4_17,ok_t4_24,Bool.true_and]
noncomputable def t4_0 : BankTree := .fork [w14,w27,w42,w61,w97] t4_1 t4_16
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_0 : t4_0.rows.all (refuses 3 t3_0)=true := by simp only [t4_0,BankTree.rows,List.all_append,ok_t4_1,ok_t4_16,Bool.true_and]
theorem safe4 : Safe 4 t4_0 := certify 3 t3_0 t4_0 safe3 ok_t4_0
noncomputable def t5_6 : BankTree := .block [[w0,w1,w6,w27,w94,w97],[w0,w1,w19,w27,w77,w94],[w0,w1,w19,w33,w65,w94],[w0,w2,w5,w27,w94,w97],[w0,w2,w6,w19,w94,w108],[w0,w2,w6,w27,w94,w96],[w0,w2,w6,w27,w94,w97],[w0,w2,w6,w27,w94,w98],[w0,w2,w6,w27,w95,w97],[w0,w2,w6,w28,w94,w97],[w0,w2,w8,w27,w94,w97],[w0,w2,w12,w27,w94,w97],[w0,w2,w16,w19,w33,w90],[w0,w2,w16,w19,w91,w114],[w0,w2,w16,w27,w91,w103],[w0,w2,w16,w32,w91,w97],[w0,w2,w16,w33,w91,w96],[w0,w2,w19,w27,w74,w94],[w0,w2,w19,w27,w75,w94],[w0,w2,w19,w27,w76,w94],[w0,w2,w19,w27,w77,w94],[w0,w2,w19,w27,w77,w95],[w0,w2,w19,w27,w79,w94],[w0,w2,w19,w27,w87,w94],[w0,w2,w19,w27,w94,w104],[w0,w2,w19,w27,w94,w115]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_6 : t5_6.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_7 : BankTree := .block [[w0,w2,w19,w28,w77,w94],[w0,w2,w19,w30,w77,w94],[w0,w2,w19,w32,w65,w94],[w0,w2,w19,w33,w64,w94],[w0,w2,w19,w33,w65,w94],[w0,w2,w19,w33,w65,w95],[w0,w2,w19,w33,w67,w94],[w0,w2,w19,w33,w71,w94],[w0,w2,w19,w33,w77,w94],[w0,w2,w19,w33,w94,w97],[w0,w2,w19,w33,w94,w109],[w0,w2,w19,w33,w94,w115],[w0,w2,w19,w34,w65,w94],[w0,w2,w19,w38,w65,w94],[w0,w2,w20,w27,w77,w94],[w0,w2,w20,w33,w65,w94],[w0,w2,w23,w27,w65,w94],[w0,w2,w24,w27,w94,w97],[w0,w2,w27,w33,w94,w97],[w0,w2,w27,w40,w62,w103],[w0,w2,w27,w42,w60,w103],[w0,w2,w27,w44,w58,w103],[w0,w2,w27,w46,w56,w103],[w0,w2,w27,w48,w54,w103],[w0,w2,w27,w50,w52,w103],[w0,w2,w27,w77,w94,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_7 : t5_7.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_5 : BankTree := .fork [w0,w2,w19,w28,w77,w94] t5_6 t5_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_5 : t5_5.rows.all (refuses 4 t4_0)=true := by simp only [t5_5,BankTree.rows,List.all_append,ok_t5_6,ok_t5_7,Bool.true_and]
noncomputable def t5_9 : BankTree := .block [[w0,w2,w27,w94,w97,w104],[w0,w2,w32,w40,w62,w97],[w0,w2,w32,w42,w60,w97],[w0,w2,w32,w44,w58,w97],[w0,w2,w32,w46,w56,w97],[w0,w2,w32,w48,w54,w97],[w0,w2,w32,w50,w52,w97],[w0,w4,w6,w27,w94,w97],[w0,w4,w19,w27,w77,w94],[w0,w4,w19,w33,w65,w94],[w0,w5,w19,w27,w71,w94],[w0,w5,w19,w30,w65,w94],[w0,w6,w12,w27,w94,w97],[w0,w6,w16,w19,w30,w90],[w0,w6,w16,w19,w91,w111],[w0,w6,w16,w27,w91,w100],[w0,w6,w16,w29,w91,w97],[w0,w6,w16,w30,w91,w96],[w0,w6,w19,w27,w68,w94],[w0,w6,w19,w27,w69,w94],[w0,w6,w19,w27,w70,w94],[w0,w6,w19,w27,w71,w94],[w0,w6,w19,w27,w71,w95],[w0,w6,w19,w27,w73,w94],[w0,w6,w19,w27,w87,w94],[w0,w6,w19,w27,w94,w101]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_9 : t5_9.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_10 : BankTree := .block [[w0,w6,w19,w27,w94,w112],[w0,w6,w19,w28,w71,w94],[w0,w6,w19,w29,w65,w94],[w0,w6,w19,w30,w64,w94],[w0,w6,w19,w30,w65,w94],[w0,w6,w19,w30,w65,w95],[w0,w6,w19,w30,w67,w94],[w0,w6,w19,w30,w71,w94],[w0,w6,w19,w30,w77,w94],[w0,w6,w19,w30,w94,w97],[w0,w6,w19,w30,w94,w109],[w0,w6,w19,w30,w94,w112],[w0,w6,w19,w31,w65,w94],[w0,w6,w19,w33,w71,w94],[w0,w6,w19,w38,w65,w94],[w0,w6,w20,w27,w71,w94],[w0,w6,w20,w30,w65,w94],[w0,w6,w21,w27,w65,w94],[w0,w6,w22,w27,w94,w97],[w0,w6,w27,w30,w94,w97],[w0,w6,w27,w40,w62,w100],[w0,w6,w27,w42,w60,w100],[w0,w6,w27,w44,w58,w100],[w0,w6,w27,w46,w56,w100],[w0,w6,w27,w48,w54,w100],[w0,w6,w27,w50,w52,w100],[w0,w6,w27,w71,w94,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_10 : t5_10.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_8 : BankTree := .fork [w0,w6,w19,w27,w94,w112] t5_9 t5_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_8 : t5_8.rows.all (refuses 4 t4_0)=true := by simp only [t5_8,BankTree.rows,List.all_append,ok_t5_9,ok_t5_10,Bool.true_and]
noncomputable def t5_4 : BankTree := .fork [w0,w2,w27,w94,w97,w104] t5_5 t5_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_4 : t5_4.rows.all (refuses 4 t4_0)=true := by simp only [t5_4,BankTree.rows,List.all_append,ok_t5_5,ok_t5_8,Bool.true_and]
noncomputable def t5_13 : BankTree := .block [[w0,w6,w27,w94,w97,w101],[w0,w6,w29,w40,w62,w97],[w0,w6,w29,w42,w60,w97],[w0,w6,w29,w44,w58,w97],[w0,w6,w29,w46,w56,w97],[w0,w6,w29,w48,w54,w97],[w0,w6,w29,w50,w52,w97],[w0,w8,w19,w27,w71,w94],[w0,w8,w19,w30,w65,w94],[w0,w9,w16,w27,w91,w97],[w0,w9,w19,w27,w65,w94],[w0,w9,w27,w40,w62,w97],[w0,w9,w27,w42,w60,w97],[w0,w9,w27,w44,w58,w97],[w0,w9,w27,w46,w56,w97],[w0,w9,w27,w48,w54,w97],[w0,w9,w27,w50,w52,w97],[w0,w10,w16,w27,w91,w97],[w0,w10,w19,w27,w65,w94],[w0,w10,w27,w40,w62,w97],[w0,w10,w27,w42,w60,w97],[w0,w10,w27,w44,w58,w97],[w0,w10,w27,w46,w56,w97],[w0,w10,w27,w48,w54,w97],[w0,w10,w27,w50,w52,w97],[w0,w11,w16,w27,w91,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_13 : t5_13.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_14 : BankTree := .block [[w0,w11,w19,w27,w65,w94],[w0,w11,w27,w40,w62,w97],[w0,w11,w27,w42,w60,w97],[w0,w11,w27,w44,w58,w97],[w0,w11,w27,w46,w56,w97],[w0,w11,w27,w48,w54,w97],[w0,w11,w27,w50,w52,w97],[w0,w12,w16,w19,w27,w90],[w0,w12,w16,w19,w91,w108],[w0,w12,w16,w27,w91,w96],[w0,w12,w16,w27,w91,w97],[w0,w12,w16,w27,w91,w98],[w0,w12,w16,w27,w93,w97],[w0,w12,w16,w27,w94,w97],[w0,w12,w16,w28,w91,w97],[w0,w12,w18,w27,w91,w97],[w0,w12,w19,w27,w64,w94],[w0,w12,w19,w27,w65,w94],[w0,w12,w19,w27,w65,w95],[w0,w12,w19,w27,w67,w94],[w0,w12,w19,w27,w71,w94],[w0,w12,w19,w27,w77,w94],[w0,w12,w19,w27,w87,w94],[w0,w12,w19,w27,w94,w97],[w0,w12,w19,w27,w94,w109],[w0,w12,w19,w28,w65,w94],[w0,w12,w19,w30,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_14 : t5_14.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_12 : BankTree := .fork [w0,w11,w19,w27,w65,w94] t5_13 t5_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_12 : t5_12.rows.all (refuses 4 t4_0)=true := by simp only [t5_12,BankTree.rows,List.all_append,ok_t5_13,ok_t5_14,Bool.true_and]
noncomputable def t5_16 : BankTree := .block [[w0,w12,w19,w33,w65,w94],[w0,w12,w19,w38,w65,w94],[w0,w12,w20,w27,w65,w94],[w0,w12,w27,w40,w62,w97],[w0,w12,w27,w40,w62,w98],[w0,w12,w27,w40,w63,w97],[w0,w12,w27,w40,w94,w97],[w0,w12,w27,w41,w62,w97],[w0,w12,w27,w42,w60,w98],[w0,w12,w27,w42,w61,w97],[w0,w12,w27,w42,w62,w97],[w0,w12,w27,w42,w91,w97],[w0,w12,w27,w42,w94,w97],[w0,w12,w27,w43,w60,w97],[w0,w12,w27,w44,w58,w97],[w0,w12,w27,w44,w58,w98],[w0,w12,w27,w44,w59,w97],[w0,w12,w27,w44,w94,w97],[w0,w12,w27,w45,w58,w97],[w0,w12,w27,w46,w56,w98],[w0,w12,w27,w46,w57,w97],[w0,w12,w27,w46,w58,w97],[w0,w12,w27,w46,w91,w97],[w0,w12,w27,w46,w94,w97],[w0,w12,w27,w47,w56,w97],[w0,w12,w27,w48,w54,w98]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_16 : t5_16.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_17 : BankTree := .block [[w0,w12,w27,w48,w55,w97],[w0,w12,w27,w48,w58,w97],[w0,w12,w27,w48,w62,w97],[w0,w12,w27,w48,w94,w97],[w0,w12,w27,w49,w54,w97],[w0,w12,w27,w50,w52,w97],[w0,w12,w27,w50,w52,w98],[w0,w12,w27,w50,w53,w97],[w0,w12,w27,w50,w54,w97],[w0,w12,w27,w50,w56,w97],[w0,w12,w27,w50,w58,w97],[w0,w12,w27,w50,w60,w97],[w0,w12,w27,w50,w62,w97],[w0,w12,w27,w50,w91,w97],[w0,w12,w27,w50,w94,w97],[w0,w12,w27,w51,w52,w97],[w0,w12,w27,w52,w94,w97],[w0,w12,w27,w54,w91,w97],[w0,w12,w27,w54,w94,w97],[w0,w12,w27,w56,w62,w97],[w0,w12,w27,w56,w94,w97],[w0,w12,w27,w58,w60,w97],[w0,w12,w27,w58,w62,w97],[w0,w12,w27,w58,w91,w97],[w0,w12,w27,w58,w94,w97],[w0,w12,w27,w60,w94,w97],[w0,w12,w27,w62,w91,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_17 : t5_17.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_15 : BankTree := .fork [w0,w12,w27,w48,w55,w97] t5_16 t5_17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_15 : t5_15.rows.all (refuses 4 t4_0)=true := by simp only [t5_15,BankTree.rows,List.all_append,ok_t5_16,ok_t5_17,Bool.true_and]
noncomputable def t5_11 : BankTree := .fork [w0,w12,w19,w33,w65,w94] t5_12 t5_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_11 : t5_11.rows.all (refuses 4 t4_0)=true := by simp only [t5_11,BankTree.rows,List.all_append,ok_t5_12,ok_t5_15,Bool.true_and]
noncomputable def t5_3 : BankTree := .fork [w0,w6,w27,w94,w97,w101] t5_4 t5_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_3 : t5_3.rows.all (refuses 4 t4_0)=true := by simp only [t5_3,BankTree.rows,List.all_append,ok_t5_4,ok_t5_11,Bool.true_and]
noncomputable def t5_21 : BankTree := .block [[w0,w12,w27,w62,w94,w97],[w0,w12,w27,w65,w94,w97],[w0,w12,w27,w91,w94,w97],[w0,w12,w27,w94,w97],[w0,w12,w28,w40,w62,w97],[w0,w12,w28,w42,w60,w97],[w0,w12,w28,w44,w58,w97],[w0,w12,w28,w46,w56,w97],[w0,w12,w28,w48,w54,w97],[w0,w12,w28,w50,w52,w97],[w0,w14,w16,w27,w91,w97],[w0,w14,w19,w27,w65,w94],[w0,w14,w27,w40,w62,w97],[w0,w14,w27,w42,w60,w97],[w0,w14,w27,w44,w58,w97],[w0,w14,w27,w46,w56,w97],[w0,w14,w27,w48,w54,w97],[w0,w14,w27,w50,w52,w97],[w0,w15,w19,w27,w65,w91],[w0,w15,w27,w40,w60,w97],[w0,w15,w27,w44,w56,w97],[w0,w15,w27,w48,w52,w97],[w0,w16,w19,w27,w81,w91],[w0,w16,w19,w27,w83,w91],[w0,w16,w19,w27,w85,w91],[w0,w16,w19,w27,w86,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_21 : t5_21.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_22 : BankTree := .block [[w0,w16,w19,w27,w87,w91],[w0,w16,w19,w27,w87,w93],[w0,w16,w19,w27,w87,w94],[w0,w16,w19,w27,w89,w91],[w0,w16,w19,w27,w91,w107],[w0,w16,w19,w27,w91,w120],[w0,w16,w19,w28,w87,w91],[w0,w16,w19,w29,w77,w91],[w0,w16,w19,w30,w75,w91],[w0,w16,w19,w30,w76,w91],[w0,w16,w19,w30,w77,w91],[w0,w16,w19,w30,w77,w93],[w0,w16,w19,w30,w77,w94],[w0,w16,w19,w30,w79,w91],[w0,w16,w19,w30,w87,w91],[w0,w16,w19,w30,w91,w104],[w0,w16,w19,w30,w91,w115],[w0,w16,w19,w30,w91,w120],[w0,w16,w19,w31,w77,w91],[w0,w16,w19,w32,w71,w91],[w0,w16,w19,w33,w69,w91],[w0,w16,w19,w33,w70,w91],[w0,w16,w19,w33,w71,w91],[w0,w16,w19,w33,w71,w93],[w0,w16,w19,w33,w71,w94],[w0,w16,w19,w33,w73,w91],[w0,w16,w19,w33,w87,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_22 : t5_22.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_20 : BankTree := .fork [w0,w16,w19,w27,w87,w91] t5_21 t5_22
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_20 : t5_20.rows.all (refuses 4 t4_0)=true := by simp only [t5_20,BankTree.rows,List.all_append,ok_t5_21,ok_t5_22,Bool.true_and]
noncomputable def t5_24 : BankTree := .block [[w0,w16,w19,w33,w91,w101],[w0,w16,w19,w33,w91,w112],[w0,w16,w19,w33,w91,w120],[w0,w16,w19,w34,w71,w91],[w0,w16,w19,w35,w65,w91],[w0,w16,w19,w36,w65,w91],[w0,w16,w19,w37,w65,w91],[w0,w16,w19,w38,w64,w91],[w0,w16,w19,w38,w65,w91],[w0,w16,w19,w38,w65,w93],[w0,w16,w19,w38,w65,w94],[w0,w16,w19,w38,w67,w91],[w0,w16,w19,w38,w71,w91],[w0,w16,w19,w38,w77,w91],[w0,w16,w19,w38,w87,w91],[w0,w16,w19,w38,w91,w97],[w0,w16,w19,w38,w91,w109],[w0,w16,w19,w38,w91,w112],[w0,w16,w19,w38,w91,w115],[w0,w16,w19,w38,w91,w120],[w0,w16,w19,w39,w65,w91],[w0,w16,w20,w27,w87,w91],[w0,w16,w20,w30,w77,w91],[w0,w16,w20,w33,w71,w91],[w0,w16,w20,w38,w65,w91],[w0,w16,w21,w27,w77,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_24 : t5_24.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_25 : BankTree := .block [[w0,w16,w21,w33,w65,w91],[w0,w16,w22,w27,w91,w104],[w0,w16,w22,w33,w91,w97],[w0,w16,w23,w27,w71,w91],[w0,w16,w23,w30,w65,w91],[w0,w16,w24,w27,w91,w101],[w0,w16,w24,w30,w91,w97],[w0,w16,w25,w27,w65,w91],[w0,w16,w26,w27,w91,w97],[w0,w16,w27,w38,w91,w97],[w0,w16,w27,w40,w60,w106],[w0,w16,w27,w44,w56,w106],[w0,w16,w27,w48,w52,w106],[w0,w16,w27,w87,w91,w97],[w0,w16,w27,w91,w97,w107],[w0,w16,w27,w91,w101,w104],[w0,w16,w30,w33,w91,w97],[w0,w16,w35,w40,w60,w97],[w0,w16,w35,w44,w56,w97],[w0,w16,w35,w48,w52,w97],[w0,w18,w19,w27,w87,w91],[w0,w18,w19,w30,w77,w91],[w0,w18,w19,w33,w71,w91],[w0,w18,w19,w38,w65,w91],[w0,w19,w22,w27,w77,w94],[w0,w19,w22,w33,w65,w94],[w0,w19,w24,w27,w71,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_25 : t5_25.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_23 : BankTree := .fork [w0,w16,w21,w33,w65,w91] t5_24 t5_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_23 : t5_23.rows.all (refuses 4 t4_0)=true := by simp only [t5_23,BankTree.rows,List.all_append,ok_t5_24,ok_t5_25,Bool.true_and]
noncomputable def t5_19 : BankTree := .fork [w0,w16,w19,w33,w91,w101] t5_20 t5_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_19 : t5_19.rows.all (refuses 4 t4_0)=true := by simp only [t5_19,BankTree.rows,List.all_append,ok_t5_20,ok_t5_23,Bool.true_and]
noncomputable def t5_28 : BankTree := .block [[w0,w19,w24,w30,w65,w94],[w0,w19,w26,w27,w65,w94],[w0,w19,w27,w30,w77,w94],[w0,w19,w27,w33,w71,w94],[w0,w19,w27,w38,w65,w94],[w0,w19,w27,w40,w62,w81],[w0,w19,w27,w40,w62,w83],[w0,w19,w27,w40,w62,w85],[w0,w19,w27,w40,w62,w87],[w0,w19,w27,w40,w62,w89],[w0,w19,w27,w40,w62,w107],[w0,w19,w27,w40,w62,w120],[w0,w19,w27,w40,w63,w87],[w0,w19,w27,w40,w87,w94],[w0,w19,w27,w41,w62,w87],[w0,w19,w27,w42,w60,w81],[w0,w19,w27,w42,w60,w83],[w0,w19,w27,w42,w60,w85],[w0,w19,w27,w42,w60,w87],[w0,w19,w27,w42,w60,w89],[w0,w19,w27,w42,w60,w107],[w0,w19,w27,w42,w60,w120],[w0,w19,w27,w42,w61,w87],[w0,w19,w27,w42,w62,w87],[w0,w19,w27,w42,w87,w91],[w0,w19,w27,w42,w87,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_28 : t5_28.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_29 : BankTree := .block [[w0,w19,w27,w43,w60,w87],[w0,w19,w27,w44,w58,w81],[w0,w19,w27,w44,w58,w83],[w0,w19,w27,w44,w58,w85],[w0,w19,w27,w44,w58,w87],[w0,w19,w27,w44,w58,w89],[w0,w19,w27,w44,w58,w107],[w0,w19,w27,w44,w58,w120],[w0,w19,w27,w44,w59,w87],[w0,w19,w27,w44,w87,w94],[w0,w19,w27,w45,w58,w87],[w0,w19,w27,w46,w56,w81],[w0,w19,w27,w46,w56,w83],[w0,w19,w27,w46,w56,w85],[w0,w19,w27,w46,w56,w87],[w0,w19,w27,w46,w56,w89],[w0,w19,w27,w46,w56,w107],[w0,w19,w27,w46,w56,w120],[w0,w19,w27,w46,w57,w87],[w0,w19,w27,w46,w58,w87],[w0,w19,w27,w46,w87,w91],[w0,w19,w27,w46,w87,w94],[w0,w19,w27,w47,w56,w87],[w0,w19,w27,w48,w54,w81],[w0,w19,w27,w48,w54,w83],[w0,w19,w27,w48,w54,w85],[w0,w19,w27,w48,w54,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_29 : t5_29.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_27 : BankTree := .fork [w0,w19,w27,w43,w60,w87] t5_28 t5_29
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_27 : t5_27.rows.all (refuses 4 t4_0)=true := by simp only [t5_27,BankTree.rows,List.all_append,ok_t5_28,ok_t5_29,Bool.true_and]
noncomputable def t5_31 : BankTree := .block [[w0,w19,w27,w48,w54,w89],[w0,w19,w27,w48,w54,w107],[w0,w19,w27,w48,w54,w120],[w0,w19,w27,w48,w55,w87],[w0,w19,w27,w48,w58,w87],[w0,w19,w27,w48,w62,w87],[w0,w19,w27,w48,w87,w94],[w0,w19,w27,w49,w54,w87],[w0,w19,w27,w50,w52,w81],[w0,w19,w27,w50,w52,w83],[w0,w19,w27,w50,w52,w85],[w0,w19,w27,w50,w52,w87],[w0,w19,w27,w50,w52,w89],[w0,w19,w27,w50,w52,w107],[w0,w19,w27,w50,w52,w120],[w0,w19,w27,w50,w53,w87],[w0,w19,w27,w50,w54,w87],[w0,w19,w27,w50,w56,w87],[w0,w19,w27,w50,w58,w87],[w0,w19,w27,w50,w60,w87],[w0,w19,w27,w50,w62,w87],[w0,w19,w27,w50,w87,w91],[w0,w19,w27,w50,w87,w94],[w0,w19,w27,w51,w52,w87],[w0,w19,w27,w52,w87,w94],[w0,w19,w27,w54,w87,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_31 : t5_31.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_32 : BankTree := .block [[w0,w19,w27,w54,w87,w94],[w0,w19,w27,w56,w62,w87],[w0,w19,w27,w56,w87,w94],[w0,w19,w27,w58,w60,w87],[w0,w19,w27,w58,w62,w87],[w0,w19,w27,w58,w87,w91],[w0,w19,w27,w58,w87,w94],[w0,w19,w27,w60,w87,w94],[w0,w19,w27,w62,w87,w91],[w0,w19,w27,w62,w87,w94],[w0,w19,w27,w65,w87,w94],[w0,w19,w27,w71,w77,w94],[w0,w19,w27,w71,w87,w94],[w0,w19,w27,w77,w87,w94],[w0,w19,w27,w87,w91,w94],[w0,w19,w27,w87,w94],[w0,w19,w28,w40,w62,w87],[w0,w19,w28,w42,w60,w87],[w0,w19,w28,w44,w58,w87],[w0,w19,w28,w46,w56,w87],[w0,w19,w28,w48,w54,w87],[w0,w19,w28,w50,w52,w87],[w0,w19,w29,w40,w62,w77],[w0,w19,w29,w42,w60,w77],[w0,w19,w29,w44,w58,w77],[w0,w19,w29,w46,w56,w77],[w0,w19,w29,w48,w54,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_32 : t5_32.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_30 : BankTree := .fork [w0,w19,w27,w54,w87,w94] t5_31 t5_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_30 : t5_30.rows.all (refuses 4 t4_0)=true := by simp only [t5_30,BankTree.rows,List.all_append,ok_t5_31,ok_t5_32,Bool.true_and]
noncomputable def t5_26 : BankTree := .fork [w0,w19,w27,w48,w54,w89] t5_27 t5_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_26 : t5_26.rows.all (refuses 4 t4_0)=true := by simp only [t5_26,BankTree.rows,List.all_append,ok_t5_27,ok_t5_30,Bool.true_and]
noncomputable def t5_18 : BankTree := .fork [w0,w19,w24,w30,w65,w94] t5_19 t5_26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_18 : t5_18.rows.all (refuses 4 t4_0)=true := by simp only [t5_18,BankTree.rows,List.all_append,ok_t5_19,ok_t5_26,Bool.true_and]
noncomputable def t5_2 : BankTree := .fork [w0,w12,w27,w62,w94,w97] t5_3 t5_18
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_2 : t5_2.rows.all (refuses 4 t4_0)=true := by simp only [t5_2,BankTree.rows,List.all_append,ok_t5_3,ok_t5_18,Bool.true_and]
noncomputable def t5_37 : BankTree := .block [[w0,w19,w29,w50,w52,w77],[w0,w19,w30,w33,w65,w94],[w0,w19,w30,w38,w65,w94],[w0,w19,w30,w40,w62,w75],[w0,w19,w30,w40,w62,w77],[w0,w19,w30,w40,w62,w79],[w0,w19,w30,w40,w62,w87],[w0,w19,w30,w40,w62,w104],[w0,w19,w30,w40,w62,w115],[w0,w19,w30,w40,w62,w120],[w0,w19,w30,w40,w63,w77],[w0,w19,w30,w40,w77,w94],[w0,w19,w30,w41,w62,w77],[w0,w19,w30,w42,w60,w75],[w0,w19,w30,w42,w60,w79],[w0,w19,w30,w42,w60,w87],[w0,w19,w30,w42,w60,w104],[w0,w19,w30,w42,w60,w115],[w0,w19,w30,w42,w60,w120],[w0,w19,w30,w42,w61,w77],[w0,w19,w30,w42,w62,w77],[w0,w19,w30,w42,w77,w91],[w0,w19,w30,w42,w77,w94],[w0,w19,w30,w43,w60,w77],[w0,w19,w30,w44,w58,w75],[w0,w19,w30,w44,w58,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_37 : t5_37.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_38 : BankTree := .block [[w0,w19,w30,w44,w58,w79],[w0,w19,w30,w44,w58,w87],[w0,w19,w30,w44,w58,w104],[w0,w19,w30,w44,w58,w115],[w0,w19,w30,w44,w58,w120],[w0,w19,w30,w44,w59,w77],[w0,w19,w30,w44,w77,w94],[w0,w19,w30,w45,w58,w77],[w0,w19,w30,w46,w56,w75],[w0,w19,w30,w46,w56,w79],[w0,w19,w30,w46,w56,w87],[w0,w19,w30,w46,w56,w104],[w0,w19,w30,w46,w56,w115],[w0,w19,w30,w46,w56,w120],[w0,w19,w30,w46,w57,w77],[w0,w19,w30,w46,w58,w77],[w0,w19,w30,w46,w77,w91],[w0,w19,w30,w46,w77,w94],[w0,w19,w30,w47,w56,w77],[w0,w19,w30,w48,w54,w75],[w0,w19,w30,w48,w54,w79],[w0,w19,w30,w48,w54,w87],[w0,w19,w30,w48,w54,w104],[w0,w19,w30,w48,w54,w115],[w0,w19,w30,w48,w54,w120],[w0,w19,w30,w48,w55,w77],[w0,w19,w30,w48,w58,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_38 : t5_38.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_36 : BankTree := .fork [w0,w19,w30,w44,w58,w79] t5_37 t5_38
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_36 : t5_36.rows.all (refuses 4 t4_0)=true := by simp only [t5_36,BankTree.rows,List.all_append,ok_t5_37,ok_t5_38,Bool.true_and]
noncomputable def t5_40 : BankTree := .block [[w0,w19,w30,w48,w62,w77],[w0,w19,w30,w48,w77,w94],[w0,w19,w30,w49,w54,w77],[w0,w19,w30,w50,w52,w75],[w0,w19,w30,w50,w52,w77],[w0,w19,w30,w50,w52,w79],[w0,w19,w30,w50,w52,w87],[w0,w19,w30,w50,w52,w104],[w0,w19,w30,w50,w52,w115],[w0,w19,w30,w50,w52,w120],[w0,w19,w30,w50,w53,w77],[w0,w19,w30,w50,w54,w77],[w0,w19,w30,w50,w56,w77],[w0,w19,w30,w50,w58,w77],[w0,w19,w30,w50,w60,w77],[w0,w19,w30,w50,w62,w77],[w0,w19,w30,w50,w77,w91],[w0,w19,w30,w50,w77,w94],[w0,w19,w30,w51,w52,w77],[w0,w19,w30,w52,w77,w94],[w0,w19,w30,w54,w77,w91],[w0,w19,w30,w54,w77,w94],[w0,w19,w30,w56,w62,w77],[w0,w19,w30,w56,w77,w94],[w0,w19,w30,w58,w60,w77],[w0,w19,w30,w58,w62,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_40 : t5_40.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_41 : BankTree := .block [[w0,w19,w30,w58,w77,w91],[w0,w19,w30,w58,w77,w94],[w0,w19,w30,w60,w77,w94],[w0,w19,w30,w62,w77,w91],[w0,w19,w30,w62,w77,w94],[w0,w19,w30,w65,w77,w94],[w0,w19,w30,w77,w91,w94],[w0,w19,w30,w77,w94],[w0,w19,w31,w40,w62,w77],[w0,w19,w31,w42,w60,w77],[w0,w19,w31,w44,w58,w77],[w0,w19,w31,w46,w56,w77],[w0,w19,w31,w48,w54,w77],[w0,w19,w31,w50,w52,w77],[w0,w19,w32,w40,w62,w71],[w0,w19,w32,w42,w60,w71],[w0,w19,w32,w44,w58,w71],[w0,w19,w32,w46,w56,w71],[w0,w19,w32,w48,w54,w71],[w0,w19,w32,w50,w52,w71],[w0,w19,w33,w38,w65,w94],[w0,w19,w33,w40,w62,w69],[w0,w19,w33,w40,w62,w71],[w0,w19,w33,w40,w62,w73],[w0,w19,w33,w40,w62,w87],[w0,w19,w33,w40,w62,w101],[w0,w19,w33,w40,w62,w112]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_41 : t5_41.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_39 : BankTree := .fork [w0,w19,w30,w58,w77,w91] t5_40 t5_41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_39 : t5_39.rows.all (refuses 4 t4_0)=true := by simp only [t5_39,BankTree.rows,List.all_append,ok_t5_40,ok_t5_41,Bool.true_and]
noncomputable def t5_35 : BankTree := .fork [w0,w19,w30,w48,w62,w77] t5_36 t5_39
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_35 : t5_35.rows.all (refuses 4 t4_0)=true := by simp only [t5_35,BankTree.rows,List.all_append,ok_t5_36,ok_t5_39,Bool.true_and]
noncomputable def t5_44 : BankTree := .block [[w0,w19,w33,w40,w62,w120],[w0,w19,w33,w40,w63,w71],[w0,w19,w33,w40,w71,w94],[w0,w19,w33,w41,w62,w71],[w0,w19,w33,w42,w60,w69],[w0,w19,w33,w42,w60,w73],[w0,w19,w33,w42,w60,w87],[w0,w19,w33,w42,w60,w101],[w0,w19,w33,w42,w60,w112],[w0,w19,w33,w42,w60,w120],[w0,w19,w33,w42,w61,w71],[w0,w19,w33,w42,w62,w71],[w0,w19,w33,w42,w71,w91],[w0,w19,w33,w42,w71,w94],[w0,w19,w33,w43,w60,w71],[w0,w19,w33,w44,w58,w69],[w0,w19,w33,w44,w58,w71],[w0,w19,w33,w44,w58,w73],[w0,w19,w33,w44,w58,w87],[w0,w19,w33,w44,w58,w101],[w0,w19,w33,w44,w58,w112],[w0,w19,w33,w44,w58,w120],[w0,w19,w33,w44,w59,w71],[w0,w19,w33,w44,w71,w94],[w0,w19,w33,w45,w58,w71],[w0,w19,w33,w46,w56,w69]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_44 : t5_44.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_45 : BankTree := .block [[w0,w19,w33,w46,w56,w73],[w0,w19,w33,w46,w56,w87],[w0,w19,w33,w46,w56,w101],[w0,w19,w33,w46,w56,w112],[w0,w19,w33,w46,w56,w120],[w0,w19,w33,w46,w57,w71],[w0,w19,w33,w46,w58,w71],[w0,w19,w33,w46,w71,w91],[w0,w19,w33,w46,w71,w94],[w0,w19,w33,w47,w56,w71],[w0,w19,w33,w48,w54,w69],[w0,w19,w33,w48,w54,w73],[w0,w19,w33,w48,w54,w87],[w0,w19,w33,w48,w54,w101],[w0,w19,w33,w48,w54,w112],[w0,w19,w33,w48,w54,w120],[w0,w19,w33,w48,w55,w71],[w0,w19,w33,w48,w58,w71],[w0,w19,w33,w48,w62,w71],[w0,w19,w33,w48,w71,w94],[w0,w19,w33,w49,w54,w71],[w0,w19,w33,w50,w52,w69],[w0,w19,w33,w50,w52,w71],[w0,w19,w33,w50,w52,w73],[w0,w19,w33,w50,w52,w87],[w0,w19,w33,w50,w52,w101],[w0,w19,w33,w50,w52,w112]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_45 : t5_45.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_43 : BankTree := .fork [w0,w19,w33,w46,w56,w73] t5_44 t5_45
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_43 : t5_43.rows.all (refuses 4 t4_0)=true := by simp only [t5_43,BankTree.rows,List.all_append,ok_t5_44,ok_t5_45,Bool.true_and]
noncomputable def t5_47 : BankTree := .block [[w0,w19,w33,w50,w52,w120],[w0,w19,w33,w50,w53,w71],[w0,w19,w33,w50,w54,w71],[w0,w19,w33,w50,w56,w71],[w0,w19,w33,w50,w58,w71],[w0,w19,w33,w50,w60,w71],[w0,w19,w33,w50,w62,w71],[w0,w19,w33,w50,w71,w91],[w0,w19,w33,w50,w71,w94],[w0,w19,w33,w51,w52,w71],[w0,w19,w33,w52,w71,w94],[w0,w19,w33,w54,w71,w91],[w0,w19,w33,w54,w71,w94],[w0,w19,w33,w56,w62,w71],[w0,w19,w33,w56,w71,w94],[w0,w19,w33,w58,w60,w71],[w0,w19,w33,w58,w62,w71],[w0,w19,w33,w58,w71,w91],[w0,w19,w33,w58,w71,w94],[w0,w19,w33,w60,w71,w94],[w0,w19,w33,w62,w71,w91],[w0,w19,w33,w62,w71,w94],[w0,w19,w33,w65,w71,w94],[w0,w19,w33,w71,w91,w94],[w0,w19,w33,w71,w94],[w0,w19,w34,w40,w62,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_47 : t5_47.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_48 : BankTree := .block [[w0,w19,w34,w42,w60,w71],[w0,w19,w34,w44,w58,w71],[w0,w19,w34,w46,w56,w71],[w0,w19,w34,w48,w54,w71],[w0,w19,w34,w50,w52,w71],[w0,w19,w35,w40,w62,w65],[w0,w19,w35,w42,w60,w65],[w0,w19,w35,w44,w58,w65],[w0,w19,w35,w46,w56,w65],[w0,w19,w35,w48,w54,w65],[w0,w19,w35,w50,w52,w65],[w0,w19,w36,w40,w62,w65],[w0,w19,w36,w42,w60,w65],[w0,w19,w36,w44,w58,w65],[w0,w19,w36,w46,w56,w65],[w0,w19,w36,w48,w54,w65],[w0,w19,w36,w50,w52,w65],[w0,w19,w37,w40,w62,w65],[w0,w19,w37,w42,w60,w65],[w0,w19,w37,w44,w58,w65],[w0,w19,w37,w46,w56,w65],[w0,w19,w37,w48,w54,w65],[w0,w19,w37,w50,w52,w65],[w0,w19,w38,w40,w62,w65],[w0,w19,w38,w40,w62,w67],[w0,w19,w38,w40,w62,w71],[w0,w19,w38,w40,w62,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_48 : t5_48.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_46 : BankTree := .fork [w0,w19,w34,w42,w60,w71] t5_47 t5_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_46 : t5_46.rows.all (refuses 4 t4_0)=true := by simp only [t5_46,BankTree.rows,List.all_append,ok_t5_47,ok_t5_48,Bool.true_and]
noncomputable def t5_42 : BankTree := .fork [w0,w19,w33,w50,w52,w120] t5_43 t5_46
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_42 : t5_42.rows.all (refuses 4 t4_0)=true := by simp only [t5_42,BankTree.rows,List.all_append,ok_t5_43,ok_t5_46,Bool.true_and]
noncomputable def t5_34 : BankTree := .fork [w0,w19,w33,w40,w62,w120] t5_35 t5_42
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_34 : t5_34.rows.all (refuses 4 t4_0)=true := by simp only [t5_34,BankTree.rows,List.all_append,ok_t5_35,ok_t5_42,Bool.true_and]
noncomputable def t5_52 : BankTree := .block [[w0,w19,w38,w40,w62,w87],[w0,w19,w38,w40,w62,w97],[w0,w19,w38,w40,w62,w109],[w0,w19,w38,w40,w62,w112],[w0,w19,w38,w40,w62,w115],[w0,w19,w38,w40,w62,w120],[w0,w19,w38,w40,w63,w65],[w0,w19,w38,w40,w65,w94],[w0,w19,w38,w41,w62,w65],[w0,w19,w38,w42,w60,w65],[w0,w19,w38,w42,w60,w67],[w0,w19,w38,w42,w60,w71],[w0,w19,w38,w42,w60,w77],[w0,w19,w38,w42,w60,w87],[w0,w19,w38,w42,w60,w97],[w0,w19,w38,w42,w60,w109],[w0,w19,w38,w42,w60,w112],[w0,w19,w38,w42,w60,w115],[w0,w19,w38,w42,w60,w120],[w0,w19,w38,w42,w61,w65],[w0,w19,w38,w42,w62,w65],[w0,w19,w38,w42,w65,w91],[w0,w19,w38,w42,w65,w94],[w0,w19,w38,w43,w60,w65],[w0,w19,w38,w44,w58,w65],[w0,w19,w38,w44,w58,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_52 : t5_52.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_53 : BankTree := .block [[w0,w19,w38,w44,w58,w71],[w0,w19,w38,w44,w58,w77],[w0,w19,w38,w44,w58,w87],[w0,w19,w38,w44,w58,w97],[w0,w19,w38,w44,w58,w109],[w0,w19,w38,w44,w58,w112],[w0,w19,w38,w44,w58,w115],[w0,w19,w38,w44,w58,w120],[w0,w19,w38,w44,w59,w65],[w0,w19,w38,w44,w65,w94],[w0,w19,w38,w45,w58,w65],[w0,w19,w38,w46,w56,w65],[w0,w19,w38,w46,w56,w67],[w0,w19,w38,w46,w56,w71],[w0,w19,w38,w46,w56,w77],[w0,w19,w38,w46,w56,w87],[w0,w19,w38,w46,w56,w97],[w0,w19,w38,w46,w56,w109],[w0,w19,w38,w46,w56,w112],[w0,w19,w38,w46,w56,w115],[w0,w19,w38,w46,w56,w120],[w0,w19,w38,w46,w57,w65],[w0,w19,w38,w46,w58,w65],[w0,w19,w38,w46,w65,w91],[w0,w19,w38,w46,w65,w94],[w0,w19,w38,w47,w56,w65],[w0,w19,w38,w48,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_53 : t5_53.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_51 : BankTree := .fork [w0,w19,w38,w44,w58,w71] t5_52 t5_53
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_51 : t5_51.rows.all (refuses 4 t4_0)=true := by simp only [t5_51,BankTree.rows,List.all_append,ok_t5_52,ok_t5_53,Bool.true_and]
noncomputable def t5_55 : BankTree := .block [[w0,w19,w38,w48,w54,w67],[w0,w19,w38,w48,w54,w71],[w0,w19,w38,w48,w54,w77],[w0,w19,w38,w48,w54,w87],[w0,w19,w38,w48,w54,w97],[w0,w19,w38,w48,w54,w109],[w0,w19,w38,w48,w54,w112],[w0,w19,w38,w48,w54,w115],[w0,w19,w38,w48,w54,w120],[w0,w19,w38,w48,w55,w65],[w0,w19,w38,w48,w58,w65],[w0,w19,w38,w48,w62,w65],[w0,w19,w38,w48,w65,w94],[w0,w19,w38,w49,w54,w65],[w0,w19,w38,w50,w52,w65],[w0,w19,w38,w50,w52,w67],[w0,w19,w38,w50,w52,w71],[w0,w19,w38,w50,w52,w77],[w0,w19,w38,w50,w52,w87],[w0,w19,w38,w50,w52,w97],[w0,w19,w38,w50,w52,w109],[w0,w19,w38,w50,w52,w112],[w0,w19,w38,w50,w52,w115],[w0,w19,w38,w50,w52,w120],[w0,w19,w38,w50,w53,w65],[w0,w19,w38,w50,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_55 : t5_55.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_56 : BankTree := .block [[w0,w19,w38,w50,w56,w65],[w0,w19,w38,w50,w58,w65],[w0,w19,w38,w50,w60,w65],[w0,w19,w38,w50,w62,w65],[w0,w19,w38,w50,w65,w91],[w0,w19,w38,w50,w65,w94],[w0,w19,w38,w51,w52,w65],[w0,w19,w38,w52,w65,w94],[w0,w19,w38,w54,w65,w91],[w0,w19,w38,w54,w65,w94],[w0,w19,w38,w56,w62,w65],[w0,w19,w38,w56,w65,w94],[w0,w19,w38,w58,w60,w65],[w0,w19,w38,w58,w62,w65],[w0,w19,w38,w58,w65,w91],[w0,w19,w38,w58,w65,w94],[w0,w19,w38,w60,w65,w94],[w0,w19,w38,w62,w65,w91],[w0,w19,w38,w62,w65,w94],[w0,w19,w38,w65,w91,w94],[w0,w19,w38,w65,w94],[w0,w19,w39,w40,w62,w65],[w0,w19,w39,w42,w60,w65],[w0,w19,w39,w44,w58,w65],[w0,w19,w39,w46,w56,w65],[w0,w19,w39,w48,w54,w65],[w0,w19,w39,w50,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_56 : t5_56.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_54 : BankTree := .fork [w0,w19,w38,w50,w56,w65] t5_55 t5_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_54 : t5_54.rows.all (refuses 4 t4_0)=true := by simp only [t5_54,BankTree.rows,List.all_append,ok_t5_55,ok_t5_56,Bool.true_and]
noncomputable def t5_50 : BankTree := .fork [w0,w19,w38,w48,w54,w67] t5_51 t5_54
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_50 : t5_50.rows.all (refuses 4 t4_0)=true := by simp only [t5_50,BankTree.rows,List.all_append,ok_t5_51,ok_t5_54,Bool.true_and]
noncomputable def t5_59 : BankTree := .block [[w0,w20,w27,w40,w62,w87],[w0,w20,w27,w42,w60,w87],[w0,w20,w27,w44,w58,w87],[w0,w20,w27,w46,w56,w87],[w0,w20,w27,w48,w54,w87],[w0,w20,w27,w50,w52,w87],[w0,w20,w30,w40,w62,w77],[w0,w20,w30,w42,w60,w77],[w0,w20,w30,w44,w58,w77],[w0,w20,w30,w46,w56,w77],[w0,w20,w30,w48,w54,w77],[w0,w20,w30,w50,w52,w77],[w0,w20,w33,w40,w62,w71],[w0,w20,w33,w42,w60,w71],[w0,w20,w33,w44,w58,w71],[w0,w20,w33,w46,w56,w71],[w0,w20,w33,w48,w54,w71],[w0,w20,w33,w50,w52,w71],[w0,w20,w38,w40,w62,w65],[w0,w20,w38,w42,w60,w65],[w0,w20,w38,w44,w58,w65],[w0,w20,w38,w46,w56,w65],[w0,w20,w38,w48,w54,w65],[w0,w20,w38,w50,w52,w65],[w0,w21,w27,w40,w62,w77],[w0,w21,w27,w42,w60,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_59 : t5_59.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_60 : BankTree := .block [[w0,w21,w27,w44,w58,w77],[w0,w21,w27,w46,w56,w77],[w0,w21,w27,w48,w54,w77],[w0,w21,w27,w50,w52,w77],[w0,w21,w33,w40,w62,w65],[w0,w21,w33,w42,w60,w65],[w0,w21,w33,w44,w58,w65],[w0,w21,w33,w46,w56,w65],[w0,w21,w33,w48,w54,w65],[w0,w21,w33,w50,w52,w65],[w0,w22,w24,w27,w65,w94],[w0,w22,w27,w40,w62,w104],[w0,w22,w27,w42,w60,w104],[w0,w22,w27,w44,w58,w104],[w0,w22,w27,w46,w56,w104],[w0,w22,w27,w48,w54,w104],[w0,w22,w27,w50,w52,w104],[w0,w22,w33,w40,w62,w97],[w0,w22,w33,w42,w60,w97],[w0,w22,w33,w44,w58,w97],[w0,w22,w33,w46,w56,w97],[w0,w22,w33,w48,w54,w97],[w0,w22,w33,w50,w52,w97],[w0,w23,w27,w40,w62,w71],[w0,w23,w27,w42,w60,w71],[w0,w23,w27,w44,w58,w71],[w0,w23,w27,w46,w56,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_60 : t5_60.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_58 : BankTree := .fork [w0,w21,w27,w44,w58,w77] t5_59 t5_60
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_58 : t5_58.rows.all (refuses 4 t4_0)=true := by simp only [t5_58,BankTree.rows,List.all_append,ok_t5_59,ok_t5_60,Bool.true_and]
noncomputable def t5_62 : BankTree := .block [[w0,w23,w27,w48,w54,w71],[w0,w23,w27,w50,w52,w71],[w0,w23,w30,w40,w62,w65],[w0,w23,w30,w42,w60,w65],[w0,w23,w30,w44,w58,w65],[w0,w23,w30,w46,w56,w65],[w0,w23,w30,w48,w54,w65],[w0,w23,w30,w50,w52,w65],[w0,w24,w27,w40,w62,w101],[w0,w24,w27,w42,w60,w101],[w0,w24,w27,w44,w58,w101],[w0,w24,w27,w46,w56,w101],[w0,w24,w27,w48,w54,w101],[w0,w24,w27,w50,w52,w101],[w0,w24,w30,w40,w62,w97],[w0,w24,w30,w42,w60,w97],[w0,w24,w30,w44,w58,w97],[w0,w24,w30,w46,w56,w97],[w0,w24,w30,w48,w54,w97],[w0,w24,w30,w50,w52,w97],[w0,w25,w27,w40,w62,w65],[w0,w25,w27,w42,w60,w65],[w0,w25,w27,w44,w58,w65],[w0,w25,w27,w46,w56,w65],[w0,w25,w27,w48,w54,w65],[w0,w25,w27,w50,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_62 : t5_62.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_63 : BankTree := .block [[w0,w26,w27,w40,w62,w97],[w0,w26,w27,w42,w60,w97],[w0,w26,w27,w44,w58,w97],[w0,w26,w27,w46,w56,w97],[w0,w26,w27,w48,w54,w97],[w0,w26,w27,w50,w52,w97],[w0,w27,w38,w40,w62,w97],[w0,w27,w38,w42,w60,w97],[w0,w27,w38,w44,w58,w97],[w0,w27,w38,w46,w56,w97],[w0,w27,w38,w48,w54,w97],[w0,w27,w38,w50,w52,w97],[w0,w27,w40,w44,w54,w106],[w0,w27,w40,w46,w52,w106],[w0,w27,w40,w62,w87,w97],[w0,w27,w40,w62,w97,w107],[w0,w27,w40,w62,w101,w104],[w0,w27,w42,w44,w52,w106],[w0,w27,w42,w60,w87,w97],[w0,w27,w42,w60,w97,w107],[w0,w27,w42,w60,w101,w104],[w0,w27,w44,w58,w87,w97],[w0,w27,w44,w58,w97,w107],[w0,w27,w44,w58,w101,w104],[w0,w27,w46,w56,w87,w97],[w0,w27,w46,w56,w97,w107],[w0,w27,w46,w56,w101,w104]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_63 : t5_63.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_61 : BankTree := .fork [w0,w26,w27,w40,w62,w97] t5_62 t5_63
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_61 : t5_61.rows.all (refuses 4 t4_0)=true := by simp only [t5_61,BankTree.rows,List.all_append,ok_t5_62,ok_t5_63,Bool.true_and]
noncomputable def t5_57 : BankTree := .fork [w0,w23,w27,w48,w54,w71] t5_58 t5_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_57 : t5_57.rows.all (refuses 4 t4_0)=true := by simp only [t5_57,BankTree.rows,List.all_append,ok_t5_58,ok_t5_61,Bool.true_and]
noncomputable def t5_49 : BankTree := .fork [w0,w20,w27,w40,w62,w87] t5_50 t5_57
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_49 : t5_49.rows.all (refuses 4 t4_0)=true := by simp only [t5_49,BankTree.rows,List.all_append,ok_t5_50,ok_t5_57,Bool.true_and]
noncomputable def t5_33 : BankTree := .fork [w0,w19,w38,w40,w62,w87] t5_34 t5_49
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_33 : t5_33.rows.all (refuses 4 t4_0)=true := by simp only [t5_33,BankTree.rows,List.all_append,ok_t5_34,ok_t5_49,Bool.true_and]
noncomputable def t5_1 : BankTree := .fork [w0,w19,w29,w50,w52,w77] t5_2 t5_33
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_1 : t5_1.rows.all (refuses 4 t4_0)=true := by simp only [t5_1,BankTree.rows,List.all_append,ok_t5_2,ok_t5_33,Bool.true_and]
noncomputable def t5_69 : BankTree := .block [[w0,w27,w48,w54,w87,w97],[w0,w27,w48,w54,w97,w107],[w0,w27,w48,w54,w101,w104],[w0,w27,w50,w52,w87,w97],[w0,w27,w50,w52,w97,w107],[w0,w27,w50,w52,w101,w104],[w0,w30,w33,w40,w62,w97],[w0,w30,w33,w42,w60,w97],[w0,w30,w33,w44,w58,w97],[w0,w30,w33,w46,w56,w97],[w0,w30,w33,w48,w54,w97],[w0,w30,w33,w50,w52,w97],[w0,w35,w40,w44,w54,w97],[w0,w35,w40,w46,w52,w97],[w0,w35,w42,w44,w52,w97],[w2,w6,w16,w19,w27,w92],[w2,w6,w16,w27,w93,w98],[w2,w6,w16,w28,w91,w98],[w2,w6,w16,w28,w93,w97],[w2,w6,w18,w27,w91,w98],[w2,w6,w18,w28,w91,w97],[w2,w6,w19,w27,w66,w94],[w2,w6,w19,w27,w67,w95],[w2,w6,w19,w28,w65,w95],[w2,w6,w19,w28,w67,w94],[w2,w6,w20,w27,w65,w95]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_69 : t5_69.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_70 : BankTree := .block [[w2,w6,w20,w28,w65,w94],[w2,w6,w27,w40,w63,w98],[w2,w6,w27,w41,w62,w98],[w2,w6,w27,w42,w61,w98],[w2,w6,w27,w43,w60,w98],[w2,w6,w27,w44,w59,w98],[w2,w6,w27,w45,w58,w98],[w2,w6,w27,w46,w57,w98],[w2,w6,w27,w47,w56,w98],[w2,w6,w27,w48,w55,w98],[w2,w6,w27,w49,w54,w98],[w2,w6,w27,w50,w53,w98],[w2,w6,w27,w51,w52,w98],[w2,w6,w28,w40,w62,w98],[w2,w6,w28,w40,w63,w97],[w2,w6,w28,w41,w62,w97],[w2,w6,w28,w42,w60,w98],[w2,w6,w28,w42,w61,w97],[w2,w6,w28,w43,w60,w97],[w2,w6,w28,w44,w58,w98],[w2,w6,w28,w44,w59,w97],[w2,w6,w28,w45,w58,w97],[w2,w6,w28,w46,w56,w98],[w2,w6,w28,w46,w57,w97],[w2,w6,w28,w47,w56,w97],[w2,w6,w28,w48,w54,w98],[w2,w6,w28,w48,w55,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_70 : t5_70.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_68 : BankTree := .fork [w2,w6,w20,w28,w65,w94] t5_69 t5_70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_68 : t5_68.rows.all (refuses 4 t4_0)=true := by simp only [t5_68,BankTree.rows,List.all_append,ok_t5_69,ok_t5_70,Bool.true_and]
noncomputable def t5_72 : BankTree := .block [[w2,w6,w28,w49,w54,w97],[w2,w6,w28,w50,w52,w98],[w2,w6,w28,w50,w53,w97],[w2,w6,w28,w51,w52,w97],[w2,w7,w16,w27,w91,w97],[w2,w7,w19,w27,w65,w94],[w2,w7,w27,w40,w62,w97],[w2,w7,w27,w42,w60,w97],[w2,w7,w27,w44,w58,w97],[w2,w7,w27,w46,w56,w97],[w2,w7,w27,w48,w54,w97],[w2,w7,w27,w50,w52,w97],[w2,w8,w16,w27,w93,w97],[w2,w8,w18,w27,w91,w97],[w2,w8,w19,w27,w65,w95],[w2,w8,w20,w27,w65,w94],[w2,w8,w27,w40,w63,w97],[w2,w8,w27,w41,w62,w97],[w2,w8,w27,w42,w61,w97],[w2,w8,w27,w43,w60,w97],[w2,w8,w27,w44,w59,w97],[w2,w8,w27,w45,w58,w97],[w2,w8,w27,w46,w57,w97],[w2,w8,w27,w47,w56,w97],[w2,w8,w27,w48,w55,w97],[w2,w8,w27,w49,w54,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_72 : t5_72.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_73 : BankTree := .block [[w2,w8,w27,w50,w53,w97],[w2,w8,w27,w51,w52,w97],[w2,w16,w19,w27,w79,w93],[w2,w16,w19,w28,w77,w93],[w2,w16,w19,w33,w66,w91],[w2,w16,w19,w33,w67,w93],[w2,w16,w19,w34,w65,w93],[w2,w16,w20,w27,w77,w93],[w2,w16,w20,w28,w77,w91],[w2,w16,w20,w33,w65,w93],[w2,w16,w20,w34,w65,w91],[w2,w18,w19,w27,w79,w91],[w2,w18,w19,w28,w77,w91],[w2,w18,w19,w33,w67,w91],[w2,w18,w19,w34,w65,w91],[w2,w18,w20,w27,w77,w91],[w2,w18,w20,w33,w65,w91],[w2,w19,w27,w40,w63,w79],[w2,w19,w27,w41,w62,w79],[w2,w19,w27,w42,w61,w79],[w2,w19,w27,w43,w60,w79],[w2,w19,w27,w44,w59,w79],[w2,w19,w27,w45,w58,w79],[w2,w19,w27,w46,w57,w79],[w2,w19,w27,w47,w56,w79],[w2,w19,w27,w48,w55,w79],[w2,w19,w27,w49,w54,w79]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_73 : t5_73.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_71 : BankTree := .fork [w2,w8,w27,w50,w53,w97] t5_72 t5_73
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_71 : t5_71.rows.all (refuses 4 t4_0)=true := by simp only [t5_71,BankTree.rows,List.all_append,ok_t5_72,ok_t5_73,Bool.true_and]
noncomputable def t5_67 : BankTree := .fork [w2,w6,w28,w49,w54,w97] t5_68 t5_71
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_67 : t5_67.rows.all (refuses 4 t4_0)=true := by simp only [t5_67,BankTree.rows,List.all_append,ok_t5_68,ok_t5_71,Bool.true_and]
noncomputable def t5_76 : BankTree := .block [[w2,w19,w27,w50,w53,w79],[w2,w19,w27,w51,w52,w79],[w2,w19,w28,w40,w63,w77],[w2,w19,w28,w41,w62,w77],[w2,w19,w28,w42,w61,w77],[w2,w19,w28,w43,w60,w77],[w2,w19,w28,w44,w59,w77],[w2,w19,w28,w45,w58,w77],[w2,w19,w28,w46,w57,w77],[w2,w19,w28,w47,w56,w77],[w2,w19,w28,w48,w55,w77],[w2,w19,w28,w49,w54,w77],[w2,w19,w28,w50,w53,w77],[w2,w19,w28,w51,w52,w77],[w2,w19,w33,w40,w63,w67],[w2,w19,w33,w41,w62,w67],[w2,w19,w33,w42,w61,w67],[w2,w19,w33,w43,w60,w67],[w2,w19,w33,w44,w59,w67],[w2,w19,w33,w45,w58,w67],[w2,w19,w33,w46,w57,w67],[w2,w19,w33,w47,w56,w67],[w2,w19,w33,w48,w55,w67],[w2,w19,w33,w49,w54,w67],[w2,w19,w33,w50,w53,w67],[w2,w19,w33,w51,w52,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_76 : t5_76.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_77 : BankTree := .block [[w2,w19,w34,w40,w63,w65],[w2,w19,w34,w41,w62,w65],[w2,w19,w34,w42,w61,w65],[w2,w19,w34,w43,w60,w65],[w2,w19,w34,w44,w59,w65],[w2,w19,w34,w45,w58,w65],[w2,w19,w34,w46,w57,w65],[w2,w19,w34,w47,w56,w65],[w2,w19,w34,w48,w55,w65],[w2,w19,w34,w49,w54,w65],[w2,w19,w34,w50,w53,w65],[w2,w19,w34,w51,w52,w65],[w2,w20,w27,w40,w63,w77],[w2,w20,w27,w41,w62,w77],[w2,w20,w27,w42,w61,w77],[w2,w20,w27,w43,w60,w77],[w2,w20,w27,w44,w59,w77],[w2,w20,w27,w45,w58,w77],[w2,w20,w27,w46,w57,w77],[w2,w20,w27,w47,w56,w77],[w2,w20,w27,w48,w55,w77],[w2,w20,w27,w49,w54,w77],[w2,w20,w27,w50,w53,w77],[w2,w20,w27,w51,w52,w77],[w2,w20,w28,w40,w62,w77],[w2,w20,w28,w42,w60,w77],[w2,w20,w28,w44,w58,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_77 : t5_77.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_75 : BankTree := .fork [w2,w19,w34,w40,w63,w65] t5_76 t5_77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_75 : t5_75.rows.all (refuses 4 t4_0)=true := by simp only [t5_75,BankTree.rows,List.all_append,ok_t5_76,ok_t5_77,Bool.true_and]
noncomputable def t5_79 : BankTree := .block [[w2,w20,w28,w46,w56,w77],[w2,w20,w28,w48,w54,w77],[w2,w20,w28,w50,w52,w77],[w2,w20,w33,w40,w63,w65],[w2,w20,w33,w41,w62,w65],[w2,w20,w33,w42,w61,w65],[w2,w20,w33,w43,w60,w65],[w2,w20,w33,w44,w59,w65],[w2,w20,w33,w45,w58,w65],[w2,w20,w33,w46,w57,w65],[w2,w20,w33,w47,w56,w65],[w2,w20,w33,w48,w55,w65],[w2,w20,w33,w49,w54,w65],[w2,w20,w33,w50,w53,w65],[w2,w20,w33,w51,w52,w65],[w2,w20,w34,w40,w62,w65],[w2,w20,w34,w42,w60,w65],[w2,w20,w34,w44,w58,w65],[w2,w20,w34,w46,w56,w65],[w2,w20,w34,w48,w54,w65],[w2,w20,w34,w50,w52,w65],[w3,w6,w16,w27,w91,w97],[w3,w6,w19,w27,w65,w94],[w3,w6,w27,w40,w62,w97],[w3,w6,w27,w42,w60,w97],[w3,w6,w27,w44,w58,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_79 : t5_79.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_80 : BankTree := .block [[w3,w6,w27,w46,w56,w97],[w3,w6,w27,w48,w54,w97],[w3,w6,w27,w50,w52,w97],[w3,w16,w19,w27,w77,w91],[w3,w16,w19,w33,w65,w91],[w3,w19,w27,w40,w62,w77],[w3,w19,w27,w42,w60,w77],[w3,w19,w27,w44,w58,w77],[w3,w19,w27,w46,w56,w77],[w3,w19,w27,w48,w54,w77],[w3,w19,w27,w50,w52,w77],[w3,w19,w33,w40,w62,w65],[w3,w19,w33,w42,w60,w65],[w3,w19,w33,w44,w58,w65],[w3,w19,w33,w46,w56,w65],[w3,w19,w33,w48,w54,w65],[w3,w19,w33,w50,w52,w65],[w4,w6,w16,w27,w93,w97],[w4,w6,w18,w27,w91,w97],[w4,w6,w19,w27,w65,w95],[w4,w6,w20,w27,w65,w94],[w4,w6,w27,w40,w63,w97],[w4,w6,w27,w41,w62,w97],[w4,w6,w27,w42,w61,w97],[w4,w6,w27,w43,w60,w97],[w4,w6,w27,w44,w59,w97],[w4,w6,w27,w45,w58,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_80 : t5_80.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_78 : BankTree := .fork [w3,w6,w27,w46,w56,w97] t5_79 t5_80
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_78 : t5_78.rows.all (refuses 4 t4_0)=true := by simp only [t5_78,BankTree.rows,List.all_append,ok_t5_79,ok_t5_80,Bool.true_and]
noncomputable def t5_74 : BankTree := .fork [w2,w20,w28,w46,w56,w77] t5_75 t5_78
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_74 : t5_74.rows.all (refuses 4 t4_0)=true := by simp only [t5_74,BankTree.rows,List.all_append,ok_t5_75,ok_t5_78,Bool.true_and]
noncomputable def t5_66 : BankTree := .fork [w2,w19,w27,w50,w53,w79] t5_67 t5_74
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_66 : t5_66.rows.all (refuses 4 t4_0)=true := by simp only [t5_66,BankTree.rows,List.all_append,ok_t5_67,ok_t5_74,Bool.true_and]
noncomputable def t5_84 : BankTree := .block [[w4,w6,w27,w46,w57,w97],[w4,w6,w27,w47,w56,w97],[w4,w6,w27,w48,w55,w97],[w4,w6,w27,w49,w54,w97],[w4,w6,w27,w50,w53,w97],[w4,w6,w27,w51,w52,w97],[w4,w8,w16,w27,w91,w97],[w4,w8,w19,w27,w65,w94],[w4,w8,w27,w40,w62,w97],[w4,w8,w27,w42,w60,w97],[w4,w8,w27,w44,w58,w97],[w4,w8,w27,w46,w56,w97],[w4,w8,w27,w48,w54,w97],[w4,w8,w27,w50,w52,w97],[w4,w16,w19,w27,w77,w93],[w4,w16,w19,w33,w65,w93],[w4,w16,w20,w27,w77,w91],[w4,w16,w20,w33,w65,w91],[w4,w18,w19,w27,w77,w91],[w4,w18,w19,w33,w65,w91],[w4,w19,w27,w40,w63,w77],[w4,w19,w27,w41,w62,w77],[w4,w19,w27,w42,w61,w77],[w4,w19,w27,w43,w60,w77],[w4,w19,w27,w44,w59,w77],[w4,w19,w27,w45,w58,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_84 : t5_84.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_85 : BankTree := .block [[w4,w19,w27,w46,w57,w77],[w4,w19,w27,w47,w56,w77],[w4,w19,w27,w48,w55,w77],[w4,w19,w27,w49,w54,w77],[w4,w19,w27,w50,w53,w77],[w4,w19,w27,w51,w52,w77],[w4,w19,w33,w40,w63,w65],[w4,w19,w33,w41,w62,w65],[w4,w19,w33,w42,w61,w65],[w4,w19,w33,w43,w60,w65],[w4,w19,w33,w44,w59,w65],[w4,w19,w33,w45,w58,w65],[w4,w19,w33,w46,w57,w65],[w4,w19,w33,w47,w56,w65],[w4,w19,w33,w48,w55,w65],[w4,w19,w33,w49,w54,w65],[w4,w19,w33,w50,w53,w65],[w4,w19,w33,w51,w52,w65],[w4,w20,w27,w40,w62,w77],[w4,w20,w27,w42,w60,w77],[w4,w20,w27,w44,w58,w77],[w4,w20,w27,w46,w56,w77],[w4,w20,w27,w48,w54,w77],[w4,w20,w27,w50,w52,w77],[w4,w20,w33,w40,w62,w65],[w4,w20,w33,w42,w60,w65],[w4,w20,w33,w44,w58,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_85 : t5_85.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_83 : BankTree := .fork [w4,w19,w27,w46,w57,w77] t5_84 t5_85
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_83 : t5_83.rows.all (refuses 4 t4_0)=true := by simp only [t5_83,BankTree.rows,List.all_append,ok_t5_84,ok_t5_85,Bool.true_and]
noncomputable def t5_87 : BankTree := .block [[w4,w20,w33,w46,w56,w65],[w4,w20,w33,w48,w54,w65],[w4,w20,w33,w50,w52,w65],[w6,w16,w19,w27,w73,w93],[w6,w16,w19,w28,w71,w93],[w6,w16,w19,w30,w66,w91],[w6,w16,w19,w30,w67,w93],[w6,w16,w19,w31,w65,w93],[w6,w16,w20,w27,w71,w93],[w6,w16,w20,w28,w71,w91],[w6,w16,w20,w30,w65,w93],[w6,w16,w20,w31,w65,w91],[w6,w18,w19,w27,w73,w91],[w6,w18,w19,w28,w71,w91],[w6,w18,w19,w30,w67,w91],[w6,w18,w19,w31,w65,w91],[w6,w18,w20,w27,w71,w91],[w6,w18,w20,w30,w65,w91],[w6,w19,w27,w40,w63,w73],[w6,w19,w27,w41,w62,w73],[w6,w19,w27,w42,w61,w73],[w6,w19,w27,w43,w60,w73],[w6,w19,w27,w44,w59,w73],[w6,w19,w27,w45,w58,w73],[w6,w19,w27,w46,w57,w73],[w6,w19,w27,w47,w56,w73]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_87 : t5_87.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_88 : BankTree := .block [[w6,w19,w27,w48,w55,w73],[w6,w19,w27,w49,w54,w73],[w6,w19,w27,w50,w53,w73],[w6,w19,w27,w51,w52,w73],[w6,w19,w28,w40,w63,w71],[w6,w19,w28,w41,w62,w71],[w6,w19,w28,w42,w61,w71],[w6,w19,w28,w43,w60,w71],[w6,w19,w28,w44,w59,w71],[w6,w19,w28,w45,w58,w71],[w6,w19,w28,w46,w57,w71],[w6,w19,w28,w47,w56,w71],[w6,w19,w28,w48,w55,w71],[w6,w19,w28,w49,w54,w71],[w6,w19,w28,w50,w53,w71],[w6,w19,w28,w51,w52,w71],[w6,w19,w30,w40,w63,w67],[w6,w19,w30,w41,w62,w67],[w6,w19,w30,w42,w61,w67],[w6,w19,w30,w43,w60,w67],[w6,w19,w30,w44,w59,w67],[w6,w19,w30,w45,w58,w67],[w6,w19,w30,w46,w57,w67],[w6,w19,w30,w47,w56,w67],[w6,w19,w30,w48,w55,w67],[w6,w19,w30,w49,w54,w67],[w6,w19,w30,w50,w53,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_88 : t5_88.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_86 : BankTree := .fork [w6,w19,w27,w48,w55,w73] t5_87 t5_88
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_86 : t5_86.rows.all (refuses 4 t4_0)=true := by simp only [t5_86,BankTree.rows,List.all_append,ok_t5_87,ok_t5_88,Bool.true_and]
noncomputable def t5_82 : BankTree := .fork [w4,w20,w33,w46,w56,w65] t5_83 t5_86
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_82 : t5_82.rows.all (refuses 4 t4_0)=true := by simp only [t5_82,BankTree.rows,List.all_append,ok_t5_83,ok_t5_86,Bool.true_and]
noncomputable def t5_91 : BankTree := .block [[w6,w19,w30,w51,w52,w67],[w6,w19,w31,w40,w63,w65],[w6,w19,w31,w41,w62,w65],[w6,w19,w31,w42,w61,w65],[w6,w19,w31,w43,w60,w65],[w6,w19,w31,w44,w59,w65],[w6,w19,w31,w45,w58,w65],[w6,w19,w31,w46,w57,w65],[w6,w19,w31,w47,w56,w65],[w6,w19,w31,w48,w55,w65],[w6,w19,w31,w49,w54,w65],[w6,w19,w31,w50,w53,w65],[w6,w19,w31,w51,w52,w65],[w6,w20,w27,w40,w63,w71],[w6,w20,w27,w41,w62,w71],[w6,w20,w27,w42,w61,w71],[w6,w20,w27,w43,w60,w71],[w6,w20,w27,w44,w59,w71],[w6,w20,w27,w45,w58,w71],[w6,w20,w27,w46,w57,w71],[w6,w20,w27,w47,w56,w71],[w6,w20,w27,w48,w55,w71],[w6,w20,w27,w49,w54,w71],[w6,w20,w27,w50,w53,w71],[w6,w20,w27,w51,w52,w71],[w6,w20,w28,w40,w62,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_91 : t5_91.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_92 : BankTree := .block [[w6,w20,w28,w42,w60,w71],[w6,w20,w28,w44,w58,w71],[w6,w20,w28,w46,w56,w71],[w6,w20,w28,w48,w54,w71],[w6,w20,w28,w50,w52,w71],[w6,w20,w30,w40,w63,w65],[w6,w20,w30,w41,w62,w65],[w6,w20,w30,w42,w61,w65],[w6,w20,w30,w43,w60,w65],[w6,w20,w30,w44,w59,w65],[w6,w20,w30,w45,w58,w65],[w6,w20,w30,w46,w57,w65],[w6,w20,w30,w47,w56,w65],[w6,w20,w30,w48,w55,w65],[w6,w20,w30,w49,w54,w65],[w6,w20,w30,w50,w53,w65],[w6,w20,w30,w51,w52,w65],[w6,w20,w31,w40,w62,w65],[w6,w20,w31,w42,w60,w65],[w6,w20,w31,w44,w58,w65],[w6,w20,w31,w46,w56,w65],[w6,w20,w31,w48,w54,w65],[w6,w20,w31,w50,w52,w65],[w7,w16,w19,w27,w71,w91],[w7,w16,w19,w30,w65,w91],[w7,w19,w27,w40,w62,w71],[w7,w19,w27,w42,w60,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_92 : t5_92.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_90 : BankTree := .fork [w6,w20,w28,w42,w60,w71] t5_91 t5_92
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_90 : t5_90.rows.all (refuses 4 t4_0)=true := by simp only [t5_90,BankTree.rows,List.all_append,ok_t5_91,ok_t5_92,Bool.true_and]
noncomputable def t5_94 : BankTree := .block [[w7,w19,w27,w44,w58,w71],[w7,w19,w27,w46,w56,w71],[w7,w19,w27,w48,w54,w71],[w7,w19,w27,w50,w52,w71],[w7,w19,w30,w40,w62,w65],[w7,w19,w30,w42,w60,w65],[w7,w19,w30,w44,w58,w65],[w7,w19,w30,w46,w56,w65],[w7,w19,w30,w48,w54,w65],[w7,w19,w30,w50,w52,w65],[w8,w16,w19,w27,w71,w93],[w8,w16,w19,w30,w65,w93],[w8,w16,w20,w27,w71,w91],[w8,w16,w20,w30,w65,w91],[w8,w18,w19,w27,w71,w91],[w8,w18,w19,w30,w65,w91],[w8,w19,w27,w40,w63,w71],[w8,w19,w27,w41,w62,w71],[w8,w19,w27,w42,w61,w71],[w8,w19,w27,w43,w60,w71],[w8,w19,w27,w44,w59,w71],[w8,w19,w27,w45,w58,w71],[w8,w19,w27,w46,w57,w71],[w8,w19,w27,w47,w56,w71],[w8,w19,w27,w48,w55,w71],[w8,w19,w27,w49,w54,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_94 : t5_94.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_95 : BankTree := .block [[w8,w19,w27,w50,w53,w71],[w8,w19,w27,w51,w52,w71],[w8,w19,w30,w40,w63,w65],[w8,w19,w30,w41,w62,w65],[w8,w19,w30,w42,w61,w65],[w8,w19,w30,w43,w60,w65],[w8,w19,w30,w44,w59,w65],[w8,w19,w30,w45,w58,w65],[w8,w19,w30,w46,w57,w65],[w8,w19,w30,w47,w56,w65],[w8,w19,w30,w48,w55,w65],[w8,w19,w30,w49,w54,w65],[w8,w19,w30,w50,w53,w65],[w8,w19,w30,w51,w52,w65],[w8,w20,w27,w40,w62,w71],[w8,w20,w27,w42,w60,w71],[w8,w20,w27,w44,w58,w71],[w8,w20,w27,w46,w56,w71],[w8,w20,w27,w48,w54,w71],[w8,w20,w27,w50,w52,w71],[w8,w20,w30,w40,w62,w65],[w8,w20,w30,w42,w60,w65],[w8,w20,w30,w44,w58,w65],[w8,w20,w30,w46,w56,w65],[w8,w20,w30,w48,w54,w65],[w8,w20,w30,w50,w52,w65],[w12,w16,w19,w27,w66,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_95 : t5_95.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_93 : BankTree := .fork [w8,w19,w27,w50,w53,w71] t5_94 t5_95
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_93 : t5_93.rows.all (refuses 4 t4_0)=true := by simp only [t5_93,BankTree.rows,List.all_append,ok_t5_94,ok_t5_95,Bool.true_and]
noncomputable def t5_89 : BankTree := .fork [w7,w19,w27,w44,w58,w71] t5_90 t5_93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_89 : t5_89.rows.all (refuses 4 t4_0)=true := by simp only [t5_89,BankTree.rows,List.all_append,ok_t5_90,ok_t5_93,Bool.true_and]
noncomputable def t5_81 : BankTree := .fork [w6,w19,w30,w51,w52,w67] t5_82 t5_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_81 : t5_81.rows.all (refuses 4 t4_0)=true := by simp only [t5_81,BankTree.rows,List.all_append,ok_t5_82,ok_t5_89,Bool.true_and]
noncomputable def t5_65 : BankTree := .fork [w4,w6,w27,w46,w57,w97] t5_66 t5_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_65 : t5_65.rows.all (refuses 4 t4_0)=true := by simp only [t5_65,BankTree.rows,List.all_append,ok_t5_66,ok_t5_81,Bool.true_and]
noncomputable def t5_100 : BankTree := .block [[w12,w16,w19,w27,w67,w93],[w12,w16,w19,w28,w65,w93],[w12,w16,w19,w28,w67,w91],[w12,w16,w20,w27,w65,w93],[w12,w16,w20,w28,w65,w91],[w12,w16,w27,w40,w61,w98],[w12,w16,w27,w41,w60,w98],[w12,w16,w27,w41,w61,w97],[w12,w16,w27,w44,w57,w98],[w12,w16,w27,w45,w56,w98],[w12,w16,w27,w45,w57,w97],[w12,w16,w27,w48,w53,w98],[w12,w16,w27,w49,w52,w98],[w12,w16,w27,w49,w53,w97],[w12,w16,w28,w40,w60,w98],[w12,w16,w28,w40,w61,w97],[w12,w16,w28,w41,w60,w97],[w12,w16,w28,w44,w56,w98],[w12,w16,w28,w44,w57,w97],[w12,w16,w28,w45,w56,w97],[w12,w16,w28,w48,w52,w98],[w12,w16,w28,w48,w53,w97],[w12,w16,w28,w49,w52,w97],[w12,w18,w19,w27,w67,w91],[w12,w18,w19,w28,w65,w91],[w12,w18,w20,w27,w65,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_100 : t5_100.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_101 : BankTree := .block [[w12,w18,w27,w40,w60,w98],[w12,w18,w27,w44,w56,w98],[w12,w18,w27,w48,w52,w98],[w12,w18,w28,w40,w60,w97],[w12,w18,w28,w44,w56,w97],[w12,w18,w28,w48,w52,w97],[w12,w19,w27,w40,w63,w67],[w12,w19,w27,w41,w62,w67],[w12,w19,w27,w42,w61,w67],[w12,w19,w27,w43,w60,w67],[w12,w19,w27,w44,w59,w67],[w12,w19,w27,w45,w58,w67],[w12,w19,w27,w46,w57,w67],[w12,w19,w27,w47,w56,w67],[w12,w19,w27,w48,w55,w67],[w12,w19,w27,w49,w54,w67],[w12,w19,w27,w50,w53,w67],[w12,w19,w27,w51,w52,w67],[w12,w19,w28,w40,w62,w67],[w12,w19,w28,w40,w63,w65],[w12,w19,w28,w41,w62,w65],[w12,w19,w28,w42,w60,w67],[w12,w19,w28,w42,w61,w65],[w12,w19,w28,w43,w60,w65],[w12,w19,w28,w44,w58,w67],[w12,w19,w28,w44,w59,w65],[w12,w19,w28,w45,w58,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_101 : t5_101.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_99 : BankTree := .fork [w12,w18,w27,w40,w60,w98] t5_100 t5_101
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_99 : t5_99.rows.all (refuses 4 t4_0)=true := by simp only [t5_99,BankTree.rows,List.all_append,ok_t5_100,ok_t5_101,Bool.true_and]
noncomputable def t5_103 : BankTree := .block [[w12,w19,w28,w46,w56,w67],[w12,w19,w28,w46,w57,w65],[w12,w19,w28,w47,w56,w65],[w12,w19,w28,w48,w54,w67],[w12,w19,w28,w48,w55,w65],[w12,w19,w28,w49,w54,w65],[w12,w19,w28,w50,w52,w67],[w12,w19,w28,w50,w53,w65],[w12,w19,w28,w51,w52,w65],[w12,w20,w27,w40,w63,w65],[w12,w20,w27,w41,w62,w65],[w12,w20,w27,w42,w61,w65],[w12,w20,w27,w43,w60,w65],[w12,w20,w27,w44,w59,w65],[w12,w20,w27,w45,w58,w65],[w12,w20,w27,w46,w57,w65],[w12,w20,w27,w47,w56,w65],[w12,w20,w27,w48,w55,w65],[w12,w20,w27,w49,w54,w65],[w12,w20,w27,w50,w53,w65],[w12,w20,w27,w51,w52,w65],[w12,w20,w28,w40,w62,w65],[w12,w20,w28,w42,w60,w65],[w12,w20,w28,w44,w58,w65],[w12,w20,w28,w46,w56,w65],[w12,w20,w28,w48,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_103 : t5_103.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_104 : BankTree := .block [[w12,w20,w28,w50,w52,w65],[w12,w27,w40,w44,w55,w98],[w12,w27,w40,w45,w54,w98],[w12,w27,w40,w46,w53,w98],[w12,w27,w40,w47,w52,w98],[w12,w27,w41,w44,w54,w98],[w12,w27,w41,w45,w54,w97],[w12,w27,w41,w46,w52,w98],[w12,w27,w41,w46,w53,w97],[w12,w27,w42,w44,w53,w98],[w12,w27,w42,w45,w52,w98],[w12,w27,w42,w45,w53,w97],[w12,w27,w43,w44,w52,w98],[w12,w28,w40,w44,w54,w98],[w12,w28,w40,w44,w55,w97],[w12,w28,w40,w45,w54,w97],[w12,w28,w40,w46,w52,w98],[w12,w28,w40,w46,w53,w97],[w12,w28,w40,w47,w52,w97],[w12,w28,w41,w44,w54,w97],[w12,w28,w41,w46,w52,w97],[w12,w28,w42,w44,w52,w98],[w12,w28,w42,w44,w53,w97],[w12,w28,w42,w45,w52,w97],[w12,w28,w43,w44,w52,w97],[w13,w16,w19,w27,w65,w91],[w13,w16,w27,w40,w60,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_104 : t5_104.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_102 : BankTree := .fork [w12,w20,w28,w50,w52,w65] t5_103 t5_104
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_102 : t5_102.rows.all (refuses 4 t4_0)=true := by simp only [t5_102,BankTree.rows,List.all_append,ok_t5_103,ok_t5_104,Bool.true_and]
noncomputable def t5_98 : BankTree := .fork [w12,w19,w28,w46,w56,w67] t5_99 t5_102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_98 : t5_98.rows.all (refuses 4 t4_0)=true := by simp only [t5_98,BankTree.rows,List.all_append,ok_t5_99,ok_t5_102,Bool.true_and]
noncomputable def t5_107 : BankTree := .block [[w13,w16,w27,w44,w56,w97],[w13,w16,w27,w48,w52,w97],[w13,w19,w27,w40,w62,w65],[w13,w19,w27,w42,w60,w65],[w13,w19,w27,w44,w58,w65],[w13,w19,w27,w46,w56,w65],[w13,w19,w27,w48,w54,w65],[w13,w19,w27,w50,w52,w65],[w13,w27,w40,w44,w54,w97],[w13,w27,w40,w46,w52,w97],[w13,w27,w42,w44,w52,w97],[w14,w16,w19,w27,w65,w93],[w14,w16,w20,w27,w65,w91],[w14,w16,w27,w40,w61,w97],[w14,w16,w27,w41,w60,w97],[w14,w16,w27,w44,w57,w97],[w14,w16,w27,w45,w56,w97],[w14,w16,w27,w48,w53,w97],[w14,w16,w27,w49,w52,w97],[w14,w18,w19,w27,w65,w91],[w14,w18,w27,w40,w60,w97],[w14,w18,w27,w44,w56,w97],[w14,w18,w27,w48,w52,w97],[w14,w19,w27,w40,w63,w65],[w14,w19,w27,w41,w62,w65],[w14,w19,w27,w42,w61,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_107 : t5_107.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_108 : BankTree := .block [[w14,w19,w27,w43,w60,w65],[w14,w19,w27,w44,w59,w65],[w14,w19,w27,w45,w58,w65],[w14,w19,w27,w46,w57,w65],[w14,w19,w27,w47,w56,w65],[w14,w19,w27,w48,w55,w65],[w14,w19,w27,w49,w54,w65],[w14,w19,w27,w50,w53,w65],[w14,w19,w27,w51,w52,w65],[w14,w20,w27,w40,w62,w65],[w14,w20,w27,w42,w60,w65],[w14,w20,w27,w44,w58,w65],[w14,w20,w27,w46,w56,w65],[w14,w20,w27,w48,w54,w65],[w14,w20,w27,w50,w52,w65],[w14,w27,w40,w44,w55,w97],[w14,w27,w40,w45,w54,w97],[w14,w27,w40,w46,w53,w97],[w14,w27,w40,w47,w52,w97],[w14,w27,w41,w44,w54,w97],[w14,w27,w41,w46,w52,w97],[w14,w27,w42,w44,w53,w97],[w14,w27,w42,w45,w52,w97],[w14,w27,w43,w44,w52,w97],[w16,w19,w27,w40,w61,w89],[w16,w19,w27,w41,w60,w89],[w16,w19,w27,w41,w61,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_108 : t5_108.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_106 : BankTree := .fork [w14,w19,w27,w43,w60,w65] t5_107 t5_108
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_106 : t5_106.rows.all (refuses 4 t4_0)=true := by simp only [t5_106,BankTree.rows,List.all_append,ok_t5_107,ok_t5_108,Bool.true_and]
noncomputable def t5_110 : BankTree := .block [[w16,w19,w27,w44,w57,w89],[w16,w19,w27,w45,w56,w89],[w16,w19,w27,w45,w57,w87],[w16,w19,w27,w48,w53,w89],[w16,w19,w27,w49,w52,w89],[w16,w19,w27,w49,w53,w87],[w16,w19,w28,w40,w61,w87],[w16,w19,w28,w41,w60,w87],[w16,w19,w28,w44,w57,w87],[w16,w19,w28,w45,w56,w87],[w16,w19,w28,w48,w53,w87],[w16,w19,w28,w49,w52,w87],[w16,w19,w30,w40,w61,w79],[w16,w19,w30,w41,w60,w79],[w16,w19,w30,w41,w61,w77],[w16,w19,w30,w44,w57,w79],[w16,w19,w30,w45,w56,w79],[w16,w19,w30,w45,w57,w77],[w16,w19,w30,w48,w53,w79],[w16,w19,w30,w49,w52,w79],[w16,w19,w30,w49,w53,w77],[w16,w19,w31,w40,w61,w77],[w16,w19,w31,w41,w60,w77],[w16,w19,w31,w44,w57,w77],[w16,w19,w31,w45,w56,w77],[w16,w19,w31,w48,w53,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_110 : t5_110.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_111 : BankTree := .block [[w16,w19,w31,w49,w52,w77],[w16,w19,w33,w40,w61,w73],[w16,w19,w33,w41,w60,w73],[w16,w19,w33,w41,w61,w71],[w16,w19,w33,w44,w57,w73],[w16,w19,w33,w45,w56,w73],[w16,w19,w33,w45,w57,w71],[w16,w19,w33,w48,w53,w73],[w16,w19,w33,w49,w52,w73],[w16,w19,w33,w49,w53,w71],[w16,w19,w34,w40,w61,w71],[w16,w19,w34,w41,w60,w71],[w16,w19,w34,w44,w57,w71],[w16,w19,w34,w45,w56,w71],[w16,w19,w34,w48,w53,w71],[w16,w19,w34,w49,w52,w71],[w16,w19,w38,w40,w61,w67],[w16,w19,w38,w41,w60,w67],[w16,w19,w38,w41,w61,w65],[w16,w19,w38,w44,w57,w67],[w16,w19,w38,w45,w56,w67],[w16,w19,w38,w45,w57,w65],[w16,w19,w38,w48,w53,w67],[w16,w19,w38,w49,w52,w67],[w16,w19,w38,w49,w53,w65],[w16,w19,w39,w40,w61,w65],[w16,w19,w39,w41,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_111 : t5_111.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_109 : BankTree := .fork [w16,w19,w31,w49,w52,w77] t5_110 t5_111
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_109 : t5_109.rows.all (refuses 4 t4_0)=true := by simp only [t5_109,BankTree.rows,List.all_append,ok_t5_110,ok_t5_111,Bool.true_and]
noncomputable def t5_105 : BankTree := .fork [w16,w19,w27,w44,w57,w89] t5_106 t5_109
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_105 : t5_105.rows.all (refuses 4 t4_0)=true := by simp only [t5_105,BankTree.rows,List.all_append,ok_t5_106,ok_t5_109,Bool.true_and]
noncomputable def t5_97 : BankTree := .fork [w13,w16,w27,w44,w56,w97] t5_98 t5_105
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_97 : t5_97.rows.all (refuses 4 t4_0)=true := by simp only [t5_97,BankTree.rows,List.all_append,ok_t5_98,ok_t5_105,Bool.true_and]
noncomputable def t5_115 : BankTree := .block [[w16,w19,w39,w44,w57,w65],[w16,w19,w39,w45,w56,w65],[w16,w19,w39,w48,w53,w65],[w16,w19,w39,w49,w52,w65],[w16,w20,w27,w40,w61,w87],[w16,w20,w27,w41,w60,w87],[w16,w20,w27,w44,w57,w87],[w16,w20,w27,w45,w56,w87],[w16,w20,w27,w48,w53,w87],[w16,w20,w27,w49,w52,w87],[w16,w20,w28,w40,w60,w87],[w16,w20,w28,w44,w56,w87],[w16,w20,w28,w48,w52,w87],[w16,w20,w30,w40,w61,w77],[w16,w20,w30,w41,w60,w77],[w16,w20,w30,w44,w57,w77],[w16,w20,w30,w45,w56,w77],[w16,w20,w30,w48,w53,w77],[w16,w20,w30,w49,w52,w77],[w16,w20,w31,w40,w60,w77],[w16,w20,w31,w44,w56,w77],[w16,w20,w31,w48,w52,w77],[w16,w20,w33,w40,w61,w71],[w16,w20,w33,w41,w60,w71],[w16,w20,w33,w44,w57,w71],[w16,w20,w33,w45,w56,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_115 : t5_115.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_116 : BankTree := .block [[w16,w20,w33,w48,w53,w71],[w16,w20,w33,w49,w52,w71],[w16,w20,w34,w40,w60,w71],[w16,w20,w34,w44,w56,w71],[w16,w20,w34,w48,w52,w71],[w16,w20,w38,w40,w61,w65],[w16,w20,w38,w41,w60,w65],[w16,w20,w38,w44,w57,w65],[w16,w20,w38,w45,w56,w65],[w16,w20,w38,w48,w53,w65],[w16,w20,w38,w49,w52,w65],[w16,w20,w39,w40,w60,w65],[w16,w20,w39,w44,w56,w65],[w16,w20,w39,w48,w52,w65],[w17,w19,w27,w40,w60,w65],[w17,w19,w27,w44,w56,w65],[w17,w19,w27,w48,w52,w65],[w17,w27,w40,w44,w52,w97],[w18,w19,w27,w40,w60,w89],[w18,w19,w27,w44,w56,w89],[w18,w19,w27,w48,w52,w89],[w18,w19,w28,w40,w60,w87],[w18,w19,w28,w44,w56,w87],[w18,w19,w28,w48,w52,w87],[w18,w19,w30,w40,w60,w79],[w18,w19,w30,w44,w56,w79],[w18,w19,w30,w48,w52,w79]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_116 : t5_116.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_114 : BankTree := .fork [w16,w20,w33,w48,w53,w71] t5_115 t5_116
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_114 : t5_114.rows.all (refuses 4 t4_0)=true := by simp only [t5_114,BankTree.rows,List.all_append,ok_t5_115,ok_t5_116,Bool.true_and]
noncomputable def t5_118 : BankTree := .block [[w18,w19,w31,w40,w60,w77],[w18,w19,w31,w44,w56,w77],[w18,w19,w31,w48,w52,w77],[w18,w19,w33,w40,w60,w73],[w18,w19,w33,w44,w56,w73],[w18,w19,w33,w48,w52,w73],[w18,w19,w34,w40,w60,w71],[w18,w19,w34,w44,w56,w71],[w18,w19,w34,w48,w52,w71],[w18,w19,w38,w40,w60,w67],[w18,w19,w38,w44,w56,w67],[w18,w19,w38,w48,w52,w67],[w18,w19,w39,w40,w60,w65],[w18,w19,w39,w44,w56,w65],[w18,w19,w39,w48,w52,w65],[w18,w20,w27,w40,w60,w87],[w18,w20,w27,w44,w56,w87],[w18,w20,w27,w48,w52,w87],[w18,w20,w30,w40,w60,w77],[w18,w20,w30,w44,w56,w77],[w18,w20,w30,w48,w52,w77],[w18,w20,w33,w40,w60,w71],[w18,w20,w33,w44,w56,w71],[w18,w20,w33,w48,w52,w71],[w18,w20,w38,w40,w60,w65],[w18,w20,w38,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_118 : t5_118.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_119 : BankTree := .block [[w18,w20,w38,w48,w52,w65],[w19,w27,w40,w44,w55,w89],[w19,w27,w40,w45,w54,w89],[w19,w27,w40,w46,w53,w89],[w19,w27,w40,w47,w52,w89],[w19,w27,w41,w44,w54,w89],[w19,w27,w41,w45,w54,w87],[w19,w27,w41,w46,w52,w89],[w19,w27,w41,w46,w53,w87],[w19,w27,w42,w44,w53,w89],[w19,w27,w42,w45,w52,w89],[w19,w27,w42,w45,w53,w87],[w19,w27,w43,w44,w52,w89],[w19,w28,w40,w44,w55,w87],[w19,w28,w40,w45,w54,w87],[w19,w28,w40,w46,w53,w87],[w19,w28,w40,w47,w52,w87],[w19,w28,w41,w44,w54,w87],[w19,w28,w41,w46,w52,w87],[w19,w28,w42,w44,w53,w87],[w19,w28,w42,w45,w52,w87],[w19,w28,w43,w44,w52,w87],[w19,w30,w40,w44,w55,w79],[w19,w30,w40,w45,w54,w79],[w19,w30,w40,w46,w53,w79],[w19,w30,w40,w47,w52,w79],[w19,w30,w41,w44,w54,w79]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_119 : t5_119.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_117 : BankTree := .fork [w18,w20,w38,w48,w52,w65] t5_118 t5_119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_117 : t5_117.rows.all (refuses 4 t4_0)=true := by simp only [t5_117,BankTree.rows,List.all_append,ok_t5_118,ok_t5_119,Bool.true_and]
noncomputable def t5_113 : BankTree := .fork [w18,w19,w31,w40,w60,w77] t5_114 t5_117
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_113 : t5_113.rows.all (refuses 4 t4_0)=true := by simp only [t5_113,BankTree.rows,List.all_append,ok_t5_114,ok_t5_117,Bool.true_and]
noncomputable def t5_122 : BankTree := .block [[w19,w30,w41,w45,w54,w77],[w19,w30,w41,w46,w52,w79],[w19,w30,w41,w46,w53,w77],[w19,w30,w42,w44,w53,w79],[w19,w30,w42,w45,w52,w79],[w19,w30,w42,w45,w53,w77],[w19,w30,w43,w44,w52,w79],[w19,w31,w40,w44,w55,w77],[w19,w31,w40,w45,w54,w77],[w19,w31,w40,w46,w53,w77],[w19,w31,w40,w47,w52,w77],[w19,w31,w41,w44,w54,w77],[w19,w31,w41,w46,w52,w77],[w19,w31,w42,w44,w53,w77],[w19,w31,w42,w45,w52,w77],[w19,w31,w43,w44,w52,w77],[w19,w33,w40,w44,w55,w73],[w19,w33,w40,w45,w54,w73],[w19,w33,w40,w46,w53,w73],[w19,w33,w40,w47,w52,w73],[w19,w33,w41,w44,w54,w73],[w19,w33,w41,w45,w54,w71],[w19,w33,w41,w46,w52,w73],[w19,w33,w41,w46,w53,w71],[w19,w33,w42,w44,w53,w73],[w19,w33,w42,w45,w52,w73]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_122 : t5_122.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_123 : BankTree := .block [[w19,w33,w42,w45,w53,w71],[w19,w33,w43,w44,w52,w73],[w19,w34,w40,w44,w55,w71],[w19,w34,w40,w45,w54,w71],[w19,w34,w40,w46,w53,w71],[w19,w34,w40,w47,w52,w71],[w19,w34,w41,w44,w54,w71],[w19,w34,w41,w46,w52,w71],[w19,w34,w42,w44,w53,w71],[w19,w34,w42,w45,w52,w71],[w19,w34,w43,w44,w52,w71],[w19,w38,w40,w44,w55,w67],[w19,w38,w40,w45,w54,w67],[w19,w38,w40,w46,w53,w67],[w19,w38,w40,w47,w52,w67],[w19,w38,w41,w44,w54,w67],[w19,w38,w41,w45,w54,w65],[w19,w38,w41,w46,w52,w67],[w19,w38,w41,w46,w53,w65],[w19,w38,w42,w44,w53,w67],[w19,w38,w42,w45,w52,w67],[w19,w38,w42,w45,w53,w65],[w19,w38,w43,w44,w52,w67],[w19,w39,w40,w44,w55,w65],[w19,w39,w40,w45,w54,w65],[w19,w39,w40,w46,w53,w65],[w19,w39,w40,w47,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_123 : t5_123.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_121 : BankTree := .fork [w19,w33,w42,w45,w53,w71] t5_122 t5_123
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_121 : t5_121.rows.all (refuses 4 t4_0)=true := by simp only [t5_121,BankTree.rows,List.all_append,ok_t5_122,ok_t5_123,Bool.true_and]
noncomputable def t5_125 : BankTree := .block [[w19,w39,w41,w44,w54,w65],[w19,w39,w41,w46,w52,w65],[w19,w39,w42,w44,w53,w65],[w19,w39,w42,w45,w52,w65],[w19,w39,w43,w44,w52,w65],[w20,w27,w40,w44,w55,w87],[w20,w27,w40,w45,w54,w87],[w20,w27,w40,w46,w53,w87],[w20,w27,w40,w47,w52,w87],[w20,w27,w41,w44,w54,w87],[w20,w27,w41,w46,w52,w87],[w20,w27,w42,w44,w53,w87],[w20,w27,w42,w45,w52,w87],[w20,w27,w43,w44,w52,w87],[w20,w28,w40,w44,w54,w87],[w20,w28,w40,w46,w52,w87],[w20,w28,w42,w44,w52,w87],[w20,w30,w40,w44,w55,w77],[w20,w30,w40,w45,w54,w77],[w20,w30,w40,w46,w53,w77],[w20,w30,w40,w47,w52,w77],[w20,w30,w41,w44,w54,w77],[w20,w30,w41,w46,w52,w77],[w20,w30,w42,w44,w53,w77],[w20,w30,w42,w45,w52,w77],[w20,w30,w43,w44,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_125 : t5_125.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_126 : BankTree := .block [[w20,w31,w40,w44,w54,w77],[w20,w31,w40,w46,w52,w77],[w20,w31,w42,w44,w52,w77],[w20,w33,w40,w44,w55,w71],[w20,w33,w40,w45,w54,w71],[w20,w33,w40,w46,w53,w71],[w20,w33,w40,w47,w52,w71],[w20,w33,w41,w44,w54,w71],[w20,w33,w41,w46,w52,w71],[w20,w33,w42,w44,w53,w71],[w20,w33,w42,w45,w52,w71],[w20,w33,w43,w44,w52,w71],[w20,w34,w40,w44,w54,w71],[w20,w34,w40,w46,w52,w71],[w20,w34,w42,w44,w52,w71],[w20,w38,w40,w44,w55,w65],[w20,w38,w40,w45,w54,w65],[w20,w38,w40,w46,w53,w65],[w20,w38,w40,w47,w52,w65],[w20,w38,w41,w44,w54,w65],[w20,w38,w41,w46,w52,w65],[w20,w38,w42,w44,w53,w65],[w20,w38,w42,w45,w52,w65],[w20,w38,w43,w44,w52,w65],[w20,w39,w40,w44,w54,w65],[w20,w39,w40,w46,w52,w65],[w20,w39,w42,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_126 : t5_126.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_124 : BankTree := .fork [w20,w31,w40,w44,w54,w77] t5_125 t5_126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_124 : t5_124.rows.all (refuses 4 t4_0)=true := by simp only [t5_124,BankTree.rows,List.all_append,ok_t5_125,ok_t5_126,Bool.true_and]
noncomputable def t5_120 : BankTree := .fork [w19,w39,w41,w44,w54,w65] t5_121 t5_124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_120 : t5_120.rows.all (refuses 4 t4_0)=true := by simp only [t5_120,BankTree.rows,List.all_append,ok_t5_121,ok_t5_124,Bool.true_and]
noncomputable def t5_112 : BankTree := .fork [w19,w30,w41,w45,w54,w77] t5_113 t5_120
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_112 : t5_112.rows.all (refuses 4 t4_0)=true := by simp only [t5_112,BankTree.rows,List.all_append,ok_t5_113,ok_t5_120,Bool.true_and]
noncomputable def t5_96 : BankTree := .fork [w16,w19,w39,w44,w57,w65] t5_97 t5_112
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_96 : t5_96.rows.all (refuses 4 t4_0)=true := by simp only [t5_96,BankTree.rows,List.all_append,ok_t5_97,ok_t5_112,Bool.true_and]
noncomputable def t5_64 : BankTree := .fork [w12,w16,w19,w27,w67,w93] t5_65 t5_96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_64 : t5_64.rows.all (refuses 4 t4_0)=true := by simp only [t5_64,BankTree.rows,List.all_append,ok_t5_65,ok_t5_96,Bool.true_and]
noncomputable def t5_0 : BankTree := .fork [w0,w27,w48,w54,w87,w97] t5_1 t5_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_0 : t5_0.rows.all (refuses 4 t4_0)=true := by simp only [t5_0,BankTree.rows,List.all_append,ok_t5_1,ok_t5_64,Bool.true_and]
theorem safe5 : Safe 5 t5_0 := certify 4 t4_0 t5_0 safe4 ok_t5_0
noncomputable def t6_6 : BankTree := .block [[w0,w1,w6,w16,w27,w91,w97],[w0,w1,w6,w19,w27,w65,w94],[w0,w1,w6,w27,w40,w62,w97],[w0,w1,w6,w27,w42,w60,w97],[w0,w1,w6,w27,w44,w58,w97],[w0,w1,w6,w27,w46,w56,w97],[w0,w1,w6,w27,w48,w54,w97],[w0,w1,w6,w27,w50,w52,w97],[w0,w1,w16,w19,w27,w77,w91],[w0,w1,w16,w19,w33,w65,w91],[w0,w1,w19,w27,w40,w62,w77],[w0,w1,w19,w27,w42,w60,w77],[w0,w1,w19,w27,w44,w58,w77],[w0,w1,w19,w27,w46,w56,w77],[w0,w1,w19,w27,w48,w54,w77],[w0,w1,w19,w27,w50,w52,w77],[w0,w1,w19,w33,w40,w62,w65],[w0,w1,w19,w33,w42,w60,w65],[w0,w1,w19,w33,w44,w58,w65],[w0,w1,w19,w33,w46,w56,w65],[w0,w1,w19,w33,w48,w54,w65],[w0,w1,w19,w33,w50,w52,w65],[w0,w2,w5,w16,w27,w91,w97],[w0,w2,w5,w19,w27,w65,w94],[w0,w2,w5,w27,w40,w62,w97],[w0,w2,w5,w27,w42,w60,w97],[w0,w2,w5,w27,w44,w58,w97],[w0,w2,w5,w27,w46,w56,w97],[w0,w2,w5,w27,w48,w54,w97],[w0,w2,w5,w27,w50,w52,w97],[w0,w2,w6,w16,w19,w27,w90],[w0,w2,w6,w16,w19,w91,w108],[w0,w2,w6,w16,w27,w91,w96],[w0,w2,w6,w16,w27,w91,w97],[w0,w2,w6,w16,w27,w91,w98],[w0,w2,w6,w16,w27,w93,w97],[w0,w2,w6,w16,w27,w94,w97],[w0,w2,w6,w16,w28,w91,w97],[w0,w2,w6,w18,w27,w91,w97],[w0,w2,w6,w19,w27,w64,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_6 : t6_6.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_7 : BankTree := .block [[w0,w2,w6,w19,w27,w65,w94],[w0,w2,w6,w19,w27,w65,w95],[w0,w2,w6,w19,w27,w67,w94],[w0,w2,w6,w19,w27,w71,w94],[w0,w2,w6,w19,w27,w77,w94],[w0,w2,w6,w19,w27,w94,w97],[w0,w2,w6,w19,w27,w94,w109],[w0,w2,w6,w19,w28,w65,w94],[w0,w2,w6,w19,w30,w65,w94],[w0,w2,w6,w19,w33,w65,w94],[w0,w2,w6,w20,w27,w65,w94],[w0,w2,w6,w27,w40,w62,w97],[w0,w2,w6,w27,w40,w62,w98],[w0,w2,w6,w27,w40,w63,w97],[w0,w2,w6,w27,w40,w94,w97],[w0,w2,w6,w27,w41,w62,w97],[w0,w2,w6,w27,w42,w60,w98],[w0,w2,w6,w27,w42,w61,w97],[w0,w2,w6,w27,w42,w62,w97],[w0,w2,w6,w27,w42,w91,w97],[w0,w2,w6,w27,w42,w94,w97],[w0,w2,w6,w27,w43,w60,w97],[w0,w2,w6,w27,w44,w58,w97],[w0,w2,w6,w27,w44,w58,w98],[w0,w2,w6,w27,w44,w59,w97],[w0,w2,w6,w27,w44,w94,w97],[w0,w2,w6,w27,w45,w58,w97],[w0,w2,w6,w27,w46,w56,w98],[w0,w2,w6,w27,w46,w57,w97],[w0,w2,w6,w27,w46,w58,w97],[w0,w2,w6,w27,w46,w91,w97],[w0,w2,w6,w27,w46,w94,w97],[w0,w2,w6,w27,w47,w56,w97],[w0,w2,w6,w27,w48,w54,w98],[w0,w2,w6,w27,w48,w55,w97],[w0,w2,w6,w27,w48,w58,w97],[w0,w2,w6,w27,w48,w62,w97],[w0,w2,w6,w27,w48,w94,w97],[w0,w2,w6,w27,w49,w54,w97],[w0,w2,w6,w27,w50,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_7 : t6_7.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_5 : BankTree := .fork [w0,w2,w6,w19,w27,w65,w94] t6_6 t6_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_5 : t6_5.rows.all (refuses 5 t5_0)=true := by simp only [t6_5,BankTree.rows,List.all_append,ok_t6_6,ok_t6_7,Bool.true_and]
noncomputable def t6_9 : BankTree := .block [[w0,w2,w6,w27,w50,w52,w98],[w0,w2,w6,w27,w50,w53,w97],[w0,w2,w6,w27,w50,w54,w97],[w0,w2,w6,w27,w50,w56,w97],[w0,w2,w6,w27,w50,w58,w97],[w0,w2,w6,w27,w50,w60,w97],[w0,w2,w6,w27,w50,w62,w97],[w0,w2,w6,w27,w50,w91,w97],[w0,w2,w6,w27,w50,w94,w97],[w0,w2,w6,w27,w51,w52,w97],[w0,w2,w6,w27,w52,w94,w97],[w0,w2,w6,w27,w54,w91,w97],[w0,w2,w6,w27,w54,w94,w97],[w0,w2,w6,w27,w56,w62,w97],[w0,w2,w6,w27,w56,w94,w97],[w0,w2,w6,w27,w58,w60,w97],[w0,w2,w6,w27,w58,w62,w97],[w0,w2,w6,w27,w58,w91,w97],[w0,w2,w6,w27,w58,w94,w97],[w0,w2,w6,w27,w60,w94,w97],[w0,w2,w6,w27,w62,w91,w97],[w0,w2,w6,w27,w62,w94,w97],[w0,w2,w6,w27,w65,w94,w97],[w0,w2,w6,w27,w91,w94,w97],[w0,w2,w6,w27,w94,w97],[w0,w2,w6,w28,w40,w62,w97],[w0,w2,w6,w28,w42,w60,w97],[w0,w2,w6,w28,w44,w58,w97],[w0,w2,w6,w28,w46,w56,w97],[w0,w2,w6,w28,w48,w54,w97],[w0,w2,w6,w28,w50,w52,w97],[w0,w2,w8,w16,w27,w91,w97],[w0,w2,w8,w19,w27,w65,w94],[w0,w2,w8,w27,w40,w62,w97],[w0,w2,w8,w27,w42,w60,w97],[w0,w2,w8,w27,w44,w58,w97],[w0,w2,w8,w27,w46,w56,w97],[w0,w2,w8,w27,w48,w54,w97],[w0,w2,w8,w27,w50,w52,w97],[w0,w2,w12,w16,w27,w91,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_9 : t6_9.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_10 : BankTree := .block [[w0,w2,w12,w19,w27,w65,w94],[w0,w2,w12,w27,w40,w62,w97],[w0,w2,w12,w27,w42,w60,w97],[w0,w2,w12,w27,w44,w58,w97],[w0,w2,w12,w27,w46,w56,w97],[w0,w2,w12,w27,w48,w54,w97],[w0,w2,w12,w27,w50,w52,w97],[w0,w2,w16,w19,w27,w75,w91],[w0,w2,w16,w19,w27,w76,w91],[w0,w2,w16,w19,w27,w77,w91],[w0,w2,w16,w19,w27,w77,w93],[w0,w2,w16,w19,w27,w77,w94],[w0,w2,w16,w19,w27,w79,w91],[w0,w2,w16,w19,w27,w87,w91],[w0,w2,w16,w19,w27,w91,w104],[w0,w2,w16,w19,w27,w91,w115],[w0,w2,w16,w19,w28,w77,w91],[w0,w2,w16,w19,w30,w77,w91],[w0,w2,w16,w19,w32,w65,w91],[w0,w2,w16,w19,w33,w64,w91],[w0,w2,w16,w19,w33,w65,w91],[w0,w2,w16,w19,w33,w65,w93],[w0,w2,w16,w19,w33,w65,w94],[w0,w2,w16,w19,w33,w67,w91],[w0,w2,w16,w19,w33,w71,w91],[w0,w2,w16,w19,w33,w77,w91],[w0,w2,w16,w19,w33,w91,w97],[w0,w2,w16,w19,w33,w91,w109],[w0,w2,w16,w19,w33,w91,w115],[w0,w2,w16,w19,w34,w65,w91],[w0,w2,w16,w19,w38,w65,w91],[w0,w2,w16,w20,w27,w77,w91],[w0,w2,w16,w20,w33,w65,w91],[w0,w2,w16,w23,w27,w65,w91],[w0,w2,w16,w24,w27,w91,w97],[w0,w2,w16,w27,w33,w91,w97],[w0,w2,w16,w27,w40,w60,w103],[w0,w2,w16,w27,w44,w56,w103],[w0,w2,w16,w27,w48,w52,w103],[w0,w2,w16,w27,w77,w91,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_10 : t6_10.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_8 : BankTree := .fork [w0,w2,w12,w19,w27,w65,w94] t6_9 t6_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_8 : t6_8.rows.all (refuses 5 t5_0)=true := by simp only [t6_8,BankTree.rows,List.all_append,ok_t6_9,ok_t6_10,Bool.true_and]
noncomputable def t6_4 : BankTree := .fork [w0,w2,w6,w27,w50,w52,w98] t6_5 t6_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_4 : t6_4.rows.all (refuses 5 t5_0)=true := by simp only [t6_4,BankTree.rows,List.all_append,ok_t6_5,ok_t6_8,Bool.true_and]
noncomputable def t6_13 : BankTree := .block [[w0,w2,w16,w27,w91,w97,w104],[w0,w2,w16,w32,w40,w60,w97],[w0,w2,w16,w32,w44,w56,w97],[w0,w2,w16,w32,w48,w52,w97],[w0,w2,w18,w19,w27,w77,w91],[w0,w2,w18,w19,w33,w65,w91],[w0,w2,w19,w24,w27,w65,w94],[w0,w2,w19,w27,w33,w65,w94],[w0,w2,w19,w27,w40,w62,w75],[w0,w2,w19,w27,w40,w62,w77],[w0,w2,w19,w27,w40,w62,w79],[w0,w2,w19,w27,w40,w62,w87],[w0,w2,w19,w27,w40,w62,w104],[w0,w2,w19,w27,w40,w62,w115],[w0,w2,w19,w27,w40,w63,w77],[w0,w2,w19,w27,w40,w77,w94],[w0,w2,w19,w27,w41,w62,w77],[w0,w2,w19,w27,w42,w60,w75],[w0,w2,w19,w27,w42,w60,w79],[w0,w2,w19,w27,w42,w60,w87],[w0,w2,w19,w27,w42,w60,w104],[w0,w2,w19,w27,w42,w60,w115],[w0,w2,w19,w27,w42,w61,w77],[w0,w2,w19,w27,w42,w62,w77],[w0,w2,w19,w27,w42,w77,w91],[w0,w2,w19,w27,w42,w77,w94],[w0,w2,w19,w27,w43,w60,w77],[w0,w2,w19,w27,w44,w58,w75],[w0,w2,w19,w27,w44,w58,w77],[w0,w2,w19,w27,w44,w58,w79],[w0,w2,w19,w27,w44,w58,w87],[w0,w2,w19,w27,w44,w58,w104],[w0,w2,w19,w27,w44,w58,w115],[w0,w2,w19,w27,w44,w59,w77],[w0,w2,w19,w27,w44,w77,w94],[w0,w2,w19,w27,w45,w58,w77],[w0,w2,w19,w27,w46,w56,w75],[w0,w2,w19,w27,w46,w56,w79],[w0,w2,w19,w27,w46,w56,w87],[w0,w2,w19,w27,w46,w56,w104]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_13 : t6_13.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_14 : BankTree := .block [[w0,w2,w19,w27,w46,w56,w115],[w0,w2,w19,w27,w46,w57,w77],[w0,w2,w19,w27,w46,w58,w77],[w0,w2,w19,w27,w46,w77,w91],[w0,w2,w19,w27,w46,w77,w94],[w0,w2,w19,w27,w47,w56,w77],[w0,w2,w19,w27,w48,w54,w75],[w0,w2,w19,w27,w48,w54,w79],[w0,w2,w19,w27,w48,w54,w87],[w0,w2,w19,w27,w48,w54,w104],[w0,w2,w19,w27,w48,w54,w115],[w0,w2,w19,w27,w48,w55,w77],[w0,w2,w19,w27,w48,w58,w77],[w0,w2,w19,w27,w48,w62,w77],[w0,w2,w19,w27,w48,w77,w94],[w0,w2,w19,w27,w49,w54,w77],[w0,w2,w19,w27,w50,w52,w75],[w0,w2,w19,w27,w50,w52,w77],[w0,w2,w19,w27,w50,w52,w79],[w0,w2,w19,w27,w50,w52,w87],[w0,w2,w19,w27,w50,w52,w104],[w0,w2,w19,w27,w50,w52,w115],[w0,w2,w19,w27,w50,w53,w77],[w0,w2,w19,w27,w50,w54,w77],[w0,w2,w19,w27,w50,w56,w77],[w0,w2,w19,w27,w50,w58,w77],[w0,w2,w19,w27,w50,w60,w77],[w0,w2,w19,w27,w50,w62,w77],[w0,w2,w19,w27,w50,w77,w91],[w0,w2,w19,w27,w50,w77,w94],[w0,w2,w19,w27,w51,w52,w77],[w0,w2,w19,w27,w52,w77,w94],[w0,w2,w19,w27,w54,w77,w91],[w0,w2,w19,w27,w54,w77,w94],[w0,w2,w19,w27,w56,w62,w77],[w0,w2,w19,w27,w56,w77,w94],[w0,w2,w19,w27,w58,w60,w77],[w0,w2,w19,w27,w58,w62,w77],[w0,w2,w19,w27,w58,w77,w91],[w0,w2,w19,w27,w58,w77,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_14 : t6_14.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_12 : BankTree := .fork [w0,w2,w19,w27,w46,w56,w115] t6_13 t6_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_12 : t6_12.rows.all (refuses 5 t5_0)=true := by simp only [t6_12,BankTree.rows,List.all_append,ok_t6_13,ok_t6_14,Bool.true_and]
noncomputable def t6_16 : BankTree := .block [[w0,w2,w19,w27,w60,w77,w94],[w0,w2,w19,w27,w62,w77,w91],[w0,w2,w19,w27,w62,w77,w94],[w0,w2,w19,w27,w65,w77,w94],[w0,w2,w19,w27,w77,w91,w94],[w0,w2,w19,w27,w77,w94],[w0,w2,w19,w28,w40,w62,w77],[w0,w2,w19,w28,w42,w60,w77],[w0,w2,w19,w28,w44,w58,w77],[w0,w2,w19,w28,w46,w56,w77],[w0,w2,w19,w28,w48,w54,w77],[w0,w2,w19,w28,w50,w52,w77],[w0,w2,w19,w30,w40,w62,w77],[w0,w2,w19,w30,w42,w60,w77],[w0,w2,w19,w30,w44,w58,w77],[w0,w2,w19,w30,w46,w56,w77],[w0,w2,w19,w30,w48,w54,w77],[w0,w2,w19,w30,w50,w52,w77],[w0,w2,w19,w32,w40,w62,w65],[w0,w2,w19,w32,w42,w60,w65],[w0,w2,w19,w32,w44,w58,w65],[w0,w2,w19,w32,w46,w56,w65],[w0,w2,w19,w32,w48,w54,w65],[w0,w2,w19,w32,w50,w52,w65],[w0,w2,w19,w33,w40,w62,w65],[w0,w2,w19,w33,w40,w62,w67],[w0,w2,w19,w33,w40,w62,w71],[w0,w2,w19,w33,w40,w62,w77],[w0,w2,w19,w33,w40,w62,w97],[w0,w2,w19,w33,w40,w62,w109],[w0,w2,w19,w33,w40,w62,w115],[w0,w2,w19,w33,w40,w63,w65],[w0,w2,w19,w33,w40,w65,w94],[w0,w2,w19,w33,w41,w62,w65],[w0,w2,w19,w33,w42,w60,w67],[w0,w2,w19,w33,w42,w60,w71],[w0,w2,w19,w33,w42,w60,w77],[w0,w2,w19,w33,w42,w60,w97],[w0,w2,w19,w33,w42,w60,w109],[w0,w2,w19,w33,w42,w60,w115]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_16 : t6_16.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_17 : BankTree := .block [[w0,w2,w19,w33,w42,w61,w65],[w0,w2,w19,w33,w42,w62,w65],[w0,w2,w19,w33,w42,w65,w91],[w0,w2,w19,w33,w42,w65,w94],[w0,w2,w19,w33,w43,w60,w65],[w0,w2,w19,w33,w44,w58,w65],[w0,w2,w19,w33,w44,w58,w67],[w0,w2,w19,w33,w44,w58,w71],[w0,w2,w19,w33,w44,w58,w77],[w0,w2,w19,w33,w44,w58,w97],[w0,w2,w19,w33,w44,w58,w109],[w0,w2,w19,w33,w44,w58,w115],[w0,w2,w19,w33,w44,w59,w65],[w0,w2,w19,w33,w44,w65,w94],[w0,w2,w19,w33,w45,w58,w65],[w0,w2,w19,w33,w46,w56,w67],[w0,w2,w19,w33,w46,w56,w71],[w0,w2,w19,w33,w46,w56,w77],[w0,w2,w19,w33,w46,w56,w97],[w0,w2,w19,w33,w46,w56,w109],[w0,w2,w19,w33,w46,w56,w115],[w0,w2,w19,w33,w46,w57,w65],[w0,w2,w19,w33,w46,w58,w65],[w0,w2,w19,w33,w46,w65,w91],[w0,w2,w19,w33,w46,w65,w94],[w0,w2,w19,w33,w47,w56,w65],[w0,w2,w19,w33,w48,w54,w67],[w0,w2,w19,w33,w48,w54,w71],[w0,w2,w19,w33,w48,w54,w77],[w0,w2,w19,w33,w48,w54,w97],[w0,w2,w19,w33,w48,w54,w109],[w0,w2,w19,w33,w48,w54,w115],[w0,w2,w19,w33,w48,w55,w65],[w0,w2,w19,w33,w48,w58,w65],[w0,w2,w19,w33,w48,w62,w65],[w0,w2,w19,w33,w48,w65,w94],[w0,w2,w19,w33,w49,w54,w65],[w0,w2,w19,w33,w50,w52,w65],[w0,w2,w19,w33,w50,w52,w67],[w0,w2,w19,w33,w50,w52,w71],[w0,w2,w19,w33,w50,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_17 : t6_17.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_15 : BankTree := .fork [w0,w2,w19,w33,w42,w61,w65] t6_16 t6_17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_15 : t6_15.rows.all (refuses 5 t5_0)=true := by simp only [t6_15,BankTree.rows,List.all_append,ok_t6_16,ok_t6_17,Bool.true_and]
noncomputable def t6_11 : BankTree := .fork [w0,w2,w19,w27,w60,w77,w94] t6_12 t6_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_11 : t6_11.rows.all (refuses 5 t5_0)=true := by simp only [t6_11,BankTree.rows,List.all_append,ok_t6_12,ok_t6_15,Bool.true_and]
noncomputable def t6_3 : BankTree := .fork [w0,w2,w16,w27,w91,w97,w104] t6_4 t6_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_3 : t6_3.rows.all (refuses 5 t5_0)=true := by simp only [t6_3,BankTree.rows,List.all_append,ok_t6_4,ok_t6_11,Bool.true_and]
noncomputable def t6_21 : BankTree := .block [[w0,w2,w19,w33,w50,w52,w97],[w0,w2,w19,w33,w50,w52,w109],[w0,w2,w19,w33,w50,w52,w115],[w0,w2,w19,w33,w50,w53,w65],[w0,w2,w19,w33,w50,w54,w65],[w0,w2,w19,w33,w50,w56,w65],[w0,w2,w19,w33,w50,w58,w65],[w0,w2,w19,w33,w50,w60,w65],[w0,w2,w19,w33,w50,w62,w65],[w0,w2,w19,w33,w50,w65,w91],[w0,w2,w19,w33,w50,w65,w94],[w0,w2,w19,w33,w51,w52,w65],[w0,w2,w19,w33,w52,w65,w94],[w0,w2,w19,w33,w54,w65,w91],[w0,w2,w19,w33,w54,w65,w94],[w0,w2,w19,w33,w56,w62,w65],[w0,w2,w19,w33,w56,w65,w94],[w0,w2,w19,w33,w58,w60,w65],[w0,w2,w19,w33,w58,w62,w65],[w0,w2,w19,w33,w58,w65,w91],[w0,w2,w19,w33,w58,w65,w94],[w0,w2,w19,w33,w60,w65,w94],[w0,w2,w19,w33,w62,w65,w91],[w0,w2,w19,w33,w62,w65,w94],[w0,w2,w19,w33,w65,w91,w94],[w0,w2,w19,w33,w65,w94],[w0,w2,w19,w34,w40,w62,w65],[w0,w2,w19,w34,w42,w60,w65],[w0,w2,w19,w34,w44,w58,w65],[w0,w2,w19,w34,w46,w56,w65],[w0,w2,w19,w34,w48,w54,w65],[w0,w2,w19,w34,w50,w52,w65],[w0,w2,w19,w38,w40,w62,w65],[w0,w2,w19,w38,w42,w60,w65],[w0,w2,w19,w38,w44,w58,w65],[w0,w2,w19,w38,w46,w56,w65],[w0,w2,w19,w38,w48,w54,w65],[w0,w2,w19,w38,w50,w52,w65],[w0,w2,w20,w27,w40,w62,w77],[w0,w2,w20,w27,w42,w60,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_21 : t6_21.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_22 : BankTree := .block [[w0,w2,w20,w27,w44,w58,w77],[w0,w2,w20,w27,w46,w56,w77],[w0,w2,w20,w27,w48,w54,w77],[w0,w2,w20,w27,w50,w52,w77],[w0,w2,w20,w33,w40,w62,w65],[w0,w2,w20,w33,w42,w60,w65],[w0,w2,w20,w33,w44,w58,w65],[w0,w2,w20,w33,w46,w56,w65],[w0,w2,w20,w33,w48,w54,w65],[w0,w2,w20,w33,w50,w52,w65],[w0,w2,w23,w27,w40,w62,w65],[w0,w2,w23,w27,w42,w60,w65],[w0,w2,w23,w27,w44,w58,w65],[w0,w2,w23,w27,w46,w56,w65],[w0,w2,w23,w27,w48,w54,w65],[w0,w2,w23,w27,w50,w52,w65],[w0,w2,w24,w27,w40,w62,w97],[w0,w2,w24,w27,w42,w60,w97],[w0,w2,w24,w27,w44,w58,w97],[w0,w2,w24,w27,w46,w56,w97],[w0,w2,w24,w27,w48,w54,w97],[w0,w2,w24,w27,w50,w52,w97],[w0,w2,w27,w33,w40,w62,w97],[w0,w2,w27,w33,w42,w60,w97],[w0,w2,w27,w33,w44,w58,w97],[w0,w2,w27,w33,w46,w56,w97],[w0,w2,w27,w33,w48,w54,w97],[w0,w2,w27,w33,w50,w52,w97],[w0,w2,w27,w40,w44,w54,w103],[w0,w2,w27,w40,w46,w52,w103],[w0,w2,w27,w40,w62,w77,w97],[w0,w2,w27,w40,w62,w97,w104],[w0,w2,w27,w42,w44,w52,w103],[w0,w2,w27,w42,w60,w77,w97],[w0,w2,w27,w42,w60,w97,w104],[w0,w2,w27,w44,w58,w77,w97],[w0,w2,w27,w44,w58,w97,w104],[w0,w2,w27,w46,w56,w77,w97],[w0,w2,w27,w46,w56,w97,w104],[w0,w2,w27,w48,w54,w77,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_22 : t6_22.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_20 : BankTree := .fork [w0,w2,w20,w27,w44,w58,w77] t6_21 t6_22
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_20 : t6_20.rows.all (refuses 5 t5_0)=true := by simp only [t6_20,BankTree.rows,List.all_append,ok_t6_21,ok_t6_22,Bool.true_and]
noncomputable def t6_24 : BankTree := .block [[w0,w2,w27,w48,w54,w97,w104],[w0,w2,w27,w50,w52,w77,w97],[w0,w2,w27,w50,w52,w97,w104],[w0,w2,w32,w40,w44,w54,w97],[w0,w2,w32,w40,w46,w52,w97],[w0,w2,w32,w42,w44,w52,w97],[w0,w4,w6,w16,w27,w91,w97],[w0,w4,w6,w19,w27,w65,w94],[w0,w4,w6,w27,w40,w62,w97],[w0,w4,w6,w27,w42,w60,w97],[w0,w4,w6,w27,w44,w58,w97],[w0,w4,w6,w27,w46,w56,w97],[w0,w4,w6,w27,w48,w54,w97],[w0,w4,w6,w27,w50,w52,w97],[w0,w4,w16,w19,w27,w77,w91],[w0,w4,w16,w19,w33,w65,w91],[w0,w4,w19,w27,w40,w62,w77],[w0,w4,w19,w27,w42,w60,w77],[w0,w4,w19,w27,w44,w58,w77],[w0,w4,w19,w27,w46,w56,w77],[w0,w4,w19,w27,w48,w54,w77],[w0,w4,w19,w27,w50,w52,w77],[w0,w4,w19,w33,w40,w62,w65],[w0,w4,w19,w33,w42,w60,w65],[w0,w4,w19,w33,w44,w58,w65],[w0,w4,w19,w33,w46,w56,w65],[w0,w4,w19,w33,w48,w54,w65],[w0,w4,w19,w33,w50,w52,w65],[w0,w5,w16,w19,w27,w71,w91],[w0,w5,w16,w19,w30,w65,w91],[w0,w5,w19,w27,w40,w62,w71],[w0,w5,w19,w27,w42,w60,w71],[w0,w5,w19,w27,w44,w58,w71],[w0,w5,w19,w27,w46,w56,w71],[w0,w5,w19,w27,w48,w54,w71],[w0,w5,w19,w27,w50,w52,w71],[w0,w5,w19,w30,w40,w62,w65],[w0,w5,w19,w30,w42,w60,w65],[w0,w5,w19,w30,w44,w58,w65],[w0,w5,w19,w30,w46,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_24 : t6_24.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_25 : BankTree := .block [[w0,w5,w19,w30,w48,w54,w65],[w0,w5,w19,w30,w50,w52,w65],[w0,w6,w12,w16,w27,w91,w97],[w0,w6,w12,w19,w27,w65,w94],[w0,w6,w12,w27,w40,w62,w97],[w0,w6,w12,w27,w42,w60,w97],[w0,w6,w12,w27,w44,w58,w97],[w0,w6,w12,w27,w46,w56,w97],[w0,w6,w12,w27,w48,w54,w97],[w0,w6,w12,w27,w50,w52,w97],[w0,w6,w16,w19,w27,w69,w91],[w0,w6,w16,w19,w27,w70,w91],[w0,w6,w16,w19,w27,w71,w91],[w0,w6,w16,w19,w27,w71,w93],[w0,w6,w16,w19,w27,w71,w94],[w0,w6,w16,w19,w27,w73,w91],[w0,w6,w16,w19,w27,w87,w91],[w0,w6,w16,w19,w27,w91,w101],[w0,w6,w16,w19,w27,w91,w112],[w0,w6,w16,w19,w28,w71,w91],[w0,w6,w16,w19,w29,w65,w91],[w0,w6,w16,w19,w30,w64,w91],[w0,w6,w16,w19,w30,w65,w91],[w0,w6,w16,w19,w30,w65,w93],[w0,w6,w16,w19,w30,w65,w94],[w0,w6,w16,w19,w30,w67,w91],[w0,w6,w16,w19,w30,w71,w91],[w0,w6,w16,w19,w30,w77,w91],[w0,w6,w16,w19,w30,w91,w97],[w0,w6,w16,w19,w30,w91,w109],[w0,w6,w16,w19,w30,w91,w112],[w0,w6,w16,w19,w31,w65,w91],[w0,w6,w16,w19,w33,w71,w91],[w0,w6,w16,w19,w38,w65,w91],[w0,w6,w16,w20,w27,w71,w91],[w0,w6,w16,w20,w30,w65,w91],[w0,w6,w16,w21,w27,w65,w91],[w0,w6,w16,w22,w27,w91,w97],[w0,w6,w16,w27,w30,w91,w97],[w0,w6,w16,w27,w40,w60,w100],[w0,w6,w16,w27,w44,w56,w100]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_25 : t6_25.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_23 : BankTree := .fork [w0,w5,w19,w30,w48,w54,w65] t6_24 t6_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_23 : t6_23.rows.all (refuses 5 t5_0)=true := by simp only [t6_23,BankTree.rows,List.all_append,ok_t6_24,ok_t6_25,Bool.true_and]
noncomputable def t6_19 : BankTree := .fork [w0,w2,w27,w48,w54,w97,w104] t6_20 t6_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_19 : t6_19.rows.all (refuses 5 t5_0)=true := by simp only [t6_19,BankTree.rows,List.all_append,ok_t6_20,ok_t6_23,Bool.true_and]
noncomputable def t6_28 : BankTree := .block [[w0,w6,w16,w27,w48,w52,w100],[w0,w6,w16,w27,w71,w91,w97],[w0,w6,w16,w27,w91,w97,w101],[w0,w6,w16,w29,w40,w60,w97],[w0,w6,w16,w29,w44,w56,w97],[w0,w6,w16,w29,w48,w52,w97],[w0,w6,w18,w19,w27,w71,w91],[w0,w6,w18,w19,w30,w65,w91],[w0,w6,w19,w22,w27,w65,w94],[w0,w6,w19,w27,w30,w65,w94],[w0,w6,w19,w27,w40,w62,w69],[w0,w6,w19,w27,w40,w62,w71],[w0,w6,w19,w27,w40,w62,w73],[w0,w6,w19,w27,w40,w62,w87],[w0,w6,w19,w27,w40,w62,w101],[w0,w6,w19,w27,w40,w62,w112],[w0,w6,w19,w27,w40,w63,w71],[w0,w6,w19,w27,w40,w71,w94],[w0,w6,w19,w27,w41,w62,w71],[w0,w6,w19,w27,w42,w60,w69],[w0,w6,w19,w27,w42,w60,w73],[w0,w6,w19,w27,w42,w60,w87],[w0,w6,w19,w27,w42,w60,w101],[w0,w6,w19,w27,w42,w60,w112],[w0,w6,w19,w27,w42,w61,w71],[w0,w6,w19,w27,w42,w62,w71],[w0,w6,w19,w27,w42,w71,w91],[w0,w6,w19,w27,w42,w71,w94],[w0,w6,w19,w27,w43,w60,w71],[w0,w6,w19,w27,w44,w58,w69],[w0,w6,w19,w27,w44,w58,w71],[w0,w6,w19,w27,w44,w58,w73],[w0,w6,w19,w27,w44,w58,w87],[w0,w6,w19,w27,w44,w58,w101],[w0,w6,w19,w27,w44,w58,w112],[w0,w6,w19,w27,w44,w59,w71],[w0,w6,w19,w27,w44,w71,w94],[w0,w6,w19,w27,w45,w58,w71],[w0,w6,w19,w27,w46,w56,w69],[w0,w6,w19,w27,w46,w56,w73]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_28 : t6_28.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_29 : BankTree := .block [[w0,w6,w19,w27,w46,w56,w87],[w0,w6,w19,w27,w46,w56,w101],[w0,w6,w19,w27,w46,w56,w112],[w0,w6,w19,w27,w46,w57,w71],[w0,w6,w19,w27,w46,w58,w71],[w0,w6,w19,w27,w46,w71,w91],[w0,w6,w19,w27,w46,w71,w94],[w0,w6,w19,w27,w47,w56,w71],[w0,w6,w19,w27,w48,w54,w69],[w0,w6,w19,w27,w48,w54,w73],[w0,w6,w19,w27,w48,w54,w87],[w0,w6,w19,w27,w48,w54,w101],[w0,w6,w19,w27,w48,w54,w112],[w0,w6,w19,w27,w48,w55,w71],[w0,w6,w19,w27,w48,w58,w71],[w0,w6,w19,w27,w48,w62,w71],[w0,w6,w19,w27,w48,w71,w94],[w0,w6,w19,w27,w49,w54,w71],[w0,w6,w19,w27,w50,w52,w69],[w0,w6,w19,w27,w50,w52,w71],[w0,w6,w19,w27,w50,w52,w73],[w0,w6,w19,w27,w50,w52,w87],[w0,w6,w19,w27,w50,w52,w101],[w0,w6,w19,w27,w50,w52,w112],[w0,w6,w19,w27,w50,w53,w71],[w0,w6,w19,w27,w50,w54,w71],[w0,w6,w19,w27,w50,w56,w71],[w0,w6,w19,w27,w50,w58,w71],[w0,w6,w19,w27,w50,w60,w71],[w0,w6,w19,w27,w50,w62,w71],[w0,w6,w19,w27,w50,w71,w91],[w0,w6,w19,w27,w50,w71,w94],[w0,w6,w19,w27,w51,w52,w71],[w0,w6,w19,w27,w52,w71,w94],[w0,w6,w19,w27,w54,w71,w91],[w0,w6,w19,w27,w54,w71,w94],[w0,w6,w19,w27,w56,w62,w71],[w0,w6,w19,w27,w56,w71,w94],[w0,w6,w19,w27,w58,w60,w71],[w0,w6,w19,w27,w58,w62,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_29 : t6_29.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_27 : BankTree := .fork [w0,w6,w19,w27,w46,w56,w87] t6_28 t6_29
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_27 : t6_27.rows.all (refuses 5 t5_0)=true := by simp only [t6_27,BankTree.rows,List.all_append,ok_t6_28,ok_t6_29,Bool.true_and]
noncomputable def t6_31 : BankTree := .block [[w0,w6,w19,w27,w58,w71,w91],[w0,w6,w19,w27,w58,w71,w94],[w0,w6,w19,w27,w60,w71,w94],[w0,w6,w19,w27,w62,w71,w91],[w0,w6,w19,w27,w62,w71,w94],[w0,w6,w19,w27,w65,w71,w94],[w0,w6,w19,w27,w71,w91,w94],[w0,w6,w19,w27,w71,w94],[w0,w6,w19,w28,w40,w62,w71],[w0,w6,w19,w28,w42,w60,w71],[w0,w6,w19,w28,w44,w58,w71],[w0,w6,w19,w28,w46,w56,w71],[w0,w6,w19,w28,w48,w54,w71],[w0,w6,w19,w28,w50,w52,w71],[w0,w6,w19,w29,w40,w62,w65],[w0,w6,w19,w29,w42,w60,w65],[w0,w6,w19,w29,w44,w58,w65],[w0,w6,w19,w29,w46,w56,w65],[w0,w6,w19,w29,w48,w54,w65],[w0,w6,w19,w29,w50,w52,w65],[w0,w6,w19,w30,w40,w62,w65],[w0,w6,w19,w30,w40,w62,w67],[w0,w6,w19,w30,w40,w62,w71],[w0,w6,w19,w30,w40,w62,w77],[w0,w6,w19,w30,w40,w62,w97],[w0,w6,w19,w30,w40,w62,w109],[w0,w6,w19,w30,w40,w62,w112],[w0,w6,w19,w30,w40,w63,w65],[w0,w6,w19,w30,w40,w65,w94],[w0,w6,w19,w30,w41,w62,w65],[w0,w6,w19,w30,w42,w60,w67],[w0,w6,w19,w30,w42,w60,w71],[w0,w6,w19,w30,w42,w60,w77],[w0,w6,w19,w30,w42,w60,w97],[w0,w6,w19,w30,w42,w60,w109],[w0,w6,w19,w30,w42,w60,w112],[w0,w6,w19,w30,w42,w61,w65],[w0,w6,w19,w30,w42,w62,w65],[w0,w6,w19,w30,w42,w65,w91],[w0,w6,w19,w30,w42,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_31 : t6_31.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_32 : BankTree := .block [[w0,w6,w19,w30,w43,w60,w65],[w0,w6,w19,w30,w44,w58,w65],[w0,w6,w19,w30,w44,w58,w67],[w0,w6,w19,w30,w44,w58,w71],[w0,w6,w19,w30,w44,w58,w77],[w0,w6,w19,w30,w44,w58,w97],[w0,w6,w19,w30,w44,w58,w109],[w0,w6,w19,w30,w44,w58,w112],[w0,w6,w19,w30,w44,w59,w65],[w0,w6,w19,w30,w44,w65,w94],[w0,w6,w19,w30,w45,w58,w65],[w0,w6,w19,w30,w46,w56,w67],[w0,w6,w19,w30,w46,w56,w71],[w0,w6,w19,w30,w46,w56,w77],[w0,w6,w19,w30,w46,w56,w97],[w0,w6,w19,w30,w46,w56,w109],[w0,w6,w19,w30,w46,w56,w112],[w0,w6,w19,w30,w46,w57,w65],[w0,w6,w19,w30,w46,w58,w65],[w0,w6,w19,w30,w46,w65,w91],[w0,w6,w19,w30,w46,w65,w94],[w0,w6,w19,w30,w47,w56,w65],[w0,w6,w19,w30,w48,w54,w67],[w0,w6,w19,w30,w48,w54,w71],[w0,w6,w19,w30,w48,w54,w77],[w0,w6,w19,w30,w48,w54,w97],[w0,w6,w19,w30,w48,w54,w109],[w0,w6,w19,w30,w48,w54,w112],[w0,w6,w19,w30,w48,w55,w65],[w0,w6,w19,w30,w48,w58,w65],[w0,w6,w19,w30,w48,w62,w65],[w0,w6,w19,w30,w48,w65,w94],[w0,w6,w19,w30,w49,w54,w65],[w0,w6,w19,w30,w50,w52,w65],[w0,w6,w19,w30,w50,w52,w67],[w0,w6,w19,w30,w50,w52,w71],[w0,w6,w19,w30,w50,w52,w77],[w0,w6,w19,w30,w50,w52,w97],[w0,w6,w19,w30,w50,w52,w109],[w0,w6,w19,w30,w50,w52,w112],[w0,w6,w19,w30,w50,w53,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_32 : t6_32.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_30 : BankTree := .fork [w0,w6,w19,w30,w43,w60,w65] t6_31 t6_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_30 : t6_30.rows.all (refuses 5 t5_0)=true := by simp only [t6_30,BankTree.rows,List.all_append,ok_t6_31,ok_t6_32,Bool.true_and]
noncomputable def t6_26 : BankTree := .fork [w0,w6,w19,w27,w58,w71,w91] t6_27 t6_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_26 : t6_26.rows.all (refuses 5 t5_0)=true := by simp only [t6_26,BankTree.rows,List.all_append,ok_t6_27,ok_t6_30,Bool.true_and]
noncomputable def t6_18 : BankTree := .fork [w0,w6,w16,w27,w48,w52,w100] t6_19 t6_26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_18 : t6_18.rows.all (refuses 5 t5_0)=true := by simp only [t6_18,BankTree.rows,List.all_append,ok_t6_19,ok_t6_26,Bool.true_and]
noncomputable def t6_2 : BankTree := .fork [w0,w2,w19,w33,w50,w52,w97] t6_3 t6_18
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_2 : t6_2.rows.all (refuses 5 t5_0)=true := by simp only [t6_2,BankTree.rows,List.all_append,ok_t6_3,ok_t6_18,Bool.true_and]
noncomputable def t6_37 : BankTree := .block [[w0,w6,w19,w30,w50,w54,w65],[w0,w6,w19,w30,w50,w56,w65],[w0,w6,w19,w30,w50,w58,w65],[w0,w6,w19,w30,w50,w60,w65],[w0,w6,w19,w30,w50,w62,w65],[w0,w6,w19,w30,w50,w65,w91],[w0,w6,w19,w30,w50,w65,w94],[w0,w6,w19,w30,w51,w52,w65],[w0,w6,w19,w30,w52,w65,w94],[w0,w6,w19,w30,w54,w65,w91],[w0,w6,w19,w30,w54,w65,w94],[w0,w6,w19,w30,w56,w62,w65],[w0,w6,w19,w30,w56,w65,w94],[w0,w6,w19,w30,w58,w60,w65],[w0,w6,w19,w30,w58,w62,w65],[w0,w6,w19,w30,w58,w65,w91],[w0,w6,w19,w30,w58,w65,w94],[w0,w6,w19,w30,w60,w65,w94],[w0,w6,w19,w30,w62,w65,w91],[w0,w6,w19,w30,w62,w65,w94],[w0,w6,w19,w30,w65,w91,w94],[w0,w6,w19,w30,w65,w94],[w0,w6,w19,w31,w40,w62,w65],[w0,w6,w19,w31,w42,w60,w65],[w0,w6,w19,w31,w44,w58,w65],[w0,w6,w19,w31,w46,w56,w65],[w0,w6,w19,w31,w48,w54,w65],[w0,w6,w19,w31,w50,w52,w65],[w0,w6,w19,w33,w40,w62,w71],[w0,w6,w19,w33,w42,w60,w71],[w0,w6,w19,w33,w44,w58,w71],[w0,w6,w19,w33,w46,w56,w71],[w0,w6,w19,w33,w48,w54,w71],[w0,w6,w19,w33,w50,w52,w71],[w0,w6,w19,w38,w40,w62,w65],[w0,w6,w19,w38,w42,w60,w65],[w0,w6,w19,w38,w44,w58,w65],[w0,w6,w19,w38,w46,w56,w65],[w0,w6,w19,w38,w48,w54,w65],[w0,w6,w19,w38,w50,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_37 : t6_37.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_38 : BankTree := .block [[w0,w6,w20,w27,w40,w62,w71],[w0,w6,w20,w27,w42,w60,w71],[w0,w6,w20,w27,w44,w58,w71],[w0,w6,w20,w27,w46,w56,w71],[w0,w6,w20,w27,w48,w54,w71],[w0,w6,w20,w27,w50,w52,w71],[w0,w6,w20,w30,w40,w62,w65],[w0,w6,w20,w30,w42,w60,w65],[w0,w6,w20,w30,w44,w58,w65],[w0,w6,w20,w30,w46,w56,w65],[w0,w6,w20,w30,w48,w54,w65],[w0,w6,w20,w30,w50,w52,w65],[w0,w6,w21,w27,w40,w62,w65],[w0,w6,w21,w27,w42,w60,w65],[w0,w6,w21,w27,w44,w58,w65],[w0,w6,w21,w27,w46,w56,w65],[w0,w6,w21,w27,w48,w54,w65],[w0,w6,w21,w27,w50,w52,w65],[w0,w6,w22,w27,w40,w62,w97],[w0,w6,w22,w27,w42,w60,w97],[w0,w6,w22,w27,w44,w58,w97],[w0,w6,w22,w27,w46,w56,w97],[w0,w6,w22,w27,w48,w54,w97],[w0,w6,w22,w27,w50,w52,w97],[w0,w6,w27,w30,w40,w62,w97],[w0,w6,w27,w30,w42,w60,w97],[w0,w6,w27,w30,w44,w58,w97],[w0,w6,w27,w30,w46,w56,w97],[w0,w6,w27,w30,w48,w54,w97],[w0,w6,w27,w30,w50,w52,w97],[w0,w6,w27,w40,w44,w54,w100],[w0,w6,w27,w40,w46,w52,w100],[w0,w6,w27,w40,w62,w71,w97],[w0,w6,w27,w40,w62,w97,w101],[w0,w6,w27,w42,w44,w52,w100],[w0,w6,w27,w42,w60,w71,w97],[w0,w6,w27,w42,w60,w97,w101],[w0,w6,w27,w44,w58,w71,w97],[w0,w6,w27,w44,w58,w97,w101],[w0,w6,w27,w46,w56,w71,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_38 : t6_38.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_36 : BankTree := .fork [w0,w6,w20,w27,w40,w62,w71] t6_37 t6_38
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_36 : t6_36.rows.all (refuses 5 t5_0)=true := by simp only [t6_36,BankTree.rows,List.all_append,ok_t6_37,ok_t6_38,Bool.true_and]
noncomputable def t6_40 : BankTree := .block [[w0,w6,w27,w46,w56,w97,w101],[w0,w6,w27,w48,w54,w71,w97],[w0,w6,w27,w48,w54,w97,w101],[w0,w6,w27,w50,w52,w71,w97],[w0,w6,w27,w50,w52,w97,w101],[w0,w6,w29,w40,w44,w54,w97],[w0,w6,w29,w40,w46,w52,w97],[w0,w6,w29,w42,w44,w52,w97],[w0,w8,w16,w19,w27,w71,w91],[w0,w8,w16,w19,w30,w65,w91],[w0,w8,w19,w27,w40,w62,w71],[w0,w8,w19,w27,w42,w60,w71],[w0,w8,w19,w27,w44,w58,w71],[w0,w8,w19,w27,w46,w56,w71],[w0,w8,w19,w27,w48,w54,w71],[w0,w8,w19,w27,w50,w52,w71],[w0,w8,w19,w30,w40,w62,w65],[w0,w8,w19,w30,w42,w60,w65],[w0,w8,w19,w30,w44,w58,w65],[w0,w8,w19,w30,w46,w56,w65],[w0,w8,w19,w30,w48,w54,w65],[w0,w8,w19,w30,w50,w52,w65],[w0,w9,w16,w19,w27,w65,w91],[w0,w9,w16,w27,w40,w60,w97],[w0,w9,w16,w27,w44,w56,w97],[w0,w9,w16,w27,w48,w52,w97],[w0,w9,w19,w27,w40,w62,w65],[w0,w9,w19,w27,w42,w60,w65],[w0,w9,w19,w27,w44,w58,w65],[w0,w9,w19,w27,w46,w56,w65],[w0,w9,w19,w27,w48,w54,w65],[w0,w9,w19,w27,w50,w52,w65],[w0,w9,w27,w40,w44,w54,w97],[w0,w9,w27,w40,w46,w52,w97],[w0,w9,w27,w42,w44,w52,w97],[w0,w10,w16,w19,w27,w65,w91],[w0,w10,w16,w27,w40,w60,w97],[w0,w10,w16,w27,w44,w56,w97],[w0,w10,w16,w27,w48,w52,w97],[w0,w10,w19,w27,w40,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_40 : t6_40.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_41 : BankTree := .block [[w0,w10,w19,w27,w42,w60,w65],[w0,w10,w19,w27,w44,w58,w65],[w0,w10,w19,w27,w46,w56,w65],[w0,w10,w19,w27,w48,w54,w65],[w0,w10,w19,w27,w50,w52,w65],[w0,w10,w27,w40,w44,w54,w97],[w0,w10,w27,w40,w46,w52,w97],[w0,w10,w27,w42,w44,w52,w97],[w0,w11,w16,w19,w27,w65,w91],[w0,w11,w16,w27,w40,w60,w97],[w0,w11,w16,w27,w44,w56,w97],[w0,w11,w16,w27,w48,w52,w97],[w0,w11,w19,w27,w40,w62,w65],[w0,w11,w19,w27,w42,w60,w65],[w0,w11,w19,w27,w44,w58,w65],[w0,w11,w19,w27,w46,w56,w65],[w0,w11,w19,w27,w48,w54,w65],[w0,w11,w19,w27,w50,w52,w65],[w0,w11,w27,w40,w44,w54,w97],[w0,w11,w27,w40,w46,w52,w97],[w0,w11,w27,w42,w44,w52,w97],[w0,w12,w16,w19,w27,w64,w91],[w0,w12,w16,w19,w27,w65,w91],[w0,w12,w16,w19,w27,w65,w93],[w0,w12,w16,w19,w27,w65,w94],[w0,w12,w16,w19,w27,w67,w91],[w0,w12,w16,w19,w27,w71,w91],[w0,w12,w16,w19,w27,w77,w91],[w0,w12,w16,w19,w27,w87,w91],[w0,w12,w16,w19,w27,w91,w97],[w0,w12,w16,w19,w27,w91,w109],[w0,w12,w16,w19,w28,w65,w91],[w0,w12,w16,w19,w30,w65,w91],[w0,w12,w16,w19,w33,w65,w91],[w0,w12,w16,w19,w38,w65,w91],[w0,w12,w16,w20,w27,w65,w91],[w0,w12,w16,w27,w40,w60,w98],[w0,w12,w16,w27,w40,w61,w97],[w0,w12,w16,w27,w40,w62,w97],[w0,w12,w16,w27,w40,w91,w97],[w0,w12,w16,w27,w41,w60,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_41 : t6_41.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_39 : BankTree := .fork [w0,w10,w19,w27,w42,w60,w65] t6_40 t6_41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_39 : t6_39.rows.all (refuses 5 t5_0)=true := by simp only [t6_39,BankTree.rows,List.all_append,ok_t6_40,ok_t6_41,Bool.true_and]
noncomputable def t6_35 : BankTree := .fork [w0,w6,w27,w46,w56,w97,w101] t6_36 t6_39
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_35 : t6_35.rows.all (refuses 5 t5_0)=true := by simp only [t6_35,BankTree.rows,List.all_append,ok_t6_36,ok_t6_39,Bool.true_and]
noncomputable def t6_44 : BankTree := .block [[w0,w12,w16,w27,w42,w60,w97],[w0,w12,w16,w27,w44,w56,w98],[w0,w12,w16,w27,w44,w57,w97],[w0,w12,w16,w27,w44,w58,w97],[w0,w12,w16,w27,w44,w91,w97],[w0,w12,w16,w27,w45,w56,w97],[w0,w12,w16,w27,w46,w56,w97],[w0,w12,w16,w27,w48,w52,w98],[w0,w12,w16,w27,w48,w53,w97],[w0,w12,w16,w27,w48,w54,w97],[w0,w12,w16,w27,w48,w56,w97],[w0,w12,w16,w27,w48,w60,w97],[w0,w12,w16,w27,w48,w91,w97],[w0,w12,w16,w27,w49,w52,w97],[w0,w12,w16,w27,w50,w52,w97],[w0,w12,w16,w27,w52,w91,w97],[w0,w12,w16,w27,w56,w60,w97],[w0,w12,w16,w27,w56,w91,w97],[w0,w12,w16,w27,w60,w91,w97],[w0,w12,w16,w27,w65,w91,w97],[w0,w12,w16,w27,w91,w97],[w0,w12,w16,w28,w40,w60,w97],[w0,w12,w16,w28,w44,w56,w97],[w0,w12,w16,w28,w48,w52,w97],[w0,w12,w18,w19,w27,w65,w91],[w0,w12,w18,w27,w40,w60,w97],[w0,w12,w18,w27,w44,w56,w97],[w0,w12,w18,w27,w48,w52,w97],[w0,w12,w19,w27,w40,w62,w65],[w0,w12,w19,w27,w40,w62,w67],[w0,w12,w19,w27,w40,w62,w71],[w0,w12,w19,w27,w40,w62,w77],[w0,w12,w19,w27,w40,w62,w87],[w0,w12,w19,w27,w40,w62,w97],[w0,w12,w19,w27,w40,w62,w109],[w0,w12,w19,w27,w40,w63,w65],[w0,w12,w19,w27,w40,w65,w94],[w0,w12,w19,w27,w41,w62,w65],[w0,w12,w19,w27,w42,w60,w67],[w0,w12,w19,w27,w42,w60,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_44 : t6_44.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_45 : BankTree := .block [[w0,w12,w19,w27,w42,w60,w77],[w0,w12,w19,w27,w42,w60,w87],[w0,w12,w19,w27,w42,w60,w97],[w0,w12,w19,w27,w42,w60,w109],[w0,w12,w19,w27,w42,w61,w65],[w0,w12,w19,w27,w42,w62,w65],[w0,w12,w19,w27,w42,w65,w91],[w0,w12,w19,w27,w42,w65,w94],[w0,w12,w19,w27,w43,w60,w65],[w0,w12,w19,w27,w44,w58,w65],[w0,w12,w19,w27,w44,w58,w67],[w0,w12,w19,w27,w44,w58,w71],[w0,w12,w19,w27,w44,w58,w77],[w0,w12,w19,w27,w44,w58,w87],[w0,w12,w19,w27,w44,w58,w97],[w0,w12,w19,w27,w44,w58,w109],[w0,w12,w19,w27,w44,w59,w65],[w0,w12,w19,w27,w44,w65,w94],[w0,w12,w19,w27,w45,w58,w65],[w0,w12,w19,w27,w46,w56,w67],[w0,w12,w19,w27,w46,w56,w71],[w0,w12,w19,w27,w46,w56,w77],[w0,w12,w19,w27,w46,w56,w87],[w0,w12,w19,w27,w46,w56,w97],[w0,w12,w19,w27,w46,w56,w109],[w0,w12,w19,w27,w46,w57,w65],[w0,w12,w19,w27,w46,w58,w65],[w0,w12,w19,w27,w46,w65,w91],[w0,w12,w19,w27,w46,w65,w94],[w0,w12,w19,w27,w47,w56,w65],[w0,w12,w19,w27,w48,w54,w67],[w0,w12,w19,w27,w48,w54,w71],[w0,w12,w19,w27,w48,w54,w77],[w0,w12,w19,w27,w48,w54,w87],[w0,w12,w19,w27,w48,w54,w97],[w0,w12,w19,w27,w48,w54,w109],[w0,w12,w19,w27,w48,w55,w65],[w0,w12,w19,w27,w48,w58,w65],[w0,w12,w19,w27,w48,w62,w65],[w0,w12,w19,w27,w48,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_45 : t6_45.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_43 : BankTree := .fork [w0,w12,w19,w27,w42,w60,w77] t6_44 t6_45
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_43 : t6_43.rows.all (refuses 5 t5_0)=true := by simp only [t6_43,BankTree.rows,List.all_append,ok_t6_44,ok_t6_45,Bool.true_and]
noncomputable def t6_47 : BankTree := .block [[w0,w12,w19,w27,w49,w54,w65],[w0,w12,w19,w27,w50,w52,w65],[w0,w12,w19,w27,w50,w52,w67],[w0,w12,w19,w27,w50,w52,w71],[w0,w12,w19,w27,w50,w52,w77],[w0,w12,w19,w27,w50,w52,w87],[w0,w12,w19,w27,w50,w52,w97],[w0,w12,w19,w27,w50,w52,w109],[w0,w12,w19,w27,w50,w53,w65],[w0,w12,w19,w27,w50,w54,w65],[w0,w12,w19,w27,w50,w56,w65],[w0,w12,w19,w27,w50,w58,w65],[w0,w12,w19,w27,w50,w60,w65],[w0,w12,w19,w27,w50,w62,w65],[w0,w12,w19,w27,w50,w65,w91],[w0,w12,w19,w27,w50,w65,w94],[w0,w12,w19,w27,w51,w52,w65],[w0,w12,w19,w27,w52,w65,w94],[w0,w12,w19,w27,w54,w65,w91],[w0,w12,w19,w27,w54,w65,w94],[w0,w12,w19,w27,w56,w62,w65],[w0,w12,w19,w27,w56,w65,w94],[w0,w12,w19,w27,w58,w60,w65],[w0,w12,w19,w27,w58,w62,w65],[w0,w12,w19,w27,w58,w65,w91],[w0,w12,w19,w27,w58,w65,w94],[w0,w12,w19,w27,w60,w65,w94],[w0,w12,w19,w27,w62,w65,w91],[w0,w12,w19,w27,w62,w65,w94],[w0,w12,w19,w27,w65,w91,w94],[w0,w12,w19,w27,w65,w94],[w0,w12,w19,w28,w40,w62,w65],[w0,w12,w19,w28,w42,w60,w65],[w0,w12,w19,w28,w44,w58,w65],[w0,w12,w19,w28,w46,w56,w65],[w0,w12,w19,w28,w48,w54,w65],[w0,w12,w19,w28,w50,w52,w65],[w0,w12,w19,w30,w40,w62,w65],[w0,w12,w19,w30,w42,w60,w65],[w0,w12,w19,w30,w44,w58,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_47 : t6_47.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_48 : BankTree := .block [[w0,w12,w19,w30,w46,w56,w65],[w0,w12,w19,w30,w48,w54,w65],[w0,w12,w19,w30,w50,w52,w65],[w0,w12,w19,w33,w40,w62,w65],[w0,w12,w19,w33,w42,w60,w65],[w0,w12,w19,w33,w44,w58,w65],[w0,w12,w19,w33,w46,w56,w65],[w0,w12,w19,w33,w48,w54,w65],[w0,w12,w19,w33,w50,w52,w65],[w0,w12,w19,w38,w40,w62,w65],[w0,w12,w19,w38,w42,w60,w65],[w0,w12,w19,w38,w44,w58,w65],[w0,w12,w19,w38,w46,w56,w65],[w0,w12,w19,w38,w48,w54,w65],[w0,w12,w19,w38,w50,w52,w65],[w0,w12,w20,w27,w40,w62,w65],[w0,w12,w20,w27,w42,w60,w65],[w0,w12,w20,w27,w44,w58,w65],[w0,w12,w20,w27,w46,w56,w65],[w0,w12,w20,w27,w48,w54,w65],[w0,w12,w20,w27,w50,w52,w65],[w0,w12,w27,w40,w42,w60,w97],[w0,w12,w27,w40,w44,w54,w98],[w0,w12,w27,w40,w44,w55,w97],[w0,w12,w27,w40,w44,w58,w97],[w0,w12,w27,w40,w44,w62,w97],[w0,w12,w27,w40,w45,w54,w97],[w0,w12,w27,w40,w46,w52,w98],[w0,w12,w27,w40,w46,w53,w97],[w0,w12,w27,w40,w46,w54,w97],[w0,w12,w27,w40,w46,w56,w97],[w0,w12,w27,w40,w46,w60,w97],[w0,w12,w27,w40,w46,w62,w97],[w0,w12,w27,w40,w47,w52,w97],[w0,w12,w27,w40,w48,w54,w97],[w0,w12,w27,w40,w50,w52,w97],[w0,w12,w27,w40,w52,w62,w97],[w0,w12,w27,w40,w54,w60,w97],[w0,w12,w27,w40,w54,w62,w97],[w0,w12,w27,w40,w60,w62,w97],[w0,w12,w27,w40,w62,w65,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_48 : t6_48.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_46 : BankTree := .fork [w0,w12,w19,w30,w46,w56,w65] t6_47 t6_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_46 : t6_46.rows.all (refuses 5 t5_0)=true := by simp only [t6_46,BankTree.rows,List.all_append,ok_t6_47,ok_t6_48,Bool.true_and]
noncomputable def t6_42 : BankTree := .fork [w0,w12,w19,w27,w49,w54,w65] t6_43 t6_46
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_42 : t6_42.rows.all (refuses 5 t5_0)=true := by simp only [t6_42,BankTree.rows,List.all_append,ok_t6_43,ok_t6_46,Bool.true_and]
noncomputable def t6_34 : BankTree := .fork [w0,w12,w16,w27,w42,w60,w97] t6_35 t6_42
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_34 : t6_34.rows.all (refuses 5 t5_0)=true := by simp only [t6_34,BankTree.rows,List.all_append,ok_t6_35,ok_t6_42,Bool.true_and]
noncomputable def t6_52 : BankTree := .block [[w0,w12,w27,w40,w62,w97],[w0,w12,w27,w41,w44,w54,w97],[w0,w12,w27,w41,w46,w52,w97],[w0,w12,w27,w42,w44,w52,w98],[w0,w12,w27,w42,w44,w53,w97],[w0,w12,w27,w42,w44,w54,w97],[w0,w12,w27,w42,w44,w56,w97],[w0,w12,w27,w42,w44,w58,w97],[w0,w12,w27,w42,w44,w60,w97],[w0,w12,w27,w42,w45,w52,w97],[w0,w12,w27,w42,w46,w52,w97],[w0,w12,w27,w42,w48,w52,w97],[w0,w12,w27,w42,w50,w52,w97],[w0,w12,w27,w42,w52,w60,w97],[w0,w12,w27,w42,w60,w65,w97],[w0,w12,w27,w42,w60,w97],[w0,w12,w27,w43,w44,w52,w97],[w0,w12,w27,w44,w46,w56,w97],[w0,w12,w27,w44,w48,w54,w97],[w0,w12,w27,w44,w50,w52,w97],[w0,w12,w27,w44,w52,w58,w97],[w0,w12,w27,w44,w54,w56,w97],[w0,w12,w27,w44,w54,w58,w97],[w0,w12,w27,w44,w56,w58,w97],[w0,w12,w27,w44,w58,w65,w97],[w0,w12,w27,w44,w58,w97],[w0,w12,w27,w46,w48,w52,w97],[w0,w12,w27,w46,w50,w52,w97],[w0,w12,w27,w46,w52,w56,w97],[w0,w12,w27,w46,w56,w65,w97],[w0,w12,w27,w46,w56,w97],[w0,w12,w27,w48,w50,w52,w97],[w0,w12,w27,w48,w52,w54,w97],[w0,w12,w27,w48,w54,w65,w97],[w0,w12,w27,w48,w54,w97],[w0,w12,w27,w50,w52,w65,w97],[w0,w12,w27,w50,w52,w97],[w0,w12,w28,w40,w44,w54,w97],[w0,w12,w28,w40,w46,w52,w97],[w0,w12,w28,w42,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_52 : t6_52.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_53 : BankTree := .block [[w0,w14,w16,w19,w27,w65,w91],[w0,w14,w16,w27,w40,w60,w97],[w0,w14,w16,w27,w44,w56,w97],[w0,w14,w16,w27,w48,w52,w97],[w0,w14,w19,w27,w40,w62,w65],[w0,w14,w19,w27,w42,w60,w65],[w0,w14,w19,w27,w44,w58,w65],[w0,w14,w19,w27,w46,w56,w65],[w0,w14,w19,w27,w48,w54,w65],[w0,w14,w19,w27,w50,w52,w65],[w0,w14,w27,w40,w44,w54,w97],[w0,w14,w27,w40,w46,w52,w97],[w0,w14,w27,w42,w44,w52,w97],[w0,w15,w19,w27,w40,w60,w65],[w0,w15,w19,w27,w44,w56,w65],[w0,w15,w19,w27,w48,w52,w65],[w0,w15,w27,w40,w44,w52,w97],[w0,w16,w19,w22,w27,w77,w91],[w0,w16,w19,w22,w33,w65,w91],[w0,w16,w19,w24,w27,w71,w91],[w0,w16,w19,w24,w30,w65,w91],[w0,w16,w19,w26,w27,w65,w91],[w0,w16,w19,w27,w30,w77,w91],[w0,w16,w19,w27,w33,w71,w91],[w0,w16,w19,w27,w38,w65,w91],[w0,w16,w19,w27,w40,w60,w81],[w0,w16,w19,w27,w40,w60,w83],[w0,w16,w19,w27,w40,w60,w85],[w0,w16,w19,w27,w40,w60,w87],[w0,w16,w19,w27,w40,w60,w89],[w0,w16,w19,w27,w40,w60,w107],[w0,w16,w19,w27,w40,w60,w120],[w0,w16,w19,w27,w40,w61,w87],[w0,w16,w19,w27,w40,w62,w87],[w0,w16,w19,w27,w40,w87,w91],[w0,w16,w19,w27,w41,w60,w87],[w0,w16,w19,w27,w42,w60,w87],[w0,w16,w19,w27,w44,w56,w81],[w0,w16,w19,w27,w44,w56,w83],[w0,w16,w19,w27,w44,w56,w85]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_53 : t6_53.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_51 : BankTree := .fork [w0,w14,w16,w19,w27,w65,w91] t6_52 t6_53
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_51 : t6_51.rows.all (refuses 5 t5_0)=true := by simp only [t6_51,BankTree.rows,List.all_append,ok_t6_52,ok_t6_53,Bool.true_and]
noncomputable def t6_55 : BankTree := .block [[w0,w16,w19,w27,w44,w56,w87],[w0,w16,w19,w27,w44,w56,w89],[w0,w16,w19,w27,w44,w56,w107],[w0,w16,w19,w27,w44,w56,w120],[w0,w16,w19,w27,w44,w57,w87],[w0,w16,w19,w27,w44,w58,w87],[w0,w16,w19,w27,w44,w87,w91],[w0,w16,w19,w27,w45,w56,w87],[w0,w16,w19,w27,w46,w56,w87],[w0,w16,w19,w27,w48,w52,w81],[w0,w16,w19,w27,w48,w52,w83],[w0,w16,w19,w27,w48,w52,w85],[w0,w16,w19,w27,w48,w52,w87],[w0,w16,w19,w27,w48,w52,w89],[w0,w16,w19,w27,w48,w52,w107],[w0,w16,w19,w27,w48,w52,w120],[w0,w16,w19,w27,w48,w53,w87],[w0,w16,w19,w27,w48,w54,w87],[w0,w16,w19,w27,w48,w56,w87],[w0,w16,w19,w27,w48,w60,w87],[w0,w16,w19,w27,w48,w87,w91],[w0,w16,w19,w27,w49,w52,w87],[w0,w16,w19,w27,w50,w52,w87],[w0,w16,w19,w27,w52,w87,w91],[w0,w16,w19,w27,w56,w60,w87],[w0,w16,w19,w27,w56,w87,w91],[w0,w16,w19,w27,w60,w87,w91],[w0,w16,w19,w27,w65,w87,w91],[w0,w16,w19,w27,w71,w77,w91],[w0,w16,w19,w27,w71,w87,w91],[w0,w16,w19,w27,w77,w87,w91],[w0,w16,w19,w27,w87,w91],[w0,w16,w19,w28,w40,w60,w87],[w0,w16,w19,w28,w44,w56,w87],[w0,w16,w19,w28,w48,w52,w87],[w0,w16,w19,w29,w40,w60,w77],[w0,w16,w19,w29,w44,w56,w77],[w0,w16,w19,w29,w48,w52,w77],[w0,w16,w19,w30,w33,w65,w91],[w0,w16,w19,w30,w38,w65,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_55 : t6_55.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_56 : BankTree := .block [[w0,w16,w19,w30,w40,w60,w75],[w0,w16,w19,w30,w40,w60,w79],[w0,w16,w19,w30,w40,w60,w87],[w0,w16,w19,w30,w40,w60,w104],[w0,w16,w19,w30,w40,w60,w115],[w0,w16,w19,w30,w40,w60,w120],[w0,w16,w19,w30,w40,w61,w77],[w0,w16,w19,w30,w40,w62,w77],[w0,w16,w19,w30,w40,w77,w91],[w0,w16,w19,w30,w41,w60,w77],[w0,w16,w19,w30,w42,w60,w77],[w0,w16,w19,w30,w44,w56,w75],[w0,w16,w19,w30,w44,w56,w79],[w0,w16,w19,w30,w44,w56,w87],[w0,w16,w19,w30,w44,w56,w104],[w0,w16,w19,w30,w44,w56,w115],[w0,w16,w19,w30,w44,w56,w120],[w0,w16,w19,w30,w44,w57,w77],[w0,w16,w19,w30,w44,w58,w77],[w0,w16,w19,w30,w44,w77,w91],[w0,w16,w19,w30,w45,w56,w77],[w0,w16,w19,w30,w46,w56,w77],[w0,w16,w19,w30,w48,w52,w75],[w0,w16,w19,w30,w48,w52,w79],[w0,w16,w19,w30,w48,w52,w87],[w0,w16,w19,w30,w48,w52,w104],[w0,w16,w19,w30,w48,w52,w115],[w0,w16,w19,w30,w48,w52,w120],[w0,w16,w19,w30,w48,w53,w77],[w0,w16,w19,w30,w48,w54,w77],[w0,w16,w19,w30,w48,w56,w77],[w0,w16,w19,w30,w48,w60,w77],[w0,w16,w19,w30,w48,w77,w91],[w0,w16,w19,w30,w49,w52,w77],[w0,w16,w19,w30,w50,w52,w77],[w0,w16,w19,w30,w52,w77,w91],[w0,w16,w19,w30,w56,w60,w77],[w0,w16,w19,w30,w56,w77,w91],[w0,w16,w19,w30,w60,w77,w91],[w0,w16,w19,w30,w65,w77,w91],[w0,w16,w19,w30,w77,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_56 : t6_56.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_54 : BankTree := .fork [w0,w16,w19,w30,w40,w60,w75] t6_55 t6_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_54 : t6_54.rows.all (refuses 5 t5_0)=true := by simp only [t6_54,BankTree.rows,List.all_append,ok_t6_55,ok_t6_56,Bool.true_and]
noncomputable def t6_50 : BankTree := .fork [w0,w16,w19,w27,w44,w56,w87] t6_51 t6_54
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_50 : t6_50.rows.all (refuses 5 t5_0)=true := by simp only [t6_50,BankTree.rows,List.all_append,ok_t6_51,ok_t6_54,Bool.true_and]
noncomputable def t6_59 : BankTree := .block [[w0,w16,w19,w31,w40,w60,w77],[w0,w16,w19,w31,w44,w56,w77],[w0,w16,w19,w31,w48,w52,w77],[w0,w16,w19,w32,w40,w60,w71],[w0,w16,w19,w32,w44,w56,w71],[w0,w16,w19,w32,w48,w52,w71],[w0,w16,w19,w33,w38,w65,w91],[w0,w16,w19,w33,w40,w60,w69],[w0,w16,w19,w33,w40,w60,w73],[w0,w16,w19,w33,w40,w60,w87],[w0,w16,w19,w33,w40,w60,w101],[w0,w16,w19,w33,w40,w60,w112],[w0,w16,w19,w33,w40,w60,w120],[w0,w16,w19,w33,w40,w61,w71],[w0,w16,w19,w33,w40,w62,w71],[w0,w16,w19,w33,w40,w71,w91],[w0,w16,w19,w33,w41,w60,w71],[w0,w16,w19,w33,w42,w60,w71],[w0,w16,w19,w33,w44,w56,w69],[w0,w16,w19,w33,w44,w56,w73],[w0,w16,w19,w33,w44,w56,w87],[w0,w16,w19,w33,w44,w56,w101],[w0,w16,w19,w33,w44,w56,w112],[w0,w16,w19,w33,w44,w56,w120],[w0,w16,w19,w33,w44,w57,w71],[w0,w16,w19,w33,w44,w58,w71],[w0,w16,w19,w33,w44,w71,w91],[w0,w16,w19,w33,w45,w56,w71],[w0,w16,w19,w33,w46,w56,w71],[w0,w16,w19,w33,w48,w52,w69],[w0,w16,w19,w33,w48,w52,w73],[w0,w16,w19,w33,w48,w52,w87],[w0,w16,w19,w33,w48,w52,w101],[w0,w16,w19,w33,w48,w52,w112],[w0,w16,w19,w33,w48,w52,w120],[w0,w16,w19,w33,w48,w53,w71],[w0,w16,w19,w33,w48,w54,w71],[w0,w16,w19,w33,w48,w56,w71],[w0,w16,w19,w33,w48,w60,w71],[w0,w16,w19,w33,w48,w71,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_59 : t6_59.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_60 : BankTree := .block [[w0,w16,w19,w33,w49,w52,w71],[w0,w16,w19,w33,w50,w52,w71],[w0,w16,w19,w33,w52,w71,w91],[w0,w16,w19,w33,w56,w60,w71],[w0,w16,w19,w33,w56,w71,w91],[w0,w16,w19,w33,w60,w71,w91],[w0,w16,w19,w33,w65,w71,w91],[w0,w16,w19,w33,w71,w91],[w0,w16,w19,w34,w40,w60,w71],[w0,w16,w19,w34,w44,w56,w71],[w0,w16,w19,w34,w48,w52,w71],[w0,w16,w19,w35,w40,w60,w65],[w0,w16,w19,w35,w44,w56,w65],[w0,w16,w19,w35,w48,w52,w65],[w0,w16,w19,w36,w40,w60,w65],[w0,w16,w19,w36,w44,w56,w65],[w0,w16,w19,w36,w48,w52,w65],[w0,w16,w19,w37,w40,w60,w65],[w0,w16,w19,w37,w44,w56,w65],[w0,w16,w19,w37,w48,w52,w65],[w0,w16,w19,w38,w40,w60,w65],[w0,w16,w19,w38,w40,w60,w67],[w0,w16,w19,w38,w40,w60,w71],[w0,w16,w19,w38,w40,w60,w77],[w0,w16,w19,w38,w40,w60,w87],[w0,w16,w19,w38,w40,w60,w97],[w0,w16,w19,w38,w40,w60,w109],[w0,w16,w19,w38,w40,w60,w112],[w0,w16,w19,w38,w40,w60,w115],[w0,w16,w19,w38,w40,w60,w120],[w0,w16,w19,w38,w40,w61,w65],[w0,w16,w19,w38,w40,w62,w65],[w0,w16,w19,w38,w40,w65,w91],[w0,w16,w19,w38,w41,w60,w65],[w0,w16,w19,w38,w42,w60,w65],[w0,w16,w19,w38,w44,w56,w65],[w0,w16,w19,w38,w44,w56,w67],[w0,w16,w19,w38,w44,w56,w71],[w0,w16,w19,w38,w44,w56,w77],[w0,w16,w19,w38,w44,w56,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_60 : t6_60.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_58 : BankTree := .fork [w0,w16,w19,w33,w49,w52,w71] t6_59 t6_60
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_58 : t6_58.rows.all (refuses 5 t5_0)=true := by simp only [t6_58,BankTree.rows,List.all_append,ok_t6_59,ok_t6_60,Bool.true_and]
noncomputable def t6_62 : BankTree := .block [[w0,w16,w19,w38,w44,w56,w97],[w0,w16,w19,w38,w44,w56,w109],[w0,w16,w19,w38,w44,w56,w112],[w0,w16,w19,w38,w44,w56,w115],[w0,w16,w19,w38,w44,w56,w120],[w0,w16,w19,w38,w44,w57,w65],[w0,w16,w19,w38,w44,w58,w65],[w0,w16,w19,w38,w44,w65,w91],[w0,w16,w19,w38,w45,w56,w65],[w0,w16,w19,w38,w46,w56,w65],[w0,w16,w19,w38,w48,w52,w65],[w0,w16,w19,w38,w48,w52,w67],[w0,w16,w19,w38,w48,w52,w71],[w0,w16,w19,w38,w48,w52,w77],[w0,w16,w19,w38,w48,w52,w87],[w0,w16,w19,w38,w48,w52,w97],[w0,w16,w19,w38,w48,w52,w109],[w0,w16,w19,w38,w48,w52,w112],[w0,w16,w19,w38,w48,w52,w115],[w0,w16,w19,w38,w48,w52,w120],[w0,w16,w19,w38,w48,w53,w65],[w0,w16,w19,w38,w48,w54,w65],[w0,w16,w19,w38,w48,w56,w65],[w0,w16,w19,w38,w48,w60,w65],[w0,w16,w19,w38,w48,w65,w91],[w0,w16,w19,w38,w49,w52,w65],[w0,w16,w19,w38,w50,w52,w65],[w0,w16,w19,w38,w52,w65,w91],[w0,w16,w19,w38,w56,w60,w65],[w0,w16,w19,w38,w56,w65,w91],[w0,w16,w19,w38,w60,w65,w91],[w0,w16,w19,w38,w65,w91],[w0,w16,w19,w39,w40,w60,w65],[w0,w16,w19,w39,w44,w56,w65],[w0,w16,w19,w39,w48,w52,w65],[w0,w16,w20,w27,w40,w60,w87],[w0,w16,w20,w27,w44,w56,w87],[w0,w16,w20,w27,w48,w52,w87],[w0,w16,w20,w30,w40,w60,w77],[w0,w16,w20,w30,w44,w56,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_62 : t6_62.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_63 : BankTree := .block [[w0,w16,w20,w30,w48,w52,w77],[w0,w16,w20,w33,w40,w60,w71],[w0,w16,w20,w33,w44,w56,w71],[w0,w16,w20,w33,w48,w52,w71],[w0,w16,w20,w38,w40,w60,w65],[w0,w16,w20,w38,w44,w56,w65],[w0,w16,w20,w38,w48,w52,w65],[w0,w16,w21,w27,w40,w60,w77],[w0,w16,w21,w27,w44,w56,w77],[w0,w16,w21,w27,w48,w52,w77],[w0,w16,w21,w33,w40,w60,w65],[w0,w16,w21,w33,w44,w56,w65],[w0,w16,w21,w33,w48,w52,w65],[w0,w16,w22,w24,w27,w65,w91],[w0,w16,w22,w27,w40,w60,w104],[w0,w16,w22,w27,w44,w56,w104],[w0,w16,w22,w27,w48,w52,w104],[w0,w16,w22,w33,w40,w60,w97],[w0,w16,w22,w33,w44,w56,w97],[w0,w16,w22,w33,w48,w52,w97],[w0,w16,w23,w27,w40,w60,w71],[w0,w16,w23,w27,w44,w56,w71],[w0,w16,w23,w27,w48,w52,w71],[w0,w16,w23,w30,w40,w60,w65],[w0,w16,w23,w30,w44,w56,w65],[w0,w16,w23,w30,w48,w52,w65],[w0,w16,w24,w27,w40,w60,w101],[w0,w16,w24,w27,w44,w56,w101],[w0,w16,w24,w27,w48,w52,w101],[w0,w16,w24,w30,w40,w60,w97],[w0,w16,w24,w30,w44,w56,w97],[w0,w16,w24,w30,w48,w52,w97],[w0,w16,w25,w27,w40,w60,w65],[w0,w16,w25,w27,w44,w56,w65],[w0,w16,w25,w27,w48,w52,w65],[w0,w16,w26,w27,w40,w60,w97],[w0,w16,w26,w27,w44,w56,w97],[w0,w16,w26,w27,w48,w52,w97],[w0,w16,w27,w38,w40,w60,w97],[w0,w16,w27,w38,w44,w56,w97],[w0,w16,w27,w38,w48,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_63 : t6_63.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_61 : BankTree := .fork [w0,w16,w20,w30,w48,w52,w77] t6_62 t6_63
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_61 : t6_61.rows.all (refuses 5 t5_0)=true := by simp only [t6_61,BankTree.rows,List.all_append,ok_t6_62,ok_t6_63,Bool.true_and]
noncomputable def t6_57 : BankTree := .fork [w0,w16,w19,w38,w44,w56,w97] t6_58 t6_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_57 : t6_57.rows.all (refuses 5 t5_0)=true := by simp only [t6_57,BankTree.rows,List.all_append,ok_t6_58,ok_t6_61,Bool.true_and]
noncomputable def t6_49 : BankTree := .fork [w0,w16,w19,w31,w40,w60,w77] t6_50 t6_57
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_49 : t6_49.rows.all (refuses 5 t5_0)=true := by simp only [t6_49,BankTree.rows,List.all_append,ok_t6_50,ok_t6_57,Bool.true_and]
noncomputable def t6_33 : BankTree := .fork [w0,w12,w27,w40,w62,w97] t6_34 t6_49
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_33 : t6_33.rows.all (refuses 5 t5_0)=true := by simp only [t6_33,BankTree.rows,List.all_append,ok_t6_34,ok_t6_49,Bool.true_and]
noncomputable def t6_1 : BankTree := .fork [w0,w6,w19,w30,w50,w54,w65] t6_2 t6_33
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_1 : t6_1.rows.all (refuses 5 t5_0)=true := by simp only [t6_1,BankTree.rows,List.all_append,ok_t6_2,ok_t6_33,Bool.true_and]
noncomputable def t6_69 : BankTree := .block [[w0,w16,w27,w40,w44,w52,w106],[w0,w16,w27,w40,w60,w87,w97],[w0,w16,w27,w40,w60,w97,w107],[w0,w16,w27,w40,w60,w101,w104],[w0,w16,w27,w44,w56,w87,w97],[w0,w16,w27,w44,w56,w97,w107],[w0,w16,w27,w44,w56,w101,w104],[w0,w16,w27,w48,w52,w87,w97],[w0,w16,w27,w48,w52,w97,w107],[w0,w16,w27,w48,w52,w101,w104],[w0,w16,w30,w33,w40,w60,w97],[w0,w16,w30,w33,w44,w56,w97],[w0,w16,w30,w33,w48,w52,w97],[w0,w16,w35,w40,w44,w52,w97],[w0,w18,w19,w27,w40,w60,w87],[w0,w18,w19,w27,w44,w56,w87],[w0,w18,w19,w27,w48,w52,w87],[w0,w18,w19,w30,w40,w60,w77],[w0,w18,w19,w30,w44,w56,w77],[w0,w18,w19,w30,w48,w52,w77],[w0,w18,w19,w33,w40,w60,w71],[w0,w18,w19,w33,w44,w56,w71],[w0,w18,w19,w33,w48,w52,w71],[w0,w18,w19,w38,w40,w60,w65],[w0,w18,w19,w38,w44,w56,w65],[w0,w18,w19,w38,w48,w52,w65],[w0,w19,w22,w27,w40,w62,w77],[w0,w19,w22,w27,w42,w60,w77],[w0,w19,w22,w27,w44,w58,w77],[w0,w19,w22,w27,w46,w56,w77],[w0,w19,w22,w27,w48,w54,w77],[w0,w19,w22,w27,w50,w52,w77],[w0,w19,w22,w33,w40,w62,w65],[w0,w19,w22,w33,w42,w60,w65],[w0,w19,w22,w33,w44,w58,w65],[w0,w19,w22,w33,w46,w56,w65],[w0,w19,w22,w33,w48,w54,w65],[w0,w19,w22,w33,w50,w52,w65],[w0,w19,w24,w27,w40,w62,w71],[w0,w19,w24,w27,w42,w60,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_69 : t6_69.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_70 : BankTree := .block [[w0,w19,w24,w27,w44,w58,w71],[w0,w19,w24,w27,w46,w56,w71],[w0,w19,w24,w27,w48,w54,w71],[w0,w19,w24,w27,w50,w52,w71],[w0,w19,w24,w30,w40,w62,w65],[w0,w19,w24,w30,w42,w60,w65],[w0,w19,w24,w30,w44,w58,w65],[w0,w19,w24,w30,w46,w56,w65],[w0,w19,w24,w30,w48,w54,w65],[w0,w19,w24,w30,w50,w52,w65],[w0,w19,w26,w27,w40,w62,w65],[w0,w19,w26,w27,w42,w60,w65],[w0,w19,w26,w27,w44,w58,w65],[w0,w19,w26,w27,w46,w56,w65],[w0,w19,w26,w27,w48,w54,w65],[w0,w19,w26,w27,w50,w52,w65],[w0,w19,w27,w30,w40,w62,w77],[w0,w19,w27,w30,w42,w60,w77],[w0,w19,w27,w30,w44,w58,w77],[w0,w19,w27,w30,w46,w56,w77],[w0,w19,w27,w30,w48,w54,w77],[w0,w19,w27,w30,w50,w52,w77],[w0,w19,w27,w33,w40,w62,w71],[w0,w19,w27,w33,w42,w60,w71],[w0,w19,w27,w33,w44,w58,w71],[w0,w19,w27,w33,w46,w56,w71],[w0,w19,w27,w33,w48,w54,w71],[w0,w19,w27,w33,w50,w52,w71],[w0,w19,w27,w38,w40,w62,w65],[w0,w19,w27,w38,w42,w60,w65],[w0,w19,w27,w38,w44,w58,w65],[w0,w19,w27,w38,w46,w56,w65],[w0,w19,w27,w38,w48,w54,w65],[w0,w19,w27,w38,w50,w52,w65],[w0,w19,w27,w40,w42,w60,w87],[w0,w19,w27,w40,w44,w54,w81],[w0,w19,w27,w40,w44,w54,w83],[w0,w19,w27,w40,w44,w54,w85],[w0,w19,w27,w40,w44,w54,w87],[w0,w19,w27,w40,w44,w54,w89]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_70 : t6_70.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_68 : BankTree := .fork [w0,w19,w24,w27,w44,w58,w71] t6_69 t6_70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_68 : t6_68.rows.all (refuses 5 t5_0)=true := by simp only [t6_68,BankTree.rows,List.all_append,ok_t6_69,ok_t6_70,Bool.true_and]
noncomputable def t6_72 : BankTree := .block [[w0,w19,w27,w40,w44,w54,w107],[w0,w19,w27,w40,w44,w54,w120],[w0,w19,w27,w40,w44,w55,w87],[w0,w19,w27,w40,w44,w58,w87],[w0,w19,w27,w40,w44,w62,w87],[w0,w19,w27,w40,w45,w54,w87],[w0,w19,w27,w40,w46,w52,w81],[w0,w19,w27,w40,w46,w52,w83],[w0,w19,w27,w40,w46,w52,w85],[w0,w19,w27,w40,w46,w52,w87],[w0,w19,w27,w40,w46,w52,w89],[w0,w19,w27,w40,w46,w52,w107],[w0,w19,w27,w40,w46,w52,w120],[w0,w19,w27,w40,w46,w53,w87],[w0,w19,w27,w40,w46,w54,w87],[w0,w19,w27,w40,w46,w56,w87],[w0,w19,w27,w40,w46,w60,w87],[w0,w19,w27,w40,w46,w62,w87],[w0,w19,w27,w40,w47,w52,w87],[w0,w19,w27,w40,w48,w54,w87],[w0,w19,w27,w40,w50,w52,w87],[w0,w19,w27,w40,w52,w62,w87],[w0,w19,w27,w40,w54,w60,w87],[w0,w19,w27,w40,w54,w62,w87],[w0,w19,w27,w40,w60,w62,w87],[w0,w19,w27,w40,w62,w65,w87],[w0,w19,w27,w40,w62,w71,w77],[w0,w19,w27,w40,w62,w71,w87],[w0,w19,w27,w40,w62,w77,w87],[w0,w19,w27,w40,w62,w87],[w0,w19,w27,w41,w44,w54,w87],[w0,w19,w27,w41,w46,w52,w87],[w0,w19,w27,w42,w44,w52,w81],[w0,w19,w27,w42,w44,w52,w83],[w0,w19,w27,w42,w44,w52,w85],[w0,w19,w27,w42,w44,w52,w87],[w0,w19,w27,w42,w44,w52,w89],[w0,w19,w27,w42,w44,w52,w107],[w0,w19,w27,w42,w44,w52,w120],[w0,w19,w27,w42,w44,w53,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_72 : t6_72.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_73 : BankTree := .block [[w0,w19,w27,w42,w44,w54,w87],[w0,w19,w27,w42,w44,w56,w87],[w0,w19,w27,w42,w44,w58,w87],[w0,w19,w27,w42,w44,w60,w87],[w0,w19,w27,w42,w45,w52,w87],[w0,w19,w27,w42,w46,w52,w87],[w0,w19,w27,w42,w48,w52,w87],[w0,w19,w27,w42,w50,w52,w87],[w0,w19,w27,w42,w52,w60,w87],[w0,w19,w27,w42,w60,w65,w87],[w0,w19,w27,w42,w60,w71,w77],[w0,w19,w27,w42,w60,w71,w87],[w0,w19,w27,w42,w60,w77,w87],[w0,w19,w27,w42,w60,w87],[w0,w19,w27,w43,w44,w52,w87],[w0,w19,w27,w44,w46,w56,w87],[w0,w19,w27,w44,w48,w54,w87],[w0,w19,w27,w44,w50,w52,w87],[w0,w19,w27,w44,w52,w58,w87],[w0,w19,w27,w44,w54,w56,w87],[w0,w19,w27,w44,w54,w58,w87],[w0,w19,w27,w44,w56,w58,w87],[w0,w19,w27,w44,w58,w65,w87],[w0,w19,w27,w44,w58,w71,w77],[w0,w19,w27,w44,w58,w71,w87],[w0,w19,w27,w44,w58,w77,w87],[w0,w19,w27,w44,w58,w87],[w0,w19,w27,w46,w48,w52,w87],[w0,w19,w27,w46,w50,w52,w87],[w0,w19,w27,w46,w52,w56,w87],[w0,w19,w27,w46,w56,w65,w87],[w0,w19,w27,w46,w56,w71,w77],[w0,w19,w27,w46,w56,w71,w87],[w0,w19,w27,w46,w56,w77,w87],[w0,w19,w27,w46,w56,w87],[w0,w19,w27,w48,w50,w52,w87],[w0,w19,w27,w48,w52,w54,w87],[w0,w19,w27,w48,w54,w65,w87],[w0,w19,w27,w48,w54,w71,w77],[w0,w19,w27,w48,w54,w71,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_73 : t6_73.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_71 : BankTree := .fork [w0,w19,w27,w42,w44,w54,w87] t6_72 t6_73
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_71 : t6_71.rows.all (refuses 5 t5_0)=true := by simp only [t6_71,BankTree.rows,List.all_append,ok_t6_72,ok_t6_73,Bool.true_and]
noncomputable def t6_67 : BankTree := .fork [w0,w19,w27,w40,w44,w54,w107] t6_68 t6_71
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_67 : t6_67.rows.all (refuses 5 t5_0)=true := by simp only [t6_67,BankTree.rows,List.all_append,ok_t6_68,ok_t6_71,Bool.true_and]
noncomputable def t6_76 : BankTree := .block [[w0,w19,w27,w48,w54,w77,w87],[w0,w19,w27,w48,w54,w87],[w0,w19,w27,w50,w52,w65,w87],[w0,w19,w27,w50,w52,w71,w77],[w0,w19,w27,w50,w52,w71,w87],[w0,w19,w27,w50,w52,w77,w87],[w0,w19,w27,w50,w52,w87],[w0,w19,w28,w40,w44,w54,w87],[w0,w19,w28,w40,w46,w52,w87],[w0,w19,w28,w42,w44,w52,w87],[w0,w19,w29,w40,w44,w54,w77],[w0,w19,w29,w40,w46,w52,w77],[w0,w19,w29,w42,w44,w52,w77],[w0,w19,w30,w33,w40,w62,w65],[w0,w19,w30,w33,w42,w60,w65],[w0,w19,w30,w33,w44,w58,w65],[w0,w19,w30,w33,w46,w56,w65],[w0,w19,w30,w33,w48,w54,w65],[w0,w19,w30,w33,w50,w52,w65],[w0,w19,w30,w38,w40,w62,w65],[w0,w19,w30,w38,w42,w60,w65],[w0,w19,w30,w38,w44,w58,w65],[w0,w19,w30,w38,w46,w56,w65],[w0,w19,w30,w38,w48,w54,w65],[w0,w19,w30,w38,w50,w52,w65],[w0,w19,w30,w40,w42,w60,w77],[w0,w19,w30,w40,w44,w54,w75],[w0,w19,w30,w40,w44,w54,w79],[w0,w19,w30,w40,w44,w54,w87],[w0,w19,w30,w40,w44,w54,w104],[w0,w19,w30,w40,w44,w54,w115],[w0,w19,w30,w40,w44,w54,w120],[w0,w19,w30,w40,w44,w55,w77],[w0,w19,w30,w40,w44,w58,w77],[w0,w19,w30,w40,w44,w62,w77],[w0,w19,w30,w40,w45,w54,w77],[w0,w19,w30,w40,w46,w52,w75],[w0,w19,w30,w40,w46,w52,w79],[w0,w19,w30,w40,w46,w52,w87],[w0,w19,w30,w40,w46,w52,w104]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_76 : t6_76.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_77 : BankTree := .block [[w0,w19,w30,w40,w46,w52,w115],[w0,w19,w30,w40,w46,w52,w120],[w0,w19,w30,w40,w46,w53,w77],[w0,w19,w30,w40,w46,w54,w77],[w0,w19,w30,w40,w46,w56,w77],[w0,w19,w30,w40,w46,w60,w77],[w0,w19,w30,w40,w46,w62,w77],[w0,w19,w30,w40,w47,w52,w77],[w0,w19,w30,w40,w48,w54,w77],[w0,w19,w30,w40,w50,w52,w77],[w0,w19,w30,w40,w52,w62,w77],[w0,w19,w30,w40,w54,w60,w77],[w0,w19,w30,w40,w54,w62,w77],[w0,w19,w30,w40,w60,w62,w77],[w0,w19,w30,w40,w62,w65,w77],[w0,w19,w30,w40,w62,w77],[w0,w19,w30,w41,w44,w54,w77],[w0,w19,w30,w41,w46,w52,w77],[w0,w19,w30,w42,w44,w52,w75],[w0,w19,w30,w42,w44,w52,w79],[w0,w19,w30,w42,w44,w52,w87],[w0,w19,w30,w42,w44,w52,w104],[w0,w19,w30,w42,w44,w52,w115],[w0,w19,w30,w42,w44,w52,w120],[w0,w19,w30,w42,w44,w53,w77],[w0,w19,w30,w42,w44,w54,w77],[w0,w19,w30,w42,w44,w56,w77],[w0,w19,w30,w42,w44,w58,w77],[w0,w19,w30,w42,w44,w60,w77],[w0,w19,w30,w42,w45,w52,w77],[w0,w19,w30,w42,w46,w52,w77],[w0,w19,w30,w42,w48,w52,w77],[w0,w19,w30,w42,w50,w52,w77],[w0,w19,w30,w42,w52,w60,w77],[w0,w19,w30,w42,w60,w65,w77],[w0,w19,w30,w42,w60,w77],[w0,w19,w30,w43,w44,w52,w77],[w0,w19,w30,w44,w46,w56,w77],[w0,w19,w30,w44,w48,w54,w77],[w0,w19,w30,w44,w50,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_77 : t6_77.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_75 : BankTree := .fork [w0,w19,w30,w40,w46,w52,w115] t6_76 t6_77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_75 : t6_75.rows.all (refuses 5 t5_0)=true := by simp only [t6_75,BankTree.rows,List.all_append,ok_t6_76,ok_t6_77,Bool.true_and]
noncomputable def t6_79 : BankTree := .block [[w0,w19,w30,w44,w52,w58,w77],[w0,w19,w30,w44,w54,w56,w77],[w0,w19,w30,w44,w54,w58,w77],[w0,w19,w30,w44,w56,w58,w77],[w0,w19,w30,w44,w58,w65,w77],[w0,w19,w30,w44,w58,w77],[w0,w19,w30,w46,w48,w52,w77],[w0,w19,w30,w46,w50,w52,w77],[w0,w19,w30,w46,w52,w56,w77],[w0,w19,w30,w46,w56,w65,w77],[w0,w19,w30,w46,w56,w77],[w0,w19,w30,w48,w50,w52,w77],[w0,w19,w30,w48,w52,w54,w77],[w0,w19,w30,w48,w54,w65,w77],[w0,w19,w30,w48,w54,w77],[w0,w19,w30,w50,w52,w65,w77],[w0,w19,w30,w50,w52,w77],[w0,w19,w31,w40,w44,w54,w77],[w0,w19,w31,w40,w46,w52,w77],[w0,w19,w31,w42,w44,w52,w77],[w0,w19,w32,w40,w44,w54,w71],[w0,w19,w32,w40,w46,w52,w71],[w0,w19,w32,w42,w44,w52,w71],[w0,w19,w33,w38,w40,w62,w65],[w0,w19,w33,w38,w42,w60,w65],[w0,w19,w33,w38,w44,w58,w65],[w0,w19,w33,w38,w46,w56,w65],[w0,w19,w33,w38,w48,w54,w65],[w0,w19,w33,w38,w50,w52,w65],[w0,w19,w33,w40,w42,w60,w71],[w0,w19,w33,w40,w44,w54,w69],[w0,w19,w33,w40,w44,w54,w73],[w0,w19,w33,w40,w44,w54,w87],[w0,w19,w33,w40,w44,w54,w101],[w0,w19,w33,w40,w44,w54,w112],[w0,w19,w33,w40,w44,w54,w120],[w0,w19,w33,w40,w44,w55,w71],[w0,w19,w33,w40,w44,w58,w71],[w0,w19,w33,w40,w44,w62,w71],[w0,w19,w33,w40,w45,w54,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_79 : t6_79.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_80 : BankTree := .block [[w0,w19,w33,w40,w46,w52,w69],[w0,w19,w33,w40,w46,w52,w73],[w0,w19,w33,w40,w46,w52,w87],[w0,w19,w33,w40,w46,w52,w101],[w0,w19,w33,w40,w46,w52,w112],[w0,w19,w33,w40,w46,w52,w120],[w0,w19,w33,w40,w46,w53,w71],[w0,w19,w33,w40,w46,w54,w71],[w0,w19,w33,w40,w46,w56,w71],[w0,w19,w33,w40,w46,w60,w71],[w0,w19,w33,w40,w46,w62,w71],[w0,w19,w33,w40,w47,w52,w71],[w0,w19,w33,w40,w48,w54,w71],[w0,w19,w33,w40,w50,w52,w71],[w0,w19,w33,w40,w52,w62,w71],[w0,w19,w33,w40,w54,w60,w71],[w0,w19,w33,w40,w54,w62,w71],[w0,w19,w33,w40,w60,w62,w71],[w0,w19,w33,w40,w62,w65,w71],[w0,w19,w33,w40,w62,w71],[w0,w19,w33,w41,w44,w54,w71],[w0,w19,w33,w41,w46,w52,w71],[w0,w19,w33,w42,w44,w52,w69],[w0,w19,w33,w42,w44,w52,w73],[w0,w19,w33,w42,w44,w52,w87],[w0,w19,w33,w42,w44,w52,w101],[w0,w19,w33,w42,w44,w52,w112],[w0,w19,w33,w42,w44,w52,w120],[w0,w19,w33,w42,w44,w53,w71],[w0,w19,w33,w42,w44,w54,w71],[w0,w19,w33,w42,w44,w56,w71],[w0,w19,w33,w42,w44,w58,w71],[w0,w19,w33,w42,w44,w60,w71],[w0,w19,w33,w42,w45,w52,w71],[w0,w19,w33,w42,w46,w52,w71],[w0,w19,w33,w42,w48,w52,w71],[w0,w19,w33,w42,w50,w52,w71],[w0,w19,w33,w42,w52,w60,w71],[w0,w19,w33,w42,w60,w65,w71],[w0,w19,w33,w42,w60,w71],[w0,w19,w33,w43,w44,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_80 : t6_80.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_78 : BankTree := .fork [w0,w19,w33,w40,w46,w52,w69] t6_79 t6_80
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_78 : t6_78.rows.all (refuses 5 t5_0)=true := by simp only [t6_78,BankTree.rows,List.all_append,ok_t6_79,ok_t6_80,Bool.true_and]
noncomputable def t6_74 : BankTree := .fork [w0,w19,w30,w44,w52,w58,w77] t6_75 t6_78
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_74 : t6_74.rows.all (refuses 5 t5_0)=true := by simp only [t6_74,BankTree.rows,List.all_append,ok_t6_75,ok_t6_78,Bool.true_and]
noncomputable def t6_66 : BankTree := .fork [w0,w19,w27,w48,w54,w77,w87] t6_67 t6_74
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_66 : t6_66.rows.all (refuses 5 t5_0)=true := by simp only [t6_66,BankTree.rows,List.all_append,ok_t6_67,ok_t6_74,Bool.true_and]
noncomputable def t6_84 : BankTree := .block [[w0,w19,w33,w44,w46,w56,w71],[w0,w19,w33,w44,w48,w54,w71],[w0,w19,w33,w44,w50,w52,w71],[w0,w19,w33,w44,w52,w58,w71],[w0,w19,w33,w44,w54,w56,w71],[w0,w19,w33,w44,w54,w58,w71],[w0,w19,w33,w44,w56,w58,w71],[w0,w19,w33,w44,w58,w65,w71],[w0,w19,w33,w44,w58,w71],[w0,w19,w33,w46,w48,w52,w71],[w0,w19,w33,w46,w50,w52,w71],[w0,w19,w33,w46,w52,w56,w71],[w0,w19,w33,w46,w56,w65,w71],[w0,w19,w33,w46,w56,w71],[w0,w19,w33,w48,w50,w52,w71],[w0,w19,w33,w48,w52,w54,w71],[w0,w19,w33,w48,w54,w65,w71],[w0,w19,w33,w48,w54,w71],[w0,w19,w33,w50,w52,w65,w71],[w0,w19,w33,w50,w52,w71],[w0,w19,w34,w40,w44,w54,w71],[w0,w19,w34,w40,w46,w52,w71],[w0,w19,w34,w42,w44,w52,w71],[w0,w19,w35,w40,w44,w54,w65],[w0,w19,w35,w40,w46,w52,w65],[w0,w19,w35,w42,w44,w52,w65],[w0,w19,w36,w40,w44,w54,w65],[w0,w19,w36,w40,w46,w52,w65],[w0,w19,w36,w42,w44,w52,w65],[w0,w19,w37,w40,w44,w54,w65],[w0,w19,w37,w40,w46,w52,w65],[w0,w19,w37,w42,w44,w52,w65],[w0,w19,w38,w40,w42,w60,w65],[w0,w19,w38,w40,w44,w54,w65],[w0,w19,w38,w40,w44,w54,w67],[w0,w19,w38,w40,w44,w54,w71],[w0,w19,w38,w40,w44,w54,w77],[w0,w19,w38,w40,w44,w54,w87],[w0,w19,w38,w40,w44,w54,w97],[w0,w19,w38,w40,w44,w54,w109]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_84 : t6_84.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_85 : BankTree := .block [[w0,w19,w38,w40,w44,w54,w112],[w0,w19,w38,w40,w44,w54,w115],[w0,w19,w38,w40,w44,w54,w120],[w0,w19,w38,w40,w44,w55,w65],[w0,w19,w38,w40,w44,w58,w65],[w0,w19,w38,w40,w44,w62,w65],[w0,w19,w38,w40,w45,w54,w65],[w0,w19,w38,w40,w46,w52,w65],[w0,w19,w38,w40,w46,w52,w67],[w0,w19,w38,w40,w46,w52,w71],[w0,w19,w38,w40,w46,w52,w77],[w0,w19,w38,w40,w46,w52,w87],[w0,w19,w38,w40,w46,w52,w97],[w0,w19,w38,w40,w46,w52,w109],[w0,w19,w38,w40,w46,w52,w112],[w0,w19,w38,w40,w46,w52,w115],[w0,w19,w38,w40,w46,w52,w120],[w0,w19,w38,w40,w46,w53,w65],[w0,w19,w38,w40,w46,w54,w65],[w0,w19,w38,w40,w46,w56,w65],[w0,w19,w38,w40,w46,w60,w65],[w0,w19,w38,w40,w46,w62,w65],[w0,w19,w38,w40,w47,w52,w65],[w0,w19,w38,w40,w48,w54,w65],[w0,w19,w38,w40,w50,w52,w65],[w0,w19,w38,w40,w52,w62,w65],[w0,w19,w38,w40,w54,w60,w65],[w0,w19,w38,w40,w54,w62,w65],[w0,w19,w38,w40,w60,w62,w65],[w0,w19,w38,w40,w62,w65],[w0,w19,w38,w41,w44,w54,w65],[w0,w19,w38,w41,w46,w52,w65],[w0,w19,w38,w42,w44,w52,w65],[w0,w19,w38,w42,w44,w52,w67],[w0,w19,w38,w42,w44,w52,w71],[w0,w19,w38,w42,w44,w52,w77],[w0,w19,w38,w42,w44,w52,w87],[w0,w19,w38,w42,w44,w52,w97],[w0,w19,w38,w42,w44,w52,w109],[w0,w19,w38,w42,w44,w52,w112]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_85 : t6_85.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_83 : BankTree := .fork [w0,w19,w38,w40,w44,w54,w112] t6_84 t6_85
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_83 : t6_83.rows.all (refuses 5 t5_0)=true := by simp only [t6_83,BankTree.rows,List.all_append,ok_t6_84,ok_t6_85,Bool.true_and]
noncomputable def t6_87 : BankTree := .block [[w0,w19,w38,w42,w44,w52,w115],[w0,w19,w38,w42,w44,w52,w120],[w0,w19,w38,w42,w44,w53,w65],[w0,w19,w38,w42,w44,w54,w65],[w0,w19,w38,w42,w44,w56,w65],[w0,w19,w38,w42,w44,w58,w65],[w0,w19,w38,w42,w44,w60,w65],[w0,w19,w38,w42,w45,w52,w65],[w0,w19,w38,w42,w46,w52,w65],[w0,w19,w38,w42,w48,w52,w65],[w0,w19,w38,w42,w50,w52,w65],[w0,w19,w38,w42,w52,w60,w65],[w0,w19,w38,w42,w60,w65],[w0,w19,w38,w43,w44,w52,w65],[w0,w19,w38,w44,w46,w56,w65],[w0,w19,w38,w44,w48,w54,w65],[w0,w19,w38,w44,w50,w52,w65],[w0,w19,w38,w44,w52,w58,w65],[w0,w19,w38,w44,w54,w56,w65],[w0,w19,w38,w44,w54,w58,w65],[w0,w19,w38,w44,w56,w58,w65],[w0,w19,w38,w44,w58,w65],[w0,w19,w38,w46,w48,w52,w65],[w0,w19,w38,w46,w50,w52,w65],[w0,w19,w38,w46,w52,w56,w65],[w0,w19,w38,w46,w56,w65],[w0,w19,w38,w48,w50,w52,w65],[w0,w19,w38,w48,w52,w54,w65],[w0,w19,w38,w48,w54,w65],[w0,w19,w38,w50,w52,w65],[w0,w19,w39,w40,w44,w54,w65],[w0,w19,w39,w40,w46,w52,w65],[w0,w19,w39,w42,w44,w52,w65],[w0,w20,w27,w40,w44,w54,w87],[w0,w20,w27,w40,w46,w52,w87],[w0,w20,w27,w42,w44,w52,w87],[w0,w20,w30,w40,w44,w54,w77],[w0,w20,w30,w40,w46,w52,w77],[w0,w20,w30,w42,w44,w52,w77],[w0,w20,w33,w40,w44,w54,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_87 : t6_87.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_88 : BankTree := .block [[w0,w20,w33,w40,w46,w52,w71],[w0,w20,w33,w42,w44,w52,w71],[w0,w20,w38,w40,w44,w54,w65],[w0,w20,w38,w40,w46,w52,w65],[w0,w20,w38,w42,w44,w52,w65],[w0,w21,w27,w40,w44,w54,w77],[w0,w21,w27,w40,w46,w52,w77],[w0,w21,w27,w42,w44,w52,w77],[w0,w21,w33,w40,w44,w54,w65],[w0,w21,w33,w40,w46,w52,w65],[w0,w21,w33,w42,w44,w52,w65],[w0,w22,w24,w27,w40,w62,w65],[w0,w22,w24,w27,w42,w60,w65],[w0,w22,w24,w27,w44,w58,w65],[w0,w22,w24,w27,w46,w56,w65],[w0,w22,w24,w27,w48,w54,w65],[w0,w22,w24,w27,w50,w52,w65],[w0,w22,w27,w40,w44,w54,w104],[w0,w22,w27,w40,w46,w52,w104],[w0,w22,w27,w42,w44,w52,w104],[w0,w22,w33,w40,w44,w54,w97],[w0,w22,w33,w40,w46,w52,w97],[w0,w22,w33,w42,w44,w52,w97],[w0,w23,w27,w40,w44,w54,w71],[w0,w23,w27,w40,w46,w52,w71],[w0,w23,w27,w42,w44,w52,w71],[w0,w23,w30,w40,w44,w54,w65],[w0,w23,w30,w40,w46,w52,w65],[w0,w23,w30,w42,w44,w52,w65],[w0,w24,w27,w40,w44,w54,w101],[w0,w24,w27,w40,w46,w52,w101],[w0,w24,w27,w42,w44,w52,w101],[w0,w24,w30,w40,w44,w54,w97],[w0,w24,w30,w40,w46,w52,w97],[w0,w24,w30,w42,w44,w52,w97],[w0,w25,w27,w40,w44,w54,w65],[w0,w25,w27,w40,w46,w52,w65],[w0,w25,w27,w42,w44,w52,w65],[w0,w26,w27,w40,w44,w54,w97],[w0,w26,w27,w40,w46,w52,w97],[w0,w26,w27,w42,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_88 : t6_88.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_86 : BankTree := .fork [w0,w20,w33,w40,w46,w52,w71] t6_87 t6_88
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_86 : t6_86.rows.all (refuses 5 t5_0)=true := by simp only [t6_86,BankTree.rows,List.all_append,ok_t6_87,ok_t6_88,Bool.true_and]
noncomputable def t6_82 : BankTree := .fork [w0,w19,w38,w42,w44,w52,w115] t6_83 t6_86
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_82 : t6_82.rows.all (refuses 5 t5_0)=true := by simp only [t6_82,BankTree.rows,List.all_append,ok_t6_83,ok_t6_86,Bool.true_and]
noncomputable def t6_91 : BankTree := .block [[w0,w27,w38,w40,w44,w54,w97],[w0,w27,w38,w40,w46,w52,w97],[w0,w27,w38,w42,w44,w52,w97],[w0,w27,w40,w44,w54,w87,w97],[w0,w27,w40,w44,w54,w97,w107],[w0,w27,w40,w44,w54,w101,w104],[w0,w27,w40,w46,w52,w87,w97],[w0,w27,w40,w46,w52,w97,w107],[w0,w27,w40,w46,w52,w101,w104],[w0,w27,w42,w44,w52,w87,w97],[w0,w27,w42,w44,w52,w97,w107],[w0,w27,w42,w44,w52,w101,w104],[w0,w30,w33,w40,w44,w54,w97],[w0,w30,w33,w40,w46,w52,w97],[w0,w30,w33,w42,w44,w52,w97],[w2,w6,w16,w19,w27,w66,w91],[w2,w6,w16,w19,w27,w67,w93],[w2,w6,w16,w19,w28,w65,w93],[w2,w6,w16,w19,w28,w67,w91],[w2,w6,w16,w20,w27,w65,w93],[w2,w6,w16,w20,w28,w65,w91],[w2,w6,w16,w27,w40,w61,w98],[w2,w6,w16,w27,w41,w60,w98],[w2,w6,w16,w27,w41,w61,w97],[w2,w6,w16,w27,w44,w57,w98],[w2,w6,w16,w27,w45,w56,w98],[w2,w6,w16,w27,w45,w57,w97],[w2,w6,w16,w27,w48,w53,w98],[w2,w6,w16,w27,w49,w52,w98],[w2,w6,w16,w27,w49,w53,w97],[w2,w6,w16,w28,w40,w60,w98],[w2,w6,w16,w28,w40,w61,w97],[w2,w6,w16,w28,w41,w60,w97],[w2,w6,w16,w28,w44,w56,w98],[w2,w6,w16,w28,w44,w57,w97],[w2,w6,w16,w28,w45,w56,w97],[w2,w6,w16,w28,w48,w52,w98],[w2,w6,w16,w28,w48,w53,w97],[w2,w6,w16,w28,w49,w52,w97],[w2,w6,w18,w19,w27,w67,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_91 : t6_91.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_92 : BankTree := .block [[w2,w6,w18,w19,w28,w65,w91],[w2,w6,w18,w20,w27,w65,w91],[w2,w6,w18,w27,w40,w60,w98],[w2,w6,w18,w27,w44,w56,w98],[w2,w6,w18,w27,w48,w52,w98],[w2,w6,w18,w28,w40,w60,w97],[w2,w6,w18,w28,w44,w56,w97],[w2,w6,w18,w28,w48,w52,w97],[w2,w6,w19,w27,w40,w63,w67],[w2,w6,w19,w27,w41,w62,w67],[w2,w6,w19,w27,w42,w61,w67],[w2,w6,w19,w27,w43,w60,w67],[w2,w6,w19,w27,w44,w59,w67],[w2,w6,w19,w27,w45,w58,w67],[w2,w6,w19,w27,w46,w57,w67],[w2,w6,w19,w27,w47,w56,w67],[w2,w6,w19,w27,w48,w55,w67],[w2,w6,w19,w27,w49,w54,w67],[w2,w6,w19,w27,w50,w53,w67],[w2,w6,w19,w27,w51,w52,w67],[w2,w6,w19,w28,w40,w62,w67],[w2,w6,w19,w28,w40,w63,w65],[w2,w6,w19,w28,w41,w62,w65],[w2,w6,w19,w28,w42,w60,w67],[w2,w6,w19,w28,w42,w61,w65],[w2,w6,w19,w28,w43,w60,w65],[w2,w6,w19,w28,w44,w58,w67],[w2,w6,w19,w28,w44,w59,w65],[w2,w6,w19,w28,w45,w58,w65],[w2,w6,w19,w28,w46,w56,w67],[w2,w6,w19,w28,w46,w57,w65],[w2,w6,w19,w28,w47,w56,w65],[w2,w6,w19,w28,w48,w54,w67],[w2,w6,w19,w28,w48,w55,w65],[w2,w6,w19,w28,w49,w54,w65],[w2,w6,w19,w28,w50,w52,w67],[w2,w6,w19,w28,w50,w53,w65],[w2,w6,w19,w28,w51,w52,w65],[w2,w6,w20,w27,w40,w63,w65],[w2,w6,w20,w27,w41,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_92 : t6_92.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_90 : BankTree := .fork [w2,w6,w18,w19,w28,w65,w91] t6_91 t6_92
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_90 : t6_90.rows.all (refuses 5 t5_0)=true := by simp only [t6_90,BankTree.rows,List.all_append,ok_t6_91,ok_t6_92,Bool.true_and]
noncomputable def t6_94 : BankTree := .block [[w2,w6,w20,w27,w42,w61,w65],[w2,w6,w20,w27,w43,w60,w65],[w2,w6,w20,w27,w44,w59,w65],[w2,w6,w20,w27,w45,w58,w65],[w2,w6,w20,w27,w46,w57,w65],[w2,w6,w20,w27,w47,w56,w65],[w2,w6,w20,w27,w48,w55,w65],[w2,w6,w20,w27,w49,w54,w65],[w2,w6,w20,w27,w50,w53,w65],[w2,w6,w20,w27,w51,w52,w65],[w2,w6,w20,w28,w40,w62,w65],[w2,w6,w20,w28,w42,w60,w65],[w2,w6,w20,w28,w44,w58,w65],[w2,w6,w20,w28,w46,w56,w65],[w2,w6,w20,w28,w48,w54,w65],[w2,w6,w20,w28,w50,w52,w65],[w2,w6,w27,w40,w44,w55,w98],[w2,w6,w27,w40,w45,w54,w98],[w2,w6,w27,w40,w46,w53,w98],[w2,w6,w27,w40,w47,w52,w98],[w2,w6,w27,w41,w44,w54,w98],[w2,w6,w27,w41,w45,w54,w97],[w2,w6,w27,w41,w46,w52,w98],[w2,w6,w27,w41,w46,w53,w97],[w2,w6,w27,w42,w44,w53,w98],[w2,w6,w27,w42,w45,w52,w98],[w2,w6,w27,w42,w45,w53,w97],[w2,w6,w27,w43,w44,w52,w98],[w2,w6,w28,w40,w44,w54,w98],[w2,w6,w28,w40,w44,w55,w97],[w2,w6,w28,w40,w45,w54,w97],[w2,w6,w28,w40,w46,w52,w98],[w2,w6,w28,w40,w46,w53,w97],[w2,w6,w28,w40,w47,w52,w97],[w2,w6,w28,w41,w44,w54,w97],[w2,w6,w28,w41,w46,w52,w97],[w2,w6,w28,w42,w44,w52,w98],[w2,w6,w28,w42,w44,w53,w97],[w2,w6,w28,w42,w45,w52,w97],[w2,w6,w28,w43,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_94 : t6_94.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_95 : BankTree := .block [[w2,w7,w16,w19,w27,w65,w91],[w2,w7,w16,w27,w40,w60,w97],[w2,w7,w16,w27,w44,w56,w97],[w2,w7,w16,w27,w48,w52,w97],[w2,w7,w19,w27,w40,w62,w65],[w2,w7,w19,w27,w42,w60,w65],[w2,w7,w19,w27,w44,w58,w65],[w2,w7,w19,w27,w46,w56,w65],[w2,w7,w19,w27,w48,w54,w65],[w2,w7,w19,w27,w50,w52,w65],[w2,w7,w27,w40,w44,w54,w97],[w2,w7,w27,w40,w46,w52,w97],[w2,w7,w27,w42,w44,w52,w97],[w2,w8,w16,w19,w27,w65,w93],[w2,w8,w16,w20,w27,w65,w91],[w2,w8,w16,w27,w40,w61,w97],[w2,w8,w16,w27,w41,w60,w97],[w2,w8,w16,w27,w44,w57,w97],[w2,w8,w16,w27,w45,w56,w97],[w2,w8,w16,w27,w48,w53,w97],[w2,w8,w16,w27,w49,w52,w97],[w2,w8,w18,w19,w27,w65,w91],[w2,w8,w18,w27,w40,w60,w97],[w2,w8,w18,w27,w44,w56,w97],[w2,w8,w18,w27,w48,w52,w97],[w2,w8,w19,w27,w40,w63,w65],[w2,w8,w19,w27,w41,w62,w65],[w2,w8,w19,w27,w42,w61,w65],[w2,w8,w19,w27,w43,w60,w65],[w2,w8,w19,w27,w44,w59,w65],[w2,w8,w19,w27,w45,w58,w65],[w2,w8,w19,w27,w46,w57,w65],[w2,w8,w19,w27,w47,w56,w65],[w2,w8,w19,w27,w48,w55,w65],[w2,w8,w19,w27,w49,w54,w65],[w2,w8,w19,w27,w50,w53,w65],[w2,w8,w19,w27,w51,w52,w65],[w2,w8,w20,w27,w40,w62,w65],[w2,w8,w20,w27,w42,w60,w65],[w2,w8,w20,w27,w44,w58,w65],[w2,w8,w20,w27,w46,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_95 : t6_95.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_93 : BankTree := .fork [w2,w7,w16,w19,w27,w65,w91] t6_94 t6_95
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_93 : t6_93.rows.all (refuses 5 t5_0)=true := by simp only [t6_93,BankTree.rows,List.all_append,ok_t6_94,ok_t6_95,Bool.true_and]
noncomputable def t6_89 : BankTree := .fork [w2,w6,w20,w27,w42,w61,w65] t6_90 t6_93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_89 : t6_89.rows.all (refuses 5 t5_0)=true := by simp only [t6_89,BankTree.rows,List.all_append,ok_t6_90,ok_t6_93,Bool.true_and]
noncomputable def t6_81 : BankTree := .fork [w0,w27,w38,w40,w44,w54,w97] t6_82 t6_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_81 : t6_81.rows.all (refuses 5 t5_0)=true := by simp only [t6_81,BankTree.rows,List.all_append,ok_t6_82,ok_t6_89,Bool.true_and]
noncomputable def t6_65 : BankTree := .fork [w0,w19,w33,w44,w46,w56,w71] t6_66 t6_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_65 : t6_65.rows.all (refuses 5 t5_0)=true := by simp only [t6_65,BankTree.rows,List.all_append,ok_t6_66,ok_t6_81,Bool.true_and]
noncomputable def t6_100 : BankTree := .block [[w2,w8,w20,w27,w48,w54,w65],[w2,w8,w20,w27,w50,w52,w65],[w2,w8,w27,w40,w44,w55,w97],[w2,w8,w27,w40,w45,w54,w97],[w2,w8,w27,w40,w46,w53,w97],[w2,w8,w27,w40,w47,w52,w97],[w2,w8,w27,w41,w44,w54,w97],[w2,w8,w27,w41,w46,w52,w97],[w2,w8,w27,w42,w44,w53,w97],[w2,w8,w27,w42,w45,w52,w97],[w2,w8,w27,w43,w44,w52,w97],[w2,w16,w19,w27,w40,w61,w79],[w2,w16,w19,w27,w41,w60,w79],[w2,w16,w19,w27,w41,w61,w77],[w2,w16,w19,w27,w44,w57,w79],[w2,w16,w19,w27,w45,w56,w79],[w2,w16,w19,w27,w45,w57,w77],[w2,w16,w19,w27,w48,w53,w79],[w2,w16,w19,w27,w49,w52,w79],[w2,w16,w19,w27,w49,w53,w77],[w2,w16,w19,w28,w40,w61,w77],[w2,w16,w19,w28,w41,w60,w77],[w2,w16,w19,w28,w44,w57,w77],[w2,w16,w19,w28,w45,w56,w77],[w2,w16,w19,w28,w48,w53,w77],[w2,w16,w19,w28,w49,w52,w77],[w2,w16,w19,w33,w40,w61,w67],[w2,w16,w19,w33,w41,w60,w67],[w2,w16,w19,w33,w41,w61,w65],[w2,w16,w19,w33,w44,w57,w67],[w2,w16,w19,w33,w45,w56,w67],[w2,w16,w19,w33,w45,w57,w65],[w2,w16,w19,w33,w48,w53,w67],[w2,w16,w19,w33,w49,w52,w67],[w2,w16,w19,w33,w49,w53,w65],[w2,w16,w19,w34,w40,w61,w65],[w2,w16,w19,w34,w41,w60,w65],[w2,w16,w19,w34,w44,w57,w65],[w2,w16,w19,w34,w45,w56,w65],[w2,w16,w19,w34,w48,w53,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_100 : t6_100.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_101 : BankTree := .block [[w2,w16,w19,w34,w49,w52,w65],[w2,w16,w20,w27,w40,w61,w77],[w2,w16,w20,w27,w41,w60,w77],[w2,w16,w20,w27,w44,w57,w77],[w2,w16,w20,w27,w45,w56,w77],[w2,w16,w20,w27,w48,w53,w77],[w2,w16,w20,w27,w49,w52,w77],[w2,w16,w20,w28,w40,w60,w77],[w2,w16,w20,w28,w44,w56,w77],[w2,w16,w20,w28,w48,w52,w77],[w2,w16,w20,w33,w40,w61,w65],[w2,w16,w20,w33,w41,w60,w65],[w2,w16,w20,w33,w44,w57,w65],[w2,w16,w20,w33,w45,w56,w65],[w2,w16,w20,w33,w48,w53,w65],[w2,w16,w20,w33,w49,w52,w65],[w2,w16,w20,w34,w40,w60,w65],[w2,w16,w20,w34,w44,w56,w65],[w2,w16,w20,w34,w48,w52,w65],[w2,w18,w19,w27,w40,w60,w79],[w2,w18,w19,w27,w44,w56,w79],[w2,w18,w19,w27,w48,w52,w79],[w2,w18,w19,w28,w40,w60,w77],[w2,w18,w19,w28,w44,w56,w77],[w2,w18,w19,w28,w48,w52,w77],[w2,w18,w19,w33,w40,w60,w67],[w2,w18,w19,w33,w44,w56,w67],[w2,w18,w19,w33,w48,w52,w67],[w2,w18,w19,w34,w40,w60,w65],[w2,w18,w19,w34,w44,w56,w65],[w2,w18,w19,w34,w48,w52,w65],[w2,w18,w20,w27,w40,w60,w77],[w2,w18,w20,w27,w44,w56,w77],[w2,w18,w20,w27,w48,w52,w77],[w2,w18,w20,w33,w40,w60,w65],[w2,w18,w20,w33,w44,w56,w65],[w2,w18,w20,w33,w48,w52,w65],[w2,w19,w27,w40,w44,w55,w79],[w2,w19,w27,w40,w45,w54,w79],[w2,w19,w27,w40,w46,w53,w79]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_101 : t6_101.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_99 : BankTree := .fork [w2,w16,w19,w34,w49,w52,w65] t6_100 t6_101
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_99 : t6_99.rows.all (refuses 5 t5_0)=true := by simp only [t6_99,BankTree.rows,List.all_append,ok_t6_100,ok_t6_101,Bool.true_and]
noncomputable def t6_103 : BankTree := .block [[w2,w19,w27,w40,w47,w52,w79],[w2,w19,w27,w41,w44,w54,w79],[w2,w19,w27,w41,w45,w54,w77],[w2,w19,w27,w41,w46,w52,w79],[w2,w19,w27,w41,w46,w53,w77],[w2,w19,w27,w42,w44,w53,w79],[w2,w19,w27,w42,w45,w52,w79],[w2,w19,w27,w42,w45,w53,w77],[w2,w19,w27,w43,w44,w52,w79],[w2,w19,w28,w40,w44,w55,w77],[w2,w19,w28,w40,w45,w54,w77],[w2,w19,w28,w40,w46,w53,w77],[w2,w19,w28,w40,w47,w52,w77],[w2,w19,w28,w41,w44,w54,w77],[w2,w19,w28,w41,w46,w52,w77],[w2,w19,w28,w42,w44,w53,w77],[w2,w19,w28,w42,w45,w52,w77],[w2,w19,w28,w43,w44,w52,w77],[w2,w19,w33,w40,w44,w55,w67],[w2,w19,w33,w40,w45,w54,w67],[w2,w19,w33,w40,w46,w53,w67],[w2,w19,w33,w40,w47,w52,w67],[w2,w19,w33,w41,w44,w54,w67],[w2,w19,w33,w41,w45,w54,w65],[w2,w19,w33,w41,w46,w52,w67],[w2,w19,w33,w41,w46,w53,w65],[w2,w19,w33,w42,w44,w53,w67],[w2,w19,w33,w42,w45,w52,w67],[w2,w19,w33,w42,w45,w53,w65],[w2,w19,w33,w43,w44,w52,w67],[w2,w19,w34,w40,w44,w55,w65],[w2,w19,w34,w40,w45,w54,w65],[w2,w19,w34,w40,w46,w53,w65],[w2,w19,w34,w40,w47,w52,w65],[w2,w19,w34,w41,w44,w54,w65],[w2,w19,w34,w41,w46,w52,w65],[w2,w19,w34,w42,w44,w53,w65],[w2,w19,w34,w42,w45,w52,w65],[w2,w19,w34,w43,w44,w52,w65],[w2,w20,w27,w40,w44,w55,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_103 : t6_103.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_104 : BankTree := .block [[w2,w20,w27,w40,w45,w54,w77],[w2,w20,w27,w40,w46,w53,w77],[w2,w20,w27,w40,w47,w52,w77],[w2,w20,w27,w41,w44,w54,w77],[w2,w20,w27,w41,w46,w52,w77],[w2,w20,w27,w42,w44,w53,w77],[w2,w20,w27,w42,w45,w52,w77],[w2,w20,w27,w43,w44,w52,w77],[w2,w20,w28,w40,w44,w54,w77],[w2,w20,w28,w40,w46,w52,w77],[w2,w20,w28,w42,w44,w52,w77],[w2,w20,w33,w40,w44,w55,w65],[w2,w20,w33,w40,w45,w54,w65],[w2,w20,w33,w40,w46,w53,w65],[w2,w20,w33,w40,w47,w52,w65],[w2,w20,w33,w41,w44,w54,w65],[w2,w20,w33,w41,w46,w52,w65],[w2,w20,w33,w42,w44,w53,w65],[w2,w20,w33,w42,w45,w52,w65],[w2,w20,w33,w43,w44,w52,w65],[w2,w20,w34,w40,w44,w54,w65],[w2,w20,w34,w40,w46,w52,w65],[w2,w20,w34,w42,w44,w52,w65],[w3,w6,w16,w19,w27,w65,w91],[w3,w6,w16,w27,w40,w60,w97],[w3,w6,w16,w27,w44,w56,w97],[w3,w6,w16,w27,w48,w52,w97],[w3,w6,w19,w27,w40,w62,w65],[w3,w6,w19,w27,w42,w60,w65],[w3,w6,w19,w27,w44,w58,w65],[w3,w6,w19,w27,w46,w56,w65],[w3,w6,w19,w27,w48,w54,w65],[w3,w6,w19,w27,w50,w52,w65],[w3,w6,w27,w40,w44,w54,w97],[w3,w6,w27,w40,w46,w52,w97],[w3,w6,w27,w42,w44,w52,w97],[w3,w16,w19,w27,w40,w60,w77],[w3,w16,w19,w27,w44,w56,w77],[w3,w16,w19,w27,w48,w52,w77],[w3,w16,w19,w33,w40,w60,w65],[w3,w16,w19,w33,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_104 : t6_104.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_102 : BankTree := .fork [w2,w20,w27,w40,w45,w54,w77] t6_103 t6_104
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_102 : t6_102.rows.all (refuses 5 t5_0)=true := by simp only [t6_102,BankTree.rows,List.all_append,ok_t6_103,ok_t6_104,Bool.true_and]
noncomputable def t6_98 : BankTree := .fork [w2,w19,w27,w40,w47,w52,w79] t6_99 t6_102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_98 : t6_98.rows.all (refuses 5 t5_0)=true := by simp only [t6_98,BankTree.rows,List.all_append,ok_t6_99,ok_t6_102,Bool.true_and]
noncomputable def t6_107 : BankTree := .block [[w3,w16,w19,w33,w48,w52,w65],[w3,w19,w27,w40,w44,w54,w77],[w3,w19,w27,w40,w46,w52,w77],[w3,w19,w27,w42,w44,w52,w77],[w3,w19,w33,w40,w44,w54,w65],[w3,w19,w33,w40,w46,w52,w65],[w3,w19,w33,w42,w44,w52,w65],[w4,w6,w16,w19,w27,w65,w93],[w4,w6,w16,w20,w27,w65,w91],[w4,w6,w16,w27,w40,w61,w97],[w4,w6,w16,w27,w41,w60,w97],[w4,w6,w16,w27,w44,w57,w97],[w4,w6,w16,w27,w45,w56,w97],[w4,w6,w16,w27,w48,w53,w97],[w4,w6,w16,w27,w49,w52,w97],[w4,w6,w18,w19,w27,w65,w91],[w4,w6,w18,w27,w40,w60,w97],[w4,w6,w18,w27,w44,w56,w97],[w4,w6,w18,w27,w48,w52,w97],[w4,w6,w19,w27,w40,w63,w65],[w4,w6,w19,w27,w41,w62,w65],[w4,w6,w19,w27,w42,w61,w65],[w4,w6,w19,w27,w43,w60,w65],[w4,w6,w19,w27,w44,w59,w65],[w4,w6,w19,w27,w45,w58,w65],[w4,w6,w19,w27,w46,w57,w65],[w4,w6,w19,w27,w47,w56,w65],[w4,w6,w19,w27,w48,w55,w65],[w4,w6,w19,w27,w49,w54,w65],[w4,w6,w19,w27,w50,w53,w65],[w4,w6,w19,w27,w51,w52,w65],[w4,w6,w20,w27,w40,w62,w65],[w4,w6,w20,w27,w42,w60,w65],[w4,w6,w20,w27,w44,w58,w65],[w4,w6,w20,w27,w46,w56,w65],[w4,w6,w20,w27,w48,w54,w65],[w4,w6,w20,w27,w50,w52,w65],[w4,w6,w27,w40,w44,w55,w97],[w4,w6,w27,w40,w45,w54,w97],[w4,w6,w27,w40,w46,w53,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_107 : t6_107.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_108 : BankTree := .block [[w4,w6,w27,w40,w47,w52,w97],[w4,w6,w27,w41,w44,w54,w97],[w4,w6,w27,w41,w46,w52,w97],[w4,w6,w27,w42,w44,w53,w97],[w4,w6,w27,w42,w45,w52,w97],[w4,w6,w27,w43,w44,w52,w97],[w4,w8,w16,w19,w27,w65,w91],[w4,w8,w16,w27,w40,w60,w97],[w4,w8,w16,w27,w44,w56,w97],[w4,w8,w16,w27,w48,w52,w97],[w4,w8,w19,w27,w40,w62,w65],[w4,w8,w19,w27,w42,w60,w65],[w4,w8,w19,w27,w44,w58,w65],[w4,w8,w19,w27,w46,w56,w65],[w4,w8,w19,w27,w48,w54,w65],[w4,w8,w19,w27,w50,w52,w65],[w4,w8,w27,w40,w44,w54,w97],[w4,w8,w27,w40,w46,w52,w97],[w4,w8,w27,w42,w44,w52,w97],[w4,w16,w19,w27,w40,w61,w77],[w4,w16,w19,w27,w41,w60,w77],[w4,w16,w19,w27,w44,w57,w77],[w4,w16,w19,w27,w45,w56,w77],[w4,w16,w19,w27,w48,w53,w77],[w4,w16,w19,w27,w49,w52,w77],[w4,w16,w19,w33,w40,w61,w65],[w4,w16,w19,w33,w41,w60,w65],[w4,w16,w19,w33,w44,w57,w65],[w4,w16,w19,w33,w45,w56,w65],[w4,w16,w19,w33,w48,w53,w65],[w4,w16,w19,w33,w49,w52,w65],[w4,w16,w20,w27,w40,w60,w77],[w4,w16,w20,w27,w44,w56,w77],[w4,w16,w20,w27,w48,w52,w77],[w4,w16,w20,w33,w40,w60,w65],[w4,w16,w20,w33,w44,w56,w65],[w4,w16,w20,w33,w48,w52,w65],[w4,w18,w19,w27,w40,w60,w77],[w4,w18,w19,w27,w44,w56,w77],[w4,w18,w19,w27,w48,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_108 : t6_108.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_106 : BankTree := .fork [w4,w6,w27,w40,w47,w52,w97] t6_107 t6_108
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_106 : t6_106.rows.all (refuses 5 t5_0)=true := by simp only [t6_106,BankTree.rows,List.all_append,ok_t6_107,ok_t6_108,Bool.true_and]
noncomputable def t6_110 : BankTree := .block [[w4,w18,w19,w33,w40,w60,w65],[w4,w18,w19,w33,w44,w56,w65],[w4,w18,w19,w33,w48,w52,w65],[w4,w19,w27,w40,w44,w55,w77],[w4,w19,w27,w40,w45,w54,w77],[w4,w19,w27,w40,w46,w53,w77],[w4,w19,w27,w40,w47,w52,w77],[w4,w19,w27,w41,w44,w54,w77],[w4,w19,w27,w41,w46,w52,w77],[w4,w19,w27,w42,w44,w53,w77],[w4,w19,w27,w42,w45,w52,w77],[w4,w19,w27,w43,w44,w52,w77],[w4,w19,w33,w40,w44,w55,w65],[w4,w19,w33,w40,w45,w54,w65],[w4,w19,w33,w40,w46,w53,w65],[w4,w19,w33,w40,w47,w52,w65],[w4,w19,w33,w41,w44,w54,w65],[w4,w19,w33,w41,w46,w52,w65],[w4,w19,w33,w42,w44,w53,w65],[w4,w19,w33,w42,w45,w52,w65],[w4,w19,w33,w43,w44,w52,w65],[w4,w20,w27,w40,w44,w54,w77],[w4,w20,w27,w40,w46,w52,w77],[w4,w20,w27,w42,w44,w52,w77],[w4,w20,w33,w40,w44,w54,w65],[w4,w20,w33,w40,w46,w52,w65],[w4,w20,w33,w42,w44,w52,w65],[w6,w16,w19,w27,w40,w61,w73],[w6,w16,w19,w27,w41,w60,w73],[w6,w16,w19,w27,w41,w61,w71],[w6,w16,w19,w27,w44,w57,w73],[w6,w16,w19,w27,w45,w56,w73],[w6,w16,w19,w27,w45,w57,w71],[w6,w16,w19,w27,w48,w53,w73],[w6,w16,w19,w27,w49,w52,w73],[w6,w16,w19,w27,w49,w53,w71],[w6,w16,w19,w28,w40,w61,w71],[w6,w16,w19,w28,w41,w60,w71],[w6,w16,w19,w28,w44,w57,w71],[w6,w16,w19,w28,w45,w56,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_110 : t6_110.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_111 : BankTree := .block [[w6,w16,w19,w28,w48,w53,w71],[w6,w16,w19,w28,w49,w52,w71],[w6,w16,w19,w30,w40,w61,w67],[w6,w16,w19,w30,w41,w60,w67],[w6,w16,w19,w30,w41,w61,w65],[w6,w16,w19,w30,w44,w57,w67],[w6,w16,w19,w30,w45,w56,w67],[w6,w16,w19,w30,w45,w57,w65],[w6,w16,w19,w30,w48,w53,w67],[w6,w16,w19,w30,w49,w52,w67],[w6,w16,w19,w30,w49,w53,w65],[w6,w16,w19,w31,w40,w61,w65],[w6,w16,w19,w31,w41,w60,w65],[w6,w16,w19,w31,w44,w57,w65],[w6,w16,w19,w31,w45,w56,w65],[w6,w16,w19,w31,w48,w53,w65],[w6,w16,w19,w31,w49,w52,w65],[w6,w16,w20,w27,w40,w61,w71],[w6,w16,w20,w27,w41,w60,w71],[w6,w16,w20,w27,w44,w57,w71],[w6,w16,w20,w27,w45,w56,w71],[w6,w16,w20,w27,w48,w53,w71],[w6,w16,w20,w27,w49,w52,w71],[w6,w16,w20,w28,w40,w60,w71],[w6,w16,w20,w28,w44,w56,w71],[w6,w16,w20,w28,w48,w52,w71],[w6,w16,w20,w30,w40,w61,w65],[w6,w16,w20,w30,w41,w60,w65],[w6,w16,w20,w30,w44,w57,w65],[w6,w16,w20,w30,w45,w56,w65],[w6,w16,w20,w30,w48,w53,w65],[w6,w16,w20,w30,w49,w52,w65],[w6,w16,w20,w31,w40,w60,w65],[w6,w16,w20,w31,w44,w56,w65],[w6,w16,w20,w31,w48,w52,w65],[w6,w18,w19,w27,w40,w60,w73],[w6,w18,w19,w27,w44,w56,w73],[w6,w18,w19,w27,w48,w52,w73],[w6,w18,w19,w28,w40,w60,w71],[w6,w18,w19,w28,w44,w56,w71],[w6,w18,w19,w28,w48,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_111 : t6_111.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_109 : BankTree := .fork [w6,w16,w19,w28,w48,w53,w71] t6_110 t6_111
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_109 : t6_109.rows.all (refuses 5 t5_0)=true := by simp only [t6_109,BankTree.rows,List.all_append,ok_t6_110,ok_t6_111,Bool.true_and]
noncomputable def t6_105 : BankTree := .fork [w4,w18,w19,w33,w40,w60,w65] t6_106 t6_109
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_105 : t6_105.rows.all (refuses 5 t5_0)=true := by simp only [t6_105,BankTree.rows,List.all_append,ok_t6_106,ok_t6_109,Bool.true_and]
noncomputable def t6_97 : BankTree := .fork [w3,w16,w19,w33,w48,w52,w65] t6_98 t6_105
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_97 : t6_97.rows.all (refuses 5 t5_0)=true := by simp only [t6_97,BankTree.rows,List.all_append,ok_t6_98,ok_t6_105,Bool.true_and]
noncomputable def t6_115 : BankTree := .block [[w6,w18,w19,w30,w40,w60,w67],[w6,w18,w19,w30,w44,w56,w67],[w6,w18,w19,w30,w48,w52,w67],[w6,w18,w19,w31,w40,w60,w65],[w6,w18,w19,w31,w44,w56,w65],[w6,w18,w19,w31,w48,w52,w65],[w6,w18,w20,w27,w40,w60,w71],[w6,w18,w20,w27,w44,w56,w71],[w6,w18,w20,w27,w48,w52,w71],[w6,w18,w20,w30,w40,w60,w65],[w6,w18,w20,w30,w44,w56,w65],[w6,w18,w20,w30,w48,w52,w65],[w6,w19,w27,w40,w44,w55,w73],[w6,w19,w27,w40,w45,w54,w73],[w6,w19,w27,w40,w46,w53,w73],[w6,w19,w27,w40,w47,w52,w73],[w6,w19,w27,w41,w44,w54,w73],[w6,w19,w27,w41,w45,w54,w71],[w6,w19,w27,w41,w46,w52,w73],[w6,w19,w27,w41,w46,w53,w71],[w6,w19,w27,w42,w44,w53,w73],[w6,w19,w27,w42,w45,w52,w73],[w6,w19,w27,w42,w45,w53,w71],[w6,w19,w27,w43,w44,w52,w73],[w6,w19,w28,w40,w44,w55,w71],[w6,w19,w28,w40,w45,w54,w71],[w6,w19,w28,w40,w46,w53,w71],[w6,w19,w28,w40,w47,w52,w71],[w6,w19,w28,w41,w44,w54,w71],[w6,w19,w28,w41,w46,w52,w71],[w6,w19,w28,w42,w44,w53,w71],[w6,w19,w28,w42,w45,w52,w71],[w6,w19,w28,w43,w44,w52,w71],[w6,w19,w30,w40,w44,w55,w67],[w6,w19,w30,w40,w45,w54,w67],[w6,w19,w30,w40,w46,w53,w67],[w6,w19,w30,w40,w47,w52,w67],[w6,w19,w30,w41,w44,w54,w67],[w6,w19,w30,w41,w45,w54,w65],[w6,w19,w30,w41,w46,w52,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_115 : t6_115.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_116 : BankTree := .block [[w6,w19,w30,w41,w46,w53,w65],[w6,w19,w30,w42,w44,w53,w67],[w6,w19,w30,w42,w45,w52,w67],[w6,w19,w30,w42,w45,w53,w65],[w6,w19,w30,w43,w44,w52,w67],[w6,w19,w31,w40,w44,w55,w65],[w6,w19,w31,w40,w45,w54,w65],[w6,w19,w31,w40,w46,w53,w65],[w6,w19,w31,w40,w47,w52,w65],[w6,w19,w31,w41,w44,w54,w65],[w6,w19,w31,w41,w46,w52,w65],[w6,w19,w31,w42,w44,w53,w65],[w6,w19,w31,w42,w45,w52,w65],[w6,w19,w31,w43,w44,w52,w65],[w6,w20,w27,w40,w44,w55,w71],[w6,w20,w27,w40,w45,w54,w71],[w6,w20,w27,w40,w46,w53,w71],[w6,w20,w27,w40,w47,w52,w71],[w6,w20,w27,w41,w44,w54,w71],[w6,w20,w27,w41,w46,w52,w71],[w6,w20,w27,w42,w44,w53,w71],[w6,w20,w27,w42,w45,w52,w71],[w6,w20,w27,w43,w44,w52,w71],[w6,w20,w28,w40,w44,w54,w71],[w6,w20,w28,w40,w46,w52,w71],[w6,w20,w28,w42,w44,w52,w71],[w6,w20,w30,w40,w44,w55,w65],[w6,w20,w30,w40,w45,w54,w65],[w6,w20,w30,w40,w46,w53,w65],[w6,w20,w30,w40,w47,w52,w65],[w6,w20,w30,w41,w44,w54,w65],[w6,w20,w30,w41,w46,w52,w65],[w6,w20,w30,w42,w44,w53,w65],[w6,w20,w30,w42,w45,w52,w65],[w6,w20,w30,w43,w44,w52,w65],[w6,w20,w31,w40,w44,w54,w65],[w6,w20,w31,w40,w46,w52,w65],[w6,w20,w31,w42,w44,w52,w65],[w7,w16,w19,w27,w40,w60,w71],[w7,w16,w19,w27,w44,w56,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_116 : t6_116.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_114 : BankTree := .fork [w6,w19,w30,w41,w46,w53,w65] t6_115 t6_116
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_114 : t6_114.rows.all (refuses 5 t5_0)=true := by simp only [t6_114,BankTree.rows,List.all_append,ok_t6_115,ok_t6_116,Bool.true_and]
noncomputable def t6_118 : BankTree := .block [[w7,w16,w19,w27,w48,w52,w71],[w7,w16,w19,w30,w40,w60,w65],[w7,w16,w19,w30,w44,w56,w65],[w7,w16,w19,w30,w48,w52,w65],[w7,w19,w27,w40,w44,w54,w71],[w7,w19,w27,w40,w46,w52,w71],[w7,w19,w27,w42,w44,w52,w71],[w7,w19,w30,w40,w44,w54,w65],[w7,w19,w30,w40,w46,w52,w65],[w7,w19,w30,w42,w44,w52,w65],[w8,w16,w19,w27,w40,w61,w71],[w8,w16,w19,w27,w41,w60,w71],[w8,w16,w19,w27,w44,w57,w71],[w8,w16,w19,w27,w45,w56,w71],[w8,w16,w19,w27,w48,w53,w71],[w8,w16,w19,w27,w49,w52,w71],[w8,w16,w19,w30,w40,w61,w65],[w8,w16,w19,w30,w41,w60,w65],[w8,w16,w19,w30,w44,w57,w65],[w8,w16,w19,w30,w45,w56,w65],[w8,w16,w19,w30,w48,w53,w65],[w8,w16,w19,w30,w49,w52,w65],[w8,w16,w20,w27,w40,w60,w71],[w8,w16,w20,w27,w44,w56,w71],[w8,w16,w20,w27,w48,w52,w71],[w8,w16,w20,w30,w40,w60,w65],[w8,w16,w20,w30,w44,w56,w65],[w8,w16,w20,w30,w48,w52,w65],[w8,w18,w19,w27,w40,w60,w71],[w8,w18,w19,w27,w44,w56,w71],[w8,w18,w19,w27,w48,w52,w71],[w8,w18,w19,w30,w40,w60,w65],[w8,w18,w19,w30,w44,w56,w65],[w8,w18,w19,w30,w48,w52,w65],[w8,w19,w27,w40,w44,w55,w71],[w8,w19,w27,w40,w45,w54,w71],[w8,w19,w27,w40,w46,w53,w71],[w8,w19,w27,w40,w47,w52,w71],[w8,w19,w27,w41,w44,w54,w71],[w8,w19,w27,w41,w46,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_118 : t6_118.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_119 : BankTree := .block [[w8,w19,w27,w42,w44,w53,w71],[w8,w19,w27,w42,w45,w52,w71],[w8,w19,w27,w43,w44,w52,w71],[w8,w19,w30,w40,w44,w55,w65],[w8,w19,w30,w40,w45,w54,w65],[w8,w19,w30,w40,w46,w53,w65],[w8,w19,w30,w40,w47,w52,w65],[w8,w19,w30,w41,w44,w54,w65],[w8,w19,w30,w41,w46,w52,w65],[w8,w19,w30,w42,w44,w53,w65],[w8,w19,w30,w42,w45,w52,w65],[w8,w19,w30,w43,w44,w52,w65],[w8,w20,w27,w40,w44,w54,w71],[w8,w20,w27,w40,w46,w52,w71],[w8,w20,w27,w42,w44,w52,w71],[w8,w20,w30,w40,w44,w54,w65],[w8,w20,w30,w40,w46,w52,w65],[w8,w20,w30,w42,w44,w52,w65],[w12,w16,w19,w27,w40,w61,w67],[w12,w16,w19,w27,w41,w60,w67],[w12,w16,w19,w27,w41,w61,w65],[w12,w16,w19,w27,w44,w57,w67],[w12,w16,w19,w27,w45,w56,w67],[w12,w16,w19,w27,w45,w57,w65],[w12,w16,w19,w27,w48,w53,w67],[w12,w16,w19,w27,w49,w52,w67],[w12,w16,w19,w27,w49,w53,w65],[w12,w16,w19,w28,w40,w60,w67],[w12,w16,w19,w28,w40,w61,w65],[w12,w16,w19,w28,w41,w60,w65],[w12,w16,w19,w28,w44,w56,w67],[w12,w16,w19,w28,w44,w57,w65],[w12,w16,w19,w28,w45,w56,w65],[w12,w16,w19,w28,w48,w52,w67],[w12,w16,w19,w28,w48,w53,w65],[w12,w16,w19,w28,w49,w52,w65],[w12,w16,w20,w27,w40,w61,w65],[w12,w16,w20,w27,w41,w60,w65],[w12,w16,w20,w27,w44,w57,w65],[w12,w16,w20,w27,w45,w56,w65],[w12,w16,w20,w27,w48,w53,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_119 : t6_119.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_117 : BankTree := .fork [w8,w19,w27,w42,w44,w53,w71] t6_118 t6_119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_117 : t6_117.rows.all (refuses 5 t5_0)=true := by simp only [t6_117,BankTree.rows,List.all_append,ok_t6_118,ok_t6_119,Bool.true_and]
noncomputable def t6_113 : BankTree := .fork [w7,w16,w19,w27,w48,w52,w71] t6_114 t6_117
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_113 : t6_113.rows.all (refuses 5 t5_0)=true := by simp only [t6_113,BankTree.rows,List.all_append,ok_t6_114,ok_t6_117,Bool.true_and]
noncomputable def t6_122 : BankTree := .block [[w12,w16,w20,w27,w49,w52,w65],[w12,w16,w20,w28,w40,w60,w65],[w12,w16,w20,w28,w44,w56,w65],[w12,w16,w20,w28,w48,w52,w65],[w12,w16,w27,w40,w44,w53,w98],[w12,w16,w27,w40,w45,w52,w98],[w12,w16,w27,w40,w45,w53,w97],[w12,w16,w27,w41,w44,w52,w98],[w12,w16,w27,w41,w44,w53,w97],[w12,w16,w27,w41,w45,w52,w97],[w12,w16,w28,w40,w44,w52,w98],[w12,w16,w28,w40,w44,w53,w97],[w12,w16,w28,w40,w45,w52,w97],[w12,w16,w28,w41,w44,w52,w97],[w12,w18,w19,w27,w40,w60,w67],[w12,w18,w19,w27,w44,w56,w67],[w12,w18,w19,w27,w48,w52,w67],[w12,w18,w19,w28,w40,w60,w65],[w12,w18,w19,w28,w44,w56,w65],[w12,w18,w19,w28,w48,w52,w65],[w12,w18,w20,w27,w40,w60,w65],[w12,w18,w20,w27,w44,w56,w65],[w12,w18,w20,w27,w48,w52,w65],[w12,w18,w27,w40,w44,w52,w98],[w12,w18,w28,w40,w44,w52,w97],[w12,w19,w27,w40,w44,w55,w67],[w12,w19,w27,w40,w45,w54,w67],[w12,w19,w27,w40,w46,w53,w67],[w12,w19,w27,w40,w47,w52,w67],[w12,w19,w27,w41,w44,w54,w67],[w12,w19,w27,w41,w45,w54,w65],[w12,w19,w27,w41,w46,w52,w67],[w12,w19,w27,w41,w46,w53,w65],[w12,w19,w27,w42,w44,w53,w67],[w12,w19,w27,w42,w45,w52,w67],[w12,w19,w27,w42,w45,w53,w65],[w12,w19,w27,w43,w44,w52,w67],[w12,w19,w28,w40,w44,w54,w67],[w12,w19,w28,w40,w44,w55,w65],[w12,w19,w28,w40,w45,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_122 : t6_122.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_123 : BankTree := .block [[w12,w19,w28,w40,w46,w52,w67],[w12,w19,w28,w40,w46,w53,w65],[w12,w19,w28,w40,w47,w52,w65],[w12,w19,w28,w41,w44,w54,w65],[w12,w19,w28,w41,w46,w52,w65],[w12,w19,w28,w42,w44,w52,w67],[w12,w19,w28,w42,w44,w53,w65],[w12,w19,w28,w42,w45,w52,w65],[w12,w19,w28,w43,w44,w52,w65],[w12,w20,w27,w40,w44,w55,w65],[w12,w20,w27,w40,w45,w54,w65],[w12,w20,w27,w40,w46,w53,w65],[w12,w20,w27,w40,w47,w52,w65],[w12,w20,w27,w41,w44,w54,w65],[w12,w20,w27,w41,w46,w52,w65],[w12,w20,w27,w42,w44,w53,w65],[w12,w20,w27,w42,w45,w52,w65],[w12,w20,w27,w43,w44,w52,w65],[w12,w20,w28,w40,w44,w54,w65],[w12,w20,w28,w40,w46,w52,w65],[w12,w20,w28,w42,w44,w52,w65],[w13,w16,w19,w27,w40,w60,w65],[w13,w16,w19,w27,w44,w56,w65],[w13,w16,w19,w27,w48,w52,w65],[w13,w16,w27,w40,w44,w52,w97],[w13,w19,w27,w40,w44,w54,w65],[w13,w19,w27,w40,w46,w52,w65],[w13,w19,w27,w42,w44,w52,w65],[w14,w16,w19,w27,w40,w61,w65],[w14,w16,w19,w27,w41,w60,w65],[w14,w16,w19,w27,w44,w57,w65],[w14,w16,w19,w27,w45,w56,w65],[w14,w16,w19,w27,w48,w53,w65],[w14,w16,w19,w27,w49,w52,w65],[w14,w16,w20,w27,w40,w60,w65],[w14,w16,w20,w27,w44,w56,w65],[w14,w16,w20,w27,w48,w52,w65],[w14,w16,w27,w40,w44,w53,w97],[w14,w16,w27,w40,w45,w52,w97],[w14,w16,w27,w41,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_123 : t6_123.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_121 : BankTree := .fork [w12,w19,w28,w40,w46,w52,w67] t6_122 t6_123
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_121 : t6_121.rows.all (refuses 5 t5_0)=true := by simp only [t6_121,BankTree.rows,List.all_append,ok_t6_122,ok_t6_123,Bool.true_and]
noncomputable def t6_125 : BankTree := .block [[w14,w18,w19,w27,w40,w60,w65],[w14,w18,w19,w27,w44,w56,w65],[w14,w18,w19,w27,w48,w52,w65],[w14,w18,w27,w40,w44,w52,w97],[w14,w19,w27,w40,w44,w55,w65],[w14,w19,w27,w40,w45,w54,w65],[w14,w19,w27,w40,w46,w53,w65],[w14,w19,w27,w40,w47,w52,w65],[w14,w19,w27,w41,w44,w54,w65],[w14,w19,w27,w41,w46,w52,w65],[w14,w19,w27,w42,w44,w53,w65],[w14,w19,w27,w42,w45,w52,w65],[w14,w19,w27,w43,w44,w52,w65],[w14,w20,w27,w40,w44,w54,w65],[w14,w20,w27,w40,w46,w52,w65],[w14,w20,w27,w42,w44,w52,w65],[w16,w19,w27,w40,w44,w53,w89],[w16,w19,w27,w40,w45,w52,w89],[w16,w19,w27,w40,w45,w53,w87],[w16,w19,w27,w41,w44,w52,w89],[w16,w19,w27,w41,w44,w53,w87],[w16,w19,w27,w41,w45,w52,w87],[w16,w19,w28,w40,w44,w53,w87],[w16,w19,w28,w40,w45,w52,w87],[w16,w19,w28,w41,w44,w52,w87],[w16,w19,w30,w40,w44,w53,w79],[w16,w19,w30,w40,w45,w52,w79],[w16,w19,w30,w40,w45,w53,w77],[w16,w19,w30,w41,w44,w52,w79],[w16,w19,w30,w41,w44,w53,w77],[w16,w19,w30,w41,w45,w52,w77],[w16,w19,w31,w40,w44,w53,w77],[w16,w19,w31,w40,w45,w52,w77],[w16,w19,w31,w41,w44,w52,w77],[w16,w19,w33,w40,w44,w53,w73],[w16,w19,w33,w40,w45,w52,w73],[w16,w19,w33,w40,w45,w53,w71],[w16,w19,w33,w41,w44,w52,w73],[w16,w19,w33,w41,w44,w53,w71],[w16,w19,w33,w41,w45,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_125 : t6_125.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_126 : BankTree := .block [[w16,w19,w34,w40,w44,w53,w71],[w16,w19,w34,w40,w45,w52,w71],[w16,w19,w34,w41,w44,w52,w71],[w16,w19,w38,w40,w44,w53,w67],[w16,w19,w38,w40,w45,w52,w67],[w16,w19,w38,w40,w45,w53,w65],[w16,w19,w38,w41,w44,w52,w67],[w16,w19,w38,w41,w44,w53,w65],[w16,w19,w38,w41,w45,w52,w65],[w16,w19,w39,w40,w44,w53,w65],[w16,w19,w39,w40,w45,w52,w65],[w16,w19,w39,w41,w44,w52,w65],[w16,w20,w27,w40,w44,w53,w87],[w16,w20,w27,w40,w45,w52,w87],[w16,w20,w27,w41,w44,w52,w87],[w16,w20,w28,w40,w44,w52,w87],[w16,w20,w30,w40,w44,w53,w77],[w16,w20,w30,w40,w45,w52,w77],[w16,w20,w30,w41,w44,w52,w77],[w16,w20,w31,w40,w44,w52,w77],[w16,w20,w33,w40,w44,w53,w71],[w16,w20,w33,w40,w45,w52,w71],[w16,w20,w33,w41,w44,w52,w71],[w16,w20,w34,w40,w44,w52,w71],[w16,w20,w38,w40,w44,w53,w65],[w16,w20,w38,w40,w45,w52,w65],[w16,w20,w38,w41,w44,w52,w65],[w16,w20,w39,w40,w44,w52,w65],[w17,w19,w27,w40,w44,w52,w65],[w18,w19,w27,w40,w44,w52,w89],[w18,w19,w28,w40,w44,w52,w87],[w18,w19,w30,w40,w44,w52,w79],[w18,w19,w31,w40,w44,w52,w77],[w18,w19,w33,w40,w44,w52,w73],[w18,w19,w34,w40,w44,w52,w71],[w18,w19,w38,w40,w44,w52,w67],[w18,w19,w39,w40,w44,w52,w65],[w18,w20,w27,w40,w44,w52,w87],[w18,w20,w30,w40,w44,w52,w77],[w18,w20,w33,w40,w44,w52,w71],[w18,w20,w38,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_126 : t6_126.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_124 : BankTree := .fork [w16,w19,w34,w40,w44,w53,w71] t6_125 t6_126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_124 : t6_124.rows.all (refuses 5 t5_0)=true := by simp only [t6_124,BankTree.rows,List.all_append,ok_t6_125,ok_t6_126,Bool.true_and]
noncomputable def t6_120 : BankTree := .fork [w14,w18,w19,w27,w40,w60,w65] t6_121 t6_124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_120 : t6_120.rows.all (refuses 5 t5_0)=true := by simp only [t6_120,BankTree.rows,List.all_append,ok_t6_121,ok_t6_124,Bool.true_and]
noncomputable def t6_112 : BankTree := .fork [w12,w16,w20,w27,w49,w52,w65] t6_113 t6_120
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_112 : t6_112.rows.all (refuses 5 t5_0)=true := by simp only [t6_112,BankTree.rows,List.all_append,ok_t6_113,ok_t6_120,Bool.true_and]
noncomputable def t6_96 : BankTree := .fork [w6,w18,w19,w30,w40,w60,w67] t6_97 t6_112
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_96 : t6_96.rows.all (refuses 5 t5_0)=true := by simp only [t6_96,BankTree.rows,List.all_append,ok_t6_97,ok_t6_112,Bool.true_and]
noncomputable def t6_64 : BankTree := .fork [w2,w8,w20,w27,w48,w54,w65] t6_65 t6_96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_64 : t6_64.rows.all (refuses 5 t5_0)=true := by simp only [t6_64,BankTree.rows,List.all_append,ok_t6_65,ok_t6_96,Bool.true_and]
noncomputable def t6_0 : BankTree := .fork [w0,w16,w27,w40,w44,w52,w106] t6_1 t6_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_0 : t6_0.rows.all (refuses 5 t5_0)=true := by simp only [t6_0,BankTree.rows,List.all_append,ok_t6_1,ok_t6_64,Bool.true_and]
theorem safe6 : Safe 6 t6_0 := certify 5 t5_0 t6_0 safe5 ok_t6_0
noncomputable def t7_6 : BankTree := .block [[w0,w1,w6,w16,w19,w27,w65,w91],[w0,w1,w6,w16,w27,w40,w60,w97],[w0,w1,w6,w16,w27,w44,w56,w97],[w0,w1,w6,w16,w27,w48,w52,w97],[w0,w1,w6,w19,w27,w40,w62,w65],[w0,w1,w6,w19,w27,w42,w60,w65],[w0,w1,w6,w19,w27,w44,w58,w65],[w0,w1,w6,w19,w27,w46,w56,w65],[w0,w1,w6,w19,w27,w48,w54,w65],[w0,w1,w6,w19,w27,w50,w52,w65],[w0,w1,w6,w27,w40,w44,w54,w97],[w0,w1,w6,w27,w40,w46,w52,w97],[w0,w1,w6,w27,w42,w44,w52,w97],[w0,w1,w16,w19,w27,w40,w60,w77],[w0,w1,w16,w19,w27,w44,w56,w77],[w0,w1,w16,w19,w27,w48,w52,w77],[w0,w1,w16,w19,w33,w40,w60,w65],[w0,w1,w16,w19,w33,w44,w56,w65],[w0,w1,w16,w19,w33,w48,w52,w65],[w0,w1,w19,w27,w40,w44,w54,w77],[w0,w1,w19,w27,w40,w46,w52,w77],[w0,w1,w19,w27,w42,w44,w52,w77],[w0,w1,w19,w33,w40,w44,w54,w65],[w0,w1,w19,w33,w40,w46,w52,w65],[w0,w1,w19,w33,w42,w44,w52,w65],[w0,w2,w5,w16,w19,w27,w65,w91]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_6 : t7_6.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_7 : BankTree := .block [[w0,w2,w5,w16,w27,w40,w60,w97],[w0,w2,w5,w16,w27,w44,w56,w97],[w0,w2,w5,w16,w27,w48,w52,w97],[w0,w2,w5,w19,w27,w40,w62,w65],[w0,w2,w5,w19,w27,w42,w60,w65],[w0,w2,w5,w19,w27,w44,w58,w65],[w0,w2,w5,w19,w27,w46,w56,w65],[w0,w2,w5,w19,w27,w48,w54,w65],[w0,w2,w5,w19,w27,w50,w52,w65],[w0,w2,w5,w27,w40,w44,w54,w97],[w0,w2,w5,w27,w40,w46,w52,w97],[w0,w2,w5,w27,w42,w44,w52,w97],[w0,w2,w6,w16,w19,w27,w64,w91],[w0,w2,w6,w16,w19,w27,w65,w91],[w0,w2,w6,w16,w19,w27,w65,w93],[w0,w2,w6,w16,w19,w27,w65,w94],[w0,w2,w6,w16,w19,w27,w67,w91],[w0,w2,w6,w16,w19,w27,w71,w91],[w0,w2,w6,w16,w19,w27,w77,w91],[w0,w2,w6,w16,w19,w27,w91,w97],[w0,w2,w6,w16,w19,w27,w91,w109],[w0,w2,w6,w16,w19,w28,w65,w91],[w0,w2,w6,w16,w19,w30,w65,w91],[w0,w2,w6,w16,w19,w33,w65,w91],[w0,w2,w6,w16,w20,w27,w65,w91],[w0,w2,w6,w16,w27,w40,w60,w98]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_7 : t7_7.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_5 : BankTree := .fork [w0,w2,w5,w16,w27,w40,w60,w97] t7_6 t7_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_5 : t7_5.rows.all (refuses 6 t6_0)=true := by simp only [t7_5,BankTree.rows,List.all_append,ok_t7_6,ok_t7_7,Bool.true_and]
noncomputable def t7_9 : BankTree := .block [[w0,w2,w6,w16,w27,w40,w61,w97],[w0,w2,w6,w16,w27,w40,w62,w97],[w0,w2,w6,w16,w27,w40,w91,w97],[w0,w2,w6,w16,w27,w41,w60,w97],[w0,w2,w6,w16,w27,w42,w60,w97],[w0,w2,w6,w16,w27,w44,w56,w98],[w0,w2,w6,w16,w27,w44,w57,w97],[w0,w2,w6,w16,w27,w44,w58,w97],[w0,w2,w6,w16,w27,w44,w91,w97],[w0,w2,w6,w16,w27,w45,w56,w97],[w0,w2,w6,w16,w27,w46,w56,w97],[w0,w2,w6,w16,w27,w48,w52,w98],[w0,w2,w6,w16,w27,w48,w53,w97],[w0,w2,w6,w16,w27,w48,w54,w97],[w0,w2,w6,w16,w27,w48,w56,w97],[w0,w2,w6,w16,w27,w48,w60,w97],[w0,w2,w6,w16,w27,w48,w91,w97],[w0,w2,w6,w16,w27,w49,w52,w97],[w0,w2,w6,w16,w27,w50,w52,w97],[w0,w2,w6,w16,w27,w52,w91,w97],[w0,w2,w6,w16,w27,w56,w60,w97],[w0,w2,w6,w16,w27,w56,w91,w97],[w0,w2,w6,w16,w27,w60,w91,w97],[w0,w2,w6,w16,w27,w65,w91,w97],[w0,w2,w6,w16,w27,w91,w97],[w0,w2,w6,w16,w28,w40,w60,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_9 : t7_9.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_10 : BankTree := .block [[w0,w2,w6,w16,w28,w44,w56,w97],[w0,w2,w6,w16,w28,w48,w52,w97],[w0,w2,w6,w18,w19,w27,w65,w91],[w0,w2,w6,w18,w27,w40,w60,w97],[w0,w2,w6,w18,w27,w44,w56,w97],[w0,w2,w6,w18,w27,w48,w52,w97],[w0,w2,w6,w19,w27,w40,w62,w65],[w0,w2,w6,w19,w27,w40,w62,w67],[w0,w2,w6,w19,w27,w40,w62,w71],[w0,w2,w6,w19,w27,w40,w62,w77],[w0,w2,w6,w19,w27,w40,w62,w97],[w0,w2,w6,w19,w27,w40,w62,w109],[w0,w2,w6,w19,w27,w40,w63,w65],[w0,w2,w6,w19,w27,w40,w65,w94],[w0,w2,w6,w19,w27,w41,w62,w65],[w0,w2,w6,w19,w27,w42,w60,w67],[w0,w2,w6,w19,w27,w42,w60,w71],[w0,w2,w6,w19,w27,w42,w60,w77],[w0,w2,w6,w19,w27,w42,w60,w97],[w0,w2,w6,w19,w27,w42,w60,w109],[w0,w2,w6,w19,w27,w42,w61,w65],[w0,w2,w6,w19,w27,w42,w62,w65],[w0,w2,w6,w19,w27,w42,w65,w91],[w0,w2,w6,w19,w27,w42,w65,w94],[w0,w2,w6,w19,w27,w43,w60,w65],[w0,w2,w6,w19,w27,w44,w58,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_10 : t7_10.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_8 : BankTree := .fork [w0,w2,w6,w16,w28,w44,w56,w97] t7_9 t7_10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_8 : t7_8.rows.all (refuses 6 t6_0)=true := by simp only [t7_8,BankTree.rows,List.all_append,ok_t7_9,ok_t7_10,Bool.true_and]
noncomputable def t7_4 : BankTree := .fork [w0,w2,w6,w16,w27,w40,w61,w97] t7_5 t7_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_4 : t7_4.rows.all (refuses 6 t6_0)=true := by simp only [t7_4,BankTree.rows,List.all_append,ok_t7_5,ok_t7_8,Bool.true_and]
noncomputable def t7_13 : BankTree := .block [[w0,w2,w6,w19,w27,w44,w58,w67],[w0,w2,w6,w19,w27,w44,w58,w71],[w0,w2,w6,w19,w27,w44,w58,w77],[w0,w2,w6,w19,w27,w44,w58,w97],[w0,w2,w6,w19,w27,w44,w58,w109],[w0,w2,w6,w19,w27,w44,w59,w65],[w0,w2,w6,w19,w27,w44,w65,w94],[w0,w2,w6,w19,w27,w45,w58,w65],[w0,w2,w6,w19,w27,w46,w56,w67],[w0,w2,w6,w19,w27,w46,w56,w71],[w0,w2,w6,w19,w27,w46,w56,w77],[w0,w2,w6,w19,w27,w46,w56,w97],[w0,w2,w6,w19,w27,w46,w56,w109],[w0,w2,w6,w19,w27,w46,w57,w65],[w0,w2,w6,w19,w27,w46,w58,w65],[w0,w2,w6,w19,w27,w46,w65,w91],[w0,w2,w6,w19,w27,w46,w65,w94],[w0,w2,w6,w19,w27,w47,w56,w65],[w0,w2,w6,w19,w27,w48,w54,w67],[w0,w2,w6,w19,w27,w48,w54,w71],[w0,w2,w6,w19,w27,w48,w54,w77],[w0,w2,w6,w19,w27,w48,w54,w97],[w0,w2,w6,w19,w27,w48,w54,w109],[w0,w2,w6,w19,w27,w48,w55,w65],[w0,w2,w6,w19,w27,w48,w58,w65],[w0,w2,w6,w19,w27,w48,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_13 : t7_13.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_14 : BankTree := .block [[w0,w2,w6,w19,w27,w48,w65,w94],[w0,w2,w6,w19,w27,w49,w54,w65],[w0,w2,w6,w19,w27,w50,w52,w65],[w0,w2,w6,w19,w27,w50,w52,w67],[w0,w2,w6,w19,w27,w50,w52,w71],[w0,w2,w6,w19,w27,w50,w52,w77],[w0,w2,w6,w19,w27,w50,w52,w97],[w0,w2,w6,w19,w27,w50,w52,w109],[w0,w2,w6,w19,w27,w50,w53,w65],[w0,w2,w6,w19,w27,w50,w54,w65],[w0,w2,w6,w19,w27,w50,w56,w65],[w0,w2,w6,w19,w27,w50,w58,w65],[w0,w2,w6,w19,w27,w50,w60,w65],[w0,w2,w6,w19,w27,w50,w62,w65],[w0,w2,w6,w19,w27,w50,w65,w91],[w0,w2,w6,w19,w27,w50,w65,w94],[w0,w2,w6,w19,w27,w51,w52,w65],[w0,w2,w6,w19,w27,w52,w65,w94],[w0,w2,w6,w19,w27,w54,w65,w91],[w0,w2,w6,w19,w27,w54,w65,w94],[w0,w2,w6,w19,w27,w56,w62,w65],[w0,w2,w6,w19,w27,w56,w65,w94],[w0,w2,w6,w19,w27,w58,w60,w65],[w0,w2,w6,w19,w27,w58,w62,w65],[w0,w2,w6,w19,w27,w58,w65,w91],[w0,w2,w6,w19,w27,w58,w65,w94]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_14 : t7_14.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_12 : BankTree := .fork [w0,w2,w6,w19,w27,w48,w65,w94] t7_13 t7_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_12 : t7_12.rows.all (refuses 6 t6_0)=true := by simp only [t7_12,BankTree.rows,List.all_append,ok_t7_13,ok_t7_14,Bool.true_and]
noncomputable def t7_16 : BankTree := .block [[w0,w2,w6,w19,w27,w60,w65,w94],[w0,w2,w6,w19,w27,w62,w65,w91],[w0,w2,w6,w19,w27,w62,w65,w94],[w0,w2,w6,w19,w27,w65,w91,w94],[w0,w2,w6,w19,w27,w65,w94],[w0,w2,w6,w19,w28,w40,w62,w65],[w0,w2,w6,w19,w28,w42,w60,w65],[w0,w2,w6,w19,w28,w44,w58,w65],[w0,w2,w6,w19,w28,w46,w56,w65],[w0,w2,w6,w19,w28,w48,w54,w65],[w0,w2,w6,w19,w28,w50,w52,w65],[w0,w2,w6,w19,w30,w40,w62,w65],[w0,w2,w6,w19,w30,w42,w60,w65],[w0,w2,w6,w19,w30,w44,w58,w65],[w0,w2,w6,w19,w30,w46,w56,w65],[w0,w2,w6,w19,w30,w48,w54,w65],[w0,w2,w6,w19,w30,w50,w52,w65],[w0,w2,w6,w19,w33,w40,w62,w65],[w0,w2,w6,w19,w33,w42,w60,w65],[w0,w2,w6,w19,w33,w44,w58,w65],[w0,w2,w6,w19,w33,w46,w56,w65],[w0,w2,w6,w19,w33,w48,w54,w65],[w0,w2,w6,w19,w33,w50,w52,w65],[w0,w2,w6,w20,w27,w40,w62,w65],[w0,w2,w6,w20,w27,w42,w60,w65],[w0,w2,w6,w20,w27,w44,w58,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_16 : t7_16.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_17 : BankTree := .block [[w0,w2,w6,w20,w27,w46,w56,w65],[w0,w2,w6,w20,w27,w48,w54,w65],[w0,w2,w6,w20,w27,w50,w52,w65],[w0,w2,w6,w27,w40,w42,w60,w97],[w0,w2,w6,w27,w40,w44,w54,w98],[w0,w2,w6,w27,w40,w44,w55,w97],[w0,w2,w6,w27,w40,w44,w58,w97],[w0,w2,w6,w27,w40,w44,w62,w97],[w0,w2,w6,w27,w40,w45,w54,w97],[w0,w2,w6,w27,w40,w46,w52,w98],[w0,w2,w6,w27,w40,w46,w53,w97],[w0,w2,w6,w27,w40,w46,w54,w97],[w0,w2,w6,w27,w40,w46,w56,w97],[w0,w2,w6,w27,w40,w46,w60,w97],[w0,w2,w6,w27,w40,w46,w62,w97],[w0,w2,w6,w27,w40,w47,w52,w97],[w0,w2,w6,w27,w40,w48,w54,w97],[w0,w2,w6,w27,w40,w50,w52,w97],[w0,w2,w6,w27,w40,w52,w62,w97],[w0,w2,w6,w27,w40,w54,w60,w97],[w0,w2,w6,w27,w40,w54,w62,w97],[w0,w2,w6,w27,w40,w60,w62,w97],[w0,w2,w6,w27,w40,w62,w65,w97],[w0,w2,w6,w27,w40,w62,w97],[w0,w2,w6,w27,w41,w44,w54,w97],[w0,w2,w6,w27,w41,w46,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_17 : t7_17.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_15 : BankTree := .fork [w0,w2,w6,w20,w27,w46,w56,w65] t7_16 t7_17
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_15 : t7_15.rows.all (refuses 6 t6_0)=true := by simp only [t7_15,BankTree.rows,List.all_append,ok_t7_16,ok_t7_17,Bool.true_and]
noncomputable def t7_11 : BankTree := .fork [w0,w2,w6,w19,w27,w60,w65,w94] t7_12 t7_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_11 : t7_11.rows.all (refuses 6 t6_0)=true := by simp only [t7_11,BankTree.rows,List.all_append,ok_t7_12,ok_t7_15,Bool.true_and]
noncomputable def t7_3 : BankTree := .fork [w0,w2,w6,w19,w27,w44,w58,w67] t7_4 t7_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_3 : t7_3.rows.all (refuses 6 t6_0)=true := by simp only [t7_3,BankTree.rows,List.all_append,ok_t7_4,ok_t7_11,Bool.true_and]
noncomputable def t7_21 : BankTree := .block [[w0,w2,w6,w27,w42,w44,w52,w98],[w0,w2,w6,w27,w42,w44,w53,w97],[w0,w2,w6,w27,w42,w44,w54,w97],[w0,w2,w6,w27,w42,w44,w56,w97],[w0,w2,w6,w27,w42,w44,w58,w97],[w0,w2,w6,w27,w42,w44,w60,w97],[w0,w2,w6,w27,w42,w45,w52,w97],[w0,w2,w6,w27,w42,w46,w52,w97],[w0,w2,w6,w27,w42,w48,w52,w97],[w0,w2,w6,w27,w42,w50,w52,w97],[w0,w2,w6,w27,w42,w52,w60,w97],[w0,w2,w6,w27,w42,w60,w65,w97],[w0,w2,w6,w27,w42,w60,w97],[w0,w2,w6,w27,w43,w44,w52,w97],[w0,w2,w6,w27,w44,w46,w56,w97],[w0,w2,w6,w27,w44,w48,w54,w97],[w0,w2,w6,w27,w44,w50,w52,w97],[w0,w2,w6,w27,w44,w52,w58,w97],[w0,w2,w6,w27,w44,w54,w56,w97],[w0,w2,w6,w27,w44,w54,w58,w97],[w0,w2,w6,w27,w44,w56,w58,w97],[w0,w2,w6,w27,w44,w58,w65,w97],[w0,w2,w6,w27,w44,w58,w97],[w0,w2,w6,w27,w46,w48,w52,w97],[w0,w2,w6,w27,w46,w50,w52,w97],[w0,w2,w6,w27,w46,w52,w56,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_21 : t7_21.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_22 : BankTree := .block [[w0,w2,w6,w27,w46,w56,w65,w97],[w0,w2,w6,w27,w46,w56,w97],[w0,w2,w6,w27,w48,w50,w52,w97],[w0,w2,w6,w27,w48,w52,w54,w97],[w0,w2,w6,w27,w48,w54,w65,w97],[w0,w2,w6,w27,w48,w54,w97],[w0,w2,w6,w27,w50,w52,w65,w97],[w0,w2,w6,w27,w50,w52,w97],[w0,w2,w6,w28,w40,w44,w54,w97],[w0,w2,w6,w28,w40,w46,w52,w97],[w0,w2,w6,w28,w42,w44,w52,w97],[w0,w2,w8,w16,w19,w27,w65,w91],[w0,w2,w8,w16,w27,w40,w60,w97],[w0,w2,w8,w16,w27,w44,w56,w97],[w0,w2,w8,w16,w27,w48,w52,w97],[w0,w2,w8,w19,w27,w40,w62,w65],[w0,w2,w8,w19,w27,w42,w60,w65],[w0,w2,w8,w19,w27,w44,w58,w65],[w0,w2,w8,w19,w27,w46,w56,w65],[w0,w2,w8,w19,w27,w48,w54,w65],[w0,w2,w8,w19,w27,w50,w52,w65],[w0,w2,w8,w27,w40,w44,w54,w97],[w0,w2,w8,w27,w40,w46,w52,w97],[w0,w2,w8,w27,w42,w44,w52,w97],[w0,w2,w12,w16,w19,w27,w65,w91],[w0,w2,w12,w16,w27,w40,w60,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_22 : t7_22.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_20 : BankTree := .fork [w0,w2,w6,w27,w46,w56,w65,w97] t7_21 t7_22
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_20 : t7_20.rows.all (refuses 6 t6_0)=true := by simp only [t7_20,BankTree.rows,List.all_append,ok_t7_21,ok_t7_22,Bool.true_and]
noncomputable def t7_24 : BankTree := .block [[w0,w2,w12,w16,w27,w44,w56,w97],[w0,w2,w12,w16,w27,w48,w52,w97],[w0,w2,w12,w19,w27,w40,w62,w65],[w0,w2,w12,w19,w27,w42,w60,w65],[w0,w2,w12,w19,w27,w44,w58,w65],[w0,w2,w12,w19,w27,w46,w56,w65],[w0,w2,w12,w19,w27,w48,w54,w65],[w0,w2,w12,w19,w27,w50,w52,w65],[w0,w2,w12,w27,w40,w44,w54,w97],[w0,w2,w12,w27,w40,w46,w52,w97],[w0,w2,w12,w27,w42,w44,w52,w97],[w0,w2,w16,w19,w24,w27,w65,w91],[w0,w2,w16,w19,w27,w33,w65,w91],[w0,w2,w16,w19,w27,w40,w60,w75],[w0,w2,w16,w19,w27,w40,w60,w79],[w0,w2,w16,w19,w27,w40,w60,w87],[w0,w2,w16,w19,w27,w40,w60,w104],[w0,w2,w16,w19,w27,w40,w60,w115],[w0,w2,w16,w19,w27,w40,w61,w77],[w0,w2,w16,w19,w27,w40,w62,w77],[w0,w2,w16,w19,w27,w40,w77,w91],[w0,w2,w16,w19,w27,w41,w60,w77],[w0,w2,w16,w19,w27,w42,w60,w77],[w0,w2,w16,w19,w27,w44,w56,w75],[w0,w2,w16,w19,w27,w44,w56,w79],[w0,w2,w16,w19,w27,w44,w56,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_24 : t7_24.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_25 : BankTree := .block [[w0,w2,w16,w19,w27,w44,w56,w104],[w0,w2,w16,w19,w27,w44,w56,w115],[w0,w2,w16,w19,w27,w44,w57,w77],[w0,w2,w16,w19,w27,w44,w58,w77],[w0,w2,w16,w19,w27,w44,w77,w91],[w0,w2,w16,w19,w27,w45,w56,w77],[w0,w2,w16,w19,w27,w46,w56,w77],[w0,w2,w16,w19,w27,w48,w52,w75],[w0,w2,w16,w19,w27,w48,w52,w79],[w0,w2,w16,w19,w27,w48,w52,w87],[w0,w2,w16,w19,w27,w48,w52,w104],[w0,w2,w16,w19,w27,w48,w52,w115],[w0,w2,w16,w19,w27,w48,w53,w77],[w0,w2,w16,w19,w27,w48,w54,w77],[w0,w2,w16,w19,w27,w48,w56,w77],[w0,w2,w16,w19,w27,w48,w60,w77],[w0,w2,w16,w19,w27,w48,w77,w91],[w0,w2,w16,w19,w27,w49,w52,w77],[w0,w2,w16,w19,w27,w50,w52,w77],[w0,w2,w16,w19,w27,w52,w77,w91],[w0,w2,w16,w19,w27,w56,w60,w77],[w0,w2,w16,w19,w27,w56,w77,w91],[w0,w2,w16,w19,w27,w60,w77,w91],[w0,w2,w16,w19,w27,w65,w77,w91],[w0,w2,w16,w19,w27,w77,w91],[w0,w2,w16,w19,w28,w40,w60,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_25 : t7_25.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_23 : BankTree := .fork [w0,w2,w16,w19,w27,w44,w56,w104] t7_24 t7_25
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_23 : t7_23.rows.all (refuses 6 t6_0)=true := by simp only [t7_23,BankTree.rows,List.all_append,ok_t7_24,ok_t7_25,Bool.true_and]
noncomputable def t7_19 : BankTree := .fork [w0,w2,w12,w16,w27,w44,w56,w97] t7_20 t7_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_19 : t7_19.rows.all (refuses 6 t6_0)=true := by simp only [t7_19,BankTree.rows,List.all_append,ok_t7_20,ok_t7_23,Bool.true_and]
noncomputable def t7_28 : BankTree := .block [[w0,w2,w16,w19,w28,w44,w56,w77],[w0,w2,w16,w19,w28,w48,w52,w77],[w0,w2,w16,w19,w30,w40,w60,w77],[w0,w2,w16,w19,w30,w44,w56,w77],[w0,w2,w16,w19,w30,w48,w52,w77],[w0,w2,w16,w19,w32,w40,w60,w65],[w0,w2,w16,w19,w32,w44,w56,w65],[w0,w2,w16,w19,w32,w48,w52,w65],[w0,w2,w16,w19,w33,w40,w60,w67],[w0,w2,w16,w19,w33,w40,w60,w71],[w0,w2,w16,w19,w33,w40,w60,w77],[w0,w2,w16,w19,w33,w40,w60,w97],[w0,w2,w16,w19,w33,w40,w60,w109],[w0,w2,w16,w19,w33,w40,w60,w115],[w0,w2,w16,w19,w33,w40,w61,w65],[w0,w2,w16,w19,w33,w40,w62,w65],[w0,w2,w16,w19,w33,w40,w65,w91],[w0,w2,w16,w19,w33,w41,w60,w65],[w0,w2,w16,w19,w33,w42,w60,w65],[w0,w2,w16,w19,w33,w44,w56,w67],[w0,w2,w16,w19,w33,w44,w56,w71],[w0,w2,w16,w19,w33,w44,w56,w77],[w0,w2,w16,w19,w33,w44,w56,w97],[w0,w2,w16,w19,w33,w44,w56,w109],[w0,w2,w16,w19,w33,w44,w56,w115],[w0,w2,w16,w19,w33,w44,w57,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_28 : t7_28.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_29 : BankTree := .block [[w0,w2,w16,w19,w33,w44,w58,w65],[w0,w2,w16,w19,w33,w44,w65,w91],[w0,w2,w16,w19,w33,w45,w56,w65],[w0,w2,w16,w19,w33,w46,w56,w65],[w0,w2,w16,w19,w33,w48,w52,w67],[w0,w2,w16,w19,w33,w48,w52,w71],[w0,w2,w16,w19,w33,w48,w52,w77],[w0,w2,w16,w19,w33,w48,w52,w97],[w0,w2,w16,w19,w33,w48,w52,w109],[w0,w2,w16,w19,w33,w48,w52,w115],[w0,w2,w16,w19,w33,w48,w53,w65],[w0,w2,w16,w19,w33,w48,w54,w65],[w0,w2,w16,w19,w33,w48,w56,w65],[w0,w2,w16,w19,w33,w48,w60,w65],[w0,w2,w16,w19,w33,w48,w65,w91],[w0,w2,w16,w19,w33,w49,w52,w65],[w0,w2,w16,w19,w33,w50,w52,w65],[w0,w2,w16,w19,w33,w52,w65,w91],[w0,w2,w16,w19,w33,w56,w60,w65],[w0,w2,w16,w19,w33,w56,w65,w91],[w0,w2,w16,w19,w33,w60,w65,w91],[w0,w2,w16,w19,w33,w65,w91],[w0,w2,w16,w19,w34,w40,w60,w65],[w0,w2,w16,w19,w34,w44,w56,w65],[w0,w2,w16,w19,w34,w48,w52,w65],[w0,w2,w16,w19,w38,w40,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_29 : t7_29.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_27 : BankTree := .fork [w0,w2,w16,w19,w33,w44,w58,w65] t7_28 t7_29
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_27 : t7_27.rows.all (refuses 6 t6_0)=true := by simp only [t7_27,BankTree.rows,List.all_append,ok_t7_28,ok_t7_29,Bool.true_and]
noncomputable def t7_31 : BankTree := .block [[w0,w2,w16,w19,w38,w44,w56,w65],[w0,w2,w16,w19,w38,w48,w52,w65],[w0,w2,w16,w20,w27,w40,w60,w77],[w0,w2,w16,w20,w27,w44,w56,w77],[w0,w2,w16,w20,w27,w48,w52,w77],[w0,w2,w16,w20,w33,w40,w60,w65],[w0,w2,w16,w20,w33,w44,w56,w65],[w0,w2,w16,w20,w33,w48,w52,w65],[w0,w2,w16,w23,w27,w40,w60,w65],[w0,w2,w16,w23,w27,w44,w56,w65],[w0,w2,w16,w23,w27,w48,w52,w65],[w0,w2,w16,w24,w27,w40,w60,w97],[w0,w2,w16,w24,w27,w44,w56,w97],[w0,w2,w16,w24,w27,w48,w52,w97],[w0,w2,w16,w27,w33,w40,w60,w97],[w0,w2,w16,w27,w33,w44,w56,w97],[w0,w2,w16,w27,w33,w48,w52,w97],[w0,w2,w16,w27,w40,w44,w52,w103],[w0,w2,w16,w27,w40,w60,w77,w97],[w0,w2,w16,w27,w40,w60,w97,w104],[w0,w2,w16,w27,w44,w56,w77,w97],[w0,w2,w16,w27,w44,w56,w97,w104],[w0,w2,w16,w27,w48,w52,w77,w97],[w0,w2,w16,w27,w48,w52,w97,w104],[w0,w2,w16,w32,w40,w44,w52,w97],[w0,w2,w18,w19,w27,w40,w60,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_31 : t7_31.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_32 : BankTree := .block [[w0,w2,w18,w19,w27,w44,w56,w77],[w0,w2,w18,w19,w27,w48,w52,w77],[w0,w2,w18,w19,w33,w40,w60,w65],[w0,w2,w18,w19,w33,w44,w56,w65],[w0,w2,w18,w19,w33,w48,w52,w65],[w0,w2,w19,w24,w27,w40,w62,w65],[w0,w2,w19,w24,w27,w42,w60,w65],[w0,w2,w19,w24,w27,w44,w58,w65],[w0,w2,w19,w24,w27,w46,w56,w65],[w0,w2,w19,w24,w27,w48,w54,w65],[w0,w2,w19,w24,w27,w50,w52,w65],[w0,w2,w19,w27,w33,w40,w62,w65],[w0,w2,w19,w27,w33,w42,w60,w65],[w0,w2,w19,w27,w33,w44,w58,w65],[w0,w2,w19,w27,w33,w46,w56,w65],[w0,w2,w19,w27,w33,w48,w54,w65],[w0,w2,w19,w27,w33,w50,w52,w65],[w0,w2,w19,w27,w40,w42,w60,w77],[w0,w2,w19,w27,w40,w44,w54,w75],[w0,w2,w19,w27,w40,w44,w54,w79],[w0,w2,w19,w27,w40,w44,w54,w87],[w0,w2,w19,w27,w40,w44,w54,w104],[w0,w2,w19,w27,w40,w44,w54,w115],[w0,w2,w19,w27,w40,w44,w55,w77],[w0,w2,w19,w27,w40,w44,w58,w77],[w0,w2,w19,w27,w40,w44,w62,w77],[w0,w2,w19,w27,w40,w45,w54,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_32 : t7_32.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_30 : BankTree := .fork [w0,w2,w18,w19,w27,w44,w56,w77] t7_31 t7_32
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_30 : t7_30.rows.all (refuses 6 t6_0)=true := by simp only [t7_30,BankTree.rows,List.all_append,ok_t7_31,ok_t7_32,Bool.true_and]
noncomputable def t7_26 : BankTree := .fork [w0,w2,w16,w19,w38,w44,w56,w65] t7_27 t7_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_26 : t7_26.rows.all (refuses 6 t6_0)=true := by simp only [t7_26,BankTree.rows,List.all_append,ok_t7_27,ok_t7_30,Bool.true_and]
noncomputable def t7_18 : BankTree := .fork [w0,w2,w16,w19,w28,w44,w56,w77] t7_19 t7_26
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_18 : t7_18.rows.all (refuses 6 t6_0)=true := by simp only [t7_18,BankTree.rows,List.all_append,ok_t7_19,ok_t7_26,Bool.true_and]
noncomputable def t7_2 : BankTree := .fork [w0,w2,w6,w27,w42,w44,w52,w98] t7_3 t7_18
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_2 : t7_2.rows.all (refuses 6 t6_0)=true := by simp only [t7_2,BankTree.rows,List.all_append,ok_t7_3,ok_t7_18,Bool.true_and]
noncomputable def t7_37 : BankTree := .block [[w0,w2,w19,w27,w40,w46,w52,w75],[w0,w2,w19,w27,w40,w46,w52,w79],[w0,w2,w19,w27,w40,w46,w52,w87],[w0,w2,w19,w27,w40,w46,w52,w104],[w0,w2,w19,w27,w40,w46,w52,w115],[w0,w2,w19,w27,w40,w46,w53,w77],[w0,w2,w19,w27,w40,w46,w54,w77],[w0,w2,w19,w27,w40,w46,w56,w77],[w0,w2,w19,w27,w40,w46,w60,w77],[w0,w2,w19,w27,w40,w46,w62,w77],[w0,w2,w19,w27,w40,w47,w52,w77],[w0,w2,w19,w27,w40,w48,w54,w77],[w0,w2,w19,w27,w40,w50,w52,w77],[w0,w2,w19,w27,w40,w52,w62,w77],[w0,w2,w19,w27,w40,w54,w60,w77],[w0,w2,w19,w27,w40,w54,w62,w77],[w0,w2,w19,w27,w40,w60,w62,w77],[w0,w2,w19,w27,w40,w62,w65,w77],[w0,w2,w19,w27,w40,w62,w77],[w0,w2,w19,w27,w41,w44,w54,w77],[w0,w2,w19,w27,w41,w46,w52,w77],[w0,w2,w19,w27,w42,w44,w52,w75],[w0,w2,w19,w27,w42,w44,w52,w79],[w0,w2,w19,w27,w42,w44,w52,w87],[w0,w2,w19,w27,w42,w44,w52,w104],[w0,w2,w19,w27,w42,w44,w52,w115]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_37 : t7_37.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_38 : BankTree := .block [[w0,w2,w19,w27,w42,w44,w53,w77],[w0,w2,w19,w27,w42,w44,w54,w77],[w0,w2,w19,w27,w42,w44,w56,w77],[w0,w2,w19,w27,w42,w44,w58,w77],[w0,w2,w19,w27,w42,w44,w60,w77],[w0,w2,w19,w27,w42,w45,w52,w77],[w0,w2,w19,w27,w42,w46,w52,w77],[w0,w2,w19,w27,w42,w48,w52,w77],[w0,w2,w19,w27,w42,w50,w52,w77],[w0,w2,w19,w27,w42,w52,w60,w77],[w0,w2,w19,w27,w42,w60,w65,w77],[w0,w2,w19,w27,w42,w60,w77],[w0,w2,w19,w27,w43,w44,w52,w77],[w0,w2,w19,w27,w44,w46,w56,w77],[w0,w2,w19,w27,w44,w48,w54,w77],[w0,w2,w19,w27,w44,w50,w52,w77],[w0,w2,w19,w27,w44,w52,w58,w77],[w0,w2,w19,w27,w44,w54,w56,w77],[w0,w2,w19,w27,w44,w54,w58,w77],[w0,w2,w19,w27,w44,w56,w58,w77],[w0,w2,w19,w27,w44,w58,w65,w77],[w0,w2,w19,w27,w44,w58,w77],[w0,w2,w19,w27,w46,w48,w52,w77],[w0,w2,w19,w27,w46,w50,w52,w77],[w0,w2,w19,w27,w46,w52,w56,w77],[w0,w2,w19,w27,w46,w56,w65,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_38 : t7_38.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_36 : BankTree := .fork [w0,w2,w19,w27,w42,w44,w53,w77] t7_37 t7_38
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_36 : t7_36.rows.all (refuses 6 t6_0)=true := by simp only [t7_36,BankTree.rows,List.all_append,ok_t7_37,ok_t7_38,Bool.true_and]
noncomputable def t7_40 : BankTree := .block [[w0,w2,w19,w27,w46,w56,w77],[w0,w2,w19,w27,w48,w50,w52,w77],[w0,w2,w19,w27,w48,w52,w54,w77],[w0,w2,w19,w27,w48,w54,w65,w77],[w0,w2,w19,w27,w48,w54,w77],[w0,w2,w19,w27,w50,w52,w65,w77],[w0,w2,w19,w27,w50,w52,w77],[w0,w2,w19,w28,w40,w44,w54,w77],[w0,w2,w19,w28,w40,w46,w52,w77],[w0,w2,w19,w28,w42,w44,w52,w77],[w0,w2,w19,w30,w40,w44,w54,w77],[w0,w2,w19,w30,w40,w46,w52,w77],[w0,w2,w19,w30,w42,w44,w52,w77],[w0,w2,w19,w32,w40,w44,w54,w65],[w0,w2,w19,w32,w40,w46,w52,w65],[w0,w2,w19,w32,w42,w44,w52,w65],[w0,w2,w19,w33,w40,w42,w60,w65],[w0,w2,w19,w33,w40,w44,w54,w67],[w0,w2,w19,w33,w40,w44,w54,w71],[w0,w2,w19,w33,w40,w44,w54,w77],[w0,w2,w19,w33,w40,w44,w54,w97],[w0,w2,w19,w33,w40,w44,w54,w109],[w0,w2,w19,w33,w40,w44,w54,w115],[w0,w2,w19,w33,w40,w44,w55,w65],[w0,w2,w19,w33,w40,w44,w58,w65],[w0,w2,w19,w33,w40,w44,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_40 : t7_40.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_41 : BankTree := .block [[w0,w2,w19,w33,w40,w45,w54,w65],[w0,w2,w19,w33,w40,w46,w52,w67],[w0,w2,w19,w33,w40,w46,w52,w71],[w0,w2,w19,w33,w40,w46,w52,w77],[w0,w2,w19,w33,w40,w46,w52,w97],[w0,w2,w19,w33,w40,w46,w52,w109],[w0,w2,w19,w33,w40,w46,w52,w115],[w0,w2,w19,w33,w40,w46,w53,w65],[w0,w2,w19,w33,w40,w46,w54,w65],[w0,w2,w19,w33,w40,w46,w56,w65],[w0,w2,w19,w33,w40,w46,w60,w65],[w0,w2,w19,w33,w40,w46,w62,w65],[w0,w2,w19,w33,w40,w47,w52,w65],[w0,w2,w19,w33,w40,w48,w54,w65],[w0,w2,w19,w33,w40,w50,w52,w65],[w0,w2,w19,w33,w40,w52,w62,w65],[w0,w2,w19,w33,w40,w54,w60,w65],[w0,w2,w19,w33,w40,w54,w62,w65],[w0,w2,w19,w33,w40,w60,w62,w65],[w0,w2,w19,w33,w40,w62,w65],[w0,w2,w19,w33,w41,w44,w54,w65],[w0,w2,w19,w33,w41,w46,w52,w65],[w0,w2,w19,w33,w42,w44,w52,w67],[w0,w2,w19,w33,w42,w44,w52,w71],[w0,w2,w19,w33,w42,w44,w52,w77],[w0,w2,w19,w33,w42,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_41 : t7_41.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_39 : BankTree := .fork [w0,w2,w19,w33,w40,w45,w54,w65] t7_40 t7_41
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_39 : t7_39.rows.all (refuses 6 t6_0)=true := by simp only [t7_39,BankTree.rows,List.all_append,ok_t7_40,ok_t7_41,Bool.true_and]
noncomputable def t7_35 : BankTree := .fork [w0,w2,w19,w27,w46,w56,w77] t7_36 t7_39
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_35 : t7_35.rows.all (refuses 6 t6_0)=true := by simp only [t7_35,BankTree.rows,List.all_append,ok_t7_36,ok_t7_39,Bool.true_and]
noncomputable def t7_44 : BankTree := .block [[w0,w2,w19,w33,w42,w44,w52,w109],[w0,w2,w19,w33,w42,w44,w52,w115],[w0,w2,w19,w33,w42,w44,w53,w65],[w0,w2,w19,w33,w42,w44,w54,w65],[w0,w2,w19,w33,w42,w44,w56,w65],[w0,w2,w19,w33,w42,w44,w58,w65],[w0,w2,w19,w33,w42,w44,w60,w65],[w0,w2,w19,w33,w42,w45,w52,w65],[w0,w2,w19,w33,w42,w46,w52,w65],[w0,w2,w19,w33,w42,w48,w52,w65],[w0,w2,w19,w33,w42,w50,w52,w65],[w0,w2,w19,w33,w42,w52,w60,w65],[w0,w2,w19,w33,w42,w60,w65],[w0,w2,w19,w33,w43,w44,w52,w65],[w0,w2,w19,w33,w44,w46,w56,w65],[w0,w2,w19,w33,w44,w48,w54,w65],[w0,w2,w19,w33,w44,w50,w52,w65],[w0,w2,w19,w33,w44,w52,w58,w65],[w0,w2,w19,w33,w44,w54,w56,w65],[w0,w2,w19,w33,w44,w54,w58,w65],[w0,w2,w19,w33,w44,w56,w58,w65],[w0,w2,w19,w33,w44,w58,w65],[w0,w2,w19,w33,w46,w48,w52,w65],[w0,w2,w19,w33,w46,w50,w52,w65],[w0,w2,w19,w33,w46,w52,w56,w65],[w0,w2,w19,w33,w46,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_44 : t7_44.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_45 : BankTree := .block [[w0,w2,w19,w33,w48,w50,w52,w65],[w0,w2,w19,w33,w48,w52,w54,w65],[w0,w2,w19,w33,w48,w54,w65],[w0,w2,w19,w33,w50,w52,w65],[w0,w2,w19,w34,w40,w44,w54,w65],[w0,w2,w19,w34,w40,w46,w52,w65],[w0,w2,w19,w34,w42,w44,w52,w65],[w0,w2,w19,w38,w40,w44,w54,w65],[w0,w2,w19,w38,w40,w46,w52,w65],[w0,w2,w19,w38,w42,w44,w52,w65],[w0,w2,w20,w27,w40,w44,w54,w77],[w0,w2,w20,w27,w40,w46,w52,w77],[w0,w2,w20,w27,w42,w44,w52,w77],[w0,w2,w20,w33,w40,w44,w54,w65],[w0,w2,w20,w33,w40,w46,w52,w65],[w0,w2,w20,w33,w42,w44,w52,w65],[w0,w2,w23,w27,w40,w44,w54,w65],[w0,w2,w23,w27,w40,w46,w52,w65],[w0,w2,w23,w27,w42,w44,w52,w65],[w0,w2,w24,w27,w40,w44,w54,w97],[w0,w2,w24,w27,w40,w46,w52,w97],[w0,w2,w24,w27,w42,w44,w52,w97],[w0,w2,w27,w33,w40,w44,w54,w97],[w0,w2,w27,w33,w40,w46,w52,w97],[w0,w2,w27,w33,w42,w44,w52,w97],[w0,w2,w27,w40,w44,w54,w77,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_45 : t7_45.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_43 : BankTree := .fork [w0,w2,w19,w33,w48,w50,w52,w65] t7_44 t7_45
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_43 : t7_43.rows.all (refuses 6 t6_0)=true := by simp only [t7_43,BankTree.rows,List.all_append,ok_t7_44,ok_t7_45,Bool.true_and]
noncomputable def t7_47 : BankTree := .block [[w0,w2,w27,w40,w44,w54,w97,w104],[w0,w2,w27,w40,w46,w52,w77,w97],[w0,w2,w27,w40,w46,w52,w97,w104],[w0,w2,w27,w42,w44,w52,w77,w97],[w0,w2,w27,w42,w44,w52,w97,w104],[w0,w4,w6,w16,w19,w27,w65,w91],[w0,w4,w6,w16,w27,w40,w60,w97],[w0,w4,w6,w16,w27,w44,w56,w97],[w0,w4,w6,w16,w27,w48,w52,w97],[w0,w4,w6,w19,w27,w40,w62,w65],[w0,w4,w6,w19,w27,w42,w60,w65],[w0,w4,w6,w19,w27,w44,w58,w65],[w0,w4,w6,w19,w27,w46,w56,w65],[w0,w4,w6,w19,w27,w48,w54,w65],[w0,w4,w6,w19,w27,w50,w52,w65],[w0,w4,w6,w27,w40,w44,w54,w97],[w0,w4,w6,w27,w40,w46,w52,w97],[w0,w4,w6,w27,w42,w44,w52,w97],[w0,w4,w16,w19,w27,w40,w60,w77],[w0,w4,w16,w19,w27,w44,w56,w77],[w0,w4,w16,w19,w27,w48,w52,w77],[w0,w4,w16,w19,w33,w40,w60,w65],[w0,w4,w16,w19,w33,w44,w56,w65],[w0,w4,w16,w19,w33,w48,w52,w65],[w0,w4,w19,w27,w40,w44,w54,w77],[w0,w4,w19,w27,w40,w46,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_47 : t7_47.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_48 : BankTree := .block [[w0,w4,w19,w27,w42,w44,w52,w77],[w0,w4,w19,w33,w40,w44,w54,w65],[w0,w4,w19,w33,w40,w46,w52,w65],[w0,w4,w19,w33,w42,w44,w52,w65],[w0,w5,w16,w19,w27,w40,w60,w71],[w0,w5,w16,w19,w27,w44,w56,w71],[w0,w5,w16,w19,w27,w48,w52,w71],[w0,w5,w16,w19,w30,w40,w60,w65],[w0,w5,w16,w19,w30,w44,w56,w65],[w0,w5,w16,w19,w30,w48,w52,w65],[w0,w5,w19,w27,w40,w44,w54,w71],[w0,w5,w19,w27,w40,w46,w52,w71],[w0,w5,w19,w27,w42,w44,w52,w71],[w0,w5,w19,w30,w40,w44,w54,w65],[w0,w5,w19,w30,w40,w46,w52,w65],[w0,w5,w19,w30,w42,w44,w52,w65],[w0,w6,w12,w16,w19,w27,w65,w91],[w0,w6,w12,w16,w27,w40,w60,w97],[w0,w6,w12,w16,w27,w44,w56,w97],[w0,w6,w12,w16,w27,w48,w52,w97],[w0,w6,w12,w19,w27,w40,w62,w65],[w0,w6,w12,w19,w27,w42,w60,w65],[w0,w6,w12,w19,w27,w44,w58,w65],[w0,w6,w12,w19,w27,w46,w56,w65],[w0,w6,w12,w19,w27,w48,w54,w65],[w0,w6,w12,w19,w27,w50,w52,w65],[w0,w6,w12,w27,w40,w44,w54,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_48 : t7_48.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_46 : BankTree := .fork [w0,w4,w19,w27,w42,w44,w52,w77] t7_47 t7_48
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_46 : t7_46.rows.all (refuses 6 t6_0)=true := by simp only [t7_46,BankTree.rows,List.all_append,ok_t7_47,ok_t7_48,Bool.true_and]
noncomputable def t7_42 : BankTree := .fork [w0,w2,w27,w40,w44,w54,w97,w104] t7_43 t7_46
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_42 : t7_42.rows.all (refuses 6 t6_0)=true := by simp only [t7_42,BankTree.rows,List.all_append,ok_t7_43,ok_t7_46,Bool.true_and]
noncomputable def t7_34 : BankTree := .fork [w0,w2,w19,w33,w42,w44,w52,w109] t7_35 t7_42
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_34 : t7_34.rows.all (refuses 6 t6_0)=true := by simp only [t7_34,BankTree.rows,List.all_append,ok_t7_35,ok_t7_42,Bool.true_and]
noncomputable def t7_52 : BankTree := .block [[w0,w6,w12,w27,w40,w46,w52,w97],[w0,w6,w12,w27,w42,w44,w52,w97],[w0,w6,w16,w19,w22,w27,w65,w91],[w0,w6,w16,w19,w27,w30,w65,w91],[w0,w6,w16,w19,w27,w40,w60,w69],[w0,w6,w16,w19,w27,w40,w60,w73],[w0,w6,w16,w19,w27,w40,w60,w87],[w0,w6,w16,w19,w27,w40,w60,w101],[w0,w6,w16,w19,w27,w40,w60,w112],[w0,w6,w16,w19,w27,w40,w61,w71],[w0,w6,w16,w19,w27,w40,w62,w71],[w0,w6,w16,w19,w27,w40,w71,w91],[w0,w6,w16,w19,w27,w41,w60,w71],[w0,w6,w16,w19,w27,w42,w60,w71],[w0,w6,w16,w19,w27,w44,w56,w69],[w0,w6,w16,w19,w27,w44,w56,w73],[w0,w6,w16,w19,w27,w44,w56,w87],[w0,w6,w16,w19,w27,w44,w56,w101],[w0,w6,w16,w19,w27,w44,w56,w112],[w0,w6,w16,w19,w27,w44,w57,w71],[w0,w6,w16,w19,w27,w44,w58,w71],[w0,w6,w16,w19,w27,w44,w71,w91],[w0,w6,w16,w19,w27,w45,w56,w71],[w0,w6,w16,w19,w27,w46,w56,w71],[w0,w6,w16,w19,w27,w48,w52,w69],[w0,w6,w16,w19,w27,w48,w52,w73]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_52 : t7_52.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_53 : BankTree := .block [[w0,w6,w16,w19,w27,w48,w52,w87],[w0,w6,w16,w19,w27,w48,w52,w101],[w0,w6,w16,w19,w27,w48,w52,w112],[w0,w6,w16,w19,w27,w48,w53,w71],[w0,w6,w16,w19,w27,w48,w54,w71],[w0,w6,w16,w19,w27,w48,w56,w71],[w0,w6,w16,w19,w27,w48,w60,w71],[w0,w6,w16,w19,w27,w48,w71,w91],[w0,w6,w16,w19,w27,w49,w52,w71],[w0,w6,w16,w19,w27,w50,w52,w71],[w0,w6,w16,w19,w27,w52,w71,w91],[w0,w6,w16,w19,w27,w56,w60,w71],[w0,w6,w16,w19,w27,w56,w71,w91],[w0,w6,w16,w19,w27,w60,w71,w91],[w0,w6,w16,w19,w27,w65,w71,w91],[w0,w6,w16,w19,w27,w71,w91],[w0,w6,w16,w19,w28,w40,w60,w71],[w0,w6,w16,w19,w28,w44,w56,w71],[w0,w6,w16,w19,w28,w48,w52,w71],[w0,w6,w16,w19,w29,w40,w60,w65],[w0,w6,w16,w19,w29,w44,w56,w65],[w0,w6,w16,w19,w29,w48,w52,w65],[w0,w6,w16,w19,w30,w40,w60,w67],[w0,w6,w16,w19,w30,w40,w60,w71],[w0,w6,w16,w19,w30,w40,w60,w77],[w0,w6,w16,w19,w30,w40,w60,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_53 : t7_53.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_51 : BankTree := .fork [w0,w6,w16,w19,w27,w48,w52,w87] t7_52 t7_53
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_51 : t7_51.rows.all (refuses 6 t6_0)=true := by simp only [t7_51,BankTree.rows,List.all_append,ok_t7_52,ok_t7_53,Bool.true_and]
noncomputable def t7_55 : BankTree := .block [[w0,w6,w16,w19,w30,w40,w60,w109],[w0,w6,w16,w19,w30,w40,w60,w112],[w0,w6,w16,w19,w30,w40,w61,w65],[w0,w6,w16,w19,w30,w40,w62,w65],[w0,w6,w16,w19,w30,w40,w65,w91],[w0,w6,w16,w19,w30,w41,w60,w65],[w0,w6,w16,w19,w30,w42,w60,w65],[w0,w6,w16,w19,w30,w44,w56,w67],[w0,w6,w16,w19,w30,w44,w56,w71],[w0,w6,w16,w19,w30,w44,w56,w77],[w0,w6,w16,w19,w30,w44,w56,w97],[w0,w6,w16,w19,w30,w44,w56,w109],[w0,w6,w16,w19,w30,w44,w56,w112],[w0,w6,w16,w19,w30,w44,w57,w65],[w0,w6,w16,w19,w30,w44,w58,w65],[w0,w6,w16,w19,w30,w44,w65,w91],[w0,w6,w16,w19,w30,w45,w56,w65],[w0,w6,w16,w19,w30,w46,w56,w65],[w0,w6,w16,w19,w30,w48,w52,w67],[w0,w6,w16,w19,w30,w48,w52,w71],[w0,w6,w16,w19,w30,w48,w52,w77],[w0,w6,w16,w19,w30,w48,w52,w97],[w0,w6,w16,w19,w30,w48,w52,w109],[w0,w6,w16,w19,w30,w48,w52,w112],[w0,w6,w16,w19,w30,w48,w53,w65],[w0,w6,w16,w19,w30,w48,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_55 : t7_55.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_56 : BankTree := .block [[w0,w6,w16,w19,w30,w48,w56,w65],[w0,w6,w16,w19,w30,w48,w60,w65],[w0,w6,w16,w19,w30,w48,w65,w91],[w0,w6,w16,w19,w30,w49,w52,w65],[w0,w6,w16,w19,w30,w50,w52,w65],[w0,w6,w16,w19,w30,w52,w65,w91],[w0,w6,w16,w19,w30,w56,w60,w65],[w0,w6,w16,w19,w30,w56,w65,w91],[w0,w6,w16,w19,w30,w60,w65,w91],[w0,w6,w16,w19,w30,w65,w91],[w0,w6,w16,w19,w31,w40,w60,w65],[w0,w6,w16,w19,w31,w44,w56,w65],[w0,w6,w16,w19,w31,w48,w52,w65],[w0,w6,w16,w19,w33,w40,w60,w71],[w0,w6,w16,w19,w33,w44,w56,w71],[w0,w6,w16,w19,w33,w48,w52,w71],[w0,w6,w16,w19,w38,w40,w60,w65],[w0,w6,w16,w19,w38,w44,w56,w65],[w0,w6,w16,w19,w38,w48,w52,w65],[w0,w6,w16,w20,w27,w40,w60,w71],[w0,w6,w16,w20,w27,w44,w56,w71],[w0,w6,w16,w20,w27,w48,w52,w71],[w0,w6,w16,w20,w30,w40,w60,w65],[w0,w6,w16,w20,w30,w44,w56,w65],[w0,w6,w16,w20,w30,w48,w52,w65],[w0,w6,w16,w21,w27,w40,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_56 : t7_56.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_54 : BankTree := .fork [w0,w6,w16,w19,w30,w48,w56,w65] t7_55 t7_56
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_54 : t7_54.rows.all (refuses 6 t6_0)=true := by simp only [t7_54,BankTree.rows,List.all_append,ok_t7_55,ok_t7_56,Bool.true_and]
noncomputable def t7_50 : BankTree := .fork [w0,w6,w16,w19,w30,w40,w60,w109] t7_51 t7_54
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_50 : t7_50.rows.all (refuses 6 t6_0)=true := by simp only [t7_50,BankTree.rows,List.all_append,ok_t7_51,ok_t7_54,Bool.true_and]
noncomputable def t7_59 : BankTree := .block [[w0,w6,w16,w21,w27,w44,w56,w65],[w0,w6,w16,w21,w27,w48,w52,w65],[w0,w6,w16,w22,w27,w40,w60,w97],[w0,w6,w16,w22,w27,w44,w56,w97],[w0,w6,w16,w22,w27,w48,w52,w97],[w0,w6,w16,w27,w30,w40,w60,w97],[w0,w6,w16,w27,w30,w44,w56,w97],[w0,w6,w16,w27,w30,w48,w52,w97],[w0,w6,w16,w27,w40,w44,w52,w100],[w0,w6,w16,w27,w40,w60,w71,w97],[w0,w6,w16,w27,w40,w60,w97,w101],[w0,w6,w16,w27,w44,w56,w71,w97],[w0,w6,w16,w27,w44,w56,w97,w101],[w0,w6,w16,w27,w48,w52,w71,w97],[w0,w6,w16,w27,w48,w52,w97,w101],[w0,w6,w16,w29,w40,w44,w52,w97],[w0,w6,w18,w19,w27,w40,w60,w71],[w0,w6,w18,w19,w27,w44,w56,w71],[w0,w6,w18,w19,w27,w48,w52,w71],[w0,w6,w18,w19,w30,w40,w60,w65],[w0,w6,w18,w19,w30,w44,w56,w65],[w0,w6,w18,w19,w30,w48,w52,w65],[w0,w6,w19,w22,w27,w40,w62,w65],[w0,w6,w19,w22,w27,w42,w60,w65],[w0,w6,w19,w22,w27,w44,w58,w65],[w0,w6,w19,w22,w27,w46,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_59 : t7_59.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_60 : BankTree := .block [[w0,w6,w19,w22,w27,w48,w54,w65],[w0,w6,w19,w22,w27,w50,w52,w65],[w0,w6,w19,w27,w30,w40,w62,w65],[w0,w6,w19,w27,w30,w42,w60,w65],[w0,w6,w19,w27,w30,w44,w58,w65],[w0,w6,w19,w27,w30,w46,w56,w65],[w0,w6,w19,w27,w30,w48,w54,w65],[w0,w6,w19,w27,w30,w50,w52,w65],[w0,w6,w19,w27,w40,w42,w60,w71],[w0,w6,w19,w27,w40,w44,w54,w69],[w0,w6,w19,w27,w40,w44,w54,w73],[w0,w6,w19,w27,w40,w44,w54,w87],[w0,w6,w19,w27,w40,w44,w54,w101],[w0,w6,w19,w27,w40,w44,w54,w112],[w0,w6,w19,w27,w40,w44,w55,w71],[w0,w6,w19,w27,w40,w44,w58,w71],[w0,w6,w19,w27,w40,w44,w62,w71],[w0,w6,w19,w27,w40,w45,w54,w71],[w0,w6,w19,w27,w40,w46,w52,w69],[w0,w6,w19,w27,w40,w46,w52,w73],[w0,w6,w19,w27,w40,w46,w52,w87],[w0,w6,w19,w27,w40,w46,w52,w101],[w0,w6,w19,w27,w40,w46,w52,w112],[w0,w6,w19,w27,w40,w46,w53,w71],[w0,w6,w19,w27,w40,w46,w54,w71],[w0,w6,w19,w27,w40,w46,w56,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_60 : t7_60.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_58 : BankTree := .fork [w0,w6,w19,w22,w27,w48,w54,w65] t7_59 t7_60
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_58 : t7_58.rows.all (refuses 6 t6_0)=true := by simp only [t7_58,BankTree.rows,List.all_append,ok_t7_59,ok_t7_60,Bool.true_and]
noncomputable def t7_62 : BankTree := .block [[w0,w6,w19,w27,w40,w46,w60,w71],[w0,w6,w19,w27,w40,w46,w62,w71],[w0,w6,w19,w27,w40,w47,w52,w71],[w0,w6,w19,w27,w40,w48,w54,w71],[w0,w6,w19,w27,w40,w50,w52,w71],[w0,w6,w19,w27,w40,w52,w62,w71],[w0,w6,w19,w27,w40,w54,w60,w71],[w0,w6,w19,w27,w40,w54,w62,w71],[w0,w6,w19,w27,w40,w60,w62,w71],[w0,w6,w19,w27,w40,w62,w65,w71],[w0,w6,w19,w27,w40,w62,w71],[w0,w6,w19,w27,w41,w44,w54,w71],[w0,w6,w19,w27,w41,w46,w52,w71],[w0,w6,w19,w27,w42,w44,w52,w69],[w0,w6,w19,w27,w42,w44,w52,w73],[w0,w6,w19,w27,w42,w44,w52,w87],[w0,w6,w19,w27,w42,w44,w52,w101],[w0,w6,w19,w27,w42,w44,w52,w112],[w0,w6,w19,w27,w42,w44,w53,w71],[w0,w6,w19,w27,w42,w44,w54,w71],[w0,w6,w19,w27,w42,w44,w56,w71],[w0,w6,w19,w27,w42,w44,w58,w71],[w0,w6,w19,w27,w42,w44,w60,w71],[w0,w6,w19,w27,w42,w45,w52,w71],[w0,w6,w19,w27,w42,w46,w52,w71],[w0,w6,w19,w27,w42,w48,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_62 : t7_62.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_63 : BankTree := .block [[w0,w6,w19,w27,w42,w50,w52,w71],[w0,w6,w19,w27,w42,w52,w60,w71],[w0,w6,w19,w27,w42,w60,w65,w71],[w0,w6,w19,w27,w42,w60,w71],[w0,w6,w19,w27,w43,w44,w52,w71],[w0,w6,w19,w27,w44,w46,w56,w71],[w0,w6,w19,w27,w44,w48,w54,w71],[w0,w6,w19,w27,w44,w50,w52,w71],[w0,w6,w19,w27,w44,w52,w58,w71],[w0,w6,w19,w27,w44,w54,w56,w71],[w0,w6,w19,w27,w44,w54,w58,w71],[w0,w6,w19,w27,w44,w56,w58,w71],[w0,w6,w19,w27,w44,w58,w65,w71],[w0,w6,w19,w27,w44,w58,w71],[w0,w6,w19,w27,w46,w48,w52,w71],[w0,w6,w19,w27,w46,w50,w52,w71],[w0,w6,w19,w27,w46,w52,w56,w71],[w0,w6,w19,w27,w46,w56,w65,w71],[w0,w6,w19,w27,w46,w56,w71],[w0,w6,w19,w27,w48,w50,w52,w71],[w0,w6,w19,w27,w48,w52,w54,w71],[w0,w6,w19,w27,w48,w54,w65,w71],[w0,w6,w19,w27,w48,w54,w71],[w0,w6,w19,w27,w50,w52,w65,w71],[w0,w6,w19,w27,w50,w52,w71],[w0,w6,w19,w28,w40,w44,w54,w71],[w0,w6,w19,w28,w40,w46,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_63 : t7_63.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_61 : BankTree := .fork [w0,w6,w19,w27,w42,w50,w52,w71] t7_62 t7_63
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_61 : t7_61.rows.all (refuses 6 t6_0)=true := by simp only [t7_61,BankTree.rows,List.all_append,ok_t7_62,ok_t7_63,Bool.true_and]
noncomputable def t7_57 : BankTree := .fork [w0,w6,w19,w27,w40,w46,w60,w71] t7_58 t7_61
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_57 : t7_57.rows.all (refuses 6 t6_0)=true := by simp only [t7_57,BankTree.rows,List.all_append,ok_t7_58,ok_t7_61,Bool.true_and]
noncomputable def t7_49 : BankTree := .fork [w0,w6,w16,w21,w27,w44,w56,w65] t7_50 t7_57
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_49 : t7_49.rows.all (refuses 6 t6_0)=true := by simp only [t7_49,BankTree.rows,List.all_append,ok_t7_50,ok_t7_57,Bool.true_and]
noncomputable def t7_33 : BankTree := .fork [w0,w6,w12,w27,w40,w46,w52,w97] t7_34 t7_49
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_33 : t7_33.rows.all (refuses 6 t6_0)=true := by simp only [t7_33,BankTree.rows,List.all_append,ok_t7_34,ok_t7_49,Bool.true_and]
noncomputable def t7_1 : BankTree := .fork [w0,w2,w19,w27,w40,w46,w52,w75] t7_2 t7_33
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_1 : t7_1.rows.all (refuses 6 t6_0)=true := by simp only [t7_1,BankTree.rows,List.all_append,ok_t7_2,ok_t7_33,Bool.true_and]
noncomputable def t7_69 : BankTree := .block [[w0,w6,w19,w28,w42,w44,w52,w71],[w0,w6,w19,w29,w40,w44,w54,w65],[w0,w6,w19,w29,w40,w46,w52,w65],[w0,w6,w19,w29,w42,w44,w52,w65],[w0,w6,w19,w30,w40,w42,w60,w65],[w0,w6,w19,w30,w40,w44,w54,w67],[w0,w6,w19,w30,w40,w44,w54,w71],[w0,w6,w19,w30,w40,w44,w54,w77],[w0,w6,w19,w30,w40,w44,w54,w97],[w0,w6,w19,w30,w40,w44,w54,w109],[w0,w6,w19,w30,w40,w44,w54,w112],[w0,w6,w19,w30,w40,w44,w55,w65],[w0,w6,w19,w30,w40,w44,w58,w65],[w0,w6,w19,w30,w40,w44,w62,w65],[w0,w6,w19,w30,w40,w45,w54,w65],[w0,w6,w19,w30,w40,w46,w52,w67],[w0,w6,w19,w30,w40,w46,w52,w71],[w0,w6,w19,w30,w40,w46,w52,w77],[w0,w6,w19,w30,w40,w46,w52,w97],[w0,w6,w19,w30,w40,w46,w52,w109],[w0,w6,w19,w30,w40,w46,w52,w112],[w0,w6,w19,w30,w40,w46,w53,w65],[w0,w6,w19,w30,w40,w46,w54,w65],[w0,w6,w19,w30,w40,w46,w56,w65],[w0,w6,w19,w30,w40,w46,w60,w65],[w0,w6,w19,w30,w40,w46,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_69 : t7_69.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_70 : BankTree := .block [[w0,w6,w19,w30,w40,w47,w52,w65],[w0,w6,w19,w30,w40,w48,w54,w65],[w0,w6,w19,w30,w40,w50,w52,w65],[w0,w6,w19,w30,w40,w52,w62,w65],[w0,w6,w19,w30,w40,w54,w60,w65],[w0,w6,w19,w30,w40,w54,w62,w65],[w0,w6,w19,w30,w40,w60,w62,w65],[w0,w6,w19,w30,w40,w62,w65],[w0,w6,w19,w30,w41,w44,w54,w65],[w0,w6,w19,w30,w41,w46,w52,w65],[w0,w6,w19,w30,w42,w44,w52,w67],[w0,w6,w19,w30,w42,w44,w52,w71],[w0,w6,w19,w30,w42,w44,w52,w77],[w0,w6,w19,w30,w42,w44,w52,w97],[w0,w6,w19,w30,w42,w44,w52,w109],[w0,w6,w19,w30,w42,w44,w52,w112],[w0,w6,w19,w30,w42,w44,w53,w65],[w0,w6,w19,w30,w42,w44,w54,w65],[w0,w6,w19,w30,w42,w44,w56,w65],[w0,w6,w19,w30,w42,w44,w58,w65],[w0,w6,w19,w30,w42,w44,w60,w65],[w0,w6,w19,w30,w42,w45,w52,w65],[w0,w6,w19,w30,w42,w46,w52,w65],[w0,w6,w19,w30,w42,w48,w52,w65],[w0,w6,w19,w30,w42,w50,w52,w65],[w0,w6,w19,w30,w42,w52,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_70 : t7_70.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_68 : BankTree := .fork [w0,w6,w19,w30,w40,w47,w52,w65] t7_69 t7_70
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_68 : t7_68.rows.all (refuses 6 t6_0)=true := by simp only [t7_68,BankTree.rows,List.all_append,ok_t7_69,ok_t7_70,Bool.true_and]
noncomputable def t7_72 : BankTree := .block [[w0,w6,w19,w30,w42,w60,w65],[w0,w6,w19,w30,w43,w44,w52,w65],[w0,w6,w19,w30,w44,w46,w56,w65],[w0,w6,w19,w30,w44,w48,w54,w65],[w0,w6,w19,w30,w44,w50,w52,w65],[w0,w6,w19,w30,w44,w52,w58,w65],[w0,w6,w19,w30,w44,w54,w56,w65],[w0,w6,w19,w30,w44,w54,w58,w65],[w0,w6,w19,w30,w44,w56,w58,w65],[w0,w6,w19,w30,w44,w58,w65],[w0,w6,w19,w30,w46,w48,w52,w65],[w0,w6,w19,w30,w46,w50,w52,w65],[w0,w6,w19,w30,w46,w52,w56,w65],[w0,w6,w19,w30,w46,w56,w65],[w0,w6,w19,w30,w48,w50,w52,w65],[w0,w6,w19,w30,w48,w52,w54,w65],[w0,w6,w19,w30,w48,w54,w65],[w0,w6,w19,w30,w50,w52,w65],[w0,w6,w19,w31,w40,w44,w54,w65],[w0,w6,w19,w31,w40,w46,w52,w65],[w0,w6,w19,w31,w42,w44,w52,w65],[w0,w6,w19,w33,w40,w44,w54,w71],[w0,w6,w19,w33,w40,w46,w52,w71],[w0,w6,w19,w33,w42,w44,w52,w71],[w0,w6,w19,w38,w40,w44,w54,w65],[w0,w6,w19,w38,w40,w46,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_72 : t7_72.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_73 : BankTree := .block [[w0,w6,w19,w38,w42,w44,w52,w65],[w0,w6,w20,w27,w40,w44,w54,w71],[w0,w6,w20,w27,w40,w46,w52,w71],[w0,w6,w20,w27,w42,w44,w52,w71],[w0,w6,w20,w30,w40,w44,w54,w65],[w0,w6,w20,w30,w40,w46,w52,w65],[w0,w6,w20,w30,w42,w44,w52,w65],[w0,w6,w21,w27,w40,w44,w54,w65],[w0,w6,w21,w27,w40,w46,w52,w65],[w0,w6,w21,w27,w42,w44,w52,w65],[w0,w6,w22,w27,w40,w44,w54,w97],[w0,w6,w22,w27,w40,w46,w52,w97],[w0,w6,w22,w27,w42,w44,w52,w97],[w0,w6,w27,w30,w40,w44,w54,w97],[w0,w6,w27,w30,w40,w46,w52,w97],[w0,w6,w27,w30,w42,w44,w52,w97],[w0,w6,w27,w40,w44,w54,w71,w97],[w0,w6,w27,w40,w44,w54,w97,w101],[w0,w6,w27,w40,w46,w52,w71,w97],[w0,w6,w27,w40,w46,w52,w97,w101],[w0,w6,w27,w42,w44,w52,w71,w97],[w0,w6,w27,w42,w44,w52,w97,w101],[w0,w8,w16,w19,w27,w40,w60,w71],[w0,w8,w16,w19,w27,w44,w56,w71],[w0,w8,w16,w19,w27,w48,w52,w71],[w0,w8,w16,w19,w30,w40,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_73 : t7_73.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_71 : BankTree := .fork [w0,w6,w19,w38,w42,w44,w52,w65] t7_72 t7_73
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_71 : t7_71.rows.all (refuses 6 t6_0)=true := by simp only [t7_71,BankTree.rows,List.all_append,ok_t7_72,ok_t7_73,Bool.true_and]
noncomputable def t7_67 : BankTree := .fork [w0,w6,w19,w30,w42,w60,w65] t7_68 t7_71
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_67 : t7_67.rows.all (refuses 6 t6_0)=true := by simp only [t7_67,BankTree.rows,List.all_append,ok_t7_68,ok_t7_71,Bool.true_and]
noncomputable def t7_76 : BankTree := .block [[w0,w8,w16,w19,w30,w44,w56,w65],[w0,w8,w16,w19,w30,w48,w52,w65],[w0,w8,w19,w27,w40,w44,w54,w71],[w0,w8,w19,w27,w40,w46,w52,w71],[w0,w8,w19,w27,w42,w44,w52,w71],[w0,w8,w19,w30,w40,w44,w54,w65],[w0,w8,w19,w30,w40,w46,w52,w65],[w0,w8,w19,w30,w42,w44,w52,w65],[w0,w9,w16,w19,w27,w40,w60,w65],[w0,w9,w16,w19,w27,w44,w56,w65],[w0,w9,w16,w19,w27,w48,w52,w65],[w0,w9,w16,w27,w40,w44,w52,w97],[w0,w9,w19,w27,w40,w44,w54,w65],[w0,w9,w19,w27,w40,w46,w52,w65],[w0,w9,w19,w27,w42,w44,w52,w65],[w0,w10,w16,w19,w27,w40,w60,w65],[w0,w10,w16,w19,w27,w44,w56,w65],[w0,w10,w16,w19,w27,w48,w52,w65],[w0,w10,w16,w27,w40,w44,w52,w97],[w0,w10,w19,w27,w40,w44,w54,w65],[w0,w10,w19,w27,w40,w46,w52,w65],[w0,w10,w19,w27,w42,w44,w52,w65],[w0,w11,w16,w19,w27,w40,w60,w65],[w0,w11,w16,w19,w27,w44,w56,w65],[w0,w11,w16,w19,w27,w48,w52,w65],[w0,w11,w16,w27,w40,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_76 : t7_76.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_77 : BankTree := .block [[w0,w11,w19,w27,w40,w44,w54,w65],[w0,w11,w19,w27,w40,w46,w52,w65],[w0,w11,w19,w27,w42,w44,w52,w65],[w0,w12,w16,w19,w27,w40,w60,w67],[w0,w12,w16,w19,w27,w40,w60,w71],[w0,w12,w16,w19,w27,w40,w60,w77],[w0,w12,w16,w19,w27,w40,w60,w87],[w0,w12,w16,w19,w27,w40,w60,w97],[w0,w12,w16,w19,w27,w40,w60,w109],[w0,w12,w16,w19,w27,w40,w61,w65],[w0,w12,w16,w19,w27,w40,w62,w65],[w0,w12,w16,w19,w27,w40,w65,w91],[w0,w12,w16,w19,w27,w41,w60,w65],[w0,w12,w16,w19,w27,w42,w60,w65],[w0,w12,w16,w19,w27,w44,w56,w67],[w0,w12,w16,w19,w27,w44,w56,w71],[w0,w12,w16,w19,w27,w44,w56,w77],[w0,w12,w16,w19,w27,w44,w56,w87],[w0,w12,w16,w19,w27,w44,w56,w97],[w0,w12,w16,w19,w27,w44,w56,w109],[w0,w12,w16,w19,w27,w44,w57,w65],[w0,w12,w16,w19,w27,w44,w58,w65],[w0,w12,w16,w19,w27,w44,w65,w91],[w0,w12,w16,w19,w27,w45,w56,w65],[w0,w12,w16,w19,w27,w46,w56,w65],[w0,w12,w16,w19,w27,w48,w52,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_77 : t7_77.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_75 : BankTree := .fork [w0,w11,w19,w27,w40,w44,w54,w65] t7_76 t7_77
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_75 : t7_75.rows.all (refuses 6 t6_0)=true := by simp only [t7_75,BankTree.rows,List.all_append,ok_t7_76,ok_t7_77,Bool.true_and]
noncomputable def t7_79 : BankTree := .block [[w0,w12,w16,w19,w27,w48,w52,w71],[w0,w12,w16,w19,w27,w48,w52,w77],[w0,w12,w16,w19,w27,w48,w52,w87],[w0,w12,w16,w19,w27,w48,w52,w97],[w0,w12,w16,w19,w27,w48,w52,w109],[w0,w12,w16,w19,w27,w48,w53,w65],[w0,w12,w16,w19,w27,w48,w54,w65],[w0,w12,w16,w19,w27,w48,w56,w65],[w0,w12,w16,w19,w27,w48,w60,w65],[w0,w12,w16,w19,w27,w48,w65,w91],[w0,w12,w16,w19,w27,w49,w52,w65],[w0,w12,w16,w19,w27,w50,w52,w65],[w0,w12,w16,w19,w27,w52,w65,w91],[w0,w12,w16,w19,w27,w56,w60,w65],[w0,w12,w16,w19,w27,w56,w65,w91],[w0,w12,w16,w19,w27,w60,w65,w91],[w0,w12,w16,w19,w27,w65,w91],[w0,w12,w16,w19,w28,w40,w60,w65],[w0,w12,w16,w19,w28,w44,w56,w65],[w0,w12,w16,w19,w28,w48,w52,w65],[w0,w12,w16,w19,w30,w40,w60,w65],[w0,w12,w16,w19,w30,w44,w56,w65],[w0,w12,w16,w19,w30,w48,w52,w65],[w0,w12,w16,w19,w33,w40,w60,w65],[w0,w12,w16,w19,w33,w44,w56,w65],[w0,w12,w16,w19,w33,w48,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_79 : t7_79.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_80 : BankTree := .block [[w0,w12,w16,w19,w38,w40,w60,w65],[w0,w12,w16,w19,w38,w44,w56,w65],[w0,w12,w16,w19,w38,w48,w52,w65],[w0,w12,w16,w20,w27,w40,w60,w65],[w0,w12,w16,w20,w27,w44,w56,w65],[w0,w12,w16,w20,w27,w48,w52,w65],[w0,w12,w16,w27,w40,w44,w52,w98],[w0,w12,w16,w27,w40,w44,w53,w97],[w0,w12,w16,w27,w40,w44,w54,w97],[w0,w12,w16,w27,w40,w44,w56,w97],[w0,w12,w16,w27,w40,w44,w60,w97],[w0,w12,w16,w27,w40,w45,w52,w97],[w0,w12,w16,w27,w40,w46,w52,w97],[w0,w12,w16,w27,w40,w48,w52,w97],[w0,w12,w16,w27,w40,w52,w60,w97],[w0,w12,w16,w27,w40,w60,w65,w97],[w0,w12,w16,w27,w40,w60,w97],[w0,w12,w16,w27,w41,w44,w52,w97],[w0,w12,w16,w27,w42,w44,w52,w97],[w0,w12,w16,w27,w44,w48,w52,w97],[w0,w12,w16,w27,w44,w52,w56,w97],[w0,w12,w16,w27,w44,w56,w65,w97],[w0,w12,w16,w27,w44,w56,w97],[w0,w12,w16,w27,w48,w52,w65,w97],[w0,w12,w16,w27,w48,w52,w97],[w0,w12,w16,w28,w40,w44,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_80 : t7_80.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_78 : BankTree := .fork [w0,w12,w16,w19,w38,w40,w60,w65] t7_79 t7_80
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_78 : t7_78.rows.all (refuses 6 t6_0)=true := by simp only [t7_78,BankTree.rows,List.all_append,ok_t7_79,ok_t7_80,Bool.true_and]
noncomputable def t7_74 : BankTree := .fork [w0,w12,w16,w19,w27,w48,w52,w71] t7_75 t7_78
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_74 : t7_74.rows.all (refuses 6 t6_0)=true := by simp only [t7_74,BankTree.rows,List.all_append,ok_t7_75,ok_t7_78,Bool.true_and]
noncomputable def t7_66 : BankTree := .fork [w0,w8,w16,w19,w30,w44,w56,w65] t7_67 t7_74
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_66 : t7_66.rows.all (refuses 6 t6_0)=true := by simp only [t7_66,BankTree.rows,List.all_append,ok_t7_67,ok_t7_74,Bool.true_and]
noncomputable def t7_84 : BankTree := .block [[w0,w12,w18,w19,w27,w40,w60,w65],[w0,w12,w18,w19,w27,w44,w56,w65],[w0,w12,w18,w19,w27,w48,w52,w65],[w0,w12,w18,w27,w40,w44,w52,w97],[w0,w12,w19,w27,w40,w42,w60,w65],[w0,w12,w19,w27,w40,w44,w54,w67],[w0,w12,w19,w27,w40,w44,w54,w71],[w0,w12,w19,w27,w40,w44,w54,w77],[w0,w12,w19,w27,w40,w44,w54,w87],[w0,w12,w19,w27,w40,w44,w54,w97],[w0,w12,w19,w27,w40,w44,w54,w109],[w0,w12,w19,w27,w40,w44,w55,w65],[w0,w12,w19,w27,w40,w44,w58,w65],[w0,w12,w19,w27,w40,w44,w62,w65],[w0,w12,w19,w27,w40,w45,w54,w65],[w0,w12,w19,w27,w40,w46,w52,w67],[w0,w12,w19,w27,w40,w46,w52,w71],[w0,w12,w19,w27,w40,w46,w52,w77],[w0,w12,w19,w27,w40,w46,w52,w87],[w0,w12,w19,w27,w40,w46,w52,w97],[w0,w12,w19,w27,w40,w46,w52,w109],[w0,w12,w19,w27,w40,w46,w53,w65],[w0,w12,w19,w27,w40,w46,w54,w65],[w0,w12,w19,w27,w40,w46,w56,w65],[w0,w12,w19,w27,w40,w46,w60,w65],[w0,w12,w19,w27,w40,w46,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_84 : t7_84.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_85 : BankTree := .block [[w0,w12,w19,w27,w40,w47,w52,w65],[w0,w12,w19,w27,w40,w48,w54,w65],[w0,w12,w19,w27,w40,w50,w52,w65],[w0,w12,w19,w27,w40,w52,w62,w65],[w0,w12,w19,w27,w40,w54,w60,w65],[w0,w12,w19,w27,w40,w54,w62,w65],[w0,w12,w19,w27,w40,w60,w62,w65],[w0,w12,w19,w27,w40,w62,w65],[w0,w12,w19,w27,w41,w44,w54,w65],[w0,w12,w19,w27,w41,w46,w52,w65],[w0,w12,w19,w27,w42,w44,w52,w67],[w0,w12,w19,w27,w42,w44,w52,w71],[w0,w12,w19,w27,w42,w44,w52,w77],[w0,w12,w19,w27,w42,w44,w52,w87],[w0,w12,w19,w27,w42,w44,w52,w97],[w0,w12,w19,w27,w42,w44,w52,w109],[w0,w12,w19,w27,w42,w44,w53,w65],[w0,w12,w19,w27,w42,w44,w54,w65],[w0,w12,w19,w27,w42,w44,w56,w65],[w0,w12,w19,w27,w42,w44,w58,w65],[w0,w12,w19,w27,w42,w44,w60,w65],[w0,w12,w19,w27,w42,w45,w52,w65],[w0,w12,w19,w27,w42,w46,w52,w65],[w0,w12,w19,w27,w42,w48,w52,w65],[w0,w12,w19,w27,w42,w50,w52,w65],[w0,w12,w19,w27,w42,w52,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_85 : t7_85.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_83 : BankTree := .fork [w0,w12,w19,w27,w40,w47,w52,w65] t7_84 t7_85
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_83 : t7_83.rows.all (refuses 6 t6_0)=true := by simp only [t7_83,BankTree.rows,List.all_append,ok_t7_84,ok_t7_85,Bool.true_and]
noncomputable def t7_87 : BankTree := .block [[w0,w12,w19,w27,w42,w60,w65],[w0,w12,w19,w27,w43,w44,w52,w65],[w0,w12,w19,w27,w44,w46,w56,w65],[w0,w12,w19,w27,w44,w48,w54,w65],[w0,w12,w19,w27,w44,w50,w52,w65],[w0,w12,w19,w27,w44,w52,w58,w65],[w0,w12,w19,w27,w44,w54,w56,w65],[w0,w12,w19,w27,w44,w54,w58,w65],[w0,w12,w19,w27,w44,w56,w58,w65],[w0,w12,w19,w27,w44,w58,w65],[w0,w12,w19,w27,w46,w48,w52,w65],[w0,w12,w19,w27,w46,w50,w52,w65],[w0,w12,w19,w27,w46,w52,w56,w65],[w0,w12,w19,w27,w46,w56,w65],[w0,w12,w19,w27,w48,w50,w52,w65],[w0,w12,w19,w27,w48,w52,w54,w65],[w0,w12,w19,w27,w48,w54,w65],[w0,w12,w19,w27,w50,w52,w65],[w0,w12,w19,w28,w40,w44,w54,w65],[w0,w12,w19,w28,w40,w46,w52,w65],[w0,w12,w19,w28,w42,w44,w52,w65],[w0,w12,w19,w30,w40,w44,w54,w65],[w0,w12,w19,w30,w40,w46,w52,w65],[w0,w12,w19,w30,w42,w44,w52,w65],[w0,w12,w19,w33,w40,w44,w54,w65],[w0,w12,w19,w33,w40,w46,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_87 : t7_87.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_88 : BankTree := .block [[w0,w12,w19,w33,w42,w44,w52,w65],[w0,w12,w19,w38,w40,w44,w54,w65],[w0,w12,w19,w38,w40,w46,w52,w65],[w0,w12,w19,w38,w42,w44,w52,w65],[w0,w12,w20,w27,w40,w44,w54,w65],[w0,w12,w20,w27,w40,w46,w52,w65],[w0,w12,w20,w27,w42,w44,w52,w65],[w0,w12,w27,w40,w42,w44,w52,w97],[w0,w12,w27,w40,w44,w46,w52,w97],[w0,w12,w27,w40,w44,w52,w54,w97],[w0,w12,w27,w40,w44,w54,w65,w97],[w0,w12,w27,w40,w44,w54,w97],[w0,w12,w27,w40,w46,w52,w65,w97],[w0,w12,w27,w40,w46,w52,w97],[w0,w12,w27,w42,w44,w52,w65,w97],[w0,w12,w27,w42,w44,w52,w97],[w0,w14,w16,w19,w27,w40,w60,w65],[w0,w14,w16,w19,w27,w44,w56,w65],[w0,w14,w16,w19,w27,w48,w52,w65],[w0,w14,w16,w27,w40,w44,w52,w97],[w0,w14,w19,w27,w40,w44,w54,w65],[w0,w14,w19,w27,w40,w46,w52,w65],[w0,w14,w19,w27,w42,w44,w52,w65],[w0,w15,w19,w27,w40,w44,w52,w65],[w0,w16,w19,w22,w27,w40,w60,w77],[w0,w16,w19,w22,w27,w44,w56,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_88 : t7_88.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_86 : BankTree := .fork [w0,w12,w19,w33,w42,w44,w52,w65] t7_87 t7_88
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_86 : t7_86.rows.all (refuses 6 t6_0)=true := by simp only [t7_86,BankTree.rows,List.all_append,ok_t7_87,ok_t7_88,Bool.true_and]
noncomputable def t7_82 : BankTree := .fork [w0,w12,w19,w27,w42,w60,w65] t7_83 t7_86
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_82 : t7_82.rows.all (refuses 6 t6_0)=true := by simp only [t7_82,BankTree.rows,List.all_append,ok_t7_83,ok_t7_86,Bool.true_and]
noncomputable def t7_91 : BankTree := .block [[w0,w16,w19,w22,w27,w48,w52,w77],[w0,w16,w19,w22,w33,w40,w60,w65],[w0,w16,w19,w22,w33,w44,w56,w65],[w0,w16,w19,w22,w33,w48,w52,w65],[w0,w16,w19,w24,w27,w40,w60,w71],[w0,w16,w19,w24,w27,w44,w56,w71],[w0,w16,w19,w24,w27,w48,w52,w71],[w0,w16,w19,w24,w30,w40,w60,w65],[w0,w16,w19,w24,w30,w44,w56,w65],[w0,w16,w19,w24,w30,w48,w52,w65],[w0,w16,w19,w26,w27,w40,w60,w65],[w0,w16,w19,w26,w27,w44,w56,w65],[w0,w16,w19,w26,w27,w48,w52,w65],[w0,w16,w19,w27,w30,w40,w60,w77],[w0,w16,w19,w27,w30,w44,w56,w77],[w0,w16,w19,w27,w30,w48,w52,w77],[w0,w16,w19,w27,w33,w40,w60,w71],[w0,w16,w19,w27,w33,w44,w56,w71],[w0,w16,w19,w27,w33,w48,w52,w71],[w0,w16,w19,w27,w38,w40,w60,w65],[w0,w16,w19,w27,w38,w44,w56,w65],[w0,w16,w19,w27,w38,w48,w52,w65],[w0,w16,w19,w27,w40,w44,w52,w81],[w0,w16,w19,w27,w40,w44,w52,w83],[w0,w16,w19,w27,w40,w44,w52,w85],[w0,w16,w19,w27,w40,w44,w52,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_91 : t7_91.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_92 : BankTree := .block [[w0,w16,w19,w27,w40,w44,w52,w89],[w0,w16,w19,w27,w40,w44,w52,w107],[w0,w16,w19,w27,w40,w44,w52,w120],[w0,w16,w19,w27,w40,w44,w53,w87],[w0,w16,w19,w27,w40,w44,w54,w87],[w0,w16,w19,w27,w40,w44,w56,w87],[w0,w16,w19,w27,w40,w44,w60,w87],[w0,w16,w19,w27,w40,w45,w52,w87],[w0,w16,w19,w27,w40,w46,w52,w87],[w0,w16,w19,w27,w40,w48,w52,w87],[w0,w16,w19,w27,w40,w52,w60,w87],[w0,w16,w19,w27,w40,w60,w65,w87],[w0,w16,w19,w27,w40,w60,w71,w77],[w0,w16,w19,w27,w40,w60,w71,w87],[w0,w16,w19,w27,w40,w60,w77,w87],[w0,w16,w19,w27,w40,w60,w87],[w0,w16,w19,w27,w41,w44,w52,w87],[w0,w16,w19,w27,w42,w44,w52,w87],[w0,w16,w19,w27,w44,w48,w52,w87],[w0,w16,w19,w27,w44,w52,w56,w87],[w0,w16,w19,w27,w44,w56,w65,w87],[w0,w16,w19,w27,w44,w56,w71,w77],[w0,w16,w19,w27,w44,w56,w71,w87],[w0,w16,w19,w27,w44,w56,w77,w87],[w0,w16,w19,w27,w44,w56,w87],[w0,w16,w19,w27,w48,w52,w65,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_92 : t7_92.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_90 : BankTree := .fork [w0,w16,w19,w27,w40,w44,w52,w89] t7_91 t7_92
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_90 : t7_90.rows.all (refuses 6 t6_0)=true := by simp only [t7_90,BankTree.rows,List.all_append,ok_t7_91,ok_t7_92,Bool.true_and]
noncomputable def t7_94 : BankTree := .block [[w0,w16,w19,w27,w48,w52,w71,w77],[w0,w16,w19,w27,w48,w52,w71,w87],[w0,w16,w19,w27,w48,w52,w77,w87],[w0,w16,w19,w27,w48,w52,w87],[w0,w16,w19,w28,w40,w44,w52,w87],[w0,w16,w19,w29,w40,w44,w52,w77],[w0,w16,w19,w30,w33,w40,w60,w65],[w0,w16,w19,w30,w33,w44,w56,w65],[w0,w16,w19,w30,w33,w48,w52,w65],[w0,w16,w19,w30,w38,w40,w60,w65],[w0,w16,w19,w30,w38,w44,w56,w65],[w0,w16,w19,w30,w38,w48,w52,w65],[w0,w16,w19,w30,w40,w44,w52,w75],[w0,w16,w19,w30,w40,w44,w52,w79],[w0,w16,w19,w30,w40,w44,w52,w87],[w0,w16,w19,w30,w40,w44,w52,w104],[w0,w16,w19,w30,w40,w44,w52,w115],[w0,w16,w19,w30,w40,w44,w52,w120],[w0,w16,w19,w30,w40,w44,w53,w77],[w0,w16,w19,w30,w40,w44,w54,w77],[w0,w16,w19,w30,w40,w44,w56,w77],[w0,w16,w19,w30,w40,w44,w60,w77],[w0,w16,w19,w30,w40,w45,w52,w77],[w0,w16,w19,w30,w40,w46,w52,w77],[w0,w16,w19,w30,w40,w48,w52,w77],[w0,w16,w19,w30,w40,w52,w60,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_94 : t7_94.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_95 : BankTree := .block [[w0,w16,w19,w30,w40,w60,w65,w77],[w0,w16,w19,w30,w40,w60,w77],[w0,w16,w19,w30,w41,w44,w52,w77],[w0,w16,w19,w30,w42,w44,w52,w77],[w0,w16,w19,w30,w44,w48,w52,w77],[w0,w16,w19,w30,w44,w52,w56,w77],[w0,w16,w19,w30,w44,w56,w65,w77],[w0,w16,w19,w30,w44,w56,w77],[w0,w16,w19,w30,w48,w52,w65,w77],[w0,w16,w19,w30,w48,w52,w77],[w0,w16,w19,w31,w40,w44,w52,w77],[w0,w16,w19,w32,w40,w44,w52,w71],[w0,w16,w19,w33,w38,w40,w60,w65],[w0,w16,w19,w33,w38,w44,w56,w65],[w0,w16,w19,w33,w38,w48,w52,w65],[w0,w16,w19,w33,w40,w44,w52,w69],[w0,w16,w19,w33,w40,w44,w52,w73],[w0,w16,w19,w33,w40,w44,w52,w87],[w0,w16,w19,w33,w40,w44,w52,w101],[w0,w16,w19,w33,w40,w44,w52,w112],[w0,w16,w19,w33,w40,w44,w52,w120],[w0,w16,w19,w33,w40,w44,w53,w71],[w0,w16,w19,w33,w40,w44,w54,w71],[w0,w16,w19,w33,w40,w44,w56,w71],[w0,w16,w19,w33,w40,w44,w60,w71],[w0,w16,w19,w33,w40,w45,w52,w71],[w0,w16,w19,w33,w40,w46,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_95 : t7_95.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_93 : BankTree := .fork [w0,w16,w19,w30,w40,w60,w65,w77] t7_94 t7_95
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_93 : t7_93.rows.all (refuses 6 t6_0)=true := by simp only [t7_93,BankTree.rows,List.all_append,ok_t7_94,ok_t7_95,Bool.true_and]
noncomputable def t7_89 : BankTree := .fork [w0,w16,w19,w27,w48,w52,w71,w77] t7_90 t7_93
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_89 : t7_89.rows.all (refuses 6 t6_0)=true := by simp only [t7_89,BankTree.rows,List.all_append,ok_t7_90,ok_t7_93,Bool.true_and]
noncomputable def t7_81 : BankTree := .fork [w0,w16,w19,w22,w27,w48,w52,w77] t7_82 t7_89
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_81 : t7_81.rows.all (refuses 6 t6_0)=true := by simp only [t7_81,BankTree.rows,List.all_append,ok_t7_82,ok_t7_89,Bool.true_and]
noncomputable def t7_65 : BankTree := .fork [w0,w12,w18,w19,w27,w40,w60,w65] t7_66 t7_81
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_65 : t7_65.rows.all (refuses 6 t6_0)=true := by simp only [t7_65,BankTree.rows,List.all_append,ok_t7_66,ok_t7_81,Bool.true_and]
noncomputable def t7_100 : BankTree := .block [[w0,w16,w19,w33,w40,w48,w52,w71],[w0,w16,w19,w33,w40,w52,w60,w71],[w0,w16,w19,w33,w40,w60,w65,w71],[w0,w16,w19,w33,w40,w60,w71],[w0,w16,w19,w33,w41,w44,w52,w71],[w0,w16,w19,w33,w42,w44,w52,w71],[w0,w16,w19,w33,w44,w48,w52,w71],[w0,w16,w19,w33,w44,w52,w56,w71],[w0,w16,w19,w33,w44,w56,w65,w71],[w0,w16,w19,w33,w44,w56,w71],[w0,w16,w19,w33,w48,w52,w65,w71],[w0,w16,w19,w33,w48,w52,w71],[w0,w16,w19,w34,w40,w44,w52,w71],[w0,w16,w19,w35,w40,w44,w52,w65],[w0,w16,w19,w36,w40,w44,w52,w65],[w0,w16,w19,w37,w40,w44,w52,w65],[w0,w16,w19,w38,w40,w44,w52,w65],[w0,w16,w19,w38,w40,w44,w52,w67],[w0,w16,w19,w38,w40,w44,w52,w71],[w0,w16,w19,w38,w40,w44,w52,w77],[w0,w16,w19,w38,w40,w44,w52,w87],[w0,w16,w19,w38,w40,w44,w52,w97],[w0,w16,w19,w38,w40,w44,w52,w109],[w0,w16,w19,w38,w40,w44,w52,w112],[w0,w16,w19,w38,w40,w44,w52,w115],[w0,w16,w19,w38,w40,w44,w52,w120]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_100 : t7_100.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_101 : BankTree := .block [[w0,w16,w19,w38,w40,w44,w53,w65],[w0,w16,w19,w38,w40,w44,w54,w65],[w0,w16,w19,w38,w40,w44,w56,w65],[w0,w16,w19,w38,w40,w44,w60,w65],[w0,w16,w19,w38,w40,w45,w52,w65],[w0,w16,w19,w38,w40,w46,w52,w65],[w0,w16,w19,w38,w40,w48,w52,w65],[w0,w16,w19,w38,w40,w52,w60,w65],[w0,w16,w19,w38,w40,w60,w65],[w0,w16,w19,w38,w41,w44,w52,w65],[w0,w16,w19,w38,w42,w44,w52,w65],[w0,w16,w19,w38,w44,w48,w52,w65],[w0,w16,w19,w38,w44,w52,w56,w65],[w0,w16,w19,w38,w44,w56,w65],[w0,w16,w19,w38,w48,w52,w65],[w0,w16,w19,w39,w40,w44,w52,w65],[w0,w16,w20,w27,w40,w44,w52,w87],[w0,w16,w20,w30,w40,w44,w52,w77],[w0,w16,w20,w33,w40,w44,w52,w71],[w0,w16,w20,w38,w40,w44,w52,w65],[w0,w16,w21,w27,w40,w44,w52,w77],[w0,w16,w21,w33,w40,w44,w52,w65],[w0,w16,w22,w24,w27,w40,w60,w65],[w0,w16,w22,w24,w27,w44,w56,w65],[w0,w16,w22,w24,w27,w48,w52,w65],[w0,w16,w22,w27,w40,w44,w52,w104]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_101 : t7_101.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_99 : BankTree := .fork [w0,w16,w19,w38,w40,w44,w53,w65] t7_100 t7_101
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_99 : t7_99.rows.all (refuses 6 t6_0)=true := by simp only [t7_99,BankTree.rows,List.all_append,ok_t7_100,ok_t7_101,Bool.true_and]
noncomputable def t7_103 : BankTree := .block [[w0,w16,w22,w33,w40,w44,w52,w97],[w0,w16,w23,w27,w40,w44,w52,w71],[w0,w16,w23,w30,w40,w44,w52,w65],[w0,w16,w24,w27,w40,w44,w52,w101],[w0,w16,w24,w30,w40,w44,w52,w97],[w0,w16,w25,w27,w40,w44,w52,w65],[w0,w16,w26,w27,w40,w44,w52,w97],[w0,w16,w27,w38,w40,w44,w52,w97],[w0,w16,w27,w40,w44,w52,w87,w97],[w0,w16,w27,w40,w44,w52,w97,w107],[w0,w16,w27,w40,w44,w52,w101,w104],[w0,w16,w30,w33,w40,w44,w52,w97],[w0,w18,w19,w27,w40,w44,w52,w87],[w0,w18,w19,w30,w40,w44,w52,w77],[w0,w18,w19,w33,w40,w44,w52,w71],[w0,w18,w19,w38,w40,w44,w52,w65],[w0,w19,w22,w27,w40,w44,w54,w77],[w0,w19,w22,w27,w40,w46,w52,w77],[w0,w19,w22,w27,w42,w44,w52,w77],[w0,w19,w22,w33,w40,w44,w54,w65],[w0,w19,w22,w33,w40,w46,w52,w65],[w0,w19,w22,w33,w42,w44,w52,w65],[w0,w19,w24,w27,w40,w44,w54,w71],[w0,w19,w24,w27,w40,w46,w52,w71],[w0,w19,w24,w27,w42,w44,w52,w71],[w0,w19,w24,w30,w40,w44,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_103 : t7_103.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_104 : BankTree := .block [[w0,w19,w24,w30,w40,w46,w52,w65],[w0,w19,w24,w30,w42,w44,w52,w65],[w0,w19,w26,w27,w40,w44,w54,w65],[w0,w19,w26,w27,w40,w46,w52,w65],[w0,w19,w26,w27,w42,w44,w52,w65],[w0,w19,w27,w30,w40,w44,w54,w77],[w0,w19,w27,w30,w40,w46,w52,w77],[w0,w19,w27,w30,w42,w44,w52,w77],[w0,w19,w27,w33,w40,w44,w54,w71],[w0,w19,w27,w33,w40,w46,w52,w71],[w0,w19,w27,w33,w42,w44,w52,w71],[w0,w19,w27,w38,w40,w44,w54,w65],[w0,w19,w27,w38,w40,w46,w52,w65],[w0,w19,w27,w38,w42,w44,w52,w65],[w0,w19,w27,w40,w42,w44,w52,w87],[w0,w19,w27,w40,w44,w46,w52,w87],[w0,w19,w27,w40,w44,w52,w54,w87],[w0,w19,w27,w40,w44,w54,w65,w87],[w0,w19,w27,w40,w44,w54,w71,w77],[w0,w19,w27,w40,w44,w54,w71,w87],[w0,w19,w27,w40,w44,w54,w77,w87],[w0,w19,w27,w40,w44,w54,w87],[w0,w19,w27,w40,w46,w52,w65,w87],[w0,w19,w27,w40,w46,w52,w71,w77],[w0,w19,w27,w40,w46,w52,w71,w87],[w0,w19,w27,w40,w46,w52,w77,w87]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_104 : t7_104.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_102 : BankTree := .fork [w0,w19,w24,w30,w40,w46,w52,w65] t7_103 t7_104
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_102 : t7_102.rows.all (refuses 6 t6_0)=true := by simp only [t7_102,BankTree.rows,List.all_append,ok_t7_103,ok_t7_104,Bool.true_and]
noncomputable def t7_98 : BankTree := .fork [w0,w16,w22,w33,w40,w44,w52,w97] t7_99 t7_102
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_98 : t7_98.rows.all (refuses 6 t6_0)=true := by simp only [t7_98,BankTree.rows,List.all_append,ok_t7_99,ok_t7_102,Bool.true_and]
noncomputable def t7_107 : BankTree := .block [[w0,w19,w27,w40,w46,w52,w87],[w0,w19,w27,w42,w44,w52,w65,w87],[w0,w19,w27,w42,w44,w52,w71,w77],[w0,w19,w27,w42,w44,w52,w71,w87],[w0,w19,w27,w42,w44,w52,w77,w87],[w0,w19,w27,w42,w44,w52,w87],[w0,w19,w30,w33,w40,w44,w54,w65],[w0,w19,w30,w33,w40,w46,w52,w65],[w0,w19,w30,w33,w42,w44,w52,w65],[w0,w19,w30,w38,w40,w44,w54,w65],[w0,w19,w30,w38,w40,w46,w52,w65],[w0,w19,w30,w38,w42,w44,w52,w65],[w0,w19,w30,w40,w42,w44,w52,w77],[w0,w19,w30,w40,w44,w46,w52,w77],[w0,w19,w30,w40,w44,w52,w54,w77],[w0,w19,w30,w40,w44,w54,w65,w77],[w0,w19,w30,w40,w44,w54,w77],[w0,w19,w30,w40,w46,w52,w65,w77],[w0,w19,w30,w40,w46,w52,w77],[w0,w19,w30,w42,w44,w52,w65,w77],[w0,w19,w30,w42,w44,w52,w77],[w0,w19,w33,w38,w40,w44,w54,w65],[w0,w19,w33,w38,w40,w46,w52,w65],[w0,w19,w33,w38,w42,w44,w52,w65],[w0,w19,w33,w40,w42,w44,w52,w71],[w0,w19,w33,w40,w44,w46,w52,w71]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_107 : t7_107.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_108 : BankTree := .block [[w0,w19,w33,w40,w44,w52,w54,w71],[w0,w19,w33,w40,w44,w54,w65,w71],[w0,w19,w33,w40,w44,w54,w71],[w0,w19,w33,w40,w46,w52,w65,w71],[w0,w19,w33,w40,w46,w52,w71],[w0,w19,w33,w42,w44,w52,w65,w71],[w0,w19,w33,w42,w44,w52,w71],[w0,w19,w38,w40,w42,w44,w52,w65],[w0,w19,w38,w40,w44,w46,w52,w65],[w0,w19,w38,w40,w44,w52,w54,w65],[w0,w19,w38,w40,w44,w54,w65],[w0,w19,w38,w40,w46,w52,w65],[w0,w19,w38,w42,w44,w52,w65],[w0,w22,w24,w27,w40,w44,w54,w65],[w0,w22,w24,w27,w40,w46,w52,w65],[w0,w22,w24,w27,w42,w44,w52,w65],[w2,w6,w16,w19,w27,w40,w61,w67],[w2,w6,w16,w19,w27,w41,w60,w67],[w2,w6,w16,w19,w27,w41,w61,w65],[w2,w6,w16,w19,w27,w44,w57,w67],[w2,w6,w16,w19,w27,w45,w56,w67],[w2,w6,w16,w19,w27,w45,w57,w65],[w2,w6,w16,w19,w27,w48,w53,w67],[w2,w6,w16,w19,w27,w49,w52,w67],[w2,w6,w16,w19,w27,w49,w53,w65],[w2,w6,w16,w19,w28,w40,w60,w67]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_108 : t7_108.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_106 : BankTree := .fork [w0,w19,w33,w40,w44,w52,w54,w71] t7_107 t7_108
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_106 : t7_106.rows.all (refuses 6 t6_0)=true := by simp only [t7_106,BankTree.rows,List.all_append,ok_t7_107,ok_t7_108,Bool.true_and]
noncomputable def t7_110 : BankTree := .block [[w2,w6,w16,w19,w28,w40,w61,w65],[w2,w6,w16,w19,w28,w41,w60,w65],[w2,w6,w16,w19,w28,w44,w56,w67],[w2,w6,w16,w19,w28,w44,w57,w65],[w2,w6,w16,w19,w28,w45,w56,w65],[w2,w6,w16,w19,w28,w48,w52,w67],[w2,w6,w16,w19,w28,w48,w53,w65],[w2,w6,w16,w19,w28,w49,w52,w65],[w2,w6,w16,w20,w27,w40,w61,w65],[w2,w6,w16,w20,w27,w41,w60,w65],[w2,w6,w16,w20,w27,w44,w57,w65],[w2,w6,w16,w20,w27,w45,w56,w65],[w2,w6,w16,w20,w27,w48,w53,w65],[w2,w6,w16,w20,w27,w49,w52,w65],[w2,w6,w16,w20,w28,w40,w60,w65],[w2,w6,w16,w20,w28,w44,w56,w65],[w2,w6,w16,w20,w28,w48,w52,w65],[w2,w6,w16,w27,w40,w44,w53,w98],[w2,w6,w16,w27,w40,w45,w52,w98],[w2,w6,w16,w27,w40,w45,w53,w97],[w2,w6,w16,w27,w41,w44,w52,w98],[w2,w6,w16,w27,w41,w44,w53,w97],[w2,w6,w16,w27,w41,w45,w52,w97],[w2,w6,w16,w28,w40,w44,w52,w98],[w2,w6,w16,w28,w40,w44,w53,w97],[w2,w6,w16,w28,w40,w45,w52,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_110 : t7_110.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_111 : BankTree := .block [[w2,w6,w16,w28,w41,w44,w52,w97],[w2,w6,w18,w19,w27,w40,w60,w67],[w2,w6,w18,w19,w27,w44,w56,w67],[w2,w6,w18,w19,w27,w48,w52,w67],[w2,w6,w18,w19,w28,w40,w60,w65],[w2,w6,w18,w19,w28,w44,w56,w65],[w2,w6,w18,w19,w28,w48,w52,w65],[w2,w6,w18,w20,w27,w40,w60,w65],[w2,w6,w18,w20,w27,w44,w56,w65],[w2,w6,w18,w20,w27,w48,w52,w65],[w2,w6,w18,w27,w40,w44,w52,w98],[w2,w6,w18,w28,w40,w44,w52,w97],[w2,w6,w19,w27,w40,w44,w55,w67],[w2,w6,w19,w27,w40,w45,w54,w67],[w2,w6,w19,w27,w40,w46,w53,w67],[w2,w6,w19,w27,w40,w47,w52,w67],[w2,w6,w19,w27,w41,w44,w54,w67],[w2,w6,w19,w27,w41,w45,w54,w65],[w2,w6,w19,w27,w41,w46,w52,w67],[w2,w6,w19,w27,w41,w46,w53,w65],[w2,w6,w19,w27,w42,w44,w53,w67],[w2,w6,w19,w27,w42,w45,w52,w67],[w2,w6,w19,w27,w42,w45,w53,w65],[w2,w6,w19,w27,w43,w44,w52,w67],[w2,w6,w19,w28,w40,w44,w54,w67],[w2,w6,w19,w28,w40,w44,w55,w65],[w2,w6,w19,w28,w40,w45,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_111 : t7_111.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_109 : BankTree := .fork [w2,w6,w16,w28,w41,w44,w52,w97] t7_110 t7_111
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_109 : t7_109.rows.all (refuses 6 t6_0)=true := by simp only [t7_109,BankTree.rows,List.all_append,ok_t7_110,ok_t7_111,Bool.true_and]
noncomputable def t7_105 : BankTree := .fork [w2,w6,w16,w19,w28,w40,w61,w65] t7_106 t7_109
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_105 : t7_105.rows.all (refuses 6 t6_0)=true := by simp only [t7_105,BankTree.rows,List.all_append,ok_t7_106,ok_t7_109,Bool.true_and]
noncomputable def t7_97 : BankTree := .fork [w0,w19,w27,w40,w46,w52,w87] t7_98 t7_105
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_97 : t7_97.rows.all (refuses 6 t6_0)=true := by simp only [t7_97,BankTree.rows,List.all_append,ok_t7_98,ok_t7_105,Bool.true_and]
noncomputable def t7_115 : BankTree := .block [[w2,w6,w19,w28,w40,w46,w52,w67],[w2,w6,w19,w28,w40,w46,w53,w65],[w2,w6,w19,w28,w40,w47,w52,w65],[w2,w6,w19,w28,w41,w44,w54,w65],[w2,w6,w19,w28,w41,w46,w52,w65],[w2,w6,w19,w28,w42,w44,w52,w67],[w2,w6,w19,w28,w42,w44,w53,w65],[w2,w6,w19,w28,w42,w45,w52,w65],[w2,w6,w19,w28,w43,w44,w52,w65],[w2,w6,w20,w27,w40,w44,w55,w65],[w2,w6,w20,w27,w40,w45,w54,w65],[w2,w6,w20,w27,w40,w46,w53,w65],[w2,w6,w20,w27,w40,w47,w52,w65],[w2,w6,w20,w27,w41,w44,w54,w65],[w2,w6,w20,w27,w41,w46,w52,w65],[w2,w6,w20,w27,w42,w44,w53,w65],[w2,w6,w20,w27,w42,w45,w52,w65],[w2,w6,w20,w27,w43,w44,w52,w65],[w2,w6,w20,w28,w40,w44,w54,w65],[w2,w6,w20,w28,w40,w46,w52,w65],[w2,w6,w20,w28,w42,w44,w52,w65],[w2,w7,w16,w19,w27,w40,w60,w65],[w2,w7,w16,w19,w27,w44,w56,w65],[w2,w7,w16,w19,w27,w48,w52,w65],[w2,w7,w16,w27,w40,w44,w52,w97],[w2,w7,w19,w27,w40,w44,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_115 : t7_115.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_116 : BankTree := .block [[w2,w7,w19,w27,w40,w46,w52,w65],[w2,w7,w19,w27,w42,w44,w52,w65],[w2,w8,w16,w19,w27,w40,w61,w65],[w2,w8,w16,w19,w27,w41,w60,w65],[w2,w8,w16,w19,w27,w44,w57,w65],[w2,w8,w16,w19,w27,w45,w56,w65],[w2,w8,w16,w19,w27,w48,w53,w65],[w2,w8,w16,w19,w27,w49,w52,w65],[w2,w8,w16,w20,w27,w40,w60,w65],[w2,w8,w16,w20,w27,w44,w56,w65],[w2,w8,w16,w20,w27,w48,w52,w65],[w2,w8,w16,w27,w40,w44,w53,w97],[w2,w8,w16,w27,w40,w45,w52,w97],[w2,w8,w16,w27,w41,w44,w52,w97],[w2,w8,w18,w19,w27,w40,w60,w65],[w2,w8,w18,w19,w27,w44,w56,w65],[w2,w8,w18,w19,w27,w48,w52,w65],[w2,w8,w18,w27,w40,w44,w52,w97],[w2,w8,w19,w27,w40,w44,w55,w65],[w2,w8,w19,w27,w40,w45,w54,w65],[w2,w8,w19,w27,w40,w46,w53,w65],[w2,w8,w19,w27,w40,w47,w52,w65],[w2,w8,w19,w27,w41,w44,w54,w65],[w2,w8,w19,w27,w41,w46,w52,w65],[w2,w8,w19,w27,w42,w44,w53,w65],[w2,w8,w19,w27,w42,w45,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_116 : t7_116.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_114 : BankTree := .fork [w2,w7,w19,w27,w40,w46,w52,w65] t7_115 t7_116
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_114 : t7_114.rows.all (refuses 6 t6_0)=true := by simp only [t7_114,BankTree.rows,List.all_append,ok_t7_115,ok_t7_116,Bool.true_and]
noncomputable def t7_118 : BankTree := .block [[w2,w8,w19,w27,w43,w44,w52,w65],[w2,w8,w20,w27,w40,w44,w54,w65],[w2,w8,w20,w27,w40,w46,w52,w65],[w2,w8,w20,w27,w42,w44,w52,w65],[w2,w16,w19,w27,w40,w44,w53,w79],[w2,w16,w19,w27,w40,w45,w52,w79],[w2,w16,w19,w27,w40,w45,w53,w77],[w2,w16,w19,w27,w41,w44,w52,w79],[w2,w16,w19,w27,w41,w44,w53,w77],[w2,w16,w19,w27,w41,w45,w52,w77],[w2,w16,w19,w28,w40,w44,w53,w77],[w2,w16,w19,w28,w40,w45,w52,w77],[w2,w16,w19,w28,w41,w44,w52,w77],[w2,w16,w19,w33,w40,w44,w53,w67],[w2,w16,w19,w33,w40,w45,w52,w67],[w2,w16,w19,w33,w40,w45,w53,w65],[w2,w16,w19,w33,w41,w44,w52,w67],[w2,w16,w19,w33,w41,w44,w53,w65],[w2,w16,w19,w33,w41,w45,w52,w65],[w2,w16,w19,w34,w40,w44,w53,w65],[w2,w16,w19,w34,w40,w45,w52,w65],[w2,w16,w19,w34,w41,w44,w52,w65],[w2,w16,w20,w27,w40,w44,w53,w77],[w2,w16,w20,w27,w40,w45,w52,w77],[w2,w16,w20,w27,w41,w44,w52,w77],[w2,w16,w20,w28,w40,w44,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_118 : t7_118.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_119 : BankTree := .block [[w2,w16,w20,w33,w40,w44,w53,w65],[w2,w16,w20,w33,w40,w45,w52,w65],[w2,w16,w20,w33,w41,w44,w52,w65],[w2,w16,w20,w34,w40,w44,w52,w65],[w2,w18,w19,w27,w40,w44,w52,w79],[w2,w18,w19,w28,w40,w44,w52,w77],[w2,w18,w19,w33,w40,w44,w52,w67],[w2,w18,w19,w34,w40,w44,w52,w65],[w2,w18,w20,w27,w40,w44,w52,w77],[w2,w18,w20,w33,w40,w44,w52,w65],[w3,w6,w16,w19,w27,w40,w60,w65],[w3,w6,w16,w19,w27,w44,w56,w65],[w3,w6,w16,w19,w27,w48,w52,w65],[w3,w6,w16,w27,w40,w44,w52,w97],[w3,w6,w19,w27,w40,w44,w54,w65],[w3,w6,w19,w27,w40,w46,w52,w65],[w3,w6,w19,w27,w42,w44,w52,w65],[w3,w16,w19,w27,w40,w44,w52,w77],[w3,w16,w19,w33,w40,w44,w52,w65],[w4,w6,w16,w19,w27,w40,w61,w65],[w4,w6,w16,w19,w27,w41,w60,w65],[w4,w6,w16,w19,w27,w44,w57,w65],[w4,w6,w16,w19,w27,w45,w56,w65],[w4,w6,w16,w19,w27,w48,w53,w65],[w4,w6,w16,w19,w27,w49,w52,w65],[w4,w6,w16,w20,w27,w40,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_119 : t7_119.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_117 : BankTree := .fork [w2,w16,w20,w33,w40,w44,w53,w65] t7_118 t7_119
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_117 : t7_117.rows.all (refuses 6 t6_0)=true := by simp only [t7_117,BankTree.rows,List.all_append,ok_t7_118,ok_t7_119,Bool.true_and]
noncomputable def t7_113 : BankTree := .fork [w2,w8,w19,w27,w43,w44,w52,w65] t7_114 t7_117
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_113 : t7_113.rows.all (refuses 6 t6_0)=true := by simp only [t7_113,BankTree.rows,List.all_append,ok_t7_114,ok_t7_117,Bool.true_and]
noncomputable def t7_122 : BankTree := .block [[w4,w6,w16,w20,w27,w44,w56,w65],[w4,w6,w16,w20,w27,w48,w52,w65],[w4,w6,w16,w27,w40,w44,w53,w97],[w4,w6,w16,w27,w40,w45,w52,w97],[w4,w6,w16,w27,w41,w44,w52,w97],[w4,w6,w18,w19,w27,w40,w60,w65],[w4,w6,w18,w19,w27,w44,w56,w65],[w4,w6,w18,w19,w27,w48,w52,w65],[w4,w6,w18,w27,w40,w44,w52,w97],[w4,w6,w19,w27,w40,w44,w55,w65],[w4,w6,w19,w27,w40,w45,w54,w65],[w4,w6,w19,w27,w40,w46,w53,w65],[w4,w6,w19,w27,w40,w47,w52,w65],[w4,w6,w19,w27,w41,w44,w54,w65],[w4,w6,w19,w27,w41,w46,w52,w65],[w4,w6,w19,w27,w42,w44,w53,w65],[w4,w6,w19,w27,w42,w45,w52,w65],[w4,w6,w19,w27,w43,w44,w52,w65],[w4,w6,w20,w27,w40,w44,w54,w65],[w4,w6,w20,w27,w40,w46,w52,w65],[w4,w6,w20,w27,w42,w44,w52,w65],[w4,w8,w16,w19,w27,w40,w60,w65],[w4,w8,w16,w19,w27,w44,w56,w65],[w4,w8,w16,w19,w27,w48,w52,w65],[w4,w8,w16,w27,w40,w44,w52,w97],[w4,w8,w19,w27,w40,w44,w54,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_122 : t7_122.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_123 : BankTree := .block [[w4,w8,w19,w27,w40,w46,w52,w65],[w4,w8,w19,w27,w42,w44,w52,w65],[w4,w16,w19,w27,w40,w44,w53,w77],[w4,w16,w19,w27,w40,w45,w52,w77],[w4,w16,w19,w27,w41,w44,w52,w77],[w4,w16,w19,w33,w40,w44,w53,w65],[w4,w16,w19,w33,w40,w45,w52,w65],[w4,w16,w19,w33,w41,w44,w52,w65],[w4,w16,w20,w27,w40,w44,w52,w77],[w4,w16,w20,w33,w40,w44,w52,w65],[w4,w18,w19,w27,w40,w44,w52,w77],[w4,w18,w19,w33,w40,w44,w52,w65],[w6,w16,w19,w27,w40,w44,w53,w73],[w6,w16,w19,w27,w40,w45,w52,w73],[w6,w16,w19,w27,w40,w45,w53,w71],[w6,w16,w19,w27,w41,w44,w52,w73],[w6,w16,w19,w27,w41,w44,w53,w71],[w6,w16,w19,w27,w41,w45,w52,w71],[w6,w16,w19,w28,w40,w44,w53,w71],[w6,w16,w19,w28,w40,w45,w52,w71],[w6,w16,w19,w28,w41,w44,w52,w71],[w6,w16,w19,w30,w40,w44,w53,w67],[w6,w16,w19,w30,w40,w45,w52,w67],[w6,w16,w19,w30,w40,w45,w53,w65],[w6,w16,w19,w30,w41,w44,w52,w67],[w6,w16,w19,w30,w41,w44,w53,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_123 : t7_123.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_121 : BankTree := .fork [w4,w8,w19,w27,w40,w46,w52,w65] t7_122 t7_123
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_121 : t7_121.rows.all (refuses 6 t6_0)=true := by simp only [t7_121,BankTree.rows,List.all_append,ok_t7_122,ok_t7_123,Bool.true_and]
noncomputable def t7_125 : BankTree := .block [[w6,w16,w19,w30,w41,w45,w52,w65],[w6,w16,w19,w31,w40,w44,w53,w65],[w6,w16,w19,w31,w40,w45,w52,w65],[w6,w16,w19,w31,w41,w44,w52,w65],[w6,w16,w20,w27,w40,w44,w53,w71],[w6,w16,w20,w27,w40,w45,w52,w71],[w6,w16,w20,w27,w41,w44,w52,w71],[w6,w16,w20,w28,w40,w44,w52,w71],[w6,w16,w20,w30,w40,w44,w53,w65],[w6,w16,w20,w30,w40,w45,w52,w65],[w6,w16,w20,w30,w41,w44,w52,w65],[w6,w16,w20,w31,w40,w44,w52,w65],[w6,w18,w19,w27,w40,w44,w52,w73],[w6,w18,w19,w28,w40,w44,w52,w71],[w6,w18,w19,w30,w40,w44,w52,w67],[w6,w18,w19,w31,w40,w44,w52,w65],[w6,w18,w20,w27,w40,w44,w52,w71],[w6,w18,w20,w30,w40,w44,w52,w65],[w7,w16,w19,w27,w40,w44,w52,w71],[w7,w16,w19,w30,w40,w44,w52,w65],[w8,w16,w19,w27,w40,w44,w53,w71],[w8,w16,w19,w27,w40,w45,w52,w71],[w8,w16,w19,w27,w41,w44,w52,w71],[w8,w16,w19,w30,w40,w44,w53,w65],[w8,w16,w19,w30,w40,w45,w52,w65],[w8,w16,w19,w30,w41,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_125 : t7_125.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_126 : BankTree := .block [[w8,w16,w20,w27,w40,w44,w52,w71],[w8,w16,w20,w30,w40,w44,w52,w65],[w8,w18,w19,w27,w40,w44,w52,w71],[w8,w18,w19,w30,w40,w44,w52,w65],[w12,w16,w19,w27,w40,w44,w53,w67],[w12,w16,w19,w27,w40,w45,w52,w67],[w12,w16,w19,w27,w40,w45,w53,w65],[w12,w16,w19,w27,w41,w44,w52,w67],[w12,w16,w19,w27,w41,w44,w53,w65],[w12,w16,w19,w27,w41,w45,w52,w65],[w12,w16,w19,w28,w40,w44,w52,w67],[w12,w16,w19,w28,w40,w44,w53,w65],[w12,w16,w19,w28,w40,w45,w52,w65],[w12,w16,w19,w28,w41,w44,w52,w65],[w12,w16,w20,w27,w40,w44,w53,w65],[w12,w16,w20,w27,w40,w45,w52,w65],[w12,w16,w20,w27,w41,w44,w52,w65],[w12,w16,w20,w28,w40,w44,w52,w65],[w12,w18,w19,w27,w40,w44,w52,w67],[w12,w18,w19,w28,w40,w44,w52,w65],[w12,w18,w20,w27,w40,w44,w52,w65],[w13,w16,w19,w27,w40,w44,w52,w65],[w14,w16,w19,w27,w40,w44,w53,w65],[w14,w16,w19,w27,w40,w45,w52,w65],[w14,w16,w19,w27,w41,w44,w52,w65],[w14,w16,w20,w27,w40,w44,w52,w65],[w14,w18,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_126 : t7_126.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_124 : BankTree := .fork [w8,w16,w20,w27,w40,w44,w52,w71] t7_125 t7_126
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_124 : t7_124.rows.all (refuses 6 t6_0)=true := by simp only [t7_124,BankTree.rows,List.all_append,ok_t7_125,ok_t7_126,Bool.true_and]
noncomputable def t7_120 : BankTree := .fork [w6,w16,w19,w30,w41,w45,w52,w65] t7_121 t7_124
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_120 : t7_120.rows.all (refuses 6 t6_0)=true := by simp only [t7_120,BankTree.rows,List.all_append,ok_t7_121,ok_t7_124,Bool.true_and]
noncomputable def t7_112 : BankTree := .fork [w4,w6,w16,w20,w27,w44,w56,w65] t7_113 t7_120
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_112 : t7_112.rows.all (refuses 6 t6_0)=true := by simp only [t7_112,BankTree.rows,List.all_append,ok_t7_113,ok_t7_120,Bool.true_and]
noncomputable def t7_96 : BankTree := .fork [w2,w6,w19,w28,w40,w46,w52,w67] t7_97 t7_112
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_96 : t7_96.rows.all (refuses 6 t6_0)=true := by simp only [t7_96,BankTree.rows,List.all_append,ok_t7_97,ok_t7_112,Bool.true_and]
noncomputable def t7_64 : BankTree := .fork [w0,w16,w19,w33,w40,w48,w52,w71] t7_65 t7_96
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_64 : t7_64.rows.all (refuses 6 t6_0)=true := by simp only [t7_64,BankTree.rows,List.all_append,ok_t7_65,ok_t7_96,Bool.true_and]
noncomputable def t7_0 : BankTree := .fork [w0,w6,w19,w28,w42,w44,w52,w71] t7_1 t7_64
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_0 : t7_0.rows.all (refuses 6 t6_0)=true := by simp only [t7_0,BankTree.rows,List.all_append,ok_t7_1,ok_t7_64,Bool.true_and]
theorem safe7 : Safe 7 t7_0 := certify 6 t6_0 t7_0 safe6 ok_t7_0
noncomputable def t8_4 : BankTree := .block [[w0,w1,w6,w16,w19,w27,w40,w60,w65],[w0,w1,w6,w16,w19,w27,w44,w56,w65],[w0,w1,w6,w16,w19,w27,w48,w52,w65],[w0,w1,w6,w16,w27,w40,w44,w52,w97],[w0,w1,w6,w19,w27,w40,w44,w54,w65],[w0,w1,w6,w19,w27,w40,w46,w52,w65],[w0,w1,w6,w19,w27,w42,w44,w52,w65],[w0,w1,w16,w19,w27,w40,w44,w52,w77],[w0,w1,w16,w19,w33,w40,w44,w52,w65],[w0,w2,w5,w16,w19,w27,w40,w60,w65],[w0,w2,w5,w16,w19,w27,w44,w56,w65],[w0,w2,w5,w16,w19,w27,w48,w52,w65],[w0,w2,w5,w16,w27,w40,w44,w52,w97],[w0,w2,w5,w19,w27,w40,w44,w54,w65],[w0,w2,w5,w19,w27,w40,w46,w52,w65],[w0,w2,w5,w19,w27,w42,w44,w52,w65],[w0,w2,w6,w16,w19,w27,w40,w60,w67],[w0,w2,w6,w16,w19,w27,w40,w60,w71],[w0,w2,w6,w16,w19,w27,w40,w60,w77],[w0,w2,w6,w16,w19,w27,w40,w60,w97],[w0,w2,w6,w16,w19,w27,w40,w60,w109],[w0,w2,w6,w16,w19,w27,w40,w61,w65],[w0,w2,w6,w16,w19,w27,w40,w62,w65],[w0,w2,w6,w16,w19,w27,w40,w65,w91],[w0,w2,w6,w16,w19,w27,w41,w60,w65],[w0,w2,w6,w16,w19,w27,w42,w60,w65],[w0,w2,w6,w16,w19,w27,w44,w56,w67],[w0,w2,w6,w16,w19,w27,w44,w56,w71],[w0,w2,w6,w16,w19,w27,w44,w56,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_4 : t8_4.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_5 : BankTree := .block [[w0,w2,w6,w16,w19,w27,w44,w56,w97],[w0,w2,w6,w16,w19,w27,w44,w56,w109],[w0,w2,w6,w16,w19,w27,w44,w57,w65],[w0,w2,w6,w16,w19,w27,w44,w58,w65],[w0,w2,w6,w16,w19,w27,w44,w65,w91],[w0,w2,w6,w16,w19,w27,w45,w56,w65],[w0,w2,w6,w16,w19,w27,w46,w56,w65],[w0,w2,w6,w16,w19,w27,w48,w52,w67],[w0,w2,w6,w16,w19,w27,w48,w52,w71],[w0,w2,w6,w16,w19,w27,w48,w52,w77],[w0,w2,w6,w16,w19,w27,w48,w52,w97],[w0,w2,w6,w16,w19,w27,w48,w52,w109],[w0,w2,w6,w16,w19,w27,w48,w53,w65],[w0,w2,w6,w16,w19,w27,w48,w54,w65],[w0,w2,w6,w16,w19,w27,w48,w56,w65],[w0,w2,w6,w16,w19,w27,w48,w60,w65],[w0,w2,w6,w16,w19,w27,w48,w65,w91],[w0,w2,w6,w16,w19,w27,w49,w52,w65],[w0,w2,w6,w16,w19,w27,w50,w52,w65],[w0,w2,w6,w16,w19,w27,w52,w65,w91],[w0,w2,w6,w16,w19,w27,w56,w60,w65],[w0,w2,w6,w16,w19,w27,w56,w65,w91],[w0,w2,w6,w16,w19,w27,w60,w65,w91],[w0,w2,w6,w16,w19,w27,w65,w91],[w0,w2,w6,w16,w19,w28,w40,w60,w65],[w0,w2,w6,w16,w19,w28,w44,w56,w65],[w0,w2,w6,w16,w19,w28,w48,w52,w65],[w0,w2,w6,w16,w19,w30,w40,w60,w65],[w0,w2,w6,w16,w19,w30,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_5 : t8_5.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_3 : BankTree := .fork [w0,w2,w6,w16,w19,w27,w44,w56,w97] t8_4 t8_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_3 : t8_3.rows.all (refuses 7 t7_0)=true := by simp only [t8_3,BankTree.rows,List.all_append,ok_t8_4,ok_t8_5,Bool.true_and]
noncomputable def t8_7 : BankTree := .block [[w0,w2,w6,w16,w19,w30,w48,w52,w65],[w0,w2,w6,w16,w19,w33,w40,w60,w65],[w0,w2,w6,w16,w19,w33,w44,w56,w65],[w0,w2,w6,w16,w19,w33,w48,w52,w65],[w0,w2,w6,w16,w20,w27,w40,w60,w65],[w0,w2,w6,w16,w20,w27,w44,w56,w65],[w0,w2,w6,w16,w20,w27,w48,w52,w65],[w0,w2,w6,w16,w27,w40,w44,w52,w98],[w0,w2,w6,w16,w27,w40,w44,w53,w97],[w0,w2,w6,w16,w27,w40,w44,w54,w97],[w0,w2,w6,w16,w27,w40,w44,w56,w97],[w0,w2,w6,w16,w27,w40,w44,w60,w97],[w0,w2,w6,w16,w27,w40,w45,w52,w97],[w0,w2,w6,w16,w27,w40,w46,w52,w97],[w0,w2,w6,w16,w27,w40,w48,w52,w97],[w0,w2,w6,w16,w27,w40,w52,w60,w97],[w0,w2,w6,w16,w27,w40,w60,w65,w97],[w0,w2,w6,w16,w27,w40,w60,w97],[w0,w2,w6,w16,w27,w41,w44,w52,w97],[w0,w2,w6,w16,w27,w42,w44,w52,w97],[w0,w2,w6,w16,w27,w44,w48,w52,w97],[w0,w2,w6,w16,w27,w44,w52,w56,w97],[w0,w2,w6,w16,w27,w44,w56,w65,w97],[w0,w2,w6,w16,w27,w44,w56,w97],[w0,w2,w6,w16,w27,w48,w52,w65,w97],[w0,w2,w6,w16,w27,w48,w52,w97],[w0,w2,w6,w16,w28,w40,w44,w52,w97],[w0,w2,w6,w18,w19,w27,w40,w60,w65],[w0,w2,w6,w18,w19,w27,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_7 : t8_7.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_8 : BankTree := .block [[w0,w2,w6,w18,w19,w27,w48,w52,w65],[w0,w2,w6,w18,w27,w40,w44,w52,w97],[w0,w2,w6,w19,w27,w40,w42,w60,w65],[w0,w2,w6,w19,w27,w40,w44,w54,w67],[w0,w2,w6,w19,w27,w40,w44,w54,w71],[w0,w2,w6,w19,w27,w40,w44,w54,w77],[w0,w2,w6,w19,w27,w40,w44,w54,w97],[w0,w2,w6,w19,w27,w40,w44,w54,w109],[w0,w2,w6,w19,w27,w40,w44,w55,w65],[w0,w2,w6,w19,w27,w40,w44,w58,w65],[w0,w2,w6,w19,w27,w40,w44,w62,w65],[w0,w2,w6,w19,w27,w40,w45,w54,w65],[w0,w2,w6,w19,w27,w40,w46,w52,w67],[w0,w2,w6,w19,w27,w40,w46,w52,w71],[w0,w2,w6,w19,w27,w40,w46,w52,w77],[w0,w2,w6,w19,w27,w40,w46,w52,w97],[w0,w2,w6,w19,w27,w40,w46,w52,w109],[w0,w2,w6,w19,w27,w40,w46,w53,w65],[w0,w2,w6,w19,w27,w40,w46,w54,w65],[w0,w2,w6,w19,w27,w40,w46,w56,w65],[w0,w2,w6,w19,w27,w40,w46,w60,w65],[w0,w2,w6,w19,w27,w40,w46,w62,w65],[w0,w2,w6,w19,w27,w40,w47,w52,w65],[w0,w2,w6,w19,w27,w40,w48,w54,w65],[w0,w2,w6,w19,w27,w40,w50,w52,w65],[w0,w2,w6,w19,w27,w40,w52,w62,w65],[w0,w2,w6,w19,w27,w40,w54,w60,w65],[w0,w2,w6,w19,w27,w40,w54,w62,w65],[w0,w2,w6,w19,w27,w40,w60,w62,w65],[w0,w2,w6,w19,w27,w40,w62,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_8 : t8_8.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_6 : BankTree := .fork [w0,w2,w6,w18,w19,w27,w48,w52,w65] t8_7 t8_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_6 : t8_6.rows.all (refuses 7 t7_0)=true := by simp only [t8_6,BankTree.rows,List.all_append,ok_t8_7,ok_t8_8,Bool.true_and]
noncomputable def t8_2 : BankTree := .fork [w0,w2,w6,w16,w19,w30,w48,w52,w65] t8_3 t8_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_2 : t8_2.rows.all (refuses 7 t7_0)=true := by simp only [t8_2,BankTree.rows,List.all_append,ok_t8_3,ok_t8_6,Bool.true_and]
noncomputable def t8_11 : BankTree := .block [[w0,w2,w6,w19,w27,w41,w44,w54,w65],[w0,w2,w6,w19,w27,w41,w46,w52,w65],[w0,w2,w6,w19,w27,w42,w44,w52,w67],[w0,w2,w6,w19,w27,w42,w44,w52,w71],[w0,w2,w6,w19,w27,w42,w44,w52,w77],[w0,w2,w6,w19,w27,w42,w44,w52,w97],[w0,w2,w6,w19,w27,w42,w44,w52,w109],[w0,w2,w6,w19,w27,w42,w44,w53,w65],[w0,w2,w6,w19,w27,w42,w44,w54,w65],[w0,w2,w6,w19,w27,w42,w44,w56,w65],[w0,w2,w6,w19,w27,w42,w44,w58,w65],[w0,w2,w6,w19,w27,w42,w44,w60,w65],[w0,w2,w6,w19,w27,w42,w45,w52,w65],[w0,w2,w6,w19,w27,w42,w46,w52,w65],[w0,w2,w6,w19,w27,w42,w48,w52,w65],[w0,w2,w6,w19,w27,w42,w50,w52,w65],[w0,w2,w6,w19,w27,w42,w52,w60,w65],[w0,w2,w6,w19,w27,w42,w60,w65],[w0,w2,w6,w19,w27,w43,w44,w52,w65],[w0,w2,w6,w19,w27,w44,w46,w56,w65],[w0,w2,w6,w19,w27,w44,w48,w54,w65],[w0,w2,w6,w19,w27,w44,w50,w52,w65],[w0,w2,w6,w19,w27,w44,w52,w58,w65],[w0,w2,w6,w19,w27,w44,w54,w56,w65],[w0,w2,w6,w19,w27,w44,w54,w58,w65],[w0,w2,w6,w19,w27,w44,w56,w58,w65],[w0,w2,w6,w19,w27,w44,w58,w65],[w0,w2,w6,w19,w27,w46,w48,w52,w65],[w0,w2,w6,w19,w27,w46,w50,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_11 : t8_11.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_12 : BankTree := .block [[w0,w2,w6,w19,w27,w46,w52,w56,w65],[w0,w2,w6,w19,w27,w46,w56,w65],[w0,w2,w6,w19,w27,w48,w50,w52,w65],[w0,w2,w6,w19,w27,w48,w52,w54,w65],[w0,w2,w6,w19,w27,w48,w54,w65],[w0,w2,w6,w19,w27,w50,w52,w65],[w0,w2,w6,w19,w28,w40,w44,w54,w65],[w0,w2,w6,w19,w28,w40,w46,w52,w65],[w0,w2,w6,w19,w28,w42,w44,w52,w65],[w0,w2,w6,w19,w30,w40,w44,w54,w65],[w0,w2,w6,w19,w30,w40,w46,w52,w65],[w0,w2,w6,w19,w30,w42,w44,w52,w65],[w0,w2,w6,w19,w33,w40,w44,w54,w65],[w0,w2,w6,w19,w33,w40,w46,w52,w65],[w0,w2,w6,w19,w33,w42,w44,w52,w65],[w0,w2,w6,w20,w27,w40,w44,w54,w65],[w0,w2,w6,w20,w27,w40,w46,w52,w65],[w0,w2,w6,w20,w27,w42,w44,w52,w65],[w0,w2,w6,w27,w40,w42,w44,w52,w97],[w0,w2,w6,w27,w40,w44,w46,w52,w97],[w0,w2,w6,w27,w40,w44,w52,w54,w97],[w0,w2,w6,w27,w40,w44,w54,w65,w97],[w0,w2,w6,w27,w40,w44,w54,w97],[w0,w2,w6,w27,w40,w46,w52,w65,w97],[w0,w2,w6,w27,w40,w46,w52,w97],[w0,w2,w6,w27,w42,w44,w52,w65,w97],[w0,w2,w6,w27,w42,w44,w52,w97],[w0,w2,w8,w16,w19,w27,w40,w60,w65],[w0,w2,w8,w16,w19,w27,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_12 : t8_12.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_10 : BankTree := .fork [w0,w2,w6,w19,w27,w46,w52,w56,w65] t8_11 t8_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_10 : t8_10.rows.all (refuses 7 t7_0)=true := by simp only [t8_10,BankTree.rows,List.all_append,ok_t8_11,ok_t8_12,Bool.true_and]
noncomputable def t8_14 : BankTree := .block [[w0,w2,w8,w16,w19,w27,w48,w52,w65],[w0,w2,w8,w16,w27,w40,w44,w52,w97],[w0,w2,w8,w19,w27,w40,w44,w54,w65],[w0,w2,w8,w19,w27,w40,w46,w52,w65],[w0,w2,w8,w19,w27,w42,w44,w52,w65],[w0,w2,w12,w16,w19,w27,w40,w60,w65],[w0,w2,w12,w16,w19,w27,w44,w56,w65],[w0,w2,w12,w16,w19,w27,w48,w52,w65],[w0,w2,w12,w16,w27,w40,w44,w52,w97],[w0,w2,w12,w19,w27,w40,w44,w54,w65],[w0,w2,w12,w19,w27,w40,w46,w52,w65],[w0,w2,w12,w19,w27,w42,w44,w52,w65],[w0,w2,w16,w19,w24,w27,w40,w60,w65],[w0,w2,w16,w19,w24,w27,w44,w56,w65],[w0,w2,w16,w19,w24,w27,w48,w52,w65],[w0,w2,w16,w19,w27,w33,w40,w60,w65],[w0,w2,w16,w19,w27,w33,w44,w56,w65],[w0,w2,w16,w19,w27,w33,w48,w52,w65],[w0,w2,w16,w19,w27,w40,w44,w52,w75],[w0,w2,w16,w19,w27,w40,w44,w52,w79],[w0,w2,w16,w19,w27,w40,w44,w52,w87],[w0,w2,w16,w19,w27,w40,w44,w52,w104],[w0,w2,w16,w19,w27,w40,w44,w52,w115],[w0,w2,w16,w19,w27,w40,w44,w53,w77],[w0,w2,w16,w19,w27,w40,w44,w54,w77],[w0,w2,w16,w19,w27,w40,w44,w56,w77],[w0,w2,w16,w19,w27,w40,w44,w60,w77],[w0,w2,w16,w19,w27,w40,w45,w52,w77],[w0,w2,w16,w19,w27,w40,w46,w52,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_14 : t8_14.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_15 : BankTree := .block [[w0,w2,w16,w19,w27,w40,w48,w52,w77],[w0,w2,w16,w19,w27,w40,w52,w60,w77],[w0,w2,w16,w19,w27,w40,w60,w65,w77],[w0,w2,w16,w19,w27,w40,w60,w77],[w0,w2,w16,w19,w27,w41,w44,w52,w77],[w0,w2,w16,w19,w27,w42,w44,w52,w77],[w0,w2,w16,w19,w27,w44,w48,w52,w77],[w0,w2,w16,w19,w27,w44,w52,w56,w77],[w0,w2,w16,w19,w27,w44,w56,w65,w77],[w0,w2,w16,w19,w27,w44,w56,w77],[w0,w2,w16,w19,w27,w48,w52,w65,w77],[w0,w2,w16,w19,w27,w48,w52,w77],[w0,w2,w16,w19,w28,w40,w44,w52,w77],[w0,w2,w16,w19,w30,w40,w44,w52,w77],[w0,w2,w16,w19,w32,w40,w44,w52,w65],[w0,w2,w16,w19,w33,w40,w44,w52,w67],[w0,w2,w16,w19,w33,w40,w44,w52,w71],[w0,w2,w16,w19,w33,w40,w44,w52,w77],[w0,w2,w16,w19,w33,w40,w44,w52,w97],[w0,w2,w16,w19,w33,w40,w44,w52,w109],[w0,w2,w16,w19,w33,w40,w44,w52,w115],[w0,w2,w16,w19,w33,w40,w44,w53,w65],[w0,w2,w16,w19,w33,w40,w44,w54,w65],[w0,w2,w16,w19,w33,w40,w44,w56,w65],[w0,w2,w16,w19,w33,w40,w44,w60,w65],[w0,w2,w16,w19,w33,w40,w45,w52,w65],[w0,w2,w16,w19,w33,w40,w46,w52,w65],[w0,w2,w16,w19,w33,w40,w48,w52,w65],[w0,w2,w16,w19,w33,w40,w52,w60,w65],[w0,w2,w16,w19,w33,w40,w60,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_15 : t8_15.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_13 : BankTree := .fork [w0,w2,w16,w19,w27,w40,w48,w52,w77] t8_14 t8_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_13 : t8_13.rows.all (refuses 7 t7_0)=true := by simp only [t8_13,BankTree.rows,List.all_append,ok_t8_14,ok_t8_15,Bool.true_and]
noncomputable def t8_9 : BankTree := .fork [w0,w2,w8,w16,w19,w27,w48,w52,w65] t8_10 t8_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_9 : t8_9.rows.all (refuses 7 t7_0)=true := by simp only [t8_9,BankTree.rows,List.all_append,ok_t8_10,ok_t8_13,Bool.true_and]
noncomputable def t8_1 : BankTree := .fork [w0,w2,w6,w19,w27,w41,w44,w54,w65] t8_2 t8_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_1 : t8_1.rows.all (refuses 7 t7_0)=true := by simp only [t8_1,BankTree.rows,List.all_append,ok_t8_2,ok_t8_9,Bool.true_and]
noncomputable def t8_19 : BankTree := .block [[w0,w2,w16,w19,w33,w41,w44,w52,w65],[w0,w2,w16,w19,w33,w42,w44,w52,w65],[w0,w2,w16,w19,w33,w44,w48,w52,w65],[w0,w2,w16,w19,w33,w44,w52,w56,w65],[w0,w2,w16,w19,w33,w44,w56,w65],[w0,w2,w16,w19,w33,w48,w52,w65],[w0,w2,w16,w19,w34,w40,w44,w52,w65],[w0,w2,w16,w19,w38,w40,w44,w52,w65],[w0,w2,w16,w20,w27,w40,w44,w52,w77],[w0,w2,w16,w20,w33,w40,w44,w52,w65],[w0,w2,w16,w23,w27,w40,w44,w52,w65],[w0,w2,w16,w24,w27,w40,w44,w52,w97],[w0,w2,w16,w27,w33,w40,w44,w52,w97],[w0,w2,w16,w27,w40,w44,w52,w77,w97],[w0,w2,w16,w27,w40,w44,w52,w97,w104],[w0,w2,w18,w19,w27,w40,w44,w52,w77],[w0,w2,w18,w19,w33,w40,w44,w52,w65],[w0,w2,w19,w24,w27,w40,w44,w54,w65],[w0,w2,w19,w24,w27,w40,w46,w52,w65],[w0,w2,w19,w24,w27,w42,w44,w52,w65],[w0,w2,w19,w27,w33,w40,w44,w54,w65],[w0,w2,w19,w27,w33,w40,w46,w52,w65],[w0,w2,w19,w27,w33,w42,w44,w52,w65],[w0,w2,w19,w27,w40,w42,w44,w52,w77],[w0,w2,w19,w27,w40,w44,w46,w52,w77],[w0,w2,w19,w27,w40,w44,w52,w54,w77],[w0,w2,w19,w27,w40,w44,w54,w65,w77],[w0,w2,w19,w27,w40,w44,w54,w77],[w0,w2,w19,w27,w40,w46,w52,w65,w77]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_19 : t8_19.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_20 : BankTree := .block [[w0,w2,w19,w27,w40,w46,w52,w77],[w0,w2,w19,w27,w42,w44,w52,w65,w77],[w0,w2,w19,w27,w42,w44,w52,w77],[w0,w2,w19,w33,w40,w42,w44,w52,w65],[w0,w2,w19,w33,w40,w44,w46,w52,w65],[w0,w2,w19,w33,w40,w44,w52,w54,w65],[w0,w2,w19,w33,w40,w44,w54,w65],[w0,w2,w19,w33,w40,w46,w52,w65],[w0,w2,w19,w33,w42,w44,w52,w65],[w0,w4,w6,w16,w19,w27,w40,w60,w65],[w0,w4,w6,w16,w19,w27,w44,w56,w65],[w0,w4,w6,w16,w19,w27,w48,w52,w65],[w0,w4,w6,w16,w27,w40,w44,w52,w97],[w0,w4,w6,w19,w27,w40,w44,w54,w65],[w0,w4,w6,w19,w27,w40,w46,w52,w65],[w0,w4,w6,w19,w27,w42,w44,w52,w65],[w0,w4,w16,w19,w27,w40,w44,w52,w77],[w0,w4,w16,w19,w33,w40,w44,w52,w65],[w0,w5,w16,w19,w27,w40,w44,w52,w71],[w0,w5,w16,w19,w30,w40,w44,w52,w65],[w0,w6,w12,w16,w19,w27,w40,w60,w65],[w0,w6,w12,w16,w19,w27,w44,w56,w65],[w0,w6,w12,w16,w19,w27,w48,w52,w65],[w0,w6,w12,w16,w27,w40,w44,w52,w97],[w0,w6,w12,w19,w27,w40,w44,w54,w65],[w0,w6,w12,w19,w27,w40,w46,w52,w65],[w0,w6,w12,w19,w27,w42,w44,w52,w65],[w0,w6,w16,w19,w22,w27,w40,w60,w65],[w0,w6,w16,w19,w22,w27,w44,w56,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_20 : t8_20.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_18 : BankTree := .fork [w0,w2,w19,w27,w40,w46,w52,w77] t8_19 t8_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_18 : t8_18.rows.all (refuses 7 t7_0)=true := by simp only [t8_18,BankTree.rows,List.all_append,ok_t8_19,ok_t8_20,Bool.true_and]
noncomputable def t8_22 : BankTree := .block [[w0,w6,w16,w19,w22,w27,w48,w52,w65],[w0,w6,w16,w19,w27,w30,w40,w60,w65],[w0,w6,w16,w19,w27,w30,w44,w56,w65],[w0,w6,w16,w19,w27,w30,w48,w52,w65],[w0,w6,w16,w19,w27,w40,w44,w52,w69],[w0,w6,w16,w19,w27,w40,w44,w52,w73],[w0,w6,w16,w19,w27,w40,w44,w52,w87],[w0,w6,w16,w19,w27,w40,w44,w52,w101],[w0,w6,w16,w19,w27,w40,w44,w52,w112],[w0,w6,w16,w19,w27,w40,w44,w53,w71],[w0,w6,w16,w19,w27,w40,w44,w54,w71],[w0,w6,w16,w19,w27,w40,w44,w56,w71],[w0,w6,w16,w19,w27,w40,w44,w60,w71],[w0,w6,w16,w19,w27,w40,w45,w52,w71],[w0,w6,w16,w19,w27,w40,w46,w52,w71],[w0,w6,w16,w19,w27,w40,w48,w52,w71],[w0,w6,w16,w19,w27,w40,w52,w60,w71],[w0,w6,w16,w19,w27,w40,w60,w65,w71],[w0,w6,w16,w19,w27,w40,w60,w71],[w0,w6,w16,w19,w27,w41,w44,w52,w71],[w0,w6,w16,w19,w27,w42,w44,w52,w71],[w0,w6,w16,w19,w27,w44,w48,w52,w71],[w0,w6,w16,w19,w27,w44,w52,w56,w71],[w0,w6,w16,w19,w27,w44,w56,w65,w71],[w0,w6,w16,w19,w27,w44,w56,w71],[w0,w6,w16,w19,w27,w48,w52,w65,w71],[w0,w6,w16,w19,w27,w48,w52,w71],[w0,w6,w16,w19,w28,w40,w44,w52,w71],[w0,w6,w16,w19,w29,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_22 : t8_22.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_23 : BankTree := .block [[w0,w6,w16,w19,w30,w40,w44,w52,w67],[w0,w6,w16,w19,w30,w40,w44,w52,w71],[w0,w6,w16,w19,w30,w40,w44,w52,w77],[w0,w6,w16,w19,w30,w40,w44,w52,w97],[w0,w6,w16,w19,w30,w40,w44,w52,w109],[w0,w6,w16,w19,w30,w40,w44,w52,w112],[w0,w6,w16,w19,w30,w40,w44,w53,w65],[w0,w6,w16,w19,w30,w40,w44,w54,w65],[w0,w6,w16,w19,w30,w40,w44,w56,w65],[w0,w6,w16,w19,w30,w40,w44,w60,w65],[w0,w6,w16,w19,w30,w40,w45,w52,w65],[w0,w6,w16,w19,w30,w40,w46,w52,w65],[w0,w6,w16,w19,w30,w40,w48,w52,w65],[w0,w6,w16,w19,w30,w40,w52,w60,w65],[w0,w6,w16,w19,w30,w40,w60,w65],[w0,w6,w16,w19,w30,w41,w44,w52,w65],[w0,w6,w16,w19,w30,w42,w44,w52,w65],[w0,w6,w16,w19,w30,w44,w48,w52,w65],[w0,w6,w16,w19,w30,w44,w52,w56,w65],[w0,w6,w16,w19,w30,w44,w56,w65],[w0,w6,w16,w19,w30,w48,w52,w65],[w0,w6,w16,w19,w31,w40,w44,w52,w65],[w0,w6,w16,w19,w33,w40,w44,w52,w71],[w0,w6,w16,w19,w38,w40,w44,w52,w65],[w0,w6,w16,w20,w27,w40,w44,w52,w71],[w0,w6,w16,w20,w30,w40,w44,w52,w65],[w0,w6,w16,w21,w27,w40,w44,w52,w65],[w0,w6,w16,w22,w27,w40,w44,w52,w97],[w0,w6,w16,w27,w30,w40,w44,w52,w97],[w0,w6,w16,w27,w40,w44,w52,w71,w97]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_23 : t8_23.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_21 : BankTree := .fork [w0,w6,w16,w19,w30,w40,w44,w52,w67] t8_22 t8_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_21 : t8_21.rows.all (refuses 7 t7_0)=true := by simp only [t8_21,BankTree.rows,List.all_append,ok_t8_22,ok_t8_23,Bool.true_and]
noncomputable def t8_17 : BankTree := .fork [w0,w6,w16,w19,w22,w27,w48,w52,w65] t8_18 t8_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_17 : t8_17.rows.all (refuses 7 t7_0)=true := by simp only [t8_17,BankTree.rows,List.all_append,ok_t8_18,ok_t8_21,Bool.true_and]
noncomputable def t8_26 : BankTree := .block [[w0,w6,w16,w27,w40,w44,w52,w97,w101],[w0,w6,w18,w19,w27,w40,w44,w52,w71],[w0,w6,w18,w19,w30,w40,w44,w52,w65],[w0,w6,w19,w22,w27,w40,w44,w54,w65],[w0,w6,w19,w22,w27,w40,w46,w52,w65],[w0,w6,w19,w22,w27,w42,w44,w52,w65],[w0,w6,w19,w27,w30,w40,w44,w54,w65],[w0,w6,w19,w27,w30,w40,w46,w52,w65],[w0,w6,w19,w27,w30,w42,w44,w52,w65],[w0,w6,w19,w27,w40,w42,w44,w52,w71],[w0,w6,w19,w27,w40,w44,w46,w52,w71],[w0,w6,w19,w27,w40,w44,w52,w54,w71],[w0,w6,w19,w27,w40,w44,w54,w65,w71],[w0,w6,w19,w27,w40,w44,w54,w71],[w0,w6,w19,w27,w40,w46,w52,w65,w71],[w0,w6,w19,w27,w40,w46,w52,w71],[w0,w6,w19,w27,w42,w44,w52,w65,w71],[w0,w6,w19,w27,w42,w44,w52,w71],[w0,w6,w19,w30,w40,w42,w44,w52,w65],[w0,w6,w19,w30,w40,w44,w46,w52,w65],[w0,w6,w19,w30,w40,w44,w52,w54,w65],[w0,w6,w19,w30,w40,w44,w54,w65],[w0,w6,w19,w30,w40,w46,w52,w65],[w0,w6,w19,w30,w42,w44,w52,w65],[w0,w8,w16,w19,w27,w40,w44,w52,w71],[w0,w8,w16,w19,w30,w40,w44,w52,w65],[w0,w9,w16,w19,w27,w40,w44,w52,w65],[w0,w10,w16,w19,w27,w40,w44,w52,w65],[w0,w11,w16,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_26 : t8_26.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_27 : BankTree := .block [[w0,w12,w16,w19,w27,w40,w44,w52,w67],[w0,w12,w16,w19,w27,w40,w44,w52,w71],[w0,w12,w16,w19,w27,w40,w44,w52,w77],[w0,w12,w16,w19,w27,w40,w44,w52,w87],[w0,w12,w16,w19,w27,w40,w44,w52,w97],[w0,w12,w16,w19,w27,w40,w44,w52,w109],[w0,w12,w16,w19,w27,w40,w44,w53,w65],[w0,w12,w16,w19,w27,w40,w44,w54,w65],[w0,w12,w16,w19,w27,w40,w44,w56,w65],[w0,w12,w16,w19,w27,w40,w44,w60,w65],[w0,w12,w16,w19,w27,w40,w45,w52,w65],[w0,w12,w16,w19,w27,w40,w46,w52,w65],[w0,w12,w16,w19,w27,w40,w48,w52,w65],[w0,w12,w16,w19,w27,w40,w52,w60,w65],[w0,w12,w16,w19,w27,w40,w60,w65],[w0,w12,w16,w19,w27,w41,w44,w52,w65],[w0,w12,w16,w19,w27,w42,w44,w52,w65],[w0,w12,w16,w19,w27,w44,w48,w52,w65],[w0,w12,w16,w19,w27,w44,w52,w56,w65],[w0,w12,w16,w19,w27,w44,w56,w65],[w0,w12,w16,w19,w27,w48,w52,w65],[w0,w12,w16,w19,w28,w40,w44,w52,w65],[w0,w12,w16,w19,w30,w40,w44,w52,w65],[w0,w12,w16,w19,w33,w40,w44,w52,w65],[w0,w12,w16,w19,w38,w40,w44,w52,w65],[w0,w12,w16,w20,w27,w40,w44,w52,w65],[w0,w12,w16,w27,w40,w44,w52,w65,w97],[w0,w12,w16,w27,w40,w44,w52,w97],[w0,w12,w18,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_27 : t8_27.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_25 : BankTree := .fork [w0,w12,w16,w19,w27,w40,w44,w52,w67] t8_26 t8_27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_25 : t8_25.rows.all (refuses 7 t7_0)=true := by simp only [t8_25,BankTree.rows,List.all_append,ok_t8_26,ok_t8_27,Bool.true_and]
noncomputable def t8_29 : BankTree := .block [[w0,w12,w19,w27,w40,w42,w44,w52,w65],[w0,w12,w19,w27,w40,w44,w46,w52,w65],[w0,w12,w19,w27,w40,w44,w52,w54,w65],[w0,w12,w19,w27,w40,w44,w54,w65],[w0,w12,w19,w27,w40,w46,w52,w65],[w0,w12,w19,w27,w42,w44,w52,w65],[w0,w14,w16,w19,w27,w40,w44,w52,w65],[w0,w16,w19,w22,w27,w40,w44,w52,w77],[w0,w16,w19,w22,w33,w40,w44,w52,w65],[w0,w16,w19,w24,w27,w40,w44,w52,w71],[w0,w16,w19,w24,w30,w40,w44,w52,w65],[w0,w16,w19,w26,w27,w40,w44,w52,w65],[w0,w16,w19,w27,w30,w40,w44,w52,w77],[w0,w16,w19,w27,w33,w40,w44,w52,w71],[w0,w16,w19,w27,w38,w40,w44,w52,w65],[w0,w16,w19,w27,w40,w44,w52,w65,w87],[w0,w16,w19,w27,w40,w44,w52,w71,w77],[w0,w16,w19,w27,w40,w44,w52,w71,w87],[w0,w16,w19,w27,w40,w44,w52,w77,w87],[w0,w16,w19,w27,w40,w44,w52,w87],[w0,w16,w19,w30,w33,w40,w44,w52,w65],[w0,w16,w19,w30,w38,w40,w44,w52,w65],[w0,w16,w19,w30,w40,w44,w52,w65,w77],[w0,w16,w19,w30,w40,w44,w52,w77],[w0,w16,w19,w33,w38,w40,w44,w52,w65],[w0,w16,w19,w33,w40,w44,w52,w65,w71],[w0,w16,w19,w33,w40,w44,w52,w71],[w0,w16,w19,w38,w40,w44,w52,w65],[w0,w16,w22,w24,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_29 : t8_29.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_30 : BankTree := .block [[w2,w6,w16,w19,w27,w40,w44,w53,w67],[w2,w6,w16,w19,w27,w40,w45,w52,w67],[w2,w6,w16,w19,w27,w40,w45,w53,w65],[w2,w6,w16,w19,w27,w41,w44,w52,w67],[w2,w6,w16,w19,w27,w41,w44,w53,w65],[w2,w6,w16,w19,w27,w41,w45,w52,w65],[w2,w6,w16,w19,w28,w40,w44,w52,w67],[w2,w6,w16,w19,w28,w40,w44,w53,w65],[w2,w6,w16,w19,w28,w40,w45,w52,w65],[w2,w6,w16,w19,w28,w41,w44,w52,w65],[w2,w6,w16,w20,w27,w40,w44,w53,w65],[w2,w6,w16,w20,w27,w40,w45,w52,w65],[w2,w6,w16,w20,w27,w41,w44,w52,w65],[w2,w6,w16,w20,w28,w40,w44,w52,w65],[w2,w6,w18,w19,w27,w40,w44,w52,w67],[w2,w6,w18,w19,w28,w40,w44,w52,w65],[w2,w6,w18,w20,w27,w40,w44,w52,w65],[w2,w7,w16,w19,w27,w40,w44,w52,w65],[w2,w8,w16,w19,w27,w40,w44,w53,w65],[w2,w8,w16,w19,w27,w40,w45,w52,w65],[w2,w8,w16,w19,w27,w41,w44,w52,w65],[w2,w8,w16,w20,w27,w40,w44,w52,w65],[w2,w8,w18,w19,w27,w40,w44,w52,w65],[w3,w6,w16,w19,w27,w40,w44,w52,w65],[w4,w6,w16,w19,w27,w40,w44,w53,w65],[w4,w6,w16,w19,w27,w40,w45,w52,w65],[w4,w6,w16,w19,w27,w41,w44,w52,w65],[w4,w6,w16,w20,w27,w40,w44,w52,w65],[w4,w6,w18,w19,w27,w40,w44,w52,w65],[w4,w8,w16,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_30 : t8_30.rows.all (refuses 7 t7_0)=true := by decide +kernel
noncomputable def t8_28 : BankTree := .fork [w2,w6,w16,w19,w27,w40,w44,w53,w67] t8_29 t8_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_28 : t8_28.rows.all (refuses 7 t7_0)=true := by simp only [t8_28,BankTree.rows,List.all_append,ok_t8_29,ok_t8_30,Bool.true_and]
noncomputable def t8_24 : BankTree := .fork [w0,w12,w19,w27,w40,w42,w44,w52,w65] t8_25 t8_28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_24 : t8_24.rows.all (refuses 7 t7_0)=true := by simp only [t8_24,BankTree.rows,List.all_append,ok_t8_25,ok_t8_28,Bool.true_and]
noncomputable def t8_16 : BankTree := .fork [w0,w6,w16,w27,w40,w44,w52,w97,w101] t8_17 t8_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_16 : t8_16.rows.all (refuses 7 t7_0)=true := by simp only [t8_16,BankTree.rows,List.all_append,ok_t8_17,ok_t8_24,Bool.true_and]
noncomputable def t8_0 : BankTree := .fork [w0,w2,w16,w19,w33,w41,w44,w52,w65] t8_1 t8_16
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_0 : t8_0.rows.all (refuses 7 t7_0)=true := by simp only [t8_0,BankTree.rows,List.all_append,ok_t8_1,ok_t8_16,Bool.true_and]
theorem safe8 : Safe 8 t8_0 := certify 7 t7_0 t8_0 safe7 ok_t8_0
noncomputable def t9_1 : BankTree := .block [[w0,w1,w6,w16,w19,w27,w40,w44,w52,w65],[w0,w2,w5,w16,w19,w27,w40,w44,w52,w65],[w0,w2,w6,w16,w19,w27,w40,w44,w52,w67],[w0,w2,w6,w16,w19,w27,w40,w44,w52,w71],[w0,w2,w6,w16,w19,w27,w40,w44,w52,w77],[w0,w2,w6,w16,w19,w27,w40,w44,w52,w97],[w0,w2,w6,w16,w19,w27,w40,w44,w52,w109],[w0,w2,w6,w16,w19,w27,w40,w44,w53,w65],[w0,w2,w6,w16,w19,w27,w40,w44,w54,w65],[w0,w2,w6,w16,w19,w27,w40,w44,w56,w65],[w0,w2,w6,w16,w19,w27,w40,w44,w60,w65],[w0,w2,w6,w16,w19,w27,w40,w45,w52,w65],[w0,w2,w6,w16,w19,w27,w40,w46,w52,w65],[w0,w2,w6,w16,w19,w27,w40,w48,w52,w65],[w0,w2,w6,w16,w19,w27,w40,w52,w60,w65],[w0,w2,w6,w16,w19,w27,w40,w60,w65],[w0,w2,w6,w16,w19,w27,w41,w44,w52,w65],[w0,w2,w6,w16,w19,w27,w42,w44,w52,w65],[w0,w2,w6,w16,w19,w27,w44,w48,w52,w65],[w0,w2,w6,w16,w19,w27,w44,w52,w56,w65],[w0,w2,w6,w16,w19,w27,w44,w56,w65],[w0,w2,w6,w16,w19,w27,w48,w52,w65],[w0,w2,w6,w16,w19,w28,w40,w44,w52,w65],[w0,w2,w6,w16,w19,w30,w40,w44,w52,w65],[w0,w2,w6,w16,w19,w33,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t9_1 : t9_1.rows.all (refuses 8 t8_0)=true := by decide +kernel
noncomputable def t9_2 : BankTree := .block [[w0,w2,w6,w16,w20,w27,w40,w44,w52,w65],[w0,w2,w6,w16,w27,w40,w44,w52,w65,w97],[w0,w2,w6,w16,w27,w40,w44,w52,w97],[w0,w2,w6,w18,w19,w27,w40,w44,w52,w65],[w0,w2,w6,w19,w27,w40,w42,w44,w52,w65],[w0,w2,w6,w19,w27,w40,w44,w46,w52,w65],[w0,w2,w6,w19,w27,w40,w44,w52,w54,w65],[w0,w2,w6,w19,w27,w40,w44,w54,w65],[w0,w2,w6,w19,w27,w40,w46,w52,w65],[w0,w2,w6,w19,w27,w42,w44,w52,w65],[w0,w2,w8,w16,w19,w27,w40,w44,w52,w65],[w0,w2,w12,w16,w19,w27,w40,w44,w52,w65],[w0,w2,w16,w19,w24,w27,w40,w44,w52,w65],[w0,w2,w16,w19,w27,w33,w40,w44,w52,w65],[w0,w2,w16,w19,w27,w40,w44,w52,w65,w77],[w0,w2,w16,w19,w27,w40,w44,w52,w77],[w0,w2,w16,w19,w33,w40,w44,w52,w65],[w0,w4,w6,w16,w19,w27,w40,w44,w52,w65],[w0,w6,w12,w16,w19,w27,w40,w44,w52,w65],[w0,w6,w16,w19,w22,w27,w40,w44,w52,w65],[w0,w6,w16,w19,w27,w30,w40,w44,w52,w65],[w0,w6,w16,w19,w27,w40,w44,w52,w65,w71],[w0,w6,w16,w19,w27,w40,w44,w52,w71],[w0,w6,w16,w19,w30,w40,w44,w52,w65],[w0,w12,w16,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t9_2 : t9_2.rows.all (refuses 8 t8_0)=true := by decide +kernel
noncomputable def t9_0 : BankTree := .fork [w0,w2,w6,w16,w20,w27,w40,w44,w52,w65] t9_1 t9_2
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t9_0 : t9_0.rows.all (refuses 8 t8_0)=true := by simp only [t9_0,BankTree.rows,List.all_append,ok_t9_1,ok_t9_2,Bool.true_and]
theorem safe9 : Safe 9 t9_0 := certify 8 t8_0 t9_0 safe8 ok_t9_0
noncomputable def t10_0 : BankTree := .block [[w0,w2,w6,w16,w19,w27,w40,w44,w52,w65]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t10_0 : t10_0.rows.all (refuses 9 t9_0)=true := by decide +kernel
theorem safe10 : Safe 10 t10_0 := certify 9 t9_0 t10_0 safe9 ok_t10_0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem knownRoots : inputs.sublists.all (fun l =>
    decide (11 < l.length) || (!(cuts l == -1) || t10_0.contains (canon l))) = true := by decide +kernel
theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 10 S := extend_live hs hl
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
  have room : ¬(11<l.length) := by omega
  have yy : t10_0.contains (canon l)=true := by simpa [room,hc] using row
  have pp : (canon l).Perm l := List.perm_insertionSort _ _
  have ez : (canon l).toFinset=l.toFinset := by
    ext v; simpa only [List.mem_toFinset] using (pp.mem_iff (a:=v))
  exact safe10 _ yy (pp.nodup_iff.mpr hnd) (ez.symm ▸ (hlS ▸ hl3))

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  rintro ⟨C, hm, hs, hr⟩
  exact no_small C hm hs hr

end PEqualNP.Outside.L_meta_23519

theorem PEqualNP.Outside.L_meta_23519 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_23519.result

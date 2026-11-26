import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20532

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

abbrev W := BitVec 108

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 54 := ((x >>> 54) &&& ~~~x).setWidth 54

def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [(BitVec.ofNat 108 ((0xff * 2^64 + 0xffc30c30c30c30c3) : Nat)), (BitVec.ofNat 108 ((0x3ffff00 * 2^64 + 0xc30c30c30c30c) : Nat)), (BitVec.ofNat 108 ((0xffffc000000 * 2^64 + 0x30c30c30c30c30) : Nat)), (BitVec.ofNat 108 ((0xfc003f00 * 2^64 + 0xfc0000000000000) : Nat)), (BitVec.ofNat 108 ((0x3f000fc000 * 2^64 + 0x1041041041041) : Nat)), (BitVec.ofNat 108 ((0xfc000000003 * 2^64 + 0xf004104104104104) : Nat)), (BitVec.ofNat 108 ((0x3f00000 * 2^64 + 0x12492492492492) : Nat)), (BitVec.ofNat 108 ((0xfc * 2^64 + 0x28a28a28a28a28) : Nat))]

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

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (54 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (54 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 54, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 54) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 108 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
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
  z == 0 || z == BitVec.allOnes 108 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 108) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 108) :
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
    · exact ⟨BitVec.allOnes 108, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 108 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 108 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 108 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 108 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 108) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 108 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 3 → Fin 5 → Bool := fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 3 × Fin 5) :=
  [(0, 0), (0, 2), (0, 4), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1), (2, 2)]

def negL : List (Fin 3 × Fin 5) :=
  [(0, 1), (0, 3), (1, 2), (1, 4), (2, 3), (2, 4)]

def samp (k : Fin 108) : Fin 3 × Fin 5 :=
  if k.val < 54 then negL.getD (k.val % 6) (0, 0) else posL.getD ((k.val - 54) / 6) (0, 0)

theorem input_rows : ∀ k : Fin 108,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 108, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 108) :
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
def atom0 : W := (BitVec.ofNat 108 ((0xfc * 2^64 + 0x0) : Nat))
def atom1 : W := (BitVec.ofNat 108 ((0xfc * 2^64 + 0x28a28a28a28a28) : Nat))
def atom2 : W := (BitVec.ofNat 108 ((0xff * 2^64 + 0xf000000000000000) : Nat))
def atom3 : W := (BitVec.ofNat 108 ((0xff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom4 : W := (BitVec.ofNat 108 ((0x3f00000 * 2^64 + 0x0) : Nat))
def atom5 : W := (BitVec.ofNat 108 ((0x3f00000 * 2^64 + 0x12492492492492) : Nat))
def atom6 : W := (BitVec.ofNat 108 ((0x3f000ff * 2^64 + 0xf000000000000000) : Nat))
def atom7 : W := (BitVec.ofNat 108 ((0x3f000ff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom8 : W := (BitVec.ofNat 108 ((0x3f000ff * 2^64 + 0xffd34d34d34d34d3) : Nat))
def atom9 : W := (BitVec.ofNat 108 ((0x3ffc000 * 2^64 + 0x0) : Nat))
def atom10 : W := (BitVec.ofNat 108 ((0x3ffc0fc * 2^64 + 0x0) : Nat))
def atom11 : W := (BitVec.ofNat 108 ((0x3ffff00 * 2^64 + 0xc30c30c30c30c) : Nat))
def atom12 : W := (BitVec.ofNat 108 ((0x3fffffc * 2^64 + 0xc30c30c30c30c) : Nat))
def atom13 : W := (BitVec.ofNat 108 ((0x3fffffc * 2^64 + 0x2cb2cb2cb2cb2c) : Nat))
def atom14 : W := (BitVec.ofNat 108 ((0xfc003f00 * 2^64 + 0xfc0000000000000) : Nat))
def atom15 : W := (BitVec.ofNat 108 ((0xfc003ffc * 2^64 + 0xfc0000000000000) : Nat))
def atom16 : W := (BitVec.ofNat 108 ((0xfc003ffc * 2^64 + 0xfe8a28a28a28a28) : Nat))
def atom17 : W := (BitVec.ofNat 108 ((0xfc003fff * 2^64 + 0xffc0000000000000) : Nat))
def atom18 : W := (BitVec.ofNat 108 ((0xfc003fff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom19 : W := (BitVec.ofNat 108 ((0xfff03f00 * 2^64 + 0xfc0000000000000) : Nat))
def atom20 : W := (BitVec.ofNat 108 ((0xfff03f00 * 2^64 + 0xfd2492492492492) : Nat))
def atom21 : W := (BitVec.ofNat 108 ((0xfff03fff * 2^64 + 0xffc0000000000000) : Nat))
def atom22 : W := (BitVec.ofNat 108 ((0xfff03fff * 2^64 + 0xffd34d34d34d34d3) : Nat))
def atom23 : W := (BitVec.ofNat 108 ((0xffffff00 * 2^64 + 0xfc0000000000000) : Nat))
def atom24 : W := (BitVec.ofNat 108 ((0xffffff00 * 2^64 + 0xfcc30c30c30c30c) : Nat))
def atom25 : W := (BitVec.ofNat 108 ((0xfffffffc * 2^64 + 0xfc0000000000000) : Nat))
def atom26 : W := (BitVec.ofNat 108 ((0xfffffffc * 2^64 + 0xfecb2cb2cb2cb2c) : Nat))
def atom27 : W := (BitVec.ofNat 108 ((0x3f000fc000 * 2^64 + 0x1041041041041) : Nat))
def atom28 : W := (BitVec.ofNat 108 ((0x3f000fc0ff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom29 : W := (BitVec.ofNat 108 ((0x3f03ffc000 * 2^64 + 0x1041041041041) : Nat))
def atom30 : W := (BitVec.ofNat 108 ((0x3f03ffc000 * 2^64 + 0x134d34d34d34d3) : Nat))
def atom31 : W := (BitVec.ofNat 108 ((0x3f03ffc0ff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom32 : W := (BitVec.ofNat 108 ((0x3f03ffc0ff * 2^64 + 0xffd34d34d34d34d3) : Nat))
def atom33 : W := (BitVec.ofNat 108 ((0x3ffc0fff00 * 2^64 + 0xfc1041041041041) : Nat))
def atom34 : W := (BitVec.ofNat 108 ((0x3ffc0fffff * 2^64 + 0xffc30c30c30c30c3) : Nat))
def atom35 : W := (BitVec.ofNat 108 ((0xfc000000003 * 2^64 + 0xf004104104104104) : Nat))
def atom36 : W := (BitVec.ofNat 108 ((0xfc0000000ff * 2^64 + 0xf004104104104104) : Nat))
def atom37 : W := (BitVec.ofNat 108 ((0xfc0000000ff * 2^64 + 0xf02cb2cb2cb2cb2c) : Nat))
def atom38 : W := (BitVec.ofNat 108 ((0xfc003ffff03 * 2^64 + 0xf00c30c30c30c30c) : Nat))
def atom39 : W := (BitVec.ofNat 108 ((0xfc003ffffff * 2^64 + 0xf00c30c30c30c30c) : Nat))
def atom40 : W := (BitVec.ofNat 108 ((0xfc003ffffff * 2^64 + 0xf02cb2cb2cb2cb2c) : Nat))
def atom41 : W := (BitVec.ofNat 108 ((0xfc0fc003f03 * 2^64 + 0xffc4104104104104) : Nat))
def atom42 : W := (BitVec.ofNat 108 ((0xfc0ffffff03 * 2^64 + 0xffcc30c30c30c30c) : Nat))
def atom43 : W := (BitVec.ofNat 108 ((0xffffc000000 * 2^64 + 0x30c30c30c30c30) : Nat))
def atom44 : W := (BitVec.ofNat 108 ((0xffffc0000fc * 2^64 + 0x30c30c30c30c30) : Nat))
def atom45 : W := (BitVec.ofNat 108 ((0xffffc0000fc * 2^64 + 0x38e38e38e38e38) : Nat))
def atom46 : W := (BitVec.ofNat 108 ((0xffffc003f00 * 2^64 + 0xff0c30c30c30c30) : Nat))
def atom47 : W := (BitVec.ofNat 108 ((0xffffc003ffc * 2^64 + 0xff8e38e38e38e38) : Nat))
def atom48 : W := (BitVec.ofNat 108 ((0xffffff00000 * 2^64 + 0x30c30c30c30c30) : Nat))
def atom49 : W := (BitVec.ofNat 108 ((0xffffff00000 * 2^64 + 0x32cb2cb2cb2cb2) : Nat))
def atom50 : W := (BitVec.ofNat 108 ((0xffffff03f00 * 2^64 + 0xff2cb2cb2cb2cb2) : Nat))
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
noncomputable def t3_0 : BankTree := .block [[atom17,atom27,atom38,atom49],[atom21,atom27,atom38,atom43],[atom23,atom28,atom35,atom45],[atom25,atom28,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t3_0 : t3_0.rows.all (refuses 2 t2_0)=true := by decide +kernel
theorem safe3 : Safe 3 t3_0 := certify 2 t2_0 t3_0 safe2 ok_t3_0
noncomputable def t4_3 : BankTree := .block [[atom1,atom3,atom27,atom42,atom50],[atom1,atom3,atom33,atom38,atom50],[atom1,atom3,atom33,atom42,atom49],[atom1,atom5,atom28,atom42,atom46],[atom1,atom5,atom34,atom38,atom46],[atom1,atom5,atom34,atom42,atom43],[atom1,atom8,atom27,atom42,atom46]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_3 : t4_3.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_4 : BankTree := .block [[atom1,atom8,atom33,atom38,atom46],[atom1,atom8,atom33,atom42,atom43],[atom1,atom14,atom28,atom38,atom48],[atom1,atom14,atom31,atom38,atom43],[atom1,atom18,atom27,atom42,atom49],[atom1,atom19,atom28,atom38,atom43],[atom1,atom20,atom28,atom42,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_4 : t4_4.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_2 : BankTree := .fork [atom1,atom8,atom33,atom38,atom46] t4_3 t4_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_2 : t4_2.rows.all (refuses 3 t3_0)=true := by simp only [t4_2,BankTree.rows,List.all_append,ok_t4_3,ok_t4_4,Bool.true_and]
noncomputable def t4_6 : BankTree := .block [[atom1,atom22,atom27,atom42,atom43],[atom1,atom23,atom28,atom35,atom43],[atom2,atom14,atom27,atom38,atom49],[atom3,atom14,atom27,atom39,atom49],[atom3,atom15,atom27,atom38,atom49],[atom3,atom16,atom33,atom38,atom49],[atom3,atom23,atom27,atom35,atom45]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_6 : t4_6.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_7 : BankTree := .block [[atom5,atom11,atom28,atom41,atom47],[atom5,atom11,atom34,atom35,atom47],[atom5,atom11,atom34,atom41,atom45],[atom5,atom13,atom28,atom41,atom46],[atom5,atom13,atom34,atom35,atom46],[atom5,atom13,atom34,atom41,atom43],[atom5,atom14,atom28,atom38,atom44],[atom5,atom14,atom28,atom39,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_7 : t4_7.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_5 : BankTree := .fork [atom5,atom11,atom28,atom41,atom47] t4_6 t4_7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_5 : t4_5.rows.all (refuses 3 t3_0)=true := by simp only [t4_5,BankTree.rows,List.all_append,ok_t4_6,ok_t4_7,Bool.true_and]
noncomputable def t4_1 : BankTree := .fork [atom1,atom22,atom27,atom42,atom43] t4_2 t4_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_1 : t4_1.rows.all (refuses 3 t3_0)=true := by simp only [t4_1,BankTree.rows,List.all_append,ok_t4_2,ok_t4_5,Bool.true_and]
noncomputable def t4_10 : BankTree := .block [[atom5,atom15,atom28,atom38,atom43],[atom5,atom16,atom34,atom38,atom43],[atom5,atom17,atom27,atom38,atom43],[atom5,atom24,atom34,atom35,atom45],[atom5,atom26,atom34,atom35,atom43],[atom6,atom14,atom27,atom38,atom43],[atom8,atom13,atom27,atom41,atom46]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_10 : t4_10.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_11 : BankTree := .block [[atom8,atom13,atom33,atom35,atom46],[atom8,atom13,atom33,atom41,atom43],[atom8,atom14,atom27,atom39,atom43],[atom8,atom15,atom27,atom38,atom43],[atom8,atom16,atom33,atom38,atom43],[atom8,atom26,atom33,atom35,atom43],[atom9,atom14,atom28,atom35,atom45],[atom10,atom14,atom28,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_11 : t4_11.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_9 : BankTree := .fork [atom8,atom13,atom33,atom35,atom46] t4_10 t4_11
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_9 : t4_9.rows.all (refuses 3 t3_0)=true := by simp only [t4_9,BankTree.rows,List.all_append,ok_t4_10,ok_t4_11,Bool.true_and]
noncomputable def t4_13 : BankTree := .block [[atom11,atom14,atom31,atom35,atom45],[atom11,atom17,atom27,atom35,atom49],[atom11,atom19,atom28,atom35,atom45],[atom11,atom20,atom28,atom41,atom45],[atom13,atom14,atom31,atom35,atom43],[atom13,atom19,atom28,atom35,atom43],[atom13,atom20,atom28,atom41,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_13 : t4_13.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_14 : BankTree := .block [[atom13,atom22,atom27,atom41,atom43],[atom14,atom28,atom38,atom45,atom49],[atom16,atom18,atom27,atom38,atom49],[atom16,atom20,atom28,atom38,atom43],[atom16,atom22,atom27,atom38,atom43],[atom20,atom24,atom28,atom35,atom45],[atom20,atom26,atom28,atom35,atom43],[atom22,atom26,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_14 : t4_14.rows.all (refuses 3 t3_0)=true := by decide +kernel
noncomputable def t4_12 : BankTree := .fork [atom13,atom22,atom27,atom41,atom43] t4_13 t4_14
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_12 : t4_12.rows.all (refuses 3 t3_0)=true := by simp only [t4_12,BankTree.rows,List.all_append,ok_t4_13,ok_t4_14,Bool.true_and]
noncomputable def t4_8 : BankTree := .fork [atom11,atom14,atom31,atom35,atom45] t4_9 t4_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_8 : t4_8.rows.all (refuses 3 t3_0)=true := by simp only [t4_8,BankTree.rows,List.all_append,ok_t4_9,ok_t4_12,Bool.true_and]
noncomputable def t4_0 : BankTree := .fork [atom5,atom15,atom28,atom38,atom43] t4_1 t4_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t4_0 : t4_0.rows.all (refuses 3 t3_0)=true := by simp only [t4_0,BankTree.rows,List.all_append,ok_t4_1,ok_t4_8,Bool.true_and]
theorem safe4 : Safe 4 t4_0 := certify 3 t3_0 t4_0 safe3 ok_t4_0
noncomputable def t5_4 : BankTree := .block [[atom0,atom3,atom14,atom27,atom38,atom49],[atom0,atom5,atom14,atom28,atom38,atom43],[atom0,atom8,atom14,atom27,atom38,atom43],[atom1,atom3,atom5,atom27,atom42,atom46],[atom1,atom3,atom5,atom33,atom38,atom46],[atom1,atom3,atom5,atom33,atom42,atom43],[atom1,atom3,atom11,atom27,atom41,atom50],[atom1,atom3,atom11,atom33,atom35,atom50],[atom1,atom3,atom11,atom33,atom41,atom49],[atom1,atom3,atom14,atom27,atom38,atom48]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_4 : t5_4.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_5 : BankTree := .block [[atom1,atom3,atom14,atom27,atom38,atom50],[atom1,atom3,atom14,atom27,atom42,atom49],[atom1,atom3,atom14,atom29,atom38,atom43],[atom1,atom3,atom14,atom33,atom38,atom49],[atom1,atom3,atom19,atom27,atom38,atom43],[atom1,atom3,atom20,atom27,atom42,atom43],[atom1,atom3,atom20,atom33,atom38,atom43],[atom1,atom3,atom23,atom27,atom35,atom43],[atom1,atom3,atom24,atom27,atom35,atom50],[atom1,atom3,atom24,atom33,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_5 : t5_5.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_3 : BankTree := .fork [atom1,atom3,atom14,atom27,atom38,atom50] t5_4 t5_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_3 : t5_3.rows.all (refuses 4 t4_0)=true := by simp only [t5_3,BankTree.rows,List.all_append,ok_t5_4,ok_t5_5,Bool.true_and]
noncomputable def t5_7 : BankTree := .block [[atom1,atom4,atom14,atom28,atom38,atom43],[atom1,atom5,atom11,atom28,atom41,atom46],[atom1,atom5,atom11,atom34,atom35,atom46],[atom1,atom5,atom11,atom34,atom41,atom43],[atom1,atom5,atom14,atom28,atom38,atom46],[atom1,atom5,atom14,atom28,atom42,atom43],[atom1,atom5,atom14,atom34,atom38,atom43],[atom1,atom5,atom18,atom27,atom38,atom46],[atom1,atom5,atom18,atom27,atom42,atom43],[atom1,atom5,atom24,atom28,atom35,atom46]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_7 : t5_7.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_8 : BankTree := .block [[atom1,atom5,atom24,atom34,atom35,atom43],[atom1,atom7,atom14,atom27,atom38,atom43],[atom1,atom8,atom11,atom27,atom41,atom46],[atom1,atom8,atom11,atom33,atom35,atom46],[atom1,atom8,atom11,atom33,atom41,atom43],[atom1,atom8,atom14,atom27,atom38,atom46],[atom1,atom8,atom14,atom27,atom38,atom49],[atom1,atom8,atom14,atom27,atom42,atom43],[atom1,atom8,atom14,atom28,atom38,atom43],[atom1,atom8,atom14,atom33,atom38,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_8 : t5_8.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_6 : BankTree := .fork [atom1,atom5,atom24,atom34,atom35,atom43] t5_7 t5_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_6 : t5_6.rows.all (refuses 4 t4_0)=true := by simp only [t5_6,BankTree.rows,List.all_append,ok_t5_7,ok_t5_8,Bool.true_and]
noncomputable def t5_2 : BankTree := .fork [atom1,atom4,atom14,atom28,atom38,atom43] t5_3 t5_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_2 : t5_2.rows.all (refuses 4 t4_0)=true := by simp only [t5_2,BankTree.rows,List.all_append,ok_t5_3,ok_t5_6,Bool.true_and]
noncomputable def t5_11 : BankTree := .block [[atom1,atom8,atom24,atom27,atom35,atom46],[atom1,atom8,atom24,atom33,atom35,atom43],[atom1,atom9,atom14,atom28,atom35,atom43],[atom1,atom11,atom14,atom28,atom35,atom48],[atom1,atom11,atom14,atom31,atom35,atom43],[atom1,atom11,atom18,atom27,atom41,atom49],[atom1,atom11,atom19,atom28,atom35,atom43],[atom1,atom11,atom20,atom28,atom41,atom43],[atom1,atom11,atom22,atom27,atom41,atom43],[atom1,atom14,atom18,atom27,atom38,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_11 : t5_11.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_12 : BankTree := .block [[atom1,atom14,atom20,atom28,atom38,atom43],[atom1,atom14,atom22,atom27,atom38,atom43],[atom1,atom14,atom27,atom28,atom38,atom49],[atom1,atom14,atom27,atom32,atom38,atom43],[atom1,atom14,atom28,atom30,atom38,atom43],[atom1,atom14,atom28,atom32,atom38,atom43],[atom1,atom14,atom28,atom38,atom43,atom49],[atom1,atom18,atom24,atom27,atom35,atom49],[atom1,atom20,atom24,atom28,atom35,atom43],[atom1,atom22,atom24,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_12 : t5_12.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_10 : BankTree := .fork [atom1,atom14,atom20,atom28,atom38,atom43] t5_11 t5_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_10 : t5_10.rows.all (refuses 4 t4_0)=true := by simp only [t5_10,BankTree.rows,List.all_append,ok_t5_11,ok_t5_12,Bool.true_and]
noncomputable def t5_14 : BankTree := .block [[atom2,atom5,atom14,atom27,atom38,atom43],[atom2,atom11,atom14,atom27,atom35,atom49],[atom3,atom5,atom11,atom27,atom41,atom47],[atom3,atom5,atom11,atom33,atom35,atom47],[atom3,atom5,atom11,atom33,atom41,atom45],[atom3,atom5,atom13,atom27,atom41,atom46],[atom3,atom5,atom13,atom33,atom35,atom46],[atom3,atom5,atom13,atom33,atom41,atom43],[atom3,atom5,atom14,atom27,atom38,atom44],[atom3,atom5,atom14,atom27,atom39,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_14 : t5_14.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_15 : BankTree := .block [[atom3,atom5,atom15,atom27,atom38,atom43],[atom3,atom5,atom16,atom33,atom38,atom43],[atom3,atom5,atom24,atom33,atom35,atom45],[atom3,atom5,atom26,atom33,atom35,atom43],[atom3,atom9,atom14,atom27,atom35,atom45],[atom3,atom11,atom14,atom27,atom36,atom49],[atom3,atom11,atom14,atom29,atom35,atom45],[atom3,atom11,atom15,atom27,atom35,atom49],[atom3,atom11,atom16,atom27,atom41,atom49],[atom3,atom11,atom16,atom33,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_15 : t5_15.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_13 : BankTree := .fork [atom3,atom5,atom15,atom27,atom38,atom43] t5_14 t5_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_13 : t5_13.rows.all (refuses 4 t4_0)=true := by simp only [t5_13,BankTree.rows,List.all_append,ok_t5_14,ok_t5_15,Bool.true_and]
noncomputable def t5_9 : BankTree := .fork [atom2,atom5,atom14,atom27,atom38,atom43] t5_10 t5_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_9 : t5_9.rows.all (refuses 4 t4_0)=true := by simp only [t5_9,BankTree.rows,List.all_append,ok_t5_10,ok_t5_13,Bool.true_and]
noncomputable def t5_1 : BankTree := .fork [atom1,atom8,atom24,atom27,atom35,atom46] t5_2 t5_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_1 : t5_1.rows.all (refuses 4 t4_0)=true := by simp only [t5_1,BankTree.rows,List.all_append,ok_t5_2,ok_t5_9,Bool.true_and]
noncomputable def t5_19 : BankTree := .block [[atom3,atom11,atom19,atom27,atom35,atom45],[atom3,atom11,atom20,atom27,atom41,atom45],[atom3,atom11,atom20,atom33,atom35,atom45],[atom3,atom12,atom14,atom27,atom35,atom49],[atom3,atom13,atom14,atom27,atom38,atom49],[atom3,atom13,atom14,atom29,atom35,atom43],[atom3,atom13,atom19,atom27,atom35,atom43],[atom3,atom13,atom20,atom27,atom41,atom43],[atom3,atom13,atom20,atom33,atom35,atom43],[atom3,atom14,atom16,atom27,atom38,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_19 : t5_19.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_20 : BankTree := .block [[atom3,atom14,atom27,atom37,atom38,atom49],[atom3,atom14,atom27,atom38,atom40,atom49],[atom3,atom14,atom27,atom38,atom45,atom49],[atom3,atom16,atom20,atom27,atom38,atom43],[atom3,atom20,atom24,atom27,atom35,atom45],[atom3,atom20,atom26,atom27,atom35,atom43],[atom4,atom11,atom14,atom28,atom35,atom45],[atom4,atom13,atom14,atom28,atom35,atom43],[atom5,atom11,atom14,atom28,atom35,atom44],[atom5,atom11,atom14,atom28,atom35,atom47]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_20 : t5_20.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_18 : BankTree := .fork [atom3,atom14,atom27,atom37,atom38,atom49] t5_19 t5_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_18 : t5_18.rows.all (refuses 4 t4_0)=true := by simp only [t5_18,BankTree.rows,List.all_append,ok_t5_19,ok_t5_20,Bool.true_and]
noncomputable def t5_22 : BankTree := .block [[atom5,atom11,atom14,atom28,atom36,atom43],[atom5,atom11,atom14,atom28,atom41,atom45],[atom5,atom11,atom14,atom34,atom35,atom45],[atom5,atom11,atom15,atom28,atom35,atom43],[atom5,atom11,atom16,atom28,atom41,atom43],[atom5,atom11,atom16,atom34,atom35,atom43],[atom5,atom11,atom17,atom27,atom35,atom43],[atom5,atom11,atom18,atom27,atom35,atom47],[atom5,atom11,atom18,atom27,atom41,atom45],[atom5,atom12,atom14,atom28,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_22 : t5_22.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_23 : BankTree := .block [[atom5,atom13,atom14,atom28,atom35,atom45],[atom5,atom13,atom14,atom28,atom35,atom46],[atom5,atom13,atom14,atom28,atom38,atom43],[atom5,atom13,atom14,atom28,atom41,atom43],[atom5,atom13,atom14,atom34,atom35,atom43],[atom5,atom13,atom18,atom27,atom35,atom46],[atom5,atom13,atom18,atom27,atom41,atom43],[atom5,atom14,atom16,atom28,atom38,atom43],[atom5,atom14,atom24,atom28,atom35,atom45],[atom5,atom14,atom26,atom28,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_23 : t5_23.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_21 : BankTree := .fork [atom5,atom13,atom14,atom28,atom35,atom45] t5_22 t5_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_21 : t5_21.rows.all (refuses 4 t4_0)=true := by simp only [t5_21,BankTree.rows,List.all_append,ok_t5_22,ok_t5_23,Bool.true_and]
noncomputable def t5_17 : BankTree := .fork [atom5,atom11,atom14,atom28,atom36,atom43] t5_18 t5_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_17 : t5_17.rows.all (refuses 4 t4_0)=true := by simp only [t5_17,BankTree.rows,List.all_append,ok_t5_18,ok_t5_21,Bool.true_and]
noncomputable def t5_26 : BankTree := .block [[atom5,atom14,atom28,atom35,atom38,atom45],[atom5,atom14,atom28,atom35,atom40,atom43],[atom5,atom14,atom28,atom37,atom38,atom43],[atom5,atom14,atom28,atom38,atom40,atom43],[atom5,atom14,atom28,atom38,atom43,atom45],[atom5,atom16,atom18,atom27,atom38,atom43],[atom5,atom18,atom24,atom27,atom35,atom45],[atom5,atom18,atom26,atom27,atom35,atom43],[atom7,atom11,atom14,atom27,atom35,atom45],[atom7,atom13,atom14,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_26 : t5_26.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_27 : BankTree := .block [[atom8,atom11,atom14,atom27,atom36,atom43],[atom8,atom11,atom14,atom28,atom35,atom45],[atom8,atom11,atom15,atom27,atom35,atom43],[atom8,atom11,atom16,atom27,atom41,atom43],[atom8,atom11,atom16,atom33,atom35,atom43],[atom8,atom12,atom14,atom27,atom35,atom43],[atom8,atom13,atom14,atom27,atom35,atom45],[atom8,atom13,atom14,atom27,atom35,atom46],[atom8,atom13,atom14,atom27,atom35,atom49],[atom8,atom13,atom14,atom27,atom38,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_27 : t5_27.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_25 : BankTree := .fork [atom8,atom11,atom14,atom27,atom36,atom43] t5_26 t5_27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_25 : t5_25.rows.all (refuses 4 t4_0)=true := by simp only [t5_25,BankTree.rows,List.all_append,ok_t5_26,ok_t5_27,Bool.true_and]
noncomputable def t5_29 : BankTree := .block [[atom8,atom13,atom14,atom27,atom41,atom43],[atom8,atom13,atom14,atom28,atom35,atom43],[atom8,atom13,atom14,atom33,atom35,atom43],[atom8,atom14,atom16,atom27,atom38,atom43],[atom8,atom14,atom26,atom27,atom35,atom43],[atom8,atom14,atom27,atom35,atom40,atom43],[atom8,atom14,atom27,atom37,atom38,atom43],[atom8,atom14,atom27,atom38,atom40,atom43],[atom11,atom14,atom20,atom28,atom35,atom45],[atom11,atom14,atom28,atom30,atom35,atom45]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_29 : t5_29.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_30 : BankTree := .block [[atom11,atom14,atom28,atom32,atom35,atom45],[atom11,atom14,atom28,atom35,atom45,atom49],[atom11,atom16,atom18,atom27,atom35,atom49],[atom11,atom16,atom20,atom28,atom35,atom43],[atom11,atom16,atom22,atom27,atom35,atom43],[atom13,atom14,atom20,atom28,atom35,atom43],[atom13,atom14,atom22,atom27,atom35,atom43],[atom13,atom14,atom27,atom32,atom35,atom43],[atom13,atom14,atom28,atom30,atom35,atom43],[atom13,atom14,atom28,atom32,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_30 : t5_30.rows.all (refuses 4 t4_0)=true := by decide +kernel
noncomputable def t5_28 : BankTree := .fork [atom11,atom14,atom28,atom32,atom35,atom45] t5_29 t5_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_28 : t5_28.rows.all (refuses 4 t4_0)=true := by simp only [t5_28,BankTree.rows,List.all_append,ok_t5_29,ok_t5_30,Bool.true_and]
noncomputable def t5_24 : BankTree := .fork [atom8,atom13,atom14,atom27,atom41,atom43] t5_25 t5_28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_24 : t5_24.rows.all (refuses 4 t4_0)=true := by simp only [t5_24,BankTree.rows,List.all_append,ok_t5_25,ok_t5_28,Bool.true_and]
noncomputable def t5_16 : BankTree := .fork [atom5,atom14,atom28,atom35,atom38,atom45] t5_17 t5_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_16 : t5_16.rows.all (refuses 4 t4_0)=true := by simp only [t5_16,BankTree.rows,List.all_append,ok_t5_17,ok_t5_24,Bool.true_and]
noncomputable def t5_0 : BankTree := .fork [atom3,atom11,atom19,atom27,atom35,atom45] t5_1 t5_16
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t5_0 : t5_0.rows.all (refuses 4 t4_0)=true := by simp only [t5_0,BankTree.rows,List.all_append,ok_t5_1,ok_t5_16,Bool.true_and]
theorem safe5 : Safe 5 t5_0 := certify 4 t4_0 t5_0 safe4 ok_t5_0
noncomputable def t6_4 : BankTree := .block [[atom0,atom3,atom5,atom14,atom27,atom38,atom43],[atom0,atom3,atom11,atom14,atom27,atom35,atom49],[atom0,atom5,atom11,atom14,atom28,atom35,atom43],[atom0,atom8,atom11,atom14,atom27,atom35,atom43],[atom1,atom3,atom4,atom14,atom27,atom38,atom43],[atom1,atom3,atom5,atom11,atom27,atom41,atom46],[atom1,atom3,atom5,atom11,atom33,atom35,atom46]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_4 : t6_4.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_5 : BankTree := .block [[atom1,atom3,atom5,atom11,atom33,atom41,atom43],[atom1,atom3,atom5,atom14,atom27,atom38,atom46],[atom1,atom3,atom5,atom14,atom27,atom38,atom49],[atom1,atom3,atom5,atom14,atom27,atom42,atom43],[atom1,atom3,atom5,atom14,atom28,atom38,atom43],[atom1,atom3,atom5,atom14,atom33,atom38,atom43],[atom1,atom3,atom5,atom24,atom27,atom35,atom46],[atom1,atom3,atom5,atom24,atom33,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_5 : t6_5.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_3 : BankTree := .fork [atom1,atom3,atom5,atom11,atom33,atom41,atom43] t6_4 t6_5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_3 : t6_3.rows.all (refuses 5 t5_0)=true := by simp only [t6_3,BankTree.rows,List.all_append,ok_t6_4,ok_t6_5,Bool.true_and]
noncomputable def t6_7 : BankTree := .block [[atom1,atom3,atom8,atom14,atom27,atom38,atom43],[atom1,atom3,atom9,atom14,atom27,atom35,atom43],[atom1,atom3,atom11,atom14,atom27,atom35,atom48],[atom1,atom3,atom11,atom14,atom27,atom35,atom50],[atom1,atom3,atom11,atom14,atom27,atom38,atom49],[atom1,atom3,atom11,atom14,atom27,atom41,atom49],[atom1,atom3,atom11,atom14,atom29,atom35,atom43],[atom1,atom3,atom11,atom14,atom33,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_7 : t6_7.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_8 : BankTree := .block [[atom1,atom3,atom11,atom19,atom27,atom35,atom43],[atom1,atom3,atom11,atom20,atom27,atom41,atom43],[atom1,atom3,atom11,atom20,atom33,atom35,atom43],[atom1,atom3,atom14,atom20,atom27,atom38,atom43],[atom1,atom3,atom14,atom24,atom27,atom35,atom49],[atom1,atom3,atom14,atom27,atom30,atom38,atom43],[atom1,atom3,atom14,atom27,atom35,atom38,atom49],[atom1,atom3,atom14,atom27,atom38,atom43,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_8 : t6_8.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_6 : BankTree := .fork [atom1,atom3,atom11,atom19,atom27,atom35,atom43] t6_7 t6_8
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_6 : t6_6.rows.all (refuses 5 t5_0)=true := by simp only [t6_6,BankTree.rows,List.all_append,ok_t6_7,ok_t6_8,Bool.true_and]
noncomputable def t6_2 : BankTree := .fork [atom1,atom3,atom8,atom14,atom27,atom38,atom43] t6_3 t6_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_2 : t6_2.rows.all (refuses 5 t5_0)=true := by simp only [t6_2,BankTree.rows,List.all_append,ok_t6_3,ok_t6_6,Bool.true_and]
noncomputable def t6_11 : BankTree := .block [[atom1,atom3,atom14,atom27,atom38,atom49],[atom1,atom3,atom20,atom24,atom27,atom35,atom43],[atom1,atom4,atom11,atom14,atom28,atom35,atom43],[atom1,atom5,atom8,atom14,atom27,atom38,atom43],[atom1,atom5,atom11,atom14,atom28,atom35,atom45],[atom1,atom5,atom11,atom14,atom28,atom35,atom46],[atom1,atom5,atom11,atom14,atom28,atom38,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_11 : t6_11.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_12 : BankTree := .block [[atom1,atom5,atom11,atom14,atom28,atom41,atom43],[atom1,atom5,atom11,atom14,atom34,atom35,atom43],[atom1,atom5,atom11,atom18,atom27,atom35,atom46],[atom1,atom5,atom11,atom18,atom27,atom41,atom43],[atom1,atom5,atom13,atom14,atom28,atom35,atom43],[atom1,atom5,atom14,atom18,atom27,atom38,atom43],[atom1,atom5,atom14,atom24,atom28,atom35,atom43],[atom1,atom5,atom14,atom27,atom28,atom38,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_12 : t6_12.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_10 : BankTree := .fork [atom1,atom5,atom11,atom14,atom28,atom41,atom43] t6_11 t6_12
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_10 : t6_10.rows.all (refuses 5 t5_0)=true := by simp only [t6_10,BankTree.rows,List.all_append,ok_t6_11,ok_t6_12,Bool.true_and]
noncomputable def t6_14 : BankTree := .block [[atom1,atom5,atom14,atom28,atom35,atom38,atom43],[atom1,atom5,atom14,atom28,atom38,atom43],[atom1,atom5,atom18,atom24,atom27,atom35,atom43],[atom1,atom7,atom11,atom14,atom27,atom35,atom43],[atom1,atom8,atom11,atom14,atom27,atom35,atom45],[atom1,atom8,atom11,atom14,atom27,atom35,atom46],[atom1,atom8,atom11,atom14,atom27,atom35,atom49],[atom1,atom8,atom11,atom14,atom27,atom38,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_14 : t6_14.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_15 : BankTree := .block [[atom1,atom8,atom11,atom14,atom27,atom41,atom43],[atom1,atom8,atom11,atom14,atom28,atom35,atom43],[atom1,atom8,atom11,atom14,atom33,atom35,atom43],[atom1,atom8,atom13,atom14,atom27,atom35,atom43],[atom1,atom8,atom14,atom24,atom27,atom35,atom43],[atom1,atom8,atom14,atom27,atom35,atom38,atom43],[atom1,atom8,atom14,atom27,atom38,atom43],[atom1,atom11,atom14,atom18,atom27,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_15 : t6_15.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_13 : BankTree := .fork [atom1,atom8,atom11,atom14,atom27,atom41,atom43] t6_14 t6_15
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_13 : t6_13.rows.all (refuses 5 t5_0)=true := by simp only [t6_13,BankTree.rows,List.all_append,ok_t6_14,ok_t6_15,Bool.true_and]
noncomputable def t6_9 : BankTree := .fork [atom1,atom5,atom14,atom28,atom35,atom38,atom43] t6_10 t6_13
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_9 : t6_9.rows.all (refuses 5 t5_0)=true := by simp only [t6_9,BankTree.rows,List.all_append,ok_t6_10,ok_t6_13,Bool.true_and]
noncomputable def t6_1 : BankTree := .fork [atom1,atom3,atom14,atom27,atom38,atom49] t6_2 t6_9
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_1 : t6_1.rows.all (refuses 5 t5_0)=true := by simp only [t6_1,BankTree.rows,List.all_append,ok_t6_2,ok_t6_9,Bool.true_and]
noncomputable def t6_19 : BankTree := .block [[atom1,atom11,atom14,atom20,atom28,atom35,atom43],[atom1,atom11,atom14,atom22,atom27,atom35,atom43],[atom1,atom11,atom14,atom27,atom28,atom35,atom49],[atom1,atom11,atom14,atom27,atom32,atom35,atom43],[atom1,atom11,atom14,atom28,atom30,atom35,atom43],[atom1,atom11,atom14,atom28,atom32,atom35,atom43],[atom1,atom11,atom14,atom28,atom35,atom43,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_19 : t6_19.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_20 : BankTree := .block [[atom2,atom5,atom11,atom14,atom27,atom35,atom43],[atom3,atom4,atom11,atom14,atom27,atom35,atom45],[atom3,atom4,atom13,atom14,atom27,atom35,atom43],[atom3,atom5,atom11,atom14,atom27,atom35,atom44],[atom3,atom5,atom11,atom14,atom27,atom35,atom47],[atom3,atom5,atom11,atom14,atom27,atom36,atom43],[atom3,atom5,atom11,atom14,atom27,atom41,atom45],[atom3,atom5,atom11,atom14,atom28,atom35,atom45]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_20 : t6_20.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_18 : BankTree := .fork [atom2,atom5,atom11,atom14,atom27,atom35,atom43] t6_19 t6_20
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_18 : t6_18.rows.all (refuses 5 t5_0)=true := by simp only [t6_18,BankTree.rows,List.all_append,ok_t6_19,ok_t6_20,Bool.true_and]
noncomputable def t6_22 : BankTree := .block [[atom3,atom5,atom11,atom14,atom33,atom35,atom45],[atom3,atom5,atom11,atom15,atom27,atom35,atom43],[atom3,atom5,atom11,atom16,atom27,atom41,atom43],[atom3,atom5,atom11,atom16,atom33,atom35,atom43],[atom3,atom5,atom12,atom14,atom27,atom35,atom43],[atom3,atom5,atom13,atom14,atom27,atom35,atom45],[atom3,atom5,atom13,atom14,atom27,atom35,atom46],[atom3,atom5,atom13,atom14,atom27,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_22 : t6_22.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_23 : BankTree := .block [[atom3,atom5,atom13,atom14,atom27,atom38,atom43],[atom3,atom5,atom13,atom14,atom27,atom41,atom43],[atom3,atom5,atom13,atom14,atom28,atom35,atom43],[atom3,atom5,atom13,atom14,atom33,atom35,atom43],[atom3,atom5,atom14,atom16,atom27,atom38,atom43],[atom3,atom5,atom14,atom24,atom27,atom35,atom45],[atom3,atom5,atom14,atom26,atom27,atom35,atom43],[atom3,atom5,atom14,atom27,atom35,atom38,atom45]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_23 : t6_23.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_21 : BankTree := .fork [atom3,atom5,atom13,atom14,atom27,atom38,atom43] t6_22 t6_23
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_21 : t6_21.rows.all (refuses 5 t5_0)=true := by simp only [t6_21,BankTree.rows,List.all_append,ok_t6_22,ok_t6_23,Bool.true_and]
noncomputable def t6_17 : BankTree := .fork [atom3,atom5,atom11,atom14,atom33,atom35,atom45] t6_18 t6_21
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_17 : t6_17.rows.all (refuses 5 t5_0)=true := by simp only [t6_17,BankTree.rows,List.all_append,ok_t6_18,ok_t6_21,Bool.true_and]
noncomputable def t6_26 : BankTree := .block [[atom3,atom5,atom14,atom27,atom35,atom40,atom43],[atom3,atom5,atom14,atom27,atom37,atom38,atom43],[atom3,atom5,atom14,atom27,atom38,atom40,atom43],[atom3,atom5,atom14,atom27,atom38,atom43,atom45],[atom3,atom8,atom11,atom14,atom27,atom35,atom45],[atom3,atom8,atom13,atom14,atom27,atom35,atom43],[atom3,atom11,atom13,atom14,atom27,atom35,atom49]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_26 : t6_26.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_27 : BankTree := .block [[atom3,atom11,atom14,atom16,atom27,atom35,atom49],[atom3,atom11,atom14,atom20,atom27,atom35,atom45],[atom3,atom11,atom14,atom27,atom30,atom35,atom45],[atom3,atom11,atom14,atom27,atom35,atom37,atom49],[atom3,atom11,atom14,atom27,atom35,atom45,atom49],[atom3,atom11,atom16,atom20,atom27,atom35,atom43],[atom3,atom13,atom14,atom20,atom27,atom35,atom43],[atom3,atom13,atom14,atom27,atom30,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_27 : t6_27.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_25 : BankTree := .fork [atom3,atom11,atom14,atom16,atom27,atom35,atom49] t6_26 t6_27
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_25 : t6_25.rows.all (refuses 5 t5_0)=true := by simp only [t6_25,BankTree.rows,List.all_append,ok_t6_26,ok_t6_27,Bool.true_and]
noncomputable def t6_29 : BankTree := .block [[atom5,atom8,atom13,atom14,atom27,atom35,atom43],[atom5,atom11,atom13,atom14,atom28,atom35,atom43],[atom5,atom11,atom14,atom16,atom28,atom35,atom43],[atom5,atom11,atom14,atom18,atom27,atom35,atom45],[atom5,atom11,atom14,atom27,atom28,atom35,atom45],[atom5,atom11,atom14,atom28,atom35,atom37,atom43],[atom5,atom11,atom14,atom28,atom35,atom43,atom45],[atom5,atom11,atom14,atom28,atom35,atom45]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_29 : t6_29.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_30 : BankTree := .block [[atom5,atom11,atom16,atom18,atom27,atom35,atom43],[atom5,atom13,atom14,atom18,atom27,atom35,atom43],[atom5,atom13,atom14,atom27,atom28,atom35,atom43],[atom5,atom13,atom14,atom28,atom35,atom43],[atom8,atom11,atom13,atom14,atom27,atom35,atom43],[atom8,atom11,atom14,atom16,atom27,atom35,atom43],[atom8,atom11,atom14,atom27,atom35,atom37,atom43],[atom8,atom13,atom14,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_30 : t6_30.rows.all (refuses 5 t5_0)=true := by decide +kernel
noncomputable def t6_28 : BankTree := .fork [atom5,atom11,atom16,atom18,atom27,atom35,atom43] t6_29 t6_30
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_28 : t6_28.rows.all (refuses 5 t5_0)=true := by simp only [t6_28,BankTree.rows,List.all_append,ok_t6_29,ok_t6_30,Bool.true_and]
noncomputable def t6_24 : BankTree := .fork [atom5,atom8,atom13,atom14,atom27,atom35,atom43] t6_25 t6_28
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_24 : t6_24.rows.all (refuses 5 t5_0)=true := by simp only [t6_24,BankTree.rows,List.all_append,ok_t6_25,ok_t6_28,Bool.true_and]
noncomputable def t6_16 : BankTree := .fork [atom3,atom5,atom14,atom27,atom35,atom40,atom43] t6_17 t6_24
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_16 : t6_16.rows.all (refuses 5 t5_0)=true := by simp only [t6_16,BankTree.rows,List.all_append,ok_t6_17,ok_t6_24,Bool.true_and]
noncomputable def t6_0 : BankTree := .fork [atom1,atom11,atom14,atom20,atom28,atom35,atom43] t6_1 t6_16
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t6_0 : t6_0.rows.all (refuses 5 t5_0)=true := by simp only [t6_0,BankTree.rows,List.all_append,ok_t6_1,ok_t6_16,Bool.true_and]
theorem safe6 : Safe 6 t6_0 := certify 5 t5_0 t6_0 safe5 ok_t6_0
noncomputable def t7_2 : BankTree := .block [[atom0,atom3,atom5,atom11,atom14,atom27,atom35,atom43],[atom1,atom3,atom4,atom11,atom14,atom27,atom35,atom43],[atom1,atom3,atom5,atom11,atom14,atom27,atom35,atom45],[atom1,atom3,atom5,atom11,atom14,atom27,atom35,atom46],[atom1,atom3,atom5,atom11,atom14,atom27,atom35,atom49],[atom1,atom3,atom5,atom11,atom14,atom27,atom38,atom43],[atom1,atom3,atom5,atom11,atom14,atom27,atom41,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_2 : t7_2.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_3 : BankTree := .block [[atom1,atom3,atom5,atom11,atom14,atom28,atom35,atom43],[atom1,atom3,atom5,atom11,atom14,atom33,atom35,atom43],[atom1,atom3,atom5,atom13,atom14,atom27,atom35,atom43],[atom1,atom3,atom5,atom14,atom24,atom27,atom35,atom43],[atom1,atom3,atom5,atom14,atom27,atom35,atom38,atom43],[atom1,atom3,atom5,atom14,atom27,atom38,atom43],[atom1,atom3,atom8,atom11,atom14,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_3 : t7_3.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_1 : BankTree := .fork [atom1,atom3,atom5,atom11,atom14,atom28,atom35,atom43] t7_2 t7_3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_1 : t7_1.rows.all (refuses 6 t6_0)=true := by simp only [t7_1,BankTree.rows,List.all_append,ok_t7_2,ok_t7_3,Bool.true_and]
noncomputable def t7_5 : BankTree := .block [[atom1,atom3,atom11,atom14,atom20,atom27,atom35,atom43],[atom1,atom3,atom11,atom14,atom27,atom30,atom35,atom43],[atom1,atom3,atom11,atom14,atom27,atom35,atom43,atom49],[atom1,atom3,atom11,atom14,atom27,atom35,atom49],[atom1,atom5,atom8,atom11,atom14,atom27,atom35,atom43],[atom1,atom5,atom11,atom14,atom18,atom27,atom35,atom43],[atom1,atom5,atom11,atom14,atom27,atom28,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_5 : t7_5.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_6 : BankTree := .block [[atom1,atom5,atom11,atom14,atom28,atom35,atom43],[atom1,atom8,atom11,atom14,atom27,atom35,atom43],[atom3,atom5,atom11,atom13,atom14,atom27,atom35,atom43],[atom3,atom5,atom11,atom14,atom16,atom27,atom35,atom43],[atom3,atom5,atom11,atom14,atom27,atom35,atom37,atom43],[atom3,atom5,atom11,atom14,atom27,atom35,atom43,atom45],[atom3,atom5,atom11,atom14,atom27,atom35,atom45],[atom3,atom5,atom13,atom14,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_6 : t7_6.rows.all (refuses 6 t6_0)=true := by decide +kernel
noncomputable def t7_4 : BankTree := .fork [atom1,atom5,atom11,atom14,atom28,atom35,atom43] t7_5 t7_6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_4 : t7_4.rows.all (refuses 6 t6_0)=true := by simp only [t7_4,BankTree.rows,List.all_append,ok_t7_5,ok_t7_6,Bool.true_and]
noncomputable def t7_0 : BankTree := .fork [atom1,atom3,atom11,atom14,atom20,atom27,atom35,atom43] t7_1 t7_4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t7_0 : t7_0.rows.all (refuses 6 t6_0)=true := by simp only [t7_0,BankTree.rows,List.all_append,ok_t7_1,ok_t7_4,Bool.true_and]
theorem safe7 : Safe 7 t7_0 := certify 6 t6_0 t7_0 safe6 ok_t7_0
noncomputable def t8_0 : BankTree := .block [[atom1,atom3,atom5,atom11,atom14,atom27,atom35,atom43]]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ok_t8_0 : t8_0.rows.all (refuses 7 t7_0)=true := by decide +kernel
theorem safe8 : Safe 8 t8_0 := certify 7 t7_0 t8_0 safe7 ok_t8_0
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem knownRoots : inputs.sublists.all (fun l =>
    decide (9 < l.length) || (!(cuts l == -1) || t8_0.contains (canon l))) = true := by decide +kernel
theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 8)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 8 S := extend_live hs hl
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
  have room : ¬(9<l.length) := by omega
  have yy : t8_0.contains (canon l)=true := by simpa [room,hc] using row
  have pp : (canon l).Perm l := List.perm_insertionSort _ _
  have ez : (canon l).toFinset=l.toFinset := by
    ext v; simpa only [List.mem_toFinset] using (pp.mem_iff (a:=v))
  exact safe8 _ yy (pp.nodup_iff.mpr hnd) (ez.symm ▸ (hlS ▸ hl3))

theorem result : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  rintro ⟨C, hm, hs, hr⟩
  exact no_small C hm hs hr

end PEqualNP.Outside.L_meta_20532

namespace PEqualNP.Outside.L_meta_20532.PaidColumn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def MonSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : MonSize n h s) : MonSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this


def rot : Fin 8 → Fin 8 := ![0,1,2,4,5,6,7,3]
def col : Fin 5 → Fin 5 := ![4,0,1,2,3]
def bits (u : Fin 3) (v : Fin 5) (i : Fin 8) : Bool := (oneEach u v).getD i.val false
theorem asList : ∀ (u : Fin 3) (v : Fin 5), List.ofFn (bits u v) = oneEach u v := by decide +kernel
theorem rotation : ∀ (u : Fin 3) (v : Fin 5), bits u v ∘ rot = bits u (col v) := by decide +kernel
theorem masks : ∀ (u : Fin 3) (v : Fin 5),
    ((3242 : ℕ).testBit (5*u.val+(col v).val) || (oneEach u v).getD 3 false) =
    (7541 : ℕ).testBit (5*u.val+v.val) := by decide +kernel

def extra (D : Circuit) : Circuit :=
  ⟨D.gates ++ [⟨.or,[D.output,3]⟩], 8 + D.size⟩

theorem extra_mono (D : Circuit) (hd : Monotone2 D) : Monotone2 (extra D) := by
  intro g hg
  change g ∈ D.gates ++ [⟨.or,[D.output,3]⟩] at hg
  rcases List.mem_append.mp hg with h | h
  · exact hd g h
  · simp only [List.mem_singleton] at h
    subst g
    constructor <;> simp

theorem extra_eval (D : Circuit) (l : List Bool) (hlen : l.length = 8) :
    (extra D).eval l = (D.eval l || l.getD 3 false) := by
  let W := wiresFrom D.gates l
  have len : W.length = 8 + D.size := by
    simpa [W,hlen,Circuit.size] using length_wiresFrom D.gates l
  have read : W.getD 3 false = l.getD 3 false := getD_wiresFrom D.gates l 3 (by omega)
  change (wiresFrom (D.gates ++ [⟨.or,[D.output,3]⟩]) l).getD (8 + D.size) false = _
  rw [wiresFrom_append]
  change (W ++ [GateOp.or.eval ([D.output,3].map fun i => W.getD i false)]).getD (8 + D.size) false = _
  rw [← len, getD_snoc_eq]
  change GateOp.or.eval ([D.output,3].map fun i => W.getD i false) =
    (W.getD D.output false || l.getD 3 false)
  simp [GateOp.eval,read]

theorem paid : RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3242 : ℕ).testBit (5*u.val+v.val)) 7 →
    RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5*u.val+v.val)) 8 := by
  rintro ⟨C,hm,hs,rep⟩
  let f : BFn 8 := fun x => C.eval (List.ofFn x)
  have h : MonSize 8 f 7 := ⟨C,hm,hs,fun _ => rfl⟩
  obtain ⟨D,hd,hsd,hev⟩ := relabel_size rot f 7 h
  refine ⟨extra D,extra_mono D hd,?_,?_⟩
  · simpa [extra,Circuit.size] using (Nat.succ_le_succ hsd)
  · intro u v
    have len : (oneEach u v).length = 8 := by rw [← asList]; simp
    have ev : D.eval (oneEach u v) = (3242 : ℕ).testBit (5*u.val+(col v).val) := by
      rw [← asList, hev, rotation]
      change C.eval (List.ofFn (bits u (col v))) = _
      rw [asList]
      exact rep u (col v)
    rw [extra_eval D _ len, ev]
    exact masks u v
end PEqualNP.Outside.L_meta_20532.PaidColumn

theorem PEqualNP.Outside.L_meta_20532 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3242 : ℕ).testBit (5 * u.val + v.val)) 7) :=
  fun h => PEqualNP.Outside.L_meta_20532.result (PEqualNP.Outside.L_meta_20532.PaidColumn.paid h)

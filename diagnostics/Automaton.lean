import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25606

abbrev Tape := ℤ → Bool

def parity (x : Tape) (z : ℤ) := xor (xor (x (z-1)) (x z)) (x (z+1))

def tick (x u : Tape) (z : ℤ) :=
  xor (xor (parity x z) (!(parity x (z+1)) && parity x (z+2))) (u z)

def trajectory (inj : ℕ → Tape) (x : Tape) (n : ℕ) :=
  (List.range n).foldl (fun s i => tick s (inj i)) x

theorem trajectory_succ (inj : ℕ → Tape) (x : Tape) (n : ℕ) :
    trajectory inj x (n+1) = tick (trajectory inj x n) (inj n) := by
  simp [trajectory, List.range_succ, List.foldl_append]

theorem parity_agree {x y : Tape} {c z : ℤ} (h : ∀ w ≤ c, x w = y w)
    (hz : z+1 ≤ c) : parity x z = parity y z := by
  unfold parity
  rw [h (z-1) (by omega), h z (by omega), h (z+1) hz]

theorem tick_agree {x y : Tape} {c z : ℤ} (u : Tape) (h : ∀ w ≤ c, x w = y w)
    (hz : z+3 ≤ c) : tick x u z = tick y u z := by
  unfold tick
  rw [parity_agree h (z := z) (by omega), parity_agree h (z := z+1) (by omega),
    parity_agree h (z := z+2) (by omega)]

theorem tick_guard {x y : Tape} {c z : ℤ} (u : Tape) (h : ∀ w ≤ c, x w = y w)
    (hz : z ≤ c-3 + ((parity y (c-1)).toNat : ℤ)) : tick x u z = tick y u z := by
  by_cases hlow : z+3 ≤ c
  · exact tick_agree u h hlow
  cases hb : parity y (c-1) with
  | false => simp [hb] at hz; omega
  | true =>
    have h1 : z+1 = c-1 := by simp [hb] at hz; omega
    have hy : parity y (z+1) = true := by rw [h1, hb]
    have hx : parity x (z+1) = true := (parity_agree h (by omega)).trans hy
    simp [tick, hx, hy, parity_agree h (z := z) (by omega)]

def endpoint (edge : ℕ → ℤ) (width : ℕ → ℕ) (t : ℕ) := edge t + (width t : ℤ)

def template (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    (t p k : ℕ) (z : ℤ) :=
  if z ≤ edge t then trajectory inj base t z
  else if z ≤ endpoint edge width t then p.testBit (z-edge t-1).toNat
  else k.testBit (z-endpoint edge width t-1).toNat

def linked (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    (t p q : ℕ) :=
  let low := min (edge t-3) (edge (t+1))
  let extra := (endpoint edge width (t+1)+3-endpoint edge width t).toNat
  (List.range (2^extra)).any (fun k =>
    (List.range (endpoint edge width (t+1)-low).toNat).all (fun offset =>
      let site := low+1+(offset : ℤ)
      tick (template base inj edge width t p k) (inj t) site ==
        template base inj edge width (t+1) q 0 site))

def advance (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    (t p : ℕ) (c : ℤ) :=
  if t = 0 then endpoint edge width 1 else
  min (endpoint edge width (t+1)) (c-3 + ((parity (template base inj edge width t p 0) (c-1)).toNat : ℤ))

theorem advance_mono (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    (t p : ℕ) : Monotone (advance base inj edge width t p) := by
  intro x y h
  rcases eq_or_lt_of_le h with rfl | hxy
  · exact le_rfl
  unfold advance
  split
  · exact le_rfl
  · apply min_le_min_left
    cases parity (template base inj edge width t p 0) (x-1) <;>
      cases parity (template base inj edge width t p 0) (y-1) <;> simp <;> omega

theorem link_completion (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    {t p q : ℕ} (hl : linked base inj edge width t p q = true) :
    ∃ k : ℕ, ∀ z ≤ endpoint edge width (t+1),
      tick (template base inj edge width t p k) (inj t) z =
        template base inj edge width (t+1) q 0 z := by
  unfold linked at hl
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hl
  refine ⟨k, ?_⟩
  intro z hz
  let low := min (edge t-3) (edge (t+1))
  by_cases hlow : z ≤ low
  · have a : z+3 ≤ edge t := by dsimp [low] at hlow; omega
    have b : z ≤ edge (t+1) := hlow.trans (min_le_right _ _)
    have same : ∀ w ≤ edge t, template base inj edge width t p k w =
        trajectory inj base t w := by intro w hw; simp [template, hw]
    rw [tick_agree (inj t) same a]
    simp [template, b, trajectory_succ]
  · have ho : (z-low-1).toNat ∈ List.range (endpoint edge width (t+1)-low).toNat := by
      apply List.mem_range.mpr
      omega
    have h := List.all_eq_true.mp hk _ ho
    have he : low+1+((z-low-1).toNat : ℤ) = z := by omega
    change (tick (template base inj edge width t p k) (inj t) (low+1+((z-low-1).toNat : ℤ)) ==
      template base inj edge width (t+1) q 0 (low+1+((z-low-1).toNat : ℤ))) = true at h
    simpa [he] using h

def cutoff (f : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (a : ℕ → ℕ) (n : ℕ) :=
  (List.range n).foldl (fun previous index => f index (a index) previous) seed

theorem cutoff_succ (f : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (a : ℕ → ℕ) (n : ℕ) :
    cutoff f seed a (n+1) = f n (a n) (cutoff f seed a n) := by
  simp [cutoff, List.range_succ, List.foldl_append]

theorem realizes (base : Tape) (inj : ℕ → Tape) (edge : ℕ → ℤ) (width : ℕ → ℕ)
    (n : ℕ) (a : ℕ → ℕ)
    (hl : ∀ t < n, linked base inj edge width t (a t) (a (t+1)) = true) :
    ∃ x : Tape, ∀ t ≤ n, ∀ z ≤ cutoff (advance base inj edge width)
      (endpoint edge width 0) a t, trajectory inj x t z = template base inj edge width t (a t) 0 z := by
  let W := template base inj edge width
  let E := endpoint edge width
  let C := cutoff (advance base inj edge width) (E 0) a
  have bounded : ∀ t, C t ≤ E t := by
    intro t
    cases t with
    | zero => exact le_rfl
    | succ t =>
      change cutoff _ _ _ (t+1) ≤ _
      rw [cutoff_succ]
      by_cases h : t = 0
      · subst t; exact le_rfl
      · simpa [advance, h, E] using (min_le_left (E (t+1))
          (C t-3 + ((parity (W t (a t) 0) (C t-1)).toNat : ℤ)))
  have extW : ∀ t p k z, z ≤ E t → W t p k z = W t p 0 z := by
    intro t p k z hz
    simp [W, template, E] at hz ⊢
    simp [hz]
  cases n with
  | zero =>
    refine ⟨W 0 (a 0) 0, ?_⟩
    intro t ht; have : t = 0 := by omega
    subst t; intro z _; rfl
  | succ n =>
    obtain ⟨k, hk⟩ := link_completion base inj edge width (hl 0 (by omega))
    let x := W 0 (a 0) k
    refine ⟨x, ?_⟩
    intro t ht
    induction t with
    | zero =>
      intro z hz
      exact extW 0 (a 0) k z hz
    | succ t ih =>
      intro z hz
      have hbound : z ≤ E (t+1) := hz.trans (bounded (t+1))
      rw [trajectory_succ]
      by_cases h0 : t = 0
      · subst t; exact hk z hbound
      · obtain ⟨b, hb⟩ := link_completion base inj edge width (hl t (by omega))
        have hw : ∀ w ≤ C t, trajectory inj x t w = W t (a t) b w := by
          intro w hw
          exact (ih (by omega) w hw).trans (extW t (a t) b w (hw.trans (bounded t))).symm
        have hpar : parity (W t (a t) b) (C t-1) = parity (W t (a t) 0) (C t-1) := by
          apply parity_agree (c := E t)
          · exact extW t (a t) b
          · have := bounded t; omega
        have hcut : z ≤ C t-3 + ((parity (W t (a t) b) (C t-1)).toNat : ℤ) := by
          rw [hpar]
          rw [cutoff_succ] at hz
          change z ≤ advance base inj edge width t (a t) (C t) at hz
          unfold advance at hz
          rw [if_neg h0] at hz
          exact hz.trans (min_le_right _ _)
        exact (tick_guard (inj t) hw hcut).trans (hb z hbound)

end PEqualNP.Outside.L_meta_25606

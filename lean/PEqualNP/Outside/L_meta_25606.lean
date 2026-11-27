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
    rw [he] at h
    simpa only [beq_iff_eq] using h

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


def good (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool) (n : ℕ) (a : ℕ → ℕ) :=
  (∀ t ≤ n, A t (a t) = true) ∧ ∀ t < n, L t (a t) (a (t+1)) = true

def reached (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (n q : ℕ) (z : ℤ) :=
  ∃ a : ℕ → ℕ, good A L n a ∧ a n = q ∧ cutoff F seed a n = z

theorem cutoff_ext (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) {a b : ℕ → ℕ} (n : ℕ)
    (h : ∀ i < n, a i = b i) : cutoff F seed a n = cutoff F seed b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cutoff_succ, cutoff_succ, h n (by omega), ih (fun i hi => h i (by omega))]

theorem reached_zero (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (q : ℕ) (z : ℤ) :
    reached A L F seed 0 q z ↔ A 0 q = true ∧ seed = z := by
  constructor
  · rintro ⟨a, hg, hq, hz⟩
    exact ⟨hq ▸ hg.1 0 le_rfl, hz⟩
  · rintro ⟨ha, rfl⟩
    refine ⟨fun _ => q, ⟨?_, ?_⟩, rfl, rfl⟩
    · intro t ht; obtain rfl : t = 0 := by omega
      exact ha
    · intro t ht; omega

theorem reached_succ (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (n q : ℕ) (z : ℤ) :
    reached A L F seed (n+1) q z ↔ A (n+1) q = true ∧
      ∃ p x, reached A L F seed n p x ∧ L n p q = true ∧ F n p x = z := by
  constructor
  · rintro ⟨a, hg, rfl, rfl⟩
    refine ⟨hg.1 _ le_rfl, a n, cutoff F seed a n, ?_, hg.2 n (by omega), (cutoff_succ ..).symm⟩
    exact ⟨a, ⟨fun t ht => hg.1 t (by omega), fun t ht => hg.2 t (by omega)⟩, rfl, rfl⟩
  · rintro ⟨ha, p, x, ⟨a, hg, hp, hx⟩, hl, hF⟩
    let b := fun i : ℕ => if i ≤ n then a i else q
    have hold : ∀ i ≤ n, b i = a i := fun i hi => if_pos hi
    have hlast : b (n+1) = q := if_neg (by omega)
    refine ⟨b, ⟨?_, ?_⟩, hlast, ?_⟩
    · intro i hi
      by_cases h : i ≤ n
      · rw [hold i h]; exact hg.1 i h
      · obtain rfl : i = n+1 := by omega
        rwa [hlast]
    · intro i hi
      by_cases h : i < n
      · rw [hold i (by omega), hold (i+1) (by omega)]
        exact hg.2 i h
      · have hin : i = n := by omega
        subst i
        rwa [hold n le_rfl, hp, hlast]
    · rw [cutoff_succ, hold n le_rfl, hp, cutoff_ext F seed (a := b) (b := a) n
        (fun i hi => hold i (by omega)), hx, hF]

def candidates (L : ℕ → ℕ → ℕ → Bool) (F : ℕ → ℕ → ℤ → ℤ)
    (size : ℕ → ℕ) (prev : ℕ → Option ℤ) (n q : ℕ) :=
  (List.range (size n)).filterMap (fun p =>
    if L n p q then (prev p).map (F n p) else none)

def tally (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (size : ℕ → ℕ) (n : ℕ) : ℕ → Option ℤ :=
  (List.range n).foldl (fun (prev : ℕ → Option ℤ) i q =>
    if A (i+1) q then (candidates L F size prev i q).max? else none)
    (fun q => if A 0 q then some seed else none)

theorem tally_succ (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (size : ℕ → ℕ) (n q : ℕ) :
    tally A L F seed size (n+1) q = if A (n+1) q then
      (candidates L F size (tally A L F seed size n) n q).max? else none := by
  simp [tally, List.range_succ, List.foldl_append]

theorem candidate_iff (L : ℕ → ℕ → ℕ → Bool) (F : ℕ → ℕ → ℤ → ℤ)
    (size : ℕ → ℕ) (prev : ℕ → Option ℤ) (n q : ℕ) (z : ℤ) :
    z ∈ candidates L F size prev n q ↔
      ∃ p x, p < size n ∧ L n p q = true ∧ prev p = some x ∧ F n p x = z := by
  unfold candidates
  constructor
  · intro hz
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hz
    cases hl : L n p q with
    | false => simp [hl] at he
    | true =>
      cases hx : prev p with
      | none => simp [hl,hx] at he
      | some x => exact ⟨p, x, List.mem_range.mp hp, hl, hx, by simpa [hl,hx] using he⟩
  · rintro ⟨p, x, hp, hl, hx, rfl⟩
    exact List.mem_filterMap.mpr ⟨p, List.mem_range.mpr hp, by simp [hl,hx]⟩

theorem list_maximum (xs : List ℤ) (q : ℤ) : xs.max? = some q ↔
    q ∈ xs ∧ ∀ x ∈ xs, x ≤ q := by
  exact List.max?_eq_some_iff

theorem list_maximum_above {xs : List ℤ} {x : ℤ} (hx : x ∈ xs) :
    ∃ b, xs.max? = some b ∧ x ≤ b := by
  cases h : xs.max? with
  | some b => exact ⟨b, rfl, ((list_maximum xs b).mp h).2 x hx⟩
  | none =>
    have he : xs = [] := by
      simpa using h
    simp [he] at hx

theorem tally_invariant (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (size : ℕ → ℕ)
    (hsize : ∀ n p, A n p = true → p < size n)
    (hmono : ∀ n p, Monotone (F n p)) (n q : ℕ) :
    (∀ z, tally A L F seed size n q = some z → reached A L F seed n q z) ∧
    (∀ z, reached A L F seed n q z → ∃ b, tally A L F seed size n q = some b ∧ z ≤ b) := by
  induction n generalizing q with
  | zero =>
    cases h : A 0 q <;> simp [tally, reached_zero, h]
  | succ n ih =>
    constructor
    · intro z hz
      rw [tally_succ] at hz
      cases h : A (n+1) q with
      | false => simp [h] at hz
      | true =>
        simp [h] at hz
        have hm := ((list_maximum _ z).mp hz).1
        obtain ⟨p,x,_,hl,hx,he⟩ := (candidate_iff ..).mp hm
        exact (reached_succ ..).mpr ⟨h,p,x,(ih p).1 x hx,hl,he⟩
    · intro z hz
      obtain ⟨ha,p,x,hx,hl,he⟩ := (reached_succ ..).mp hz
      obtain ⟨b,hb,hle⟩ := (ih p).2 x hx
      have hp : p < size n := by
        obtain ⟨a,hg,hq,_⟩ := hx
        exact hsize n p (hq ▸ hg.1 n le_rfl)
      have hm : F n p b ∈ candidates L F size (tally A L F seed size n) n q :=
        (candidate_iff ..).mpr ⟨p,b,hp,hl,hb,rfl⟩
      obtain ⟨v,hv,hbv⟩ := list_maximum_above hm
      exact ⟨v, by simpa [tally_succ, ha] using hv, he ▸ (le_trans (hmono n p hle) hbv)⟩

theorem best_path (A : ℕ → ℕ → Bool) (L : ℕ → ℕ → ℕ → Bool)
    (F : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (size : ℕ → ℕ)
    (hsize : ∀ n p, A n p = true → p < size n) (hmono : ∀ n p, Monotone (F n p))
    (n q : ℕ) (v : ℤ) :
    tally A L F seed size n q = some v ↔
      (∃ a : ℕ → ℕ, good A L n a ∧ a n = q ∧ cutoff F seed a n = v) ∧
      ∀ b : ℕ → ℕ, good A L n b → b n = q → cutoff F seed b n ≤ v := by
  obtain ⟨hs,hc⟩ := tally_invariant A L F seed size hsize hmono n q
  constructor
  · intro hv
    refine ⟨hs v hv, ?_⟩
    intro b hg hq
    obtain ⟨w,hw,hbw⟩ := hc _ ⟨b,hg,hq,rfl⟩
    have : w = v := Option.some.inj (hw.symm.trans hv)
    simpa [this] using hbw
  · rintro ⟨hr,hu⟩
    obtain ⟨w,hw,hvw⟩ := hc v hr
    obtain ⟨a,hg,hq,hz⟩ := hs w hw
    have hwv := hu a hg hq
    rw [hz] at hwv
    simpa [le_antisymm hwv hvw] using hw

end PEqualNP.Outside.L_meta_25606

open PEqualNP.Outside.L_meta_25606 in
theorem PEqualNP.Outside.L_meta_25606 : let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let step := fun (x inj : ℤ → Bool) (z : ℤ) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
∀ (n : ℕ) (base : ℤ → Bool) (inj : ℕ → ℤ → Bool) (edge : ℕ → ℤ)
    (width mask : ℕ → ℕ),
  let run := fun (x : ℤ → Bool) (rounds : ℕ) =>
    (List.range rounds).foldl (fun state tick => step state (inj tick)) x
  let cap := fun time => edge time + (width time : ℤ)
  let word := fun (layer pattern extraBits : ℕ) (z : ℤ) =>
    if z ≤ edge layer then run base layer z
    else if z ≤ cap layer then pattern.testBit (z-edge layer-1).toNat
    else extraBits.testBit (z-cap layer-1).toNat
  let admitted := fun (layerIndex label : ℕ) => decide (label < 2^(width layerIndex)) && (mask layerIndex).testBit label
  let link := fun (oldTime source dest : ℕ) =>
    let low := min (edge oldTime-3) (edge (oldTime+1))
    let extra := (cap (oldTime+1)+3-cap oldTime).toNat
    (List.range (2^extra)).any (fun completion =>
      (List.range (cap (oldTime+1)-low).toNat).all (fun offset =>
        let site := low+1+(offset : ℤ)
        step (word oldTime source completion) (inj oldTime) site == word (oldTime+1) dest 0 site))
  let carry := fun (fromTime fromPattern : ℕ) (certified : ℤ) =>
    if fromTime = 0 then cap 1 else
      min (cap (fromTime+1)) (certified-3 + ((mix (word fromTime fromPattern 0) (certified-1)).toNat : ℤ))
  let scores := (List.range n).foldl (fun (prev : ℕ → Option ℤ) stage child =>
    if admitted (stage+1) child then
      ((List.range (2^(width stage))).filterMap (fun parent =>
        if link stage parent child then (prev parent).map (carry stage parent) else none)).max?
    else none) (fun parent => if admitted 0 parent then some (cap 0) else none)
  let legal := fun (a : ℕ → ℕ) => (∀ t ≤ n, admitted t (a t) = true) ∧
    ∀ t < n, link t (a t) (a (t+1)) = true
  let limitAt := fun (a : ℕ → ℕ) (length : ℕ) =>
    (List.range length).foldl (fun previous index => carry index (a index) previous) (cap 0)
  (∀ a : ℕ → ℕ, legal a → ∃ initial : ℤ → Bool, ∀ t ≤ n, ∀ z ≤ limitAt a t,
    run initial t z = word t (a t) 0 z) ∧
  ∀ (q : ℕ) (best : ℤ), scores q = some best ↔
    (∃ a : ℕ → ℕ, legal a ∧ a n = q ∧ limitAt a n = best) ∧
    ∀ b : ℕ → ℕ, legal b → b n = q → limitAt b n ≤ best := by
  dsimp only
  intro n base inj edge width mask
  let A := fun (t p : ℕ) => decide (p < 2^(width t)) && (mask t).testBit p
  have hs : ∀ t p, A t p = true → p < 2^(width t) := by
    intro t p h
    by_cases hlt : p < 2^width t
    · exact hlt
    · simp [A, hlt] at h
  constructor
  · intro a ha
    exact realizes base inj edge width n a ha.2
  · intro q v
    exact best_path A (linked base inj edge width) (advance base inj edge width)
      (endpoint edge width 0) (fun t => 2^(width t)) hs (advance_mono base inj edge width) n q v

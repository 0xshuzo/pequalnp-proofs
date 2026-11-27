import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25606

def cutoff (f : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (a : ℕ → ℕ) (n : ℕ) :=
  (List.range n).foldl (fun previous index => f index (a index) previous) seed

theorem cutoff_succ (f : ℕ → ℕ → ℤ → ℤ) (seed : ℤ) (a : ℕ → ℕ) (n : ℕ) :
    cutoff f seed a (n+1) = f n (a n) (cutoff f seed a n) := by
  simp [cutoff, List.range_succ, List.foldl_append]


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

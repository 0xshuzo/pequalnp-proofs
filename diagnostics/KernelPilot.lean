import Mathlib

namespace PetersenMemo

abbrev StatePool := List (BitVec 29)
abbrev Cache := Std.HashSet (Nat × StatePool)

def reference (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) :
    Nat → StatePool → Bool
  | 0, xs => hit xs
  | k+1, xs => hit xs || (children (k+1) xs).any (reference hit children k)

def visit (step : StatePool → Cache → Bool × Cache) : List StatePool → Cache → Bool × Cache
  | [], memo => (false, memo)
  | x::xs, memo =>
    let result := step x memo
    if result.1 then result else visit step xs result.2

def memoized (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) :
    Nat → StatePool → Cache → Bool × Cache
  | 0, xs, table => (hit xs, table)
  | k+1, xs, table =>
    if hit xs then (true, table)
    else if (k+1, xs) ∈ table then (false, table)
    else
      let result := visit (memoized hit children k) (children (k+1) xs) table
      if result.1 then result else
        (false, if (children (k+1) xs).isEmpty = true then result.2 else result.2.insert (k+1, xs))

def Invariant (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (memo : Cache) : Prop :=
  ∀ key ∈ memo, reference hit children key.1 key.2 = false

lemma visit_spec (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (k : Nat)
    (step : StatePool → Cache → Bool × Cache)
    (hstep : ∀ x m, Invariant hit children m →
      (step x m).1 = reference hit children k x ∧ Invariant hit children (step x m).2)
    (xs : List StatePool) (m : Cache) (hm : Invariant hit children m) :
    (visit step xs m).1 = xs.any (reference hit children k) ∧
      Invariant hit children (visit step xs m).2 := by
  induction xs generalizing m with
  | nil => exact ⟨rfl, hm⟩
  | cons x xs ih =>
    obtain ⟨hx, hnew⟩ := hstep x m hm
    cases h : (step x m).1 with
    | false => simpa [visit,h,←hx] using ih _ hnew
    | true => simpa [visit,h,←hx] using hnew

lemma memoized_spec (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool)
    (k : Nat) (xs : StatePool) (m : Cache) (hm : Invariant hit children m) :
    (memoized hit children k xs m).1 = reference hit children k xs ∧
      Invariant hit children (memoized hit children k xs m).2 := by
  induction k generalizing xs m with
  | zero => exact ⟨rfl,hm⟩
  | succ k ih =>
    cases hx : hit xs with
    | true => simpa [memoized, reference, hx] using hm
    | false =>
      by_cases seen : (k+1,xs) ∈ m
      · have no := hm _ seen
        simpa only [memoized,hx,Bool.false_eq_true,ite_false,if_pos seen,no,true_and] using hm
      · obtain ⟨v, valid⟩ := visit_spec hit children k (memoized hit children k) ih (children (k+1) xs) m hm
        cases h : (visit (memoized hit children k) (children (k+1) xs) m).1 with
        | true => simpa [memoized,reference,hx,seen,h,←v] using valid
        | false =>
          have no : reference hit children (k+1) xs = false := by simp [reference,hx,←v,h]
          have extended : Invariant hit children ((visit (memoized hit children k) (children (k+1) xs) m).2.insert (k+1,xs)) := by
            intro key hk
            rcases Std.HashSet.mem_insert.mp hk with eq | old
            · have e : (k+1,xs) = key := eq_of_beq eq
              exact e ▸ no
            · exact valid key old
          by_cases empty : (children (k+1) xs).isEmpty = true
          · simpa [memoized,hx,seen,h,no,empty] using valid
          · simpa [memoized,hx,seen,h,no,empty] using extended

lemma from_empty (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (k : Nat) (xs : StatePool) :
    (memoized hit children k xs ∅).1 = reference hit children k xs := by
  apply (memoized_spec hit children k xs ∅ ?_).1
  intro key h
  simpa using h

end PetersenMemo

namespace PetersenPacked

abbrev W := BitVec 29

def rowCover (p : Nat) : List W → W
  | [] => 0
  | w::xs => if w.getLsbD p = true then ~~~w ||| rowCover p xs else rowCover p xs

lemma rowCover_bits (p n : Nat) (hn : n < 29) (xs : List W) :
    (rowCover p xs).getLsbD n = xs.any (fun w => w.getLsbD p && !(w.getLsbD n)) := by
  induction xs with
  | nil => exact BitVec.getLsbD_zero
  | cons w xs ih =>
    cases hv : w.getLsbD p <;>
      simp only [rowCover,hv,↓reduceIte,BitVec.getLsbD_or,BitVec.getLsbD_not,hn,decide_true,
        Bool.true_and,Bool.false_and,Bool.false_or,List.any_cons,ih]

def covers (xs : List W) : Bool :=
  (List.range 16).all fun p => (rowCover p xs ||| 65535) == BitVec.allOnes 29

lemma coverage_full (xs : List W) (h : ∀ p : Fin 16, ∀ n : Fin 13,
    xs.any (fun w => w.getLsbD p.val && !(w.getLsbD (n.val + 16))) = true) : covers xs = true := by
  have low : ∀ i : Fin 16, (65535 : W).getLsbD i.val = true := by decide +kernel
  have high : ∀ i : Fin 13, (65535 : W).getLsbD (i.val+16) = false := by decide +kernel
  apply List.all_eq_true.mpr
  intro p hp
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or,BitVec.getLsbD_allOnes]
  simp only [hi,decide_true]
  by_cases below : i < 16
  · have yes := low ⟨i,below⟩
    rw [show (65535 : W).getLsbD i = true from yes, Bool.or_true]
  · let n : Fin 13 := ⟨i-16,by omega⟩
    have eq : i = n.val+16 := by dsimp [n]; omega
    rw [eq,high n,Bool.or_false,rowCover_bits p _ (by omega)]
    exact h ⟨p,List.mem_range.mp hp⟩ n

end PetersenPacked

namespace PetersenMask

abbrev W := BitVec 29

def combine (d : Bool) (a b : W) : W := if d then a ||| b else a &&& b

def next (U : List W) (x : W) : Prop :=
  x ∉ U ∧ ∃ a ∈ U, ∃ b ∈ U, x = a &&& b ∨ x = a ||| b

def Valid (U s : List W) : Prop :=
  ∀ j (hj : j < s.length), next (U ++ s.take j) s[j]

inductive Live (target : W) : ℕ → Finset W → Prop where
  | stop : Live target 0 {target}
  | step {k : ℕ} {R : Finset W} (d : Bool) (a b : W)
      (diff : a ≠ b) (fresh : combine d a b ∉ insert a (insert b R))
      (tail : Live target k (insert (combine d a b) R)) :
      Live target (k + 1) (insert a (insert b R))

lemma step_tail {U : List W} {x : W} {s : List W} (leg : Valid U (x :: s)) :
    next U x ∧ Valid (U ++ [x]) s := by
  constructor
  · have h := leg 0 (by simp)
    simpa using h
  · intro j hj
    have h := leg (j+1) (by simp; omega)
    simpa [List.append_assoc] using h

lemma compile {target : W} (U s : List W) (leg : Valid U s) (hit : target ∈ U ++ s) :
    ∃ k ≤ s.length, ∃ S : Finset W, (∀ w ∈ S, w ∈ U) ∧ Live target k S := by
  induction s generalizing U with
  | nil =>
    exact ⟨0, Nat.zero_le _, {target}, by simpa using hit, .stop⟩
  | cons x s ih =>
    obtain ⟨⟨new, a, ha, b, hb, op⟩, legal⟩ := step_tail leg
    have hit' : target ∈ (U ++ [x]) ++ s := by simpa [List.append_assoc] using hit
    obtain ⟨k, small, S, sub, tail⟩ := ih (U ++ [x]) legal hit'
    by_cases used : x ∈ S
    · let R := S.erase x
      have rest : ∀ w ∈ R, w ∈ U := by
        intro w hw
        have q := Finset.mem_erase.mp hw
        have h := sub w q.2
        exact (List.mem_append.mp h).resolve_right (fun eq => q.1 (List.mem_singleton.mp eq))
      have eqS : insert x R = S := Finset.insert_erase used
      have ab : a ≠ b := by
        rintro rfl
        rcases op with h | h
        · exact new (by simpa [h] using ha)
        · exact new (by simpa [h] using ha)
      have fresh : x ∉ insert a (insert b R) := by
        intro h
        rcases Finset.mem_insert.mp h with e | h
        · exact new (by simpa only [e] using ha)
        rcases Finset.mem_insert.mp h with e | h
        · exact new (by simpa only [e] using hb)
        exact (Finset.mem_erase.mp h).1 rfl
      have src : ∀ w ∈ insert a (insert b R), w ∈ U := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        exact rest w hw
      refine ⟨k+1, by simp; omega, insert a (insert b R), src, ?_⟩
      rcases op with h | h
      · apply Live.step false a b ab
        · simpa only [combine, Bool.false_eq_true, ↓reduceIte, ← h] using fresh
        · simpa only [combine, Bool.false_eq_true, ↓reduceIte, ← h, eqS] using tail
      · apply Live.step true a b ab
        · simpa only [combine, ↓reduceIte, ← h] using fresh
        · simpa only [combine, ↓reduceIte, ← h, eqS] using tail
    · refine ⟨k,by simp; omega,S,?_,tail⟩
      intro w hw
      rcases List.mem_append.mp (sub w hw) with old | e
      · exact old
      · exact False.elim (used (List.mem_singleton.mp e ▸ hw))

lemma live_card {target : W} {k : ℕ} {S : Finset W} (h : Live target k S) :
    S.card ≤ k + 1 := by
  induction h with
  | stop => simp
  | @step k R d a b diff fresh tail ih =>
    have hz : combine d a b ∉ R := fun h => fresh (by simp [h])
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b R)
    have h2 := Finset.card_insert_le b R
    omega

def sep (w : W) (p n : ℕ) : Prop :=
  w.getLsbD p = true ∧ w.getLsbD n = false

lemma sep_combine (d : Bool) (a b : W) (p n : ℕ) (h : sep (combine d a b) p n) :
    sep a p n ∨ sep b p n := by
  cases d <;> cases ha : a.getLsbD p <;> cases hb : a.getLsbD n <;>
    cases hc : b.getLsbD p <;> cases hd : b.getLsbD n <;>
    simp_all [combine, sep, BitVec.getLsbD_and, BitVec.getLsbD_or]

lemma live_sep {target : W} {k : ℕ} {S : Finset W} (h : Live target k S)
    (p n : ℕ) (test : sep target p n) : ∃ w ∈ S, sep w p n := by
  induction h with
  | stop => exact ⟨_,by simp,test⟩
  | @step k R d a b diff fresh tail ih =>
    obtain ⟨w,hw,hval⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | rest
    · rcases sep_combine d a b p n hval with ha | hb
      · exact ⟨a,by simp,ha⟩
      · exact ⟨b,by simp,hb⟩
    · exact ⟨w,by simp [rest],hval⟩


def base : List W :=
  [0,536870911,503381504,18022921,176694291,70599750,30017540,987296,107774216,
   359669808,427868608,33489407,18813609]

def raw : List W :=
  [503381504,18022921,176694291,70599750,30017540,987296,107774216,359669808,427868608]

def witnesses : List (ℕ × ℕ) :=
  [(9,16),(0,19),(0,16),(1,19),(2,16),(5,20),(3,16),(4,19),(6,16)]

lemma raw_witnesses : ∀ i : Fin 9, let p := witnesses.getD i.val (0,0)
    sep 65535 p.1 p.2 ∧ ∀ w ∈ base, sep w p.1 p.2 → w = raw.getD i.val 0 := by
  intro i
  fin_cases i <;> simp only [base, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, sep] <;> decide +kernel

lemma live_all_raw {k : ℕ} {S : Finset W} (h : Live 65535 k S) (sub : ∀ w ∈ S, w ∈ base) :
    ∀ x ∈ raw, x ∈ S := by
  intro x hx
  obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hx
  have jb : j < 9 := by simpa [raw] using hj
  have w := raw_witnesses ⟨j,jb⟩
  obtain ⟨a,ha,ok⟩ := live_sep h _ _ w.1
  have eq := w.2 a (sub a ha) ok
  rw [List.getD_eq_getElem _ _ hj] at eq
  simpa only [eq,e] using ha

lemma live_nonconstant {x : W} {k : ℕ} {S : Finset W} (live : Live x k S)
    (target : x ≠ 0 ∧ x ≠ BitVec.allOnes 29) :
    ∀ w ∈ S, w ≠ 0 ∧ w ≠ BitVec.allOnes 29 := by
  induction live with
  | stop => simpa using target
  | @step k R d a b diff fresh tail ih =>
    have hz : combine d a b ≠ a ∧ combine d a b ≠ b := by
      refine ⟨fun e => fresh (by simp [e]),fun e => fresh (by simp [e])⟩
    have properA : a ≠ 0 ∧ a ≠ BitVec.allOnes 29 := by
      constructor <;> intro eq <;> subst a <;> cases d <;>
        simp only [combine, Bool.false_eq_true, ite_false, ite_true, BitVec.allOnes_and,
          BitVec.allOnes_or, BitVec.and_allOnes, BitVec.or_allOnes, BitVec.zero_and,
          BitVec.zero_or, BitVec.and_zero, BitVec.or_zero] at hz <;> simp at hz
    have properB : b ≠ 0 ∧ b ≠ BitVec.allOnes 29 := by
      constructor <;> intro eq <;> subst b <;> cases d <;>
        simp only [combine, Bool.false_eq_true, ite_false, ite_true, BitVec.allOnes_and,
          BitVec.allOnes_or, BitVec.and_allOnes, BitVec.or_allOnes, BitVec.zero_and,
          BitVec.zero_or, BitVec.and_zero, BitVec.or_zero] at hz <;> simp at hz
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact properA
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact properB
    exact ih w (Finset.mem_insert_of_mem hw)

lemma root_shape {k : ℕ} {S : Finset W} (h : Live 65535 k S) (sub : ∀ w ∈ S, w ∈ base) :
    ∃ extra : List W, extra ∈ [[],[33489407],[18813609],[33489407,18813609]] ∧
      S = (raw ++ extra).toFinset := by
  have need := live_all_raw h sub
  have proper := live_nonconstant h (by decide)
  have src (w : W) (hw : w ∈ S) : w ∈ raw ∨ w = 33489407 ∨ w = 18813609 := by
    have mem := sub w hw
    change w ∈ 0 :: BitVec.allOnes 29 :: raw ++ [33489407,18813609] at mem
    have ne := proper w hw
    have h1 := (List.mem_cons.mp mem).resolve_left ne.1
    have h2 := (List.mem_cons.mp h1).resolve_left ne.2
    simpa using h2
  by_cases h1 : (33489407 : W) ∈ S <;> by_cases h2 : (18813609 : W) ∈ S
  · refine ⟨[33489407,18813609], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨src w, fun p => by rcases p with hw | rfl | rfl; exact need _ hw; exact h1; exact h2⟩
  · refine ⟨[33489407], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact Or.inl r
      · exact Or.inr rfl
      · exact (h2 hw).elim
    · rintro (r | rfl)
      · exact need _ r
      · exact h1
  · refine ⟨[18813609], by simp, ?_⟩
    ext w
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact Or.inl r
      · exact (h1 hw).elim
      · exact Or.inr rfl
    · rintro (r | rfl)
      · exact need _ r
      · exact h2
  · refine ⟨[], by simp, ?_⟩
    ext w
    simp only [List.append_nil,List.mem_toFinset]
    constructor
    · intro hw
      rcases src w hw with r | rfl | rfl
      · exact r
      · exact (h1 hw).elim
      · exact (h2 hw).elim
    · exact need w


def separates (xs : List W) : Bool :=
  (List.range 16).all fun p => (List.range 13).all fun q =>
    xs.any fun w => w.getLsbD p && !(w.getLsbD (q + 16))

lemma separates_live {k : ℕ} {xs : List W} (h : Live 65535 k xs.toFinset) :
    separates xs = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have hp' : p < 16 := List.mem_range.mp hp
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 13 := List.mem_range.mp hq
  have bits : ∀ (p : Fin 16) (q : Fin 13), sep 65535 p.val (q.val + 16) := by
    dsimp only [sep]
    decide +kernel
  obtain ⟨w,hw,yes,no⟩ := live_sep h p (q+16) (bits ⟨p,hp'⟩ ⟨q,hq'⟩)
  exact List.any_eq_true.mpr ⟨w,List.mem_toFinset.mp hw,by simp [yes,no]⟩

def orderedInsert (z : W) : List W → List W
  | [] => [z]
  | w::ws => if z < w then z::w::ws else w::orderedInsert z ws

lemma perm_orderedInsert (z : W) (xs : List W) : (orderedInsert z xs).Perm (z::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons w ws ih =>
    unfold orderedInsert
    split
    · exact List.Perm.refl _
    · exact (ih.cons w).trans (List.Perm.swap z w ws)

def updated (xs : List W) (a b z : W) (ka kb : Bool) : List W :=
  orderedInsert z (xs.filter (fun w => (ka || w != a) && (kb || w != b)))

def can (fuel : Nat) (xs : List W) : Bool :=
  match fuel with
  | 0 => xs.contains 65535
  | fuel + 1 =>
    xs.contains 65535 ||
      ((decide (xs.length ≤ fuel + 2) && separates xs) &&
       xs.any fun a => xs.any fun b =>
        decide (a < b) && [false,true].any fun d =>
          let z := combine d a b
          (!(xs.contains z) && decide (z ≠ 0 ∧ z ≠ BitVec.allOnes 29)) && [false,true].any fun ka => [false,true].any fun kb =>
            can fuel (updated xs a b z ka kb))

lemma act_lists {R : Finset W} {xs : List W} {d : Bool} {a b : W}
    (h : xs.toFinset = insert a (insert b R)) (nd : xs.Nodup)
    (fz : combine d a b ∉ insert a (insert b R)) :
    let y := updated xs a b (combine d a b) (decide (a ∈ R)) (decide (b ∈ R))
    y.Nodup ∧ y.toFinset = insert (combine d a b) R := by
  dsimp only
  let keep := fun w : W => (decide (a ∈ R) || w != a) && (decide (b ∈ R) || w != b)
  have mem (w : W) : w ∈ xs ↔ w = a ∨ w = b ∨ w ∈ R := by
    change w ∈ xs ↔ _
    rw [← List.mem_toFinset, h]
    simp
  have mf (w : W) : w ∈ xs.filter keep ↔ w ∈ R := by
    simp only [List.mem_filter, mem, keep, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, bne_iff_ne]
    by_cases wa : w = a <;> by_cases wb : w = b <;> simp_all
  have perm := perm_orderedInsert (combine d a b) (xs.filter keep)
  change (orderedInsert (combine d a b) (xs.filter keep)).Nodup ∧
    (orderedInsert (combine d a b) (xs.filter keep)).toFinset = insert (combine d a b) R
  constructor
  · apply perm.nodup_iff.mpr
    apply List.nodup_cons.mpr
    have nf : combine d a b ∉ R := fun hR => fz (by simp [hR])
    exact ⟨fun hz => nf ((mf _).mp hz), nd.filter _⟩
  · ext w
    simp only [List.mem_toFinset,perm.mem_iff,List.mem_cons,mf,Finset.mem_insert]

def hit (xs : List W) := xs.contains 65535

def branches (budget : Nat) (xs : List W) : List (List W) :=
  if xs.length ≤ budget + 1 ∧ PetersenPacked.covers xs = true then
    xs.flatMap fun c => xs.flatMap fun e =>
      if c < e then [false,true].flatMap fun d =>
        let z := combine d c e
        if z ∉ xs ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 29 then
          [false,true].flatMap fun ka => [false,true].map fun kb => updated xs c e z ka kb
        else []
      else []
  else []

lemma branch_mem {n budget : Nat} {xs : List W} {c e : W} {d : Bool}
    (bound : xs.length ≤ budget+1) (live : Live 65535 n xs.toFinset)
    (hc : c ∈ xs) (he : e ∈ xs) (order : c < e) (new : combine d c e ∉ xs)
    (proper : combine d c e ≠ 0 ∧ combine d c e ≠ BitVec.allOnes 29) (ka kb : Bool) :
    updated xs c e (combine d c e) ka kb ∈ branches budget xs := by
  have sep := separates_live live
  have coverage : PetersenPacked.covers xs = true := by
    apply PetersenPacked.coverage_full
    intro p n
    apply List.all_eq_true.mp (List.all_eq_true.mp sep p.val (List.mem_range.mpr p.isLt)) n.val
      (List.mem_range.mpr n.isLt)
  rw [branches, if_pos ⟨bound,coverage⟩]
  apply List.mem_flatMap.mpr ⟨c,hc,?_⟩
  apply List.mem_flatMap.mpr ⟨e,he,?_⟩
  rw [if_pos order]
  apply List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩
  dsimp only
  rw [if_pos ⟨new,proper⟩]
  apply List.mem_flatMap.mpr ⟨ka,by cases ka <;> simp,?_⟩
  exact List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩

lemma memo_complete {k : ℕ} {S : Finset W} (h : Live 65535 k S) :
    ∀ fuel (xs : List W), k ≤ fuel → xs.Nodup → xs.toFinset = S → PetersenMemo.reference hit branches fuel xs = true := by
  induction h with
  | stop =>
    intro fuel xs _ _ eq
    have ht : (65535 : W) ∈ xs := List.mem_toFinset.mp (by rw [eq]; simp)
    have hit : xs.contains (65535 : W) = true := List.contains_iff_mem.mpr ht
    cases fuel with
    | zero => exact hit
    | succ _ => exact Bool.or_eq_true_iff.mpr (Or.inl hit)
  | @step k R d a b diff fresh tail ih =>
    intro fuel xs small nd eq
    cases fuel with
    | zero => omega
    | succ fuel =>
      have live : Live 65535 (k+1) xs.toFinset := eq.symm ▸ Live.step d a b diff fresh tail
      have sz := live_card live
      have el : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup nd
      have bound : xs.length ≤ fuel + 2 := by omega
      obtain ⟨c,e,ordered,state,word⟩ : ∃ c e : W, c < e ∧
          xs.toFinset = insert c (insert e R) ∧ combine d c e = combine d a b := by
        by_cases ab : a.toNat < b.toNat
        · exact ⟨a,b,ab,eq,rfl⟩
        · have ne : a.toNat ≠ b.toNat := fun h => diff (BitVec.eq_of_toNat_eq h)
          have ba : b.toNat < a.toNat := by omega
          refine ⟨b,a,ba,?_,?_⟩
          · simpa only [Finset.insert_comm b a] using eq
          · cases d <;> simp only [combine, ↓reduceIte, BitVec.or_comm b a, BitVec.and_comm b a]
      have hc : c ∈ xs := List.mem_toFinset.mp (by rw [state]; simp)
      have he : e ∈ xs := List.mem_toFinset.mp (by rw [state]; simp)
      have fz : combine d c e ∉ insert c (insert e R) := by
        rw [←state,eq,word]
        exact fresh
      have hz : combine d c e ∉ xs := by simpa [←state] using fz
      have tail' : Live 65535 k (insert (combine d c e) R) := by rw [word]; exact tail
      have proper := live_nonconstant tail' (by decide) (combine d c e) (by simp)
      have close := act_lists state nd fz
      have accepted := ih fuel _ (by omega) close.1 (by simpa only [word] using close.2)
      apply Bool.or_eq_true_iff.mpr (Or.inr ?_)
      apply List.any_eq_true.mpr
      refine ⟨_,branch_mem (by omega) live hc he ordered hz proper _ _,accepted⟩

theorem memo_lower_bound
    (checks : ∀ extra ∈ ([[],[33489407],[18813609],[33489407,18813609]] : List (List W)),
      (PetersenMemo.memoized hit branches 13 (raw ++ extra) ∅).1 = false)
    (program : List W) (len : program.length ≤ 13) (legal : Valid base program) :
    (65535 : W) ∉ base ++ program := by
  intro occurs
  obtain ⟨k,hk,S,sub,live⟩ := compile base program legal occurs
  obtain ⟨extra,he,eq⟩ := root_shape live sub
  have nodup : (raw ++ extra).Nodup := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide +kernel
  have yes := memo_complete live 13 (raw ++ extra) (by omega) nodup eq.symm
  have no := checks extra he
  rw [PetersenMemo.from_empty] at no
  exact Bool.noConfusion (yes.symm.trans no)

end PetersenMask

namespace PetersenMask

lemma test_hit : hit raw = false := by decide +kernel
lemma test_cover : PetersenPacked.covers raw = true := by decide +kernel
lemma test_children : (branches 9 raw).isEmpty = false := by decide +kernel
lemma test_hash_empty : (9,raw) ∉ (∅ : PetersenMemo.Cache) := by decide +kernel
lemma test_hash_insert : (9,raw) ∈ (∅ : PetersenMemo.Cache).insert (9,raw) := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reference9 : PetersenMemo.reference hit branches 9 raw = false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma cheapPool : (PetersenMemo.memoized hit branches 9 raw ∅).1 = false := by decide +kernel
end PetersenMask

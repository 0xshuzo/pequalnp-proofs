import Mathlib
import PEqualNP.Defs

namespace PetersenMemo

abbrev StatePool := List (BitVec 29)
abbrev Key := Nat × StatePool

inductive Cache where
  | empty
  | node (bucket : List Key) (left right : Cache)

namespace Cache

def keys : Cache → List Key
  | .empty => []
  | .node ks _ _ => ks

def lo : Cache → Cache
  | .empty => .empty
  | .node _ l _ => l

def hi : Cache → Cache
  | .empty => .empty
  | .node _ _ r => r

def entries : Cache → List Key
  | .empty => []
  | .node ks l r => ks ++ (entries l ++ entries r)

lemma components (m : Cache) : entries m = keys m ++ (entries (lo m) ++ entries (hi m)) := by cases m <;> rfl

def code (key : Key) : Nat :=
  key.2.foldl (fun h w => (h * 65599 + w.toNat + 1) % 131071) (key.1 + 11)

def containsAt : Nat → Nat → Key → Cache → Bool
  | _,_,_,.empty => false
  | 0,_,key,.node ks _ _ => ks.contains key
  | d+1,h,key,.node _ l r =>
    if h % 2 = 0 then containsAt d (h / 2) key l else containsAt d (h / 2) key r

def addAt : Nat → Nat → Key → Cache → Cache
  | 0,_,key,m => .node (key::keys m) (lo m) (hi m)
  | d+1,h,key,m => if h % 2 = 0 then .node (keys m) (addAt d (h / 2) key (lo m)) (hi m)
                     else .node (keys m) (lo m) (addAt d (h / 2) key (hi m))

def has (m : Cache) (key : Key) := containsAt 17 (code key) key m

def add (m : Cache) (key : Key) := addAt 17 (code key) key m

lemma contains_spec (d h : Nat) (key : Key) (m : Cache) :
    containsAt d h key m = true → key ∈ entries m := by
  induction d generalizing h m with
  | zero =>
    cases m with
    | empty => simp [containsAt]
    | node ks l r => intro found; exact List.mem_append_left _ (List.contains_iff_mem.mp found)
  | succ d ih =>
    cases m with
    | empty => simp [containsAt]
    | node ks l r =>
      intro found
      change (if h % 2 = 0 then containsAt d (h / 2) key l else containsAt d (h / 2) key r) = true at found
      apply List.mem_append_right
      split at found
      · exact List.mem_append_left _ (ih _ _ found)
      · exact List.mem_append_right _ (ih _ _ found)

lemma add_spec (d h : Nat) (key : Key) (m : Cache) (x : Key) :
    x ∈ entries (addAt d h key m) → x = key ∨ x ∈ entries m := by
  induction d generalizing h m with
  | zero =>
    rw [components m]
    simp only [addAt,entries,List.mem_append,List.mem_cons]
    tauto
  | succ d ih =>
    rw [components m]
    simp only [addAt]
    split
    · simp only [entries,List.mem_append]
      rintro (k | l | r)
      · exact Or.inr (Or.inl k)
      · rcases ih _ _ l with eq | old
        · exact Or.inl eq
        · exact Or.inr (Or.inr (Or.inl old))
      · exact Or.inr (Or.inr (Or.inr r))
    · simp only [entries,List.mem_append]
      rintro (k | l | r)
      · exact Or.inr (Or.inl k)
      · exact Or.inr (Or.inr (Or.inl l))
      · rcases ih _ _ r with eq | old
        · exact Or.inl eq
        · exact Or.inr (Or.inr (Or.inr old))

end Cache


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
    else if table.has (k+1, xs) = true then (false, table)
    else
      let result := visit (memoized hit children k) (children (k+1) xs) table
      if result.1 then result else
        (false, if (children (k+1) xs).isEmpty = true then result.2 else result.2.add (k+1, xs))

def Invariant (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (memo : Cache) : Prop :=
  ∀ key ∈ memo.entries, reference hit children key.1 key.2 = false

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
      by_cases seen : m.has (k+1,xs) = true
      · have no := hm _ (Cache.contains_spec _ _ _ _ seen)
        simpa [memoized,hx,seen,no] using hm
      · obtain ⟨v, valid⟩ := visit_spec hit children k (memoized hit children k) ih (children (k+1) xs) m hm
        cases h : (visit (memoized hit children k) (children (k+1) xs) m).1 with
        | true => simpa [memoized,reference,hx,seen,h,←v] using valid
        | false =>
          have no : reference hit children (k+1) xs = false := by simp [reference,hx,←v,h]
          have extended : Invariant hit children ((visit (memoized hit children k) (children (k+1) xs) m).2.add (k+1,xs)) := by
            intro key hk
            rcases Cache.add_spec _ _ _ _ _ hk with eq | old
            · exact eq.symm ▸ no
            · exact valid key old
          by_cases empty : (children (k+1) xs).isEmpty = true
          · simpa [memoized,hx,seen,h,no,empty] using valid
          · simpa [memoized,hx,seen,h,no,empty] using extended

lemma from_empty (hit : StatePool → Bool) (children : Nat → StatePool → List StatePool) (k : Nat) (xs : StatePool) :
    (memoized hit children k xs .empty).1 = reference hit children k xs := by
  apply (memoized_spec hit children k xs .empty ?_).1
  intro key h
  exact (List.not_mem_nil h).elim

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
      simp only [rowCover,hv,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_or,BitVec.getLsbD_not,hn,decide_true,
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
      (PetersenMemo.memoized hit branches 13 (raw ++ extra) .empty).1 = false)
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

namespace Reconstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 9 → Bool
abbrev Wire := X → Bool

def edge (x : X) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def rows : List Nat := [6,12,24,66,132,160,264,288,320,3,13,17,33,133,265,321,42,50,104,116,138,200,208,276,402,69,201,261,385]
def point (i : Fin 29) (j : Fin 9) := (rows.getD i.val 0).testBit j.val

def below (x y : X) : Prop := x 0 = y 0 ∧ ∀ j, x j = true → y j = true

def Good (w : W) (f : Wire) : Prop :=
  (∀ i : Fin 29, f (point i) = w.getLsbD i.val) ∧
  ∀ x y, below x y → f x = true → f y = true

lemma full {f : Wire} (h : Good 65535 f) (x : X) : f x = edge x := by
  have extrema : ∀ y : X,
      (edge y = true → ∃ i : Fin 29, (65535 : W).getLsbD i.val = true ∧ below (point i) y) ∧
      (edge y = false → ∃ i : Fin 29, (65535 : W).getLsbD i.val = false ∧ below y (point i)) := by
    dsimp only [below]
    decide +kernel
  cases e : edge x with
  | true =>
    obtain ⟨i,bit,le⟩ := (extrema x).1 e
    exact h.2 _ _ le ((h.1 i).trans bit)
  | false =>
    obtain ⟨i,bit,le⟩ := (extrema x).2 e
    cases ex : f x with
    | false => rfl
    | true => exact Bool.noConfusion ((h.2 _ _ le ex).symm.trans ((h.1 i).trans bit))

def readFn (bank : List Wire) (x : X) := bank.map fun f => f x

lemma location (bank : List Wire) (f : Wire) (hf : f ∈ bank) :
    ∃ j : Nat, ∀ x : X, (readFn bank x).getD j false = f x := by
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hf
  refine ⟨j,?_⟩
  intro x
  rw [List.getD_eq_getElem _ _ (by simpa [readFn] using hj)]
  simp only [readFn,List.getElem_map,eq]

def combFn (d : Bool) (f g : Wire) (x : X) := if d = true then f x || g x else f x && g x

lemma good_combine {a b : W} {f g : Wire} (ha : Good a f) (hb : Good b g) (d : Bool) :
    Good (combine d a b) (combFn d f g) := by
  constructor
  · intro i
    cases d <;> simp [combine,combFn,ha.1 i,hb.1 i,BitVec.getLsbD_or,BitVec.getLsbD_and]
  · intro x y hxy h
    cases d with
    | false => exact Bool.and_eq_true_iff.mpr ⟨ha.2 x y hxy (Bool.and_eq_true_iff.mp h).1,
          hb.2 x y hxy (Bool.and_eq_true_iff.mp h).2⟩
    | true =>
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ha.2 x y hxy h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (hb.2 x y hxy h))

def Represents (bank : List Wire) (S : Finset W) : Prop := ∀ w ∈ S, ∃ f ∈ bank, Good w f

lemma build {k : Nat} {S : Finset W} (live : Live 65535 k S) (bank : List Wire) (rep : Represents bank S) :
    ∃ (gs : List Gate) (out : Nat) (f : Wire), gs.length = k ∧ FanInTwo ⟨gs,out⟩ ∧
      Good 65535 f ∧ ∀ x : X, (Circuit.mk gs out).eval (readFn bank x) = f x := by
  induction live generalizing bank with
  | stop =>
    obtain ⟨f,mem,good⟩ := rep 65535 (by simp)
    obtain ⟨j,get⟩ := location bank f mem
    exact ⟨[],j,f,rfl,fun g h => (List.not_mem_nil h).elim,good,get⟩
  | @step k R d a b diff fresh tail ih =>
    obtain ⟨f,hf,gf⟩ := rep a (by simp)
    obtain ⟨g,hg,gg⟩ := rep b (by simp)
    obtain ⟨i,ri⟩ := location bank f hf
    obtain ⟨j,rj⟩ := location bank g hg
    let op : GateOp := if d = true then .or else .and
    let gate : Gate := ⟨op,[i,j]⟩
    let z := combFn d f g
    have rep' : Represents (bank ++ [z]) (insert (combine d a b) R) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact ⟨z,List.mem_append_right _ (by simp),good_combine gf gg d⟩
      obtain ⟨v,hv,ok⟩ := rep w (by simp [hr])
      exact ⟨v,List.mem_append_left _ hv,ok⟩
    obtain ⟨gs,out,fn,sz,fan,good,semantics⟩ := ih (bank ++ [z]) rep'
    refine ⟨gate::gs,out,fn,by simp [sz],?_,good,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hr
      · cases d <;> simp [gate,op]
      · exact fan t hr
    · intro x
      have nextVal : op.eval ([i,j].map (fun t => (readFn bank x).getD t false)) = z x := by
        simp only [List.map_cons,List.map_nil,ri x,rj x]
        cases d <;> simp [op,z,combFn,GateOp.eval]
      change (Circuit.mk gs out).eval (readFn bank x ++ [op.eval ([i,j].map (fun t => (readFn bank x).getD t false))]) = fn x
      rw [nextVal]
      simpa only [readFn,List.map_append,List.map_cons,List.map_nil] using semantics x

def prim : List Wire := List.ofFn fun j : Fin 9 => fun x : X => x j
def minus : Wire := fun x => !(x 0)

lemma initial : Represents (prim ++ [minus]) (raw ++ [33489407]).toFinset := by
  have coords : ∀ i : Fin 9, ∀ j : Fin 29, point j i = (raw.getD i.val 0).getLsbD j.val := by decide +kernel
  have negbits : ∀ j : Fin 29, minus (point j) = (33489407 : W).getLsbD j.val := by decide +kernel
  intro w hw
  rcases List.mem_append.mp (List.mem_toFinset.mp hw) with r | r
  · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp r
    have bound : j < 9 := by simpa [raw] using hj
    let idx : Fin 9 := ⟨j,bound⟩
    have mem : (fun x : X => x idx) ∈ prim := List.mem_ofFn.mpr ⟨idx,rfl⟩
    refine ⟨_,List.mem_append_left _ mem,?_,fun x y h => h.2 idx⟩
    intro i
    have c := coords idx i
    change point i idx = (raw.getD j 0).getLsbD i.val at c
    simpa only [List.getD_eq_getElem _ _ hj,eq] using c
  · have eq := List.mem_singleton.mp r
    subst w
    refine ⟨minus,List.mem_append_right _ (by simp),negbits,?_⟩
    intro x y h
    simp only [minus,h.1,imp_self]

lemma no_or
    (bound : ∀ D : Circuit, FanInTwo D → (∀ x : X, D.eval (List.ofFn x) = edge x) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    {k : Nat} {S : Finset W} (small : k ≤ 13) (live : Live 65535 k S)
    (source : S ⊆ (raw ++ [33489407]).toFinset) : False := by
  obtain ⟨gs,out,f,len,fan,good,sem⟩ := build live (prim ++ [minus]) (fun w hw => initial w (source hw))
  let negGate : Gate := ⟨.not,[0]⟩
  let D : Circuit := ⟨negGate::gs,out⟩
  have ok : FanInTwo D := by
    intro g hg
    change g ∈ negGate::gs at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl),by decide⟩
    · exact fan g hg
  have output (x : X) : D.eval (List.ofFn x) = edge x := by
    have read0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    change (Circuit.mk gs out).eval (List.ofFn x ++ [!(List.ofFn x).getD 0 false]) = edge x
    rw [read0]
    have init : readFn (prim ++ [minus]) x = List.ofFn x ++ [!x 0] := by
      simp [readFn,prim,minus,List.map_ofFn,Function.comp_def]
    rw [←init,sem x]
    exact full good x
  have lower := bound D ok output
  let charged (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  change 14 ≤ (negGate::gs).countP charged at lower
  have zero : charged negGate = false := rfl
  have maxC := List.countP_le_length (p := charged) (l := gs)
  simp [List.countP_cons,zero] at lower
  omega

end Reconstruction
namespace Reconstruction

abbrev IsConst (w : W) := w = 0 ∨ w = BitVec.allOnes 29

def countConst (p : W → W) (S : Finset W) := (S.filter fun w => IsConst (p w)).card

lemma count_insert (p : W → W) (w : W) (S : Finset W) :
    countConst p (insert w S) ≤ countConst p S + (if IsConst (p w) then 1 else 0) := by
  by_cases hc : IsConst (p w)
  · simp only [countConst,Finset.filter_insert,if_pos hc]
    exact Finset.card_insert_le _ _
  · simp [countConst,Finset.filter_insert,hc]

lemma count_fresh (p : W → W) (w : W) (S : Finset W) (fresh : w ∉ S) :
    countConst p (insert w S) = countConst p S + (if IsConst (p w) then 1 else 0) := by
  by_cases hc : IsConst (p w)
  · have no : w ∉ (S.filter fun u => IsConst (p u)) := fun h => fresh (Finset.mem_filter.mp h).1
    simp [countConst,Finset.filter_insert,hc,Finset.card_insert_of_notMem no]
  · simp [countConst,Finset.filter_insert,hc]

lemma const_rules (d : Bool) (a b : W) :
    (IsConst a ∨ IsConst b → combine d a b = a ∨ combine d a b = b) ∧
    (IsConst a → IsConst b → IsConst (combine d a b)) := by
  constructor
  · rintro ((rfl|rfl)|(rfl|rfl)) <;> cases d <;>
      simp only [combine,Bool.false_eq_true,ite_false,ite_true,BitVec.zero_or,BitVec.or_zero,
        BitVec.zero_and,BitVec.and_zero,BitVec.allOnes_and,BitVec.and_allOnes,BitVec.allOnes_or,BitVec.or_allOnes] <;> simp
  · rintro (rfl|rfl) (rfl|rfl) <;> cases d <;> decide +kernel

def faceRows : List Nat := [6,12,66,132,160,264,288,320,320,320,320,320,320,320,320,320,
    42,100,104,138,200,260,386,386,386,386,386,386,386]

def facePoint (i : Fin 29) (j : Fin 9) := (faceRows.getD i.val 0).testBit j.val

def face (f : Wire) : W := (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 29 => f (facePoint i)))).cast (by simp)

lemma face_bit (f : Wire) (i : Fin 29) : (face f).getLsbD i.val = f (facePoint i) := by
  simp only [face,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  fin_cases i <;> rfl

lemma face_combine (d : Bool) (f g : Wire) : face (combFn d f g) = combine d (face f) (face g) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 29 := ⟨i,hi⟩
  cases d <;> simp only [combine,combFn,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,
    BitVec.getLsbD_or,show (face f).getLsbD i = f (facePoint j) from face_bit f j,
    show (face g).getLsbD i = g (facePoint j) from face_bit g j] <;> apply face_bit _ j

lemma face_target {f : Wire} (hg : Good 65535 f) : face f = 65535 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 29 := ⟨i,hi⟩
  have chart : ∀ j : Fin 29, edge (facePoint j) = (65535 : W).getLsbD j.val := by decide +kernel
  exact (face_bit f j).trans ((full hg _).trans (chart j))

lemma pvalid_append {base log : List W} {v : W} (h : Valid base log) (hfresh : v ∉ base ++ log)
    (hv : ∃ a ∈ base ++ log, ∃ b ∈ base ++ log, v = a &&& b ∨ v = a ||| b) :
    Valid base (log ++ [v]) := by
  intro j hj
  by_cases hj' : j < log.length
  · simpa only [List.getElem_append_left hj', List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
  · have eq : j = log.length := by simp at hj; omega
    subst j
    simpa [next] using And.intro hfresh hv

lemma project_live {k : Nat} {S : Finset W} (live : Live 65535 k S) (base log : List W)
    (legal : Valid base log) (lab : W → Wire)
    (avail : ∀ w ∈ S, Good w (lab w) ∧ face (lab w) ∈ base ++ log) :
    ∃ out : List W, Valid base out ∧ 65535 ∈ base ++ out ∧
      out.length + countConst (fun w => face (lab w)) S ≤ log.length + k := by
  induction live generalizing log lab with
  | stop =>
    have a := avail 65535 (by simp)
    have tgt := face_target a.1
    have nonconst : ¬IsConst (65535 : W) := by decide +kernel
    refine ⟨log,legal,by simpa only [tgt] using a.2,?_⟩
    simp [countConst]
    change face (lab (65535 : W)) ≠ 0 ∧ face (lab (65535 : W)) ≠ BitVec.allOnes 29
    rw [tgt]
    decide +kernel
  | @step k R d a b diff fresh tail ih =>
    let z := combine d a b
    let p := fun w : W => face (lab w)
    let fz := combFn d (lab a) (lab b)
    let lab' (w : W) := if w = z then fz else lab w
    let p' := fun w : W => face (lab' w)
    have az := avail a (by simp)
    have bz := avail b (by simp)
    have fzGood : Good z fz := good_combine az.1 bz.1 d
    have znot : z ∉ R := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have pZ : p' z = combine d (p a) (p b) := by simpa [p',lab',fz,p] using face_combine d (lab a) (lab b)
    have agree (w : W) (hw : w ∈ R) : lab' w = lab w := by
      have ne : w ≠ z := fun e => znot (e ▸ hw)
      simp [lab',ne]
    have eqCount : countConst p' R = countConst p R := by
      unfold countConst
      congr 1
      ext w
      by_cases hw : w ∈ R <;> simp [hw,p',p,agree w]
    have ab := count_insert p a (insert b R)
    have br := count_insert p b R
    have zc := count_fresh p' z R znot
    rw [eqCount,pZ] at zc
    have lift_avail (more : List W) (old : base ++ log ⊆ base ++ more)
        (inZ : p' z ∈ base ++ more) :
        ∀ w ∈ insert z R, Good w (lab' w) ∧ face (lab' w) ∈ base ++ more := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact ⟨by simpa [lab'] using fzGood,inZ⟩
      have oldw := avail w (by simp [hr])
      exact ⟨by simpa only [agree w hr] using oldw.1,by simpa only [agree w hr] using old oldw.2⟩
    by_cases mem : p' z ∈ base ++ log
    · obtain ⟨out,ok,goal,size⟩ := ih log legal lab' (lift_avail log (fun _ h => h) mem)
      refine ⟨out,ok,goal,?_⟩
      change out.length + countConst p (insert a (insert b R)) ≤ log.length + (k+1)
      change out.length + countConst p' (insert z R) ≤ log.length + k at size
      by_cases ca : IsConst (p a) <;> by_cases cb : IsConst (p b)
      · have cz := (const_rules d (p a) (p b)).2 ca cb
        simp only [if_pos ca,if_pos cb,if_pos cz] at ab br zc
        omega
      · simp only [if_pos ca,if_neg cb] at ab br
        split at zc <;> omega
      · simp only [if_neg ca,if_pos cb] at ab br
        split at zc <;> omega
      · simp only [if_neg ca,if_neg cb] at ab br
        split at zc <;> omega
    · have clear : ¬IsConst (p a) ∧ ¬IsConst (p b) := by
        have h (c : IsConst (p a) ∨ IsConst (p b)) : False := by
          rcases (const_rules d (p a) (p b)).1 c with e | e
          · exact mem (by simpa only [pZ,e] using az.2)
          · exact mem (by simpa only [pZ,e] using bz.2)
        exact ⟨fun e => h (Or.inl e),fun e => h (Or.inr e)⟩
      have validGate : ∃ x ∈ base ++ log, ∃ y ∈ base ++ log, p' z = x &&& y ∨ p' z = x ||| y := by
        refine ⟨p a,az.2,p b,bz.2,?_⟩
        cases d <;> simp [pZ,combine]
      let more := log ++ [p' z]
      have extl : base ++ log ⊆ base ++ more := by
        dsimp [more]; rw [←List.append_assoc]; exact fun _ h => List.mem_append_left _ h
      have inz : p' z ∈ base ++ more := by simp [more]
      obtain ⟨out,ok,goal,size⟩ := ih more (pvalid_append legal mem validGate) lab' (lift_avail more extl inz)
      refine ⟨out,ok,goal,?_⟩
      change out.length + countConst p (insert a (insert b R)) ≤ log.length + (k+1)
      change out.length + countConst p' (insert z R) ≤ (log ++ [p' z]).length + k at size
      simp only [List.length_append,List.length_singleton,if_neg clear.1,if_neg clear.2] at size ab br
      split at zc <;> omega

end Reconstruction
namespace Reconstruction

def unsigned : List W := [533266437,2228235,1900578,458832,1507204,534249496,534839264]
def faceBase : List W := 0 :: BitVec.allOnes 29 :: unsigned ++ [533659733]
def faceWitnesses : List (Nat × Nat) := [(0,17),(0,16),(1,17),(4,19),(2,16),(3,17),(5,16)]

def origin (w : W) (x : X) : Bool :=
  if w = 503381504 then x 0 else if w = 18022921 then x 1 else if w = 176694291 then x 2 else
  if w = 70599750 then x 3 else if w = 30017540 then x 4 else if w = 987296 then x 5 else
  if w = 107774216 then x 6 else if w = 359669808 then x 7 else if w = 427868608 then x 8 else
  if w = 33489407 then !(x 0) else x 1 || x 5

lemma original_avail (w : W) (hw : w ∈ (raw ++ [33489407,18813609]).toFinset) :
    Good w (origin w) ∧ face (origin w) ∈ faceBase ++ [] := by
  have bits : ∀ u ∈ raw ++ [33489407,18813609], ∀ i : Fin 29, origin u (point i) = u.getLsbD i.val := by
    simp only [raw,List.cons_append,List.nil_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    decide +kernel
  have faceMem : ∀ u ∈ raw ++ [33489407,18813609], face (origin u) ∈ faceBase ++ [] := by
    simp only [raw,List.cons_append,List.nil_append,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    decide +kernel
  have old := List.mem_toFinset.mp hw
  refine ⟨⟨bits w old,?_⟩,faceMem w old⟩
  intro x y h
  have primMono (i : Fin 9) : x i = true → y i = true := h.2 i
  have negMono : !(x 0) = true → !(y 0) = true := by rw [h.1]; exact id
  have orMono : (x 1 || x 5) = true → (y 1 || y 5) = true := by
    intro yes
    rcases Bool.or_eq_true_iff.mp yes with v | v
    · exact Bool.or_eq_true_iff.mpr (Or.inl (primMono 1 v))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (primMono 5 v))
  unfold origin
  repeat' first | split | assumption | exact primMono _

lemma chart_face_raw : ∀ i : Fin 7, let p := faceWitnesses.getD i.val (0,0)
    sep 65535 p.1 p.2 ∧ ∀ w ∈ faceBase, sep w p.1 p.2 → w = unsigned.getD i.val 0 := by
  intro i
  fin_cases i <;> simp only [faceBase,unsigned,List.cons_append,List.nil_append,List.forall_mem_cons,
    List.not_mem_nil,false_implies,implies_true,and_true,sep] <;> decide +kernel

lemma face_root {k : Nat} {S : Finset W} (live : Live 65535 k S)
    (sub : ∀ w ∈ S, w ∈ faceBase) : S = unsigned.toFinset ∨ S = (unsigned ++ [533659733]).toFinset := by
  have need (x : W) (mem : x ∈ unsigned) : x ∈ S := by
    obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp mem
    have jb : j < 7 := by simpa [unsigned] using hj
    have w := chart_face_raw ⟨j,jb⟩
    obtain ⟨a,ha,ok⟩ := live_sep live _ _ w.1
    have eq := w.2 a (sub a ha) ok
    rw [List.getD_eq_getElem _ _ hj] at eq
    simpa only [eq,e] using ha
  have proper := live_nonconstant live (by decide)
  have src (w : W) (hw : w ∈ S) : w ∈ unsigned ∨ w = 533659733 := by
    have m := sub w hw
    change w ∈ 0 :: BitVec.allOnes 29 :: unsigned ++ [533659733] at m
    have h1 := (List.mem_cons.mp m).resolve_left (proper w hw).1
    have h2 := (List.mem_cons.mp h1).resolve_left (proper w hw).2
    simpa using h2
  by_cases ex : (533659733 : W) ∈ S
  · right
    ext w
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton]
    refine ⟨src w,?_⟩
    rintro (r | rfl)
    · exact need _ r
    · exact ex
  · left
    ext w
    simp only [List.mem_toFinset]
    refine ⟨?_,need w⟩
    intro hw
    rcases src w hw with r | rfl
    · exact r
    · exact (ex hw).elim

lemma small_face {k : Nat} (small : k ≤ 13) (live : Live 65535 k (raw ++ [33489407,18813609]).toFinset)
    (check0 : (PetersenMemo.memoized hit branches 10 unsigned .empty).1 = false)
    (check1 : (PetersenMemo.memoized hit branches 10 (unsigned ++ [533659733]) .empty).1 = false) : False := by
  obtain ⟨p,valid,target,budget⟩ := project_live live faceBase [] (by intro j h; simp at h) origin original_avail
  have count : countConst (fun w => face (origin w)) (raw ++ [33489407,18813609]).toFinset = 3 := by decide +kernel
  rw [count] at budget
  obtain ⟨m,hm,S,sub,h⟩ := compile faceBase p valid target
  have tiny : m ≤ 10 := by simp only [List.length_nil,Nat.zero_add] at budget; omega
  rcases face_root h sub with eq | eq
  · have yes := memo_complete h 10 unsigned tiny (by decide +kernel) eq.symm
    rw [PetersenMemo.from_empty] at check0
    exact Bool.noConfusion (yes.symm.trans check0)
  · have yes := memo_complete h 10 (unsigned ++ [533659733]) tiny (by decide +kernel) eq.symm
    rw [PetersenMemo.from_empty] at check1
    exact Bool.noConfusion (yes.symm.trans check1)

end Reconstruction

end PetersenMask

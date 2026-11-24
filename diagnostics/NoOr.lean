import Mathlib
import PEqualNP.Defs

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

def updated (xs : List W) (a b z : W) (ka kb : Bool) : List W :=
  z :: xs.filter (fun w => (ka || w != a) && (kb || w != b))

def can (fuel : Nat) (xs : List W) : Bool :=
  match fuel with
  | 0 => xs.contains 65535
  | fuel + 1 =>
    xs.contains 65535 ||
      ((decide (xs.length ≤ fuel + 2) && separates xs) &&
       xs.any fun a => xs.any fun b =>
        decide (a ≠ b) && [false,true].any fun d =>
          let z := combine d a b
          !(xs.contains z) && [false,true].any fun ka => [false,true].any fun kb =>
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
  change (combine d a b :: xs.filter keep).Nodup ∧
    (combine d a b :: xs.filter keep).toFinset = insert (combine d a b) R
  constructor
  · apply List.nodup_cons.mpr
    have nf : combine d a b ∉ R := fun hR => fz (by simp [hR])
    exact ⟨fun hz => nf ((mf _).mp hz), nd.filter _⟩
  · ext w
    simp only [List.mem_toFinset,List.mem_cons,mf,Finset.mem_insert]

lemma can_complete {k : ℕ} {S : Finset W} (h : Live 65535 k S) :
    ∀ fuel (xs : List W), k ≤ fuel → xs.Nodup → xs.toFinset = S → can fuel xs = true := by
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
      have ha : a ∈ xs := List.mem_toFinset.mp (by rw [eq]; simp)
      have hb : b ∈ xs := List.mem_toFinset.mp (by rw [eq]; simp)
      have hz : combine d a b ∉ xs := by simpa [← eq] using fresh
      have close := act_lists eq nd fresh
      have accepted := ih fuel _ (by omega) close.1 close.2
      apply Bool.or_eq_true_iff.mpr (Or.inr ?_)
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp [bound,separates_live live],List.any_eq_true.mpr ⟨a,ha,?_⟩⟩
      apply List.any_eq_true.mpr ⟨b,hb,?_⟩
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simpa using diff,List.any_eq_true.mpr ⟨d,by cases d <;> simp,?_⟩⟩
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simpa using hz,List.any_eq_true.mpr ⟨decide (a ∈ R),by cases decide (a ∈ R) <;> simp,?_⟩⟩
      exact List.any_eq_true.mpr ⟨decide (b ∈ R),by cases decide (b ∈ R) <;> simp,accepted⟩


theorem numeric_lower_bound
    (checks : ∀ extra ∈ ([[],[33489407],[18813609],[33489407,18813609]] : List (List W)),
      can 13 (raw ++ extra) = false)
    (program : List W) (len : program.length ≤ 13) (legal : Valid base program) :
    (65535 : W) ∉ base ++ program := by
  intro hit
  obtain ⟨k,hk,S,sub,live⟩ := compile base program legal hit
  obtain ⟨extra,he,eq⟩ := root_shape live sub
  have nodup : (raw ++ extra).Nodup := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide +kernel
  have yes := can_complete live 13 (raw ++ extra) (by omega) nodup eq.symm
  have no := checks extra he
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

end PetersenMask

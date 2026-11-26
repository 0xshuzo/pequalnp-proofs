import PEqualNP.Outside.L_pcx_162

namespace PEqualNP.Outside.L_pcx_170_tree

open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 4
abbrev C := Clause V
abbrev Tag := Fin 45

inductive Tree : C → Nat → Prop where
  | ax {A : C} (h : A ∈ PHP 5 4) : Tree A 1
  | step {P N R : C} {a b : Nat} (left : Tree P a) (right : Tree N b)
      (resolved : IsResolvent P N R) : Tree R (a+b)

def samples : Array (List Nat) := #[[541200,295440,533520,164880,272400,149520,540960,295200,529440,99360,268320,84000,532800,164160,528960,98880,137280,75840,270720,147840,266880,82560,136320,74880],[541185,295425,533505,164865,272385,149505,540930,295170,529410,99330,268290,83970,532740,164100,528900,98820,137220,75780,270600,147720,266760,82440,136200,74760],[540705,294945,532545,163905,270465,147585,540690,294930,528450,98370,266370,82050,532500,163860,528420,98340,135300,73860,270360,147480,266280,81960,135240,73800],[525345,264225,524865,133185,262785,132225,525330,264210,524610,67650,262530,66690,524820,133140,524580,67620,131460,66180,262680,132120,262440,66600,131400,66120],[33825,18465,33345,10305,17025,9345,33810,18450,33090,6210,16770,5250,33300,10260,33060,6180,8580,4740,16920,9240,16680,5160,8520,4680],[541201,295441,533521,164881,272401,149521],[540962,295202,529442,99362,268322,84002],[532804,164164,528964,98884,137284,75844],[270728,147848,266888,82568,136328,74888],[540961,295201,532801,164161,270721,147841],[541202,295442,528962,98882,266882,82562],[533524,164884,529444,99364,136324,74884],[272408,149528,268328,84008,137288,75848],[529441,268321,528961,137281,266881,136321],[533522,272402,532802,75842,270722,74882],[541204,149524,540964,84004,147844,82564],[295448,164888,295208,99368,164168,98888],[99361,84001,98881,75841,82561,74881],[164882,149522,164162,137282,147842,136322],[295444,272404,295204,268324,270724,266884],[541208,533528,540968,529448,532808,528968],[540946,295186,532756,164116,270616,147736],[541217,295457,528932,98852,266792,82472],[533569,164929,529474,99394,136264,74824],[272513,149633,268418,84098,137348,75908],[529426,268306,528916,137236,266776,136216],[533537,272417,532772,75812,270632,74792],[541249,149569,540994,84034,147784,82504],[295553,164993,295298,99458,164228,98948],[99346,83986,98836,75796,82456,74776],[164897,149537,164132,137252,147752,136232],[295489,272449,295234,268354,270664,266824],[541313,533633,541058,529538,532868,529028],[528706,266626,528676,135556,266536,135496],[533057,270977,533012,74372,270872,74312],[541729,148609,541714,83074,148504,82984],[296993,165953,296978,100418,165908,100388],[98626,82306,98596,74116,82216,74056],[164417,148097,164372,135812,147992,135752],[295969,271489,295954,267394,271384,267304],[542753,534593,542738,530498,534548,530468],[71746,70786,71716,70276,70696,70216],[141377,140417,141332,139652,140312,139592],[280609,279169,280594,278914,279064,278824],[558113,557633,558098,557378,557588,557348]]
def pts (k : Tag) : List Nat := samples[k.val]!
def asg (m : Nat) (v : V) : Bool := m.testBit (4*v.1.val+v.2.val)

def sat (m : Nat) (R : C) : Bool := decide (∃ z ∈ R, asg m z.1 = z.2)
theorem satSound {m : Nat} {R : C} (h : sat m R = true) : ClauseSat (asg m) R := by
  change (∃ z ∈ R, asg m z.1 = z.2)
  exact of_decide_eq_true h

def protects (id : Tag) (R : C) : Bool :=
  (List.finRange 45).all fun t => t == id || (pts t).all fun m => sat m R
theorem protectsSound {id : Tag} {R : C} (h : protects id R = true)
    {t : Tag} (m : Nat) (hm : m ∈ pts t) (bad : ¬ ClauseSat (asg m) R) : t = id := by
  have e := List.all_eq_true.mp h t (List.mem_finRange t)
  rcases Bool.or_eq_true_iff.mp e with same | good
  · exact eq_of_beq same
  · exact (bad (satSound (List.all_eq_true.mp good m hm))).elim

def row (i : Fin 5) : C := Finset.univ.image (fun h : Fin 4 => ((i,h),true))
def col (i k : Fin 5) (h : Fin 4) : C := {((i,h),false),((k,h),false)}
def colTag (i k : Fin 5) (h : Fin 4) : Tag :=
  let a := min i.val k.val
  let b := max i.val k.val
  Fin.ofNat 45 (5+4*(a*(9-a)/2+(b-a-1))+h.val)
set_option maxHeartbeats 0 in
theorem rowsOK : ∀ i : Fin 5, protects (Fin.ofNat 45 i.val) (row i) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem colsOK : ∀ i k : Fin 5, ∀ h : Fin 4, i ≠ k → protects (colTag i k h) (col i k h) = true := by decide +kernel

theorem tags {R : C} (h : R ∈ PHP 5 4) : ∃ id : Tag, protects id R = true := by
  rcases h with ⟨i,rfl⟩ | ⟨i,k,q,ne,rfl⟩
  · exact ⟨_,rowsOK i⟩
  · exact ⟨_,colsOK i k q ne⟩

theorem leftBad {P N : C} {v : V} {x : V → Bool}
    (bad : ¬ClauseSat x (P.erase (v,true) ∪ N.erase (v,false)))
    (bit : x v = false) : ¬ClauseSat x P := by
  rintro ⟨z,hz,hv⟩
  have diff : z ≠ (v,true) := by
    rintro rfl
    change x v = true at hv
    simp [bit] at hv
  exact bad ⟨z,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨diff,hz⟩),hv⟩

theorem rightBad {P N : C} {v : V} {x : V → Bool}
    (bad : ¬ClauseSat x (P.erase (v,true) ∪ N.erase (v,false)))
    (bit : x v = true) : ¬ClauseSat x N := by
  rintro ⟨z,hz,hv⟩
  have diff : z ≠ (v,false) := by
    rintro rfl
    change x v = false at hv
    simp [bit] at hv
  exact bad ⟨z,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨diff,hz⟩),hv⟩

theorem leafBank {R : C} {n : Nat} (tree : Tree R n) :
    ∃ T : Finset Tag, T.card ≤ n ∧
      ∀ t m, m ∈ pts t → ¬ClauseSat (asg m) R → t ∈ T := by
  induction tree with
  | ax h =>
    obtain ⟨id,hid⟩ := tags h
    exact ⟨{id},by simp,fun t m h bad => Finset.mem_singleton.mpr (protectsSound hid m h bad)⟩
  | step l r hr hl hh =>
    obtain ⟨v,_,_,rfl⟩ := hr
    obtain ⟨A,ha,ah⟩ := hl
    obtain ⟨B,hb,bh⟩ := hh
    refine ⟨A∪B,(Finset.card_union_le A B).trans (Nat.add_le_add ha hb),?_⟩
    intro t m hm bad
    cases bit : asg m v with
    | false => exact Finset.mem_union_left _ (ah t m hm (leftBad bad bit))
    | true => exact Finset.mem_union_right _ (bh t m hm (rightBad bad bit))

def labelSet (test : Nat → Bool) : Finset Tag :=
  Finset.univ.filter (fun k => (pts k).any test)

theorem labelBound {R : C} {n : Nat} (tree : Tree R n) (test : Nat → Bool)
    (h : ∀ t m, m ∈ pts t → test m = true → ¬ClauseSat (asg m) R) : (labelSet test).card ≤ n := by
  obtain ⟨T,ht,nodes⟩ := leafBank tree
  apply (Finset.card_le_card (show labelSet test ⊆ T from ?_)).trans ht
  intro k hk
  obtain ⟨m,hm,yes⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hk).2
  exact nodes k m hm (h k m hm yes)

def cut (v : V) (b : Bool) (m : Nat) := asg m v == b
def cut2 (u v : V) (b : Bool) (m : Nat) := cut u false m && cut v b m

set_option maxHeartbeats 0 in
theorem countOne : ∀ u : V,
    41 ≤ (labelSet (cut u false)).card ∧ 26 ≤ (labelSet (cut u true)).card := by decide +kernel

def branch (test : Nat → Bool) (v : V) (b : Bool) (m : Nat) := test m && cut v b m

theorem posLabel {test : Nat → Bool} (t : Tag) (m : Nat) (hm : m ∈ pts t) (hx : test m = true) :
    0 < (labelSet test).card :=
  Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.any_eq_true.mpr ⟨m,hm,hx⟩⟩⟩

theorem splitLower {R : C} {n : Nat} (tree : Tree R n) (test : Nat → Bool) (k : Nat)
    (many : 1 < (labelSet test).card)
    (cost : ∀ v : V, 0 < (labelSet (branch test v false)).card →
       0 < (labelSet (branch test v true)).card →
       k ≤ (labelSet (branch test v false)).card + (labelSet (branch test v true)).card)
    (bad : ∀ t m, m ∈ pts t → test m = true → ¬ClauseSat (asg m) R) : k ≤ n := by
  induction tree with
  | ax h => have hb := labelBound (Tree.ax h) test bad; omega
  | step left right hr il ir =>
    obtain ⟨v,_,_,rfl⟩ := hr
    by_cases f : 0 < (labelSet (branch test v false)).card
    · by_cases t : 0 < (labelSet (branch test v true)).card
      · have hl := labelBound left (branch test v false) (by
          intro s m hm yes
          obtain ⟨ht,hv⟩ := Bool.and_eq_true_iff.mp yes
          exact leftBad (bad s m hm ht) (eq_of_beq hv))
        have hh := labelBound right (branch test v true) (by
          intro s m hm yes
          obtain ⟨ht,hv⟩ := Bool.and_eq_true_iff.mp yes
          exact rightBad (bad s m hm ht) (eq_of_beq hv))
        exact (cost v f t).trans (Nat.add_le_add hl hh)
      · have hl := il (by
          intro s m hm ht
          apply leftBad (bad s m hm ht)
          cases hs : asg m v with
          | false => rfl
          | true => exact (t (posLabel (test := branch test v true) s m hm (by simp [branch,cut,ht,hs]))).elim)
        omega
    · have hh := ir (by
        intro s m hm ht
        apply rightBad (bad s m hm ht)
        cases hs : asg m v with
        | true => rfl
        | false => exact (f (posLabel (test := branch test v false) s m hm (by simp [branch,cut,ht,hs]))).elim)
      omega

def cold2 (u v : V) (b : Bool) := branch (cut u false) v b

def coldCost (u v : V) (b : Bool) : Nat :=
  if u.1 = v.1 then if b then 26 else 50
  else if u.2 = v.2 then if b then 25 else 53
  else if b then 23 else 53

def hot (u : V) (m : Nat) : Bool := cut u true m &&
  ((m &&& ((15 <<< (4*u.1.val)) ||| (69905 <<< u.2.val))) == (1 <<< (4*u.1.val+u.2.val)))

set_option maxHeartbeats 0
set_option maxRecDepth 32768

private theorem coldMany : ∀ u v : V, u ≠ v → ∀ b : Bool, 1 < (labelSet (cold2 u v b)).card := by decide +kernel
private theorem coldSplit : ∀ u v : V, u ≠ v → ∀ (b : Bool) (w : V),
    0 < (labelSet (branch (cold2 u v b) w false)).card → 0 < (labelSet (branch (cold2 u v b) w true)).card →
    coldCost u v b ≤ (labelSet (branch (cold2 u v b) w false)).card + (labelSet (branch (cold2 u v b) w true)).card := by decide +kernel
private theorem hotMany : ∀ u : V, 1 < (labelSet (hot u)).card := by decide +kernel
private theorem hotSplit : ∀ u v : V, 0 < (labelSet (branch (hot u) v false)).card →
    0 < (labelSet (branch (hot u) v true)).card →
    31 ≤ (labelSet (branch (hot u) v false)).card + (labelSet (branch (hot u) v true)).card := by decide +kernel
private theorem joined : ∀ u v : V, 76 ≤ coldCost u v false + coldCost u v true := by decide +kernel

theorem cold76 {R : C} {n : Nat} (tree : Tree R n) (u : V)
    (bad : ∀ t m, m ∈ pts t → asg m u = false → ¬ClauseSat (asg m) R) : 76 ≤ n := by
  induction tree with
  | ax h =>
    have hb := labelBound (Tree.ax h) (cut u false) (fun t m hm yes => bad t m hm (eq_of_beq yes))
    have hc := (countOne u).1
    omega
  | step left right hr il ir =>
    obtain ⟨v,_,_,rfl⟩ := hr
    by_cases e : u = v
    · subst v
      have hl := il (fun t m hm bit => leftBad (bad t m hm bit) bit)
      omega
    · have hl := splitLower left (cold2 u v false) (coldCost u v false) (coldMany u v e false) (coldSplit u v e false) (by
        intro t m hm yes
        obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp yes
        exact leftBad (bad t m hm (eq_of_beq a)) (eq_of_beq b))
      have hh := splitLower right (cold2 u v true) (coldCost u v true) (coldMany u v e true) (coldSplit u v e true) (by
        intro t m hm yes
        obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp yes
        exact rightBad (bad t m hm (eq_of_beq a)) (eq_of_beq b))
      exact (joined u v).trans (Nat.add_le_add hl hh)

theorem treeCost107 {R : C} {n : Nat} (tree : Tree R n)
    (bad : ∀ t m, m ∈ pts t → ¬ClauseSat (asg m) R) : 107 ≤ n := by
  cases tree with
  | ax h =>
    have hb := labelBound (Tree.ax h) (hot (0,0)) (fun t m hm _ => bad t m hm)
    have hh := hotMany (0,0)
    omega
  | step left right hr =>
    obtain ⟨v,_,_,rfl⟩ := hr
    have hl := cold76 left v (fun t m hm bit => leftBad (bad t m hm) bit)
    have hh := splitLower right (hot v) 31 (hotMany v) (hotSplit v) (fun t m hm ht =>
      rightBad (bad t m hm) (eq_of_beq (Bool.and_eq_true_iff.mp ht).1))
    omega

theorem tree107 {n : Nat} (tree : Tree ∅ n) : 107 ≤ n :=
  treeCost107 tree (by rintro t m hm ⟨l,hl,_⟩; simp at hl)

end PEqualNP.Outside.L_pcx_170_tree

namespace PEqualNP.Outside.L_pcx_170_physical
open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_162 (Step clauseOf ValidTrace isAxStep ax_lower)
open PEqualNP.Outside.L_pcx_170_tree (C Tree tree107)

/-- `U` records the physical indices of resolution occurrences. Axioms can be shared. -/
inductive Nonreusing (tr : List Step) : C → Finset (Fin tr.length) → Nat → Prop where
  | ax {A : C} (h : A ∈ PHP 5 4) : Nonreusing tr A ∅ 1
  | resolve {P N R : C} {a b : Nat} {S T : Finset (Fin tr.length)} (i : Fin tr.length)
      (left : Nonreusing tr P S a) (right : Nonreusing tr N T b) (r : IsResolvent P N R)
      (site : clauseOf (tr.get i) = R) (derived : isAxStep (tr.get i) = false)
      (apart : Disjoint S T) (fresh : i ∉ S ∪ T) :
      Nonreusing tr R (insert i (S ∪ T)) (a+b)

theorem measured {tr : List Step} {R : C} {U : Finset (Fin tr.length)} {n : Nat}
    (g : Nonreusing tr R U n) : Tree R n ∧ U.card + 1 = n ∧ ∀ i ∈ U, isAxStep (tr.get i) = false := by
  induction g with
  | ax h => exact ⟨Tree.ax h,by simp,by simp⟩
  | resolve i l r res hs hd hst hi il ir =>
    obtain ⟨tl,cl,sl⟩ := il
    obtain ⟨tr',cr,sr⟩ := ir
    refine ⟨Tree.step tl tr' res,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hi,Finset.card_union_of_disjoint hst]
      omega
    · intro j hj
      rcases Finset.mem_insert.mp hj with eq | h
      · exact eq.symm ▸ hd
      · rcases Finset.mem_union.mp h with h | h
        · exact sl j h
        · exact sr j h

theorem physical151 {tr : List Step} (valid : ValidTrace tr) (empty : (∅ : C) ∈ tr.map clauseOf)
    {U : Finset (Fin tr.length)} {n : Nat} (g : Nonreusing tr ∅ U n) : 151 ≤ tr.length := by
  obtain ⟨tree,card,kind⟩ := measured g
  have tn := tree107 tree
  let A := Finset.univ.filter (fun i : Fin tr.length => isAxStep (tr.get i))
  have ca : tr.countP isAxStep = A.card := by
    simpa [A] using List.countP_ofFn (fun i : Fin tr.length => tr.get i) isAxStep
  have dj : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro i hi ha
    have yes : isAxStep (tr.get i) = true := (Finset.mem_filter.mp ha).2
    rw [kind i hi] at yes
    contradiction
  have h := Finset.card_le_card (Finset.subset_univ (U ∪ A))
  rw [Finset.card_union_of_disjoint dj,Finset.card_univ,Fintype.card_fin] at h
  have a := ax_lower valid empty
  omega

end PEqualNP.Outside.L_pcx_170_physical

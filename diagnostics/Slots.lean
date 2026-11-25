import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
abbrev Row := Fin 60
def fullMask : Nat := 1152921504606846975
def rows : Array Nat := #[672,784,1120,1288,2128,2184,644,770,1092,1281,2114,2177,532,546,1036,1057,2058,2065,84,98,140,161,266,273,1289,2185,1121,2129,1100,2122,673,785,652,778,596,610,786,2130,674,2186,660,2193,1122,1290,1108,1297,1164,1185,676,1124,788,1292,802,1313,2132,2188,2146,2209,2314,2321]
def ones : Array Nat := #[729761264001255936,364805838240031872,58354402365559104,326590701323239464,595657351441551378,230673451842052101,90657122719368468,180640694878079073,881623687009141386,5912485265682627,12099026304418572,1134909993020230704]
def zeros : Array Nat := #[423160240605591039,788115666366815103,1094567102241287871,826330803283607511,557264153165295597,922248052764794874,1062264381887478507,972280809728767902,271297817597705589,1147009019341164348,1140822478302428403,18011511586616271]
def labelMasks : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def lits : List (Literal V) := [((0,0),false),((0,0),true),((0,1),false),((0,1),true),((0,2),false),((0,2),true),((1,0),false),((1,0),true),((1,1),false),((1,1),true),((1,2),false),((1,2),true),((2,0),false),((2,0),true),((2,1),false),((2,1),true),((2,2),false),((2,2),true),((3,0),false),((3,0),true),((3,1),false),((3,1),true),((3,2),false),((3,2),true)]

def port (v : V) : Nat := 3 * v.1.val + v.2.val

def assignment (r : Row) (v : V) : Bool := (rows[r.val]!).testBit (port v)

def keep (l : Literal V) : Nat := if l.2 then zeros[port l.1]! else ones[port l.1]!

def cut (C : Cl) (s : Nat) (l : Literal V) : Nat := if l ∈ C then s &&& keep l else s

def privateMask (C : Cl) : Nat := lits.foldl (cut C) fullMask

theorem fullBit (r : Row) : fullMask.testBit r.val = true := by
  revert r; decide +kernel

theorem keepBit (l : Literal V) (r : Row) :
    (keep l).testBit r.val = true ↔ assignment r l.1 ≠ l.2 := by
  revert l r; decide +kernel

theorem listed (l : Literal V) : l ∈ lits := by
  revert l; decide +kernel

theorem cutList (C : Cl) (s : Nat) (ls : List (Literal V)) (r : Row) :
    (ls.foldl (cut C) s).testBit r.val = true ↔
      s.testBit r.val = true ∧ (∀ l ∈ ls, l ∈ C → assignment r l.1 ≠ l.2) := by
  induction ls generalizing s with
  | nil => simp
  | cons l t ih =>
    rw [List.foldl_cons, ih]
    by_cases h : l ∈ C
    · simp only [cut, if_pos h, Nat.testBit_and, Bool.and_eq_true, keepBit,
        List.mem_cons]
      aesop
    · simp only [cut, if_neg h, List.mem_cons]
      aesop

theorem privateBit (C : Cl) (r : Row) :
    (privateMask C).testBit r.val = true ↔ ¬ClauseSat (assignment r) C := by
  rw [privateMask,cutList]
  simp only [fullBit, true_and]
  constructor
  · rintro h ⟨l,hl,yes⟩
    exact h l (listed l) hl yes
  · intro h l _ hl yes
    exact h ⟨l,hl,yes⟩

def posAx (i : Fin 4) : Cl := Finset.univ.image (fun j : Fin 3 => ((i,j),true))
def negAx (i j : Fin 4) (h : Fin 3) : Cl := {((i,h),false),((j,h),false)}

theorem posListed (i : Fin 4) : privateMask (posAx i) ∈ labelMasks.toList := by
  revert i; decide +kernel

theorem negListed (i j : Fin 4) (h : Fin 3) (ne : i ≠ j) :
    privateMask (negAx i j h) ∈ labelMasks.toList := by
  revert i j h; decide +kernel

theorem axListed {C : Cl} (hc : C ∈ PHP 4 3) : privateMask C ∈ labelMasks.toList := by
  rcases hc with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact posListed i
  · exact negListed i j h ne

def labels : Array Nat := #[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21]
def negA : Array Nat := #[0,0,0,0,1,2,2,3,3,3,1,2,2,3,3,3,1,2,2,3,3,3]
def negB : Array Nat := #[0,0,0,0,0,0,1,0,1,2,0,0,1,0,1,2,0,0,1,0,1,2]
def negH : Array Nat := #[0,1,2,3,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2]
def neighborData : Array Nat := #[199070,207135,203418,211672,223579,227801,52219084800,56447205376,53358886912,57669582848,60757901312,61897703424,14252007158185984,14806229738061824,14559458097102848,15126668658081792,16499065327976448,16789198958755840,4035837755673286803456,4181123879652259004416,4111894546180319739904,4260585391477584035840,4329814724949523300352,4405871515456556236800,2359299,2883589,1030792151042,1168231104516,962074771456,1099514249216,378302368699121664,414331165718085633,360287970191212544,396316767210438656,324259997804396544,342274465033355264,117440576,167772416,57174604644352,70368744177984,52776658796544,74766975238144,21905508587530092672,25364273101350633664,20752587083057463296,26517194606108475392,23058491664788094976,24211417567441453056,6442450944,8589942784,3377699720531968,3940649673961472,3659182213431296,4222134314336256,1328165573307087732736,1475739525896764149760,1401952549612663341056,1549526502203413495808,1623317982086067912704,1697105239855882829824]

abbrev Label := Fin 22

def labelOf (r : Row) : Label := Fin.ofNat 22 labels[r.val]!

def axiomAt (b : Label) : Cl :=
  if b.val < 4 then posAx (Fin.ofNat 4 b.val)
  else negAx (Fin.ofNat 4 (negA[b.val]!)) (Fin.ofNat 4 (negB[b.val]!)) (Fin.ofNat 3 (negH[b.val]!))

def otherRow (r : Row) (v : V) : Row :=
  Fin.ofNat 60 ((neighborData[r.val]! >>> (6*port v)) % 64)

theorem posAxNamed : ∀ i : Fin 4, ∃ a : Label, axiomAt a = posAx i := by decide +kernel
theorem negAxNamed : ∀ i j : Fin 4, ∀ h : Fin 3, i ≠ j → ∃ a : Label, axiomAt a = negAx i j h := by decide +kernel

theorem axNamed {C : Cl} (ax : C ∈ PHP 4 3) : ∃ a : Label, axiomAt a = C := by
  rcases ax with ⟨i,rfl⟩ | ⟨i,j,h,ne,rfl⟩
  · exact posAxNamed i
  · exact negAxNamed i j h ne

theorem privateByName : ∀ r : Row, ∀ b : Label,
    (privateMask (axiomAt b)).testBit r.val = decide (labelOf r = b) := by decide +kernel

theorem axiomFlag (r : Row) (b : Label) :
    ¬ClauseSat (assignment r) (axiomAt b) ↔ labelOf r = b := by
  rw [← privateBit,privateByName,decide_eq_true_eq]

theorem everyLabel : ∀ b : Label, ∃ r : Row, labelOf r = b := by decide +kernel

theorem nameUnique {a b : Label} (eq : axiomAt a = axiomAt b) : a = b := by
  obtain ⟨r,h⟩ := everyLabel a
  have yes := (axiomFlag r a).2 h
  rw [eq,axiomFlag] at yes
  exact h.symm.trans yes

theorem neighborVar : ∀ r : Row, ∀ v : V, ∀ bit : Bool,
    (v,bit) ∈ axiomAt (labelOf r) →
    assignment (otherRow r v) v = bit ∧
    (∀ q : V, q ≠ v → assignment (otherRow r v) q = assignment r q) ∧
    labelOf (otherRow r v) ≠ labelOf r := by decide +kernel

def Taut (C : Cl) : Prop := ∃ v : V, (v,true) ∈ C ∧ (v,false) ∈ C

theorem falseAtFlip (a b : V → Bool) {D : Cl} {v : V} {t : Bool}
    (pivot : (v,t) ∈ D) (clean : ¬Taut D) (changed : b v ≠ t)
    (fixed : ∀ q ≠ v, b q = a q) (prior : ¬ClauseSat a (D.erase (v,t))) :
    ¬ClauseSat b D := by
  rintro ⟨⟨q,z⟩,m,hit⟩
  change b q = z at hit
  by_cases eq : q = v
  · subst q
    cases t <;> cases z
    · exact changed hit
    · exact clean ⟨v,m,pivot⟩
    · exact clean ⟨v,pivot,m⟩
    · exact changed hit
  · have mem : (q,z) ∈ D.erase (v,t) := Finset.mem_erase.mpr ⟨by simp [eq],m⟩
    exact prior ⟨(q,z),mem,(fixed q eq).symm.trans hit⟩

def posRows : Array Nat := #[5,3,4,2,1,0,11,9,10,8,7,6,17,15,16,14,13,12,23,21,22,20,19,18]
def posIDs : Array Nat := #[5,4,3,1,2,0,11,10,9,7,8,6,17,16,15,13,14,12,23,22,21,19,20,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def edgeLabels : Array Nat := #[4,10,16,5,11,17,6,12,18,7,13,19,8,14,20,9,15,21]
def edgeIDs : Array Nat := #[0,0,0,0,0,3,6,9,12,15,1,4,7,10,13,16,2,5,8,11,14,17]
def segments : Array Nat := #[192,3,1280,20,2560,40,12288,12,81920,33,163840,18,49152,768,135168,2112,73728,1152,786432,48,5242880,10,10485760,5,3145728,3072,8650752,640,4718592,320,12582912,196608,2621440,40960,1310720,20480]
def ports : Array Nat := #[3,0,4,1,5,2,6,0,7,1,8,2,6,3,7,4,8,5,9,0,10,1,11,2,9,3,10,4,11,5,9,6,10,7,11,8]
def move (s a : Nat) : Nat :=
  if a < 36 then s ||| segments[a]! else
    (List.range 36).foldl (fun t b =>
      let z := segments[b]!
      let w := segments[b ^^^ 1]!
      if ports[b]! + 36 == a && (s &&& z == z || s &&& w == w) then t ||| z else t) s

def Inc (a b : Nat) : Prop := ∀ k, a.testBit k = true → b.testBit k = true

theorem incRefl (a : Nat) : Inc a a := fun _ t => t

theorem incTrans {a b c : Nat} (ab : Inc a b) (bc : Inc b c) : Inc a c :=
  fun k h => bc k (ab k h)

theorem incIff (a b : Nat) : Inc a b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and]
    cases ha : a.testBit k with
    | false => rfl
    | true => simp [h k ha]
  · intro h k ha
    have q := congrArg (fun t : Nat => t.testBit k) h
    simpa [Nat.testBit_and,ha] using q

theorem incOr {a b c d : Nat} (h : Inc a b) (g : Inc c d) : Inc (a ||| c) (b ||| d) := by
  intro k hk
  rw [Nat.testBit_or,Bool.or_eq_true] at hk ⊢
  exact hk.imp (h k) (g k)

theorem incLeft (a b : Nat) : Inc a (a ||| b) := by
  intro k h; simp [Nat.testBit_or,h]

def gain (s a b acc : Nat) : Nat :=
  let z := segments[b]!
  let w := segments[b ^^^ 1]!
  if ports[b]! + 36 == a && (s &&& z == z || s &&& w == w) then acc ||| z else acc

theorem smallerMark {s t z : Nat} (h : Inc s t) (hz : s &&& z = z) :
    t &&& z = z := by
  rw [Nat.and_comm] at hz ⊢
  exact (incIff z t).1 (incTrans ((incIff z s).2 hz) h)

theorem gainMono {s t x y : Nat} (a b : Nat) (st : Inc s t) (xy : Inc x y) :
    Inc (gain s a b x) (gain t a b y) := by
  unfold gain
  dsimp only
  split <;> split
  · exact incOr xy (incRefl _)
  · rename_i hs ht
    simp only [Bool.and_eq_true, Bool.or_eq_true,beq_iff_eq] at hs ht
    exact False.elim (ht ⟨hs.1, hs.2.imp (smallerMark st) (smallerMark st)⟩)
  · exact incTrans xy (incLeft _ _)
  · exact xy

theorem moveMono {s t : Nat} (st : Inc s t) (a : Nat) : Inc (move s a) (move t a) := by
  unfold move
  split
  · exact incOr st (incRefl _)
  · change Inc ((List.range 36).foldl (fun x b => gain s a b x) s)
               ((List.range 36).foldl (fun y b => gain t a b y) t)
    generalize List.range 36 = bs
    have aux (l : List Nat) {u v : Nat} (uv : Inc u v) :
        Inc (l.foldl (fun x b => gain s a b x) u) (l.foldl (fun y b => gain t a b y) v) := by
      induction l generalizing u v with
      | nil => exact uv
      | cons b l ih => exact ih (gainMono a b st uv)
    exact aux bs st


abbrev PP := Fin 24
abbrev Edge := Fin 18
abbrev End := Fin 36
def positiveRow (p : PP) : Row := Fin.ofNat 60 posRows[p.val]!
def positiveID (r : Row) : PP := Fin.ofNat 24 posIDs[r.val]!
def edgeID (a : Label) : Edge := Fin.ofNat 18 edgeIDs[a.val]!
def edgeName (e : Edge) : Label := Fin.ofNat 22 edgeLabels[e.val]!
def endEdge (e : End) : Edge := Fin.ofNat 18 (e.val/2)
def endpoint (a : Label) (v : V) : End :=
  let b := 2*(edgeID a).val
  Fin.ofNat 36 (if ports[b]! = port v then b else b+1)
def seg (e : End) := segments[e.val]!
def isMarked (s : Nat) (p : PP) := s.testBit p.val = true
def enabled (s : Nat) (e : Edge) : Prop :=
  Inc segments[2*e.val]! s ∨ Inc segments[2*e.val+1]! s

theorem positiveLabs : ∀ p : PP, (labelOf (positiveRow p)).val < 4 := by decide +kernel
theorem canonPos : ∀ r : Row, (labelOf r).val < 4 → positiveRow (positiveID r) = r := by decide +kernel
theorem edgeLab : ∀ b : Label, 4 ≤ b.val → edgeName (edgeID b) = b := by decide +kernel
theorem edgeLab2 : ∀ e : Edge, edgeID (edgeName e) = e ∧ 4 ≤ (edgeName e).val := by decide +kernel
theorem signs : ∀ b : Label, ∀ v : V, ∀ t : Bool, (v,t) ∈ axiomAt b → (t = true ↔ b.val < 4) := by decide +kernel
theorem endpoints : ∀ b : Label, ∀ v : V, (v,false) ∈ axiomAt b →
    endEdge (endpoint b v) = edgeID b ∧ ports[(endpoint b v).val]! = port v := by decide +kernel
theorem posFlip : ∀ p : PP, ∀ v : V, (v,true) ∈ axiomAt (labelOf (positiveRow p)) →
    let b := labelOf (otherRow (positiveRow p) v)
    (v,false) ∈ axiomAt b ∧ (seg (endpoint b v)).testBit p.val = true := by decide +kernel
theorem backPair : ∀ b : Label, ∀ v : V, (v,false) ∈ axiomAt b → ∀ p : PP,
    (seg (endpoint b v)).testBit p.val = true →
    let r := otherRow (positiveRow p) v
    labelOf r = b ∧ otherRow r v = positiveRow p := by decide +kernel
theorem segSmall : ∀ e : End, seg e < 2^24 := by decide +kernel

theorem incFromPositive (s : Nat) (e : End)
    (h : ∀ p : PP, (seg e).testBit p.val = true → isMarked s p) : Inc (seg e) s := by
  intro k hit
  by_cases sm : k < 24
  · exact h ⟨k,sm⟩ hit
  · have dead := Nat.testBit_lt_two_pow (lt_of_lt_of_le (segSmall e)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 24 ≤ k)))
    simp [dead] at hit

theorem growGain (s a b base : Nat) : Inc base (gain s a b base) := by
  unfold gain
  dsimp only
  split
  · exact incLeft _ _
  · exact incRefl _

theorem growFoldGain (s a : Nat) (xs : List Nat) (base : Nat) :
    Inc base (xs.foldl (fun x b => gain s a b x) base) := by
  induction xs generalizing base with
  | nil => exact incRefl _
  | cons b xs ih => exact incTrans (growGain s a b base) (ih _)

theorem moveGrows (s a : Nat) : Inc s (move s a) := by
  unfold move
  split
  · exact incLeft _ _
  · exact growFoldGain s a _ s

theorem directGain (s : Nat) (e : End) : Inc (seg e) (move s e.val) := by
  intro k t
  simp [seg,move,e.isLt,Nat.testBit_or] at t ⊢
  exact Or.inr t

theorem portGain (s : Nat) (e : End) (active : enabled s (endEdge e)) :
    Inc (seg e) (move s (36+ports[e.val]!)) := by
  have pair : ∀ f : End,
      (segments[2*(endEdge f).val]! = seg f ∧ segments[2*(endEdge f).val+1]! = segments[f.val ^^^ 1]!) ∨
      (segments[2*(endEdge f).val+1]! = seg f ∧ segments[2*(endEdge f).val]! = segments[f.val ^^^ 1]!) := by decide +kernel
  have act : Inc (seg e) s ∨ Inc segments[e.val ^^^ 1]! s := by
    rcases pair e with ⟨u,v⟩ | ⟨u,v⟩
    · simpa [enabled,u,v] using active
    · simpa [enabled,u,v,or_comm] using active
  have one (x : Nat) : Inc (seg e) (gain s (36+ports[e.val]!) e.val x) := by
    have flag : s &&& seg e = seg e ∨ s &&& segments[e.val ^^^ 1]! = segments[e.val ^^^ 1]! := by
      rcases act with h | h
      · exact Or.inl (by rw [Nat.and_comm]; exact (incIff _ _).1 h)
      · exact Or.inr (by rw [Nat.and_comm]; exact (incIff _ _).1 h)
    have yes : ((ports[e.val]! + 36 == 36 + ports[e.val]!) &&
        (s &&& segments[e.val]! == segments[e.val]! || s &&& segments[e.val ^^^ 1]! == segments[e.val ^^^ 1]!)) = true := by
      simpa [Bool.and_eq_true,Bool.or_eq_true,seg,Nat.add_comm] using flag
    intro k m
    unfold gain
    dsimp only
    rw [if_pos yes,Nat.testBit_or,Bool.or_eq_true]
    exact Or.inr m
  have loop (xs : List Nat) (x : Nat) (member : e.val ∈ xs) :
      Inc (seg e) (xs.foldl (fun q b => gain s (36+ports[e.val]!) b q) x) := by
    induction xs generalizing x with
    | nil => simp at member
    | cons b bs ih =>
      rcases List.mem_cons.mp member with eq | mem
      · subst b
        exact incTrans (one x) (growFoldGain s _ _ _)
      · exact ih _ mem
  unfold move
  rw [if_neg (by omega)]
  exact loop _ _ (List.mem_range.mpr e.isLt)

theorem makesActive (s : Nat) (e : End) (all : Inc (seg e) s) : enabled s (endEdge e) := by
  have alt : ∀ f : End, segments[2*(endEdge f).val]! = seg f ∨ segments[2*(endEdge f).val+1]! = seg f := by decide +kernel
  rcases alt e with h | h
  · exact Or.inl (h ▸ all)
  · exact Or.inr (h ▸ all)

theorem enabledUp {s t : Nat} (g : Inc s t) (e : Edge) (x : enabled s e) : enabled t e :=
  x.imp (fun h => incTrans h g) (fun h => incTrans h g)

theorem badParent (a : V → Bool) {C D R : Cl} (h : IsResolvent C D R) (bad : ¬ClauseSat a R) :
    ¬ClauseSat a C ∨ ¬ClauseSat a D := by
  classical
  by_contra! both
  obtain ⟨v,_,_,rfl⟩ := h
  obtain ⟨l,ml,el⟩ := both.1
  obtain ⟨t,mt,et⟩ := both.2
  by_cases left : l = (v,true)
  · have right : t ≠ (v,false) := by
      intro he; subst t; subst l
      change a v = true at el
      change a v = false at et
      simp [el] at et
    exact bad ⟨t,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨right,mt⟩),et⟩
  · exact bad ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨left,ml⟩),el⟩


def GoodAt (s : Nat) (C : Cl) : Prop :=
  (∀ p : PP, ¬ClauseSat (assignment (positiveRow p)) C → isMarked s p) ∧
  (∀ r : Row, 4 ≤ (labelOf r).val → ¬ClauseSat (assignment r) C → enabled s (edgeID (labelOf r)))

theorem posSource {a : Label} {v : V} (hp : (v,true) ∈ axiomAt a) : a.val < 4 :=
  (signs a v true hp).1 rfl

theorem negSource {a : Label} {v : V} (hp : (v,false) ∈ axiomAt a) : 4 ≤ a.val := by
  have := signs a v false hp
  simp at this
  omega

theorem positiveOpposite {b : Label} (h : 4 ≤ b.val) (p : PP) :
    ClauseSat (assignment (positiveRow p)) (axiomAt b) := by
  by_contra bad
  have eq := (axiomFlag _ _).1 bad
  have lt := positiveLabs p
  rw [eq] at lt
  omega

theorem negativeOpposite {a : Label} (h : a.val < 4) (r : Row) (hr : 4 ≤ (labelOf r).val) :
    ClauseSat (assignment r) (axiomAt a) := by
  by_contra bad
  have eq := (axiomFlag _ _).1 bad
  rw [eq] at hr
  omega

theorem flipRight {a : Label} {v : V} {D : Cl} (hp : (v,true) ∈ axiomAt a) (hn : (v,false) ∈ D)
    (clean : ¬Taut D) (r : Row) (lab : labelOf r = a)
    (wrong : ¬ClauseSat (assignment r) ((axiomAt a).erase (v,true) ∪ D.erase (v,false))) :
    ¬ClauseSat (assignment (otherRow r v)) D := by
  have side := neighborVar r v true (by simpa [lab] using hp)
  apply falseAtFlip (assignment r) _ hn clean (by simp [side.1]) side.2.1
  rintro ⟨l,h,yes⟩
  exact wrong ⟨l,Finset.mem_union_right _ h,yes⟩

theorem flipLeft {b : Label} {v : V} {C : Cl} (hp : (v,true) ∈ C) (hn : (v,false) ∈ axiomAt b)
    (clean : ¬Taut C) (r : Row) (lab : labelOf r = b)
    (wrong : ¬ClauseSat (assignment r) (C.erase (v,true) ∪ (axiomAt b).erase (v,false))) :
    ¬ClauseSat (assignment (otherRow r v)) C := by
  have side := neighborVar r v false (by simpa [lab] using hn)
  apply falseAtFlip (assignment r) _ hp clean (by simp [side.1]) side.2.1
  rintro ⟨l,h,yes⟩
  exact wrong ⟨l,Finset.mem_union_left _ h,yes⟩

theorem noRaw {s : Nat} {C D R : Cl} (sc : GoodAt s C) (sd : GoodAt s D)
    (res : IsResolvent C D R) : GoodAt s R :=
  ⟨fun p h => (badParent _ res h).elim (sc.1 p) (sd.1 p),
   fun r hr h => (badParent _ res h).elim (sc.2 r hr) (sd.2 r hr)⟩

theorem twoRaw (s : Nat) (a b : Label) (v : V) (hp : (v,true) ∈ axiomAt a)
    (hn : (v,false) ∈ axiomAt b) (clean : ¬Taut (axiomAt b)) :
    GoodAt (move s (endpoint b v).val) ((axiomAt a).erase (v,true) ∪ (axiomAt b).erase (v,false)) := by
  let e := endpoint b v
  have res : IsResolvent (axiomAt a) (axiomAt b) _ := ⟨v,hp,hn,rfl⟩
  constructor
  · intro p h
    have badA := (badParent (assignment (positiveRow p)) res h).resolve_right
      (not_not.mpr (positiveOpposite (negSource hn) p))
    have lab := (axiomFlag _ _).1 badA
    have badB := flipRight hp hn clean _ lab h
    have lb := (axiomFlag _ _).1 badB
    have grp := (posFlip p v (by simpa [lab] using hp)).2
    rw [lb] at grp
    exact directGain s e p.val grp
  · intro r far h
    have badB := (badParent (assignment r) res h).resolve_left
      (not_not.mpr (negativeOpposite (posSource hp) r far))
    have eq := (axiomFlag _ _).1 badB
    rw [eq,← (endpoints b v hn).1]
    exact makesActive _ e (directGain s e)

theorem leftRaw (s : Nat) (a : Label) (v : V) {D : Cl} (hp : (v,true) ∈ axiomAt a)
    (hn : (v,false) ∈ D) (clean : ¬Taut D) (know : GoodAt s D) :
    GoodAt (move s (36+port v)) ((axiomAt a).erase (v,true) ∪ D.erase (v,false)) := by
  have res : IsResolvent (axiomAt a) D _ := ⟨v,hp,hn,rfl⟩
  have grow := moveGrows s (36+port v)
  constructor
  · intro p h
    rcases badParent _ res h with left | right
    · have lab := (axiomFlag _ _).1 left
      let b := labelOf (otherRow (positiveRow p) v)
      obtain ⟨neg,hit⟩ := posFlip p v (by simpa [lab] using hp)
      have prior := flipRight hp hn clean _ lab h
      have ready := know.2 (otherRow (positiveRow p) v) (negSource neg) prior
      have e := endpoints b v neg
      have gain := portGain s (endpoint b v) (by simpa [e.1] using ready)
      rw [e.2] at gain
      exact gain p.val hit
    · exact grow p.val (know.1 p right)
  · intro r far h
    have older := (badParent (assignment r) res h).resolve_left
      (not_not.mpr (negativeOpposite (posSource hp) r far))
    exact enabledUp grow _ (know.2 r far older)

theorem rightRaw (s : Nat) (b : Label) (v : V) {C : Cl} (hp : (v,true) ∈ C)
    (hn : (v,false) ∈ axiomAt b) (clean : ¬Taut C) (know : GoodAt s C)
    (sole : enabled s (edgeID b) ∨ ∀ r, labelOf r = b →
      ¬ClauseSat (assignment r) (C.erase (v,true) ∪ (axiomAt b).erase (v,false))) :
    GoodAt s (C.erase (v,true) ∪ (axiomAt b).erase (v,false)) := by
  have res : IsResolvent C (axiomAt b) _ := ⟨v,hp,hn,rfl⟩
  have able : enabled s (edgeID b) := by
    rcases sole with ready | all
    · exact ready
    · rw [← (endpoints b v hn).1]
      apply makesActive
      apply incFromPositive
      intro p hit
      obtain ⟨lab,back⟩ := backPair b v hn p hit
      have older := flipLeft hp hn clean _ lab (all _ lab)
      rw [back] at older
      exact know.1 p older
  constructor
  · intro p h
    exact know.1 p ((badParent (assignment (positiveRow p)) res h).resolve_right
        (not_not.mpr (positiveOpposite (negSource hn) p)))
  · intro r far h
    rcases badParent _ res h with left | right
    · exact know.2 r far left
    · rw [(axiomFlag _ _).1 right]
      exact able

abbrev IndexedClause := Clause (Fin 4 × Fin 3)

/-- Parents are physical lines, identified by their position in the newest-first list. -/
inductive LineReason (F : Set IndexedClause) (rows : List IndexedClause)
    (k : Nat) (R : IndexedClause) : Type where
  | ax (member : R ∈ F)
  | res (i j : Nat) (C D : IndexedClause)
      (earlierLeft : k < i) (earlierRight : k < j)
      (leftLine : rows[i]? = some C) (rightLine : rows[j]? = some D)
      (resolve : IsResolvent C D R)

private theorem address {rows : List IndexedClause} {C : IndexedClause}
    (h : C ∈ rows) : ∃ i : Nat, rows[i]? = some C := by
  induction rows with
  | nil => simp at h
  | cons r rows ih =>
    rcases List.mem_cons.mp h with eq | tail
    · subst r
      exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih tail
      exact ⟨i+1, by simpa using hi⟩

private def shiftReason {F rows k R} (x : LineReason F rows k R) (newest : IndexedClause) :
    LineReason F (newest :: rows) (k+1) R := by
  cases x with
  | ax h => exact .ax h
  | res i j C D hi hj hC hD step =>
    exact .res (i+1) (j+1) C D (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
      (by simpa using hC) (by simpa using hD) step

private theorem extendReasons {F rows R}
    (front : Nonempty (LineReason F (R :: rows) 0 R))
    (old : ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C)) :
    ∀ k C, (R :: rows)[k]? = some C → Nonempty (LineReason F (R :: rows) k C) := by
  intro k C h
  cases k with
  | zero =>
    have eq : R = C := Option.some.inj h
    subst C
    exact front
  | succ k =>
    obtain ⟨reason⟩ := old k C (by simpa using h)
    exact ⟨shiftReason reason R⟩

theorem indexedDerivation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsDerivation F rows) :
    ∀ k C, rows[k]? = some C → Nonempty (LineReason F rows k C) := by
  induction h with
  | nil => simp
  | ax _ mem ih => exact extendReasons ⟨.ax mem⟩ ih
  | res _ left right step ih =>
    obtain ⟨i, hi⟩ := address left
    obtain ⟨j, hj⟩ := address right
    exact extendReasons ⟨.res (i+1) (j+1) _ _ (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (by simpa using hi) (by simpa using hj) step⟩ ih

theorem indexedRefutation {F : Set IndexedClause} {rows : List IndexedClause}
    (h : IsRefutation F rows) :
    ∃ root : Nat, rows[root]? = some ∅ ∧
      Nonempty ((i : Fin rows.length) → LineReason F rows i.val rows[i.val]) := by
  obtain ⟨root, hr⟩ := address h.2
  refine ⟨root, hr, ⟨fun i => Classical.choice (indexedDerivation h.1 i.val rows[i.val] ?_)⟩⟩
  simp [i.isLt]


def linksOf {F rows k C} (r : LineReason F rows k C) : Option (Fin rows.length × Fin rows.length) :=
  match r with
  | .ax _ => none
  | .res i j _ _ _ _ hi hj _ =>
    some (⟨i,(List.getElem?_eq_some_iff.mp hi).1⟩,⟨j,(List.getElem?_eq_some_iff.mp hj).1⟩)

structure Links {n : Nat} (atLine : Fin n → Cl) where
  parent : Fin n → Option (Fin n × Fin n)
  ax : ∀ i, parent i = none → atLine i ∈ PHP 4 3
  rule : ∀ i j k, parent i = some (j,k) →
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent (atLine j) (atLine k) (atLine i)

theorem flatAx {rows : List Cl} {i : Fin rows.length}
    (r : LineReason (PHP 4 3) rows i.val rows[i.val]) (h : linksOf r = none) :
    rows[i.val] ∈ PHP 4 3 := by
  cases r with
  | ax mem => exact mem
  | res => simp [linksOf] at h

theorem flatRes {rows : List Cl} {i j k : Fin rows.length}
    (r : LineReason (PHP 4 3) rows i.val rows[i.val]) (h : linksOf r = some (j,k)) :
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent rows[j.val] rows[k.val] rows[i.val] := by
  cases r with
  | ax => simp [linksOf] at h
  | res u v C D hu hv hC hD rr =>
    change some (_,_) = some (j,k) at h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa [(List.getElem?_eq_some_iff.mp hC).2,(List.getElem?_eq_some_iff.mp hD).2] using
      (show i.val < u ∧ i.val < v ∧ IsResolvent C D rows[i.val] from ⟨hu,hv,rr⟩)

def asLinks {rows : List Cl}
    (reas : (i : Fin rows.length) → LineReason (PHP 4 3) rows i.val rows[i.val]) :
    Links (fun i : Fin rows.length => rows[i.val]) where
  parent i := linksOf (reas i)
  ax i := flatAx (reas i)
  rule i j k := flatRes (reas i)

def ReadAt {n : Nat} {C : Fin n → Cl} (g : Links C) (b : Label) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧
    ((g.parent j = none ∧ C j = axiomAt b) ∨ (g.parent k = none ∧ C k = axiomAt b))

theorem firstRead {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Row)
    (i : Fin n) (notAx : g.parent i ≠ none) (bad : ¬ClauseSat (assignment r) (C i)) :
    ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
  classical
  have aux (m : Nat) : ∀ i : Fin n, n-i.val = m → g.parent i ≠ none →
      ¬ClauseSat (assignment r) (C i) →
      ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro i eq notAx bad
      cases link : g.parent i with
      | none => exact False.elim (notAx link)
      | some jk =>
        obtain ⟨j,k⟩ := jk
        obtain ⟨hj,hk,step⟩ := g.rule i j k link
        have follow (u : Fin n) (old : i.val < u.val) (endpoint : u = j ∨ u = k)
            (wrong : ¬ClauseSat (assignment r) (C u)) :
            ∃ v, ReadAt g (labelOf r) v ∧ ¬ClauseSat (assignment r) (C v) := by
          by_cases raw : g.parent u = none
          · obtain ⟨b,name⟩ := axNamed (g.ax u raw)
            have lab : labelOf r = b := (axiomFlag r b).1 (by simpa [name] using wrong)
            have nm : C u = axiomAt (labelOf r) := by rw [lab,name]
            refine ⟨i,⟨j,k,link,?_⟩,bad⟩
            rcases endpoint with rfl | rfl
            · exact Or.inl ⟨raw,nm⟩
            · exact Or.inr ⟨raw,nm⟩
          · exact ih (n-u.val) (by have := i.isLt; have := u.isLt; omega) u rfl raw wrong
        rcases badParent (assignment r) step bad with jl | kr
        · exact follow j hj (Or.inl rfl) jl
        · exact follow k hk (Or.inr rfl) kr
  exact aux _ i rfl notAx bad

theorem rootNotAx {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅) :
    g.parent i ≠ none := by
  intro raw
  obtain ⟨b,nm⟩ := axNamed (g.ax i raw)
  have nonempty : ∀ a : Label, axiomAt a ≠ ∅ := by decide +kernel
  exact nonempty b (nm.trans emp)

theorem privateCoverage {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅)
    (r : Row) : ∃ u, ReadAt g (labelOf r) u ∧ ¬ClauseSat (assignment r) (C u) := by
  apply firstRead g r i (rootNotAx g i emp)
  simp [emp,ClauseSat]

theorem uniqueReadFails {n : Nat} {C : Fin n → Cl} (g : Links C) (i : Fin n) (emp : C i = ∅)
    (b : Label) (u : Fin n) (sole : ∀ j, ReadAt g b j → j = u)
    (r : Row) (lab : labelOf r = b) : ¬ClauseSat (assignment r) (C u) := by
  obtain ⟨j,read,bad⟩ := privateCoverage g i emp r
  rw [lab] at read
  exact sole j read ▸ bad

variable {n : Nat} {C : Fin n → Cl}
def LeftRaw (g : Links C) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧ g.parent j = none

def RightRead (g : Links C) (e : Edge) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧ g.parent k = none ∧ C k = axiomAt (edgeName e)

noncomputable def rights (g : Links C) (e : Edge) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (RightRead g e)

noncomputable def excepts (g : Links C) : Finset Edge := by
  classical
  exact Finset.univ.filter (fun e => 2 ≤ (rights g e).card)

theorem rightOfRead (g : Links C) (e : Edge) {i : Fin n} (h : ReadAt g (edgeName e) i) :
    RightRead g e i := by
  obtain ⟨j,k,link,raw | raw⟩ := h
  · obtain ⟨v,pos,_,_⟩ := (g.rule _ _ _ link).2.2
    rw [raw.2] at pos
    have lt := posSource pos
    have far := (edgeLab2 e).2
    omega
  · exact ⟨j,k,link,raw⟩

theorem allRight (g : Links C) (root : Fin n) (emp : C root = ∅) (e : Edge) :
    (rights g e).Nonempty := by
  classical
  obtain ⟨r,lab⟩ := everyLabel (edgeName e)
  obtain ⟨j,read,_⟩ := privateCoverage g root emp r
  rw [lab] at read
  exact ⟨j, by simpa [rights] using rightOfRead g e read⟩

theorem uniqueOrPaid (g : Links C) (root : Fin n) (emp : C root = ∅)
    {u : Fin n} {b : Label} (far : 4 ≤ b.val) (read : ReadAt g b u) (s : Nat)
    (prepaid : ∀ e ∈ excepts g, enabled s e) :
    enabled s (edgeID b) ∨ ∀ r, labelOf r = b → ¬ClauseSat (assignment r) (C u) := by
  classical
  by_cases pay : edgeID b ∈ excepts g
  · exact Or.inl (prepaid _ pay)
  · right
    apply uniqueReadFails g root emp b u
    intro j hj
    have inv := edgeLab b far
    have ofRead {k : Fin n} (r : ReadAt g b k) : k ∈ rights g (edgeID b) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,rightOfRead g (edgeID b) (by simpa [inv] using r)⟩
    have small : (rights g (edgeID b)).card ≤ 1 := by
      simpa [excepts] using pay
    exact Finset.card_le_one.mp small j (ofRead hj) u (ofRead read)

theorem countNegative (g : Links C) (root : Fin n) (emp : C root = ∅) :
    18 + (excepts g).card ≤ ∑ e : Edge, (rights g e).card := by
  classical
  have sub : ∑ e : Edge, (1 + (if e ∈ excepts g then 1 else 0)) ≤
      ∑ e : Edge, (rights g e).card := by
    apply Finset.sum_le_sum
    intro e _
    by_cases h : e ∈ excepts g
    · have big : 2 ≤ (rights g e).card := by simpa [excepts] using h
      simpa [h] using big
    · have pos := Finset.card_pos.mpr (allRight g root emp e)
      simpa only [if_neg h,Nat.add_zero] using pos
  simpa [Finset.sum_add_distrib] using sub

theorem goodUp {s t : Nat} (up : Inc s t) {D : Cl} (known : GoodAt s D) : GoodAt t D :=
  ⟨fun p bad => up p.val (known.1 p bad),fun r far bad => enabledUp up _ (known.2 r far bad)⟩

theorem portUnder (v : V) : port v < 12 := by revert v; decide +kernel

def act (s : Nat) (a : Option (Fin 48)) : Nat := match a with
  | none => s
  | some q => move s q.val

theorem actGrows (s : Nat) (a : Option (Fin 48)) : Inc s (act s a) := by
  cases a with
  | none => exact incRefl _
  | some x => exact moveGrows _ _

theorem lineStep (g : Links C) (root : Fin n) (emp : C root = ∅) (clean : ∀ i, ¬Taut (C i))
    (i : Fin n) (s : Nat) (prepaid : ∀ e ∈ excepts g, enabled s e)
    (older : ∀ j : Fin n, i.val < j.val → g.parent j ≠ none → GoodAt s (C j)) :
    ∃ a : Option (Fin 48), (a ≠ none ↔ LeftRaw g i) ∧
      (g.parent i ≠ none → GoodAt (act s a) (C i)) := by
  classical
  cases why : g.parent i with
  | none =>
    refine ⟨none,?_,by simp [why]⟩
    simp [LeftRaw,why]
  | some jk =>
    obtain ⟨j,k⟩ := jk
    obtain ⟨hj,hk,v,pos,neg,eq⟩ := g.rule i j k why
    have left : LeftRaw g i ↔ g.parent j = none := by simp [LeftRaw,why]
    by_cases rawj : g.parent j = none
    · obtain ⟨a,ea⟩ := axNamed (g.ax _ rawj)
      rw [← ea] at pos
      by_cases rawk : g.parent k = none
      · obtain ⟨b,eb⟩ := axNamed (g.ax _ rawk)
        rw [← eb] at neg
        let e := endpoint b v
        let a0 : Fin 48 := ⟨e.val,by have := e.isLt; omega⟩
        refine ⟨some a0,by simp [left,rawj],?_⟩
        intro _
        rw [eq,← ea,← eb]
        exact twoRaw s a b v pos neg (by simpa [eb] using clean k)
      · let a0 : Fin 48 := ⟨36+port v,by have := portUnder v; omega⟩
        refine ⟨some a0,by simp [left,rawj],?_⟩
        intro _
        rw [eq,← ea]
        exact leftRaw s a v pos neg (clean k) (older k hk rawk)
    · by_cases rawk : g.parent k = none
      · obtain ⟨b,eb⟩ := axNamed (g.ax _ rawk)
        rw [← eb] at neg
        have rd : ReadAt g b i := ⟨j,k,why,Or.inr ⟨rawk,eb.symm⟩⟩
        have sole := uniqueOrPaid g root emp (negSource neg) rd s prepaid
        rw [eq,← eb] at sole
        refine ⟨none,by simp [left,rawj],?_⟩
        intro _
        rw [eq,← eb]
        exact rightRaw s b v pos neg (clean j) (older j hj rawj) sole
      · refine ⟨none,by simp [left,rawj],?_⟩
        intro _
        exact noRaw (older j hj rawj) (older k hk rawk) (g.rule i j k why).2.2


def runMoves (moves : List (Fin 48)) (s : Nat) : Nat :=
  moves.foldl (fun x a => move x a.val) s

theorem runGrows (moves : List (Fin 48)) (s : Nat) : Inc s (runMoves moves s) := by
  induction moves generalizing s with
  | nil => exact incRefl _
  | cons a as ih => exact incTrans (moveGrows _ _) (ih _)

def firstEnd (e : Edge) : End := ⟨2*e.val,by have := e.isLt; omega⟩
def seedMove (e : Edge) : Fin 48 := ⟨(firstEnd e).val,by have := (firstEnd e).isLt; omega⟩
theorem firstEndEq : ∀ e : Edge, endEdge (firstEnd e) = e := by decide +kernel
theorem seedsEnable (es : List Edge) (s : Nat) (e : Edge) (m : e ∈ es) :
    enabled (runMoves (es.map seedMove) s) e := by
  induction es generalizing s with
  | nil => simp at m
  | cons d ds ih =>
    rcases List.mem_cons.mp m with rfl | mem
    · have first := firstEndEq e
      have ready := makesActive _ (firstEnd e) (directGain s (firstEnd e))
      rw [first] at ready
      exact enabledUp (runGrows (ds.map seedMove) _) _ ready
    · exact ih (move s (seedMove d).val) mem

noncomputable def posFrom (g : Links C) (k : Nat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => k ≤ i.val ∧ LeftRaw g i)

theorem posSubset (g : Links C) (i : Fin n) : posFrom g (i.val+1) ⊆ posFrom g i.val := by
  classical
  intro j hj
  simp [posFrom] at hj ⊢
  exact ⟨by omega,hj.2⟩

theorem posGain (g : Links C) (i : Fin n) (reads : LeftRaw g i) :
    (posFrom g (i.val+1)).card+1 ≤ (posFrom g i.val).card := by
  classical
  have notyet : i ∉ posFrom g (i.val+1) := by simp [posFrom]
  rw [← Finset.card_insert_of_notMem notyet]
  apply Finset.card_le_card
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | earlier
  · simpa [posFrom] using reads
  · exact posSubset g i earlier

theorem simulateLines (g : Links C) (root : Fin n) (emp : C root = ∅) (clean : ∀ i, ¬Taut (C i))
    (s0 : Nat) (p0 : ∀ e ∈ excepts g, enabled s0 e) :
    ∃ xs : List (Fin 48), xs.length ≤ (posFrom g 0).card ∧
      ∀ p : PP, isMarked (runMoves xs s0) p := by
  classical
  have go : ∀ m : Nat, m ≤ n → ∃ xs : List (Fin 48), xs.length ≤ (posFrom g (n-m)).card ∧
      (∀ e ∈ excepts g, enabled (runMoves xs s0) e) ∧
      (∀ j : Fin n, n-m ≤ j.val → g.parent j ≠ none → GoodAt (runMoves xs s0) (C j)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨[],by simp,p0,?_⟩
      intro j far
      have := j.isLt
      omega
    | succ m ih =>
      intro le
      let i : Fin n := ⟨n-(m+1),by omega⟩
      have times : n-m = i.val+1 := by dsimp [i]; omega
      obtain ⟨xs,oldSize,paid,known⟩ := ih (by omega)
      rw [times] at oldSize known
      have earlier (j : Fin n) (lt : i.val < j.val) (non : g.parent j ≠ none) :
          GoodAt (runMoves xs s0) (C j) := known j lt non
      obtain ⟨a,raw,now⟩ := lineStep g root emp clean i (runMoves xs s0) paid earlier
      refine ⟨xs ++ a.toList,?_,?_,?_⟩
      · change (xs ++ a.toList).length ≤ (posFrom g i.val).card
        cases a with
        | none => simpa using oldSize.trans (Finset.card_le_card (posSubset g i))
        | some v =>
          have more := posGain g i (raw.mp (by simp))
          simp; omega
      · intro e he
        have up := actGrows (runMoves xs s0) a
        have ready := enabledUp up e (paid e he)
        cases a <;> simpa [runMoves,act,List.foldl_append] using ready
      · intro j after non
        change i.val ≤ j.val at after
        have update : GoodAt (act (runMoves xs s0) a) (C j) := by
          by_cases atHead : j=i
          · subst j; exact now non
          · have lt : i.val < j.val := by
              have ne : j.val ≠ i.val := fun h => atHead (Fin.ext h)
              omega
            exact goodUp (actGrows _ _) (earlier j lt non)
        cases a <;> simpa [runMoves,act,List.foldl_append] using update
  obtain ⟨xs,sz,_,all⟩ := go n (by omega)
  simp only [Nat.sub_self] at sz all
  refine ⟨xs,sz,?_⟩
  intro p
  apply (all root (by omega) (rootNotAx g root emp)).1 p
  simp [emp,ClauseSat]

theorem rawLowerFromGame (hard : ∀ xs : List (Fin 48), xs.length ≤ 8 →
    ¬∀ p : PP, isMarked (runMoves xs 0) p) (g : Links C) (root : Fin n)
    (emp : C root = ∅) (clean : ∀ i, ¬Taut (C i)) :
    27 ≤ (posFrom g 0).card + ∑ e : Edge, (rights g e).card := by
  classical
  let start := (excepts g).toList.map seedMove
  have paid (e : Edge) (he : e ∈ excepts g) : enabled (runMoves start 0) e :=
    seedsEnable _ 0 e (by simpa using he)
  obtain ⟨xs,maxsz,covered⟩ := simulateLines g root emp clean _ paid
  have neg := countNegative g root emp
  by_contra! small
  have cnt : start.length = (excepts g).card := by simp [start]
  apply hard (start ++ xs) (by rw [List.length_append]; omega)
  simpa [runMoves,List.foldl_append] using covered


def RightRaw (g : Links C) (i : Fin n) : Prop := ∃ j k, g.parent i = some (j,k) ∧ g.parent k = none

theorem uniqueEdge (g : Links C) {i : Fin n} {e f : Edge}
    (a : RightRead g e i) (b : RightRead g f i) : e=f := by
  obtain ⟨j,k,u,_,ue⟩ := a
  obtain ⟨j',k',u',_,uf⟩ := b
  have parents := Prod.mk.inj (Option.some.inj (u.symm.trans u'))
  obtain rfl := parents.2
  have keys := congrArg edgeID (nameUnique (ue.symm.trans uf))
  simpa [(edgeLab2 e).1,(edgeLab2 f).1] using keys

theorem existsRight (g : Links C) (i : Fin n) : RightRaw g i ↔ ∃ e, RightRead g e i := by
  constructor
  · rintro ⟨j,k,link,raw⟩
    obtain ⟨b,eb⟩ := axNamed (g.ax _ raw)
    obtain ⟨v,_,neg,_⟩ := (g.rule i j k link).2.2
    rw [← eb] at neg
    exact ⟨edgeID b,j,k,link,raw,by rw [edgeLab b (negSource neg),eb]⟩
  · rintro ⟨_,j,k,link,raw,_⟩
    exact ⟨j,k,link,raw⟩

noncomputable def rawSlots (g : Links C) : Nat := by
  classical
  exact ∑ i : Fin n, ((if LeftRaw g i then 1 else 0) + (if RightRaw g i then 1 else 0))

theorem slots_eq (g : Links C) :
    rawSlots g = (posFrom g 0).card + ∑ e : Edge, (rights g e).card := by
  classical
  have rightOne (i : Fin n) :
      (∑ e : Edge, if RightRead g e i then (1 : Nat) else 0) = if RightRaw g i then 1 else 0 := by
    by_cases h : RightRaw g i
    · obtain ⟨e,he⟩ := (existsRight g i).1 h
      have eq (f : Edge) : RightRead g f i ↔ f=e :=
        ⟨fun hf => uniqueEdge g hf he,fun x => x ▸ he⟩
      simp [eq,h]
    · have na (e : Edge) : ¬ RightRead g e i := fun r => h ((existsRight g i).2 ⟨e,r⟩)
      simp [na,h]
  have rightsEq : (∑ e : Edge, (rights g e).card) = ∑ i : Fin n, if RightRaw g i then 1 else 0 := by
    calc
      _ = ∑ e : Edge, ∑ i : Fin n, if RightRead g e i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [rights,Finset.card_filter]
      _ = ∑ i : Fin n, ∑ e : Edge, if RightRead g e i then 1 else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun i _ => rightOne i)
  rw [rawSlots,Finset.sum_add_distrib,rightsEq]
  congr 1
  simp [posFrom,Finset.card_filter]

theorem everySource (g : Links C) (root : Fin n) (emp : C root = ∅) (b : Label) :
    ∃ i, g.parent i = none ∧ C i = axiomAt b := by
  obtain ⟨r,lab⟩ := everyLabel b
  obtain ⟨u,read,_⟩ := privateCoverage g root emp r
  rw [lab] at read
  obtain ⟨i,j,_,hi | hj⟩ := read
  · exact ⟨i,hi⟩
  · exact ⟨j,hj⟩

theorem distinctSources (g : Links C) (root : Fin n) (emp : C root = ∅) :
    ∃ f : Label → Fin n, Function.Injective f ∧ ∀ b, g.parent (f b) = none ∧ C (f b) = axiomAt b := by
  classical
  choose f raw nm using (everySource g root emp)
  refine ⟨f,?_,fun b => ⟨raw b,nm b⟩⟩
  intro a b eq
  exact nameUnique ((nm a).symm.trans ((congrArg C eq).trans (nm b)))

end PCX150

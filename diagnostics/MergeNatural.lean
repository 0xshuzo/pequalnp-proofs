import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3

abbrev Cl := Clause V

abbrev Row := Fin 60

def fullMask : Nat := 0xfffffffffffffff

def rows : Array Nat := #[672,784,1120,1288,2128,2184,644,770,1092,1281,2114,2177,532,546,1036,1057,2058,2065,84,98,140,161,266,273,1289,2185,1121,2129,1100,2122,673,785,652,778,596,610,786,2130,674,2186,660,2193,1122,1290,1108,1297,1164,1185,676,1124,788,1292,802,1313,2132,2188,2146,2209,2314,2321]

def ones : Array Nat := #[0xa20a200cfa28a00,0x5100cfa20492480,0xcf510510145140,0x488488333514028,0x844333488861012,0x33384484428a005,90657122719368468,0x281c3c142300861,0xc3c281281c0028a,5912485265682627,0x2afc001500c30c,0xfc002a02a030c30]

def zeros : Array Nat := #[0x5df5dff305d75ff,0xaeff305dfb6db7f,0xf30aefaefebaebf,0xb77b77cccaebfd7,0x7bbcccb7779efed,0xccc7bb7bbd75ffa,0xebdebd3c3f3faeb,0xd7e3c3ebdcff79e,0x3c3d7ed7e3ffd75,0xfeafea03fffcf3c,0xfd503ffeaff3cf3,0x3ffd5fd5fcf3cf]

def labelMasks : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,0xc0000000000,52776558133248,0xc00000000000,844424930131968,0xc000000000000,0x30000000000000,0xc0000000000000,0x300000000000000,0xc00000000000000]

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

def neighborData : Array Nat := #[199070,207135,203418,211672,223579,227801,52219084800,56447205376,53358886912,57669582848,60757901312,61897703424,0x32a22000000000,0x349a3000000000,0x33b9c000000000,0x35bda000000000,0x3a9dd000000000,0x3ba5b000000000,0xdac880000000000000,0xe2a8c0000000000000,0xdee800000000000000,0xe6f780000000000000,0xeab840000000000000,0xeed7c0000000000000,2359299,2883589,0xf000000002,1168231104516,962074771456,1099514249216,0x540000000000000,0x5c0000000000001,0x500000000180000,0x5800000001c0000,0x48000c000000000,0x4c000d000000000,117440576,167772416,57174604644352,70368744177984,52776658796544,74766975238144,0x13000000000000080,0x160000000000000c0,0x12000000008000000,0x17000000009000000,0x14000380000000000,0x150003c0000000000,6442450944,8589942784,0xc000000001000,0xe000000003000,0xd0001c0000000,0xf000240000000,0x480000000000004000,0x500000000000005000,0x4c0000000280000000,0x5400000002c0000000,0x580010000000000000,0x5c0011000000000000]

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
      have one : 1 ≤ (rights g e).card := Nat.succ_le_of_lt pos
      simpa only [if_neg h,Nat.add_zero] using one
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
  have leftEq : (∑ i : Fin n, if LeftRaw g i then 1 else 0) = (posFrom g 0).card := by
    symm
    rw [posFrom,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.zero_le,true_and]
  have split : (∑ i : Fin n, ((if LeftRaw g i then 1 else 0) + (if RightRaw g i then 1 else 0))) =
      (∑ i : Fin n, if LeftRaw g i then 1 else 0) + (∑ i : Fin n, if RightRaw g i then 1 else 0) :=
    Finset.sum_add_distrib
  exact split.trans (congrArg₂ Nat.add leftEq rightsEq.symm)

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
namespace PCX150
open PEqualNP.ProofComplexity
theorem tautMono {C D : Cl} (sub : C ⊆ D) : Taut C → Taut D := by
  rintro ⟨v,a,b⟩
  exact ⟨v,sub a,sub b⟩

theorem thinLeft {C D : Cl} {v : V} (t : Taut C)
    (clean : ¬ Taut (C.erase (v,true) ∪ D.erase (v,false))) :
    D ⊆ C.erase (v,true) ∪ D.erase (v,false) := by
  obtain ⟨w,yes,no⟩ := t
  have same : w = v := by
    by_contra neq
    exact clean ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp [neq],yes⟩),
      Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,no⟩)⟩
  subst w
  intro l hl
  by_cases eq : l = (v,false)
  · subst l
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,no⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨eq,hl⟩)

theorem thinRight {C D : Cl} {v : V} (t : Taut D)
    (clean : ¬ Taut (C.erase (v,true) ∪ D.erase (v,false))) :
    C ⊆ C.erase (v,true) ∪ D.erase (v,false) := by
  obtain ⟨w,yes,no⟩ := t
  have same : w = v := by
    by_contra neq
    exact clean ⟨w,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp,yes⟩),
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp [neq],no⟩)⟩
  subst w
  intro l hl
  by_cases eq : l = (v,true)
  · subst l
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp,yes⟩)
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hl⟩)

def Tracks (src dst : List Cl) : Prop :=
  ∀ C ∈ src, ¬ Taut C → ∃ D ∈ dst, D ⊆ C

theorem oldTrack {π τ : List Cl} (track : Tracks π τ) (R : Cl)
    (head : ¬Taut R → ∃ D ∈ τ, D ⊆ R) : Tracks (R::π) τ := by
  intro C hC clean
  rcases List.mem_cons.mp hC with rfl | hC
  · exact head clean
  · exact track C hC clean

theorem newTrack {π τ : List Cl} (track : Tracks π τ) {R S : Cl}
    (sub : S ⊆ R) : Tracks (R::π) (S::τ) := by
  intro C hC clean
  rcases List.mem_cons.mp hC with rfl | hC
  · exact ⟨S,by simp,sub⟩
  · obtain ⟨D,m,sm⟩ := track C hC clean
    exact ⟨D,List.mem_cons_of_mem _ m,sm⟩

theorem cleanDerivation {F : Set Cl} {π : List Cl} (hπ : IsDerivation F π) :
    ∃ τ : List Cl, IsDerivation F τ ∧ τ.length ≤ π.length ∧
      (∀ C ∈ τ, ¬ Taut C) ∧ Tracks π τ := by
  classical
  induction hπ with
  | nil =>
    exact ⟨[],.nil,by simp,by simp,by intro C h; simp at h⟩
  | @ax π C _ ax ih =>
    obtain ⟨τ,der,size,pure,track⟩ := ih
    by_cases bad : Taut C
    · exact ⟨τ,der,by simp only [List.length_cons]; omega,pure,oldTrack track C (fun nc => False.elim (nc bad))⟩
    · refine ⟨C::τ,.ax der ax,by simpa using size,?_,newTrack track (Finset.Subset.rfl)⟩
      intro D m
      rcases List.mem_cons.mp m with rfl | m
      · exact bad
      · exact pure D m
  | @res π C D R _ mC mD step ih =>
    obtain ⟨τ,der,size,pure,track⟩ := ih
    have skip (q : ¬Taut R → ∃ S ∈ τ, S ⊆ R) :
        ∃ τ' : List Cl, IsDerivation F τ' ∧ τ'.length ≤ (R::π).length ∧
        (∀ E ∈ τ', ¬ Taut E) ∧ Tracks (R::π) τ' :=
      ⟨τ,der,by simp only [List.length_cons]; omega,pure,oldTrack track R q⟩
    by_cases bad : Taut R
    · exact skip (fun nc => False.elim (nc bad))
    obtain ⟨v,hp,hn,hr⟩ := step
    by_cases tc : Taut C
    · have sub : D ⊆ R := by rw [hr]; exact thinLeft tc (hr ▸ bad)
      obtain ⟨S,m,s⟩ := track D mD (fun b => bad (tautMono sub b))
      exact skip (fun _ => ⟨S,m,fun _ h => sub (s h)⟩)
    by_cases td : Taut D
    · have sub : C ⊆ R := by rw [hr]; exact thinRight td (hr ▸ bad)
      obtain ⟨S,m,s⟩ := track C mC (fun b => bad (tautMono sub b))
      exact skip (fun _ => ⟨S,m,fun _ h => sub (s h)⟩)
    obtain ⟨A,mA,sa⟩ := track C mC tc
    obtain ⟨B,mB,sb⟩ := track D mD td
    by_cases pa : (v,true) ∈ A
    · by_cases pb : (v,false) ∈ B
      · let S := A.erase (v,true) ∪ B.erase (v,false)
        have sub : S ⊆ R := by
          rw [hr]
          apply Finset.union_subset_union
          · exact Finset.erase_subset_erase _ sa
          · exact Finset.erase_subset_erase _ sb
        have res : IsResolvent A B S := ⟨v,pa,pb,rfl⟩
        refine ⟨S::τ,.res der mA mB res,by simpa using size,?_,newTrack track sub⟩
        intro E m
        rcases List.mem_cons.mp m with rfl | m
        · exact fun te => bad (tautMono sub te)
        · exact pure E m
      · apply skip
        intro _
        refine ⟨B,mB,?_⟩
        rw [hr]
        intro l hl
        exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun eq => pb (eq ▸ hl),sb hl⟩)
    · apply skip
      intro _
      refine ⟨A,mA,?_⟩
      rw [hr]
      intro l hl
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun eq => pa (eq ▸ hl),sa hl⟩)

theorem cleanRefutation {F : Set Cl} {π : List Cl} (h : IsRefutation F π) :
    ∃ τ : List Cl, IsRefutation F τ ∧ τ.length ≤ π.length ∧ ∀ C ∈ τ, ¬ Taut C := by
  obtain ⟨τ,der,sz,pure,track⟩ := cleanDerivation h.1
  have ok : ¬Taut (∅ : Cl) := by simp [Taut]
  obtain ⟨D,m,sub⟩ := track ∅ h.2 ok
  have eq : D = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by intro x hx; exact Finset.notMem_empty x (sub hx))
  exact ⟨τ,⟨der,eq ▸ m⟩,sz,pure⟩

end PCX150
namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}
/-- One physical rule contributes separately for each of its two argument positions. -/
def contribution (g : Links C) (i v : Fin n) : Nat :=
  match g.parent i with
  | none => 0
  | some (j,k) => (if v=j then 1 else 0)+(if v=k then 1 else 0)

def incoming (g : Links C) (v : Fin n) : Nat := ∑ i : Fin n, g.contribution i v

noncomputable def derived (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i ≠ none)

noncomputable def raws (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i = none)

theorem rawAndDerived (g : Links C) : g.raws.card + g.derived.card = n := by
  classical
  simpa [raws,derived] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun i => g.parent i = none) (fun _ => (1 : Nat)))

theorem chargeRow (g : Links C) (i : Fin n) :
    ∑ v : Fin n, g.contribution i v = if g.parent i = none then 0 else 2 := by
  cases h : g.parent i with
  | none => simp [contribution,h]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp [contribution,h,Finset.sum_add_distrib]

theorem totalIncoming (g : Links C) : ∑ v : Fin n, g.incoming v = 2*g.derived.card := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ v : Fin n, g.contribution i v := Finset.sum_comm
    _ = ∑ i : Fin n, if g.parent i = none then 0 else 2 :=
      Finset.sum_congr rfl (fun i _ => g.chargeRow i)
    _ = ∑ _i ∈ g.derived, 2 := by
      rw [derived,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : g.parent i = none <;> simp [h]
    _ = _ := by simp [Nat.mul_comm]

theorem rawIncoming (g : Links C) : ∑ v ∈ g.raws, g.incoming v = rawSlots g := by
  classical
  change (∑ v ∈ g.raws, ∑ i : Fin n, g.contribution i v) = _
  rw [Finset.sum_comm]
  unfold rawSlots
  apply Finset.sum_congr rfl
  intro i _
  cases h : g.parent i with
  | none => simp [contribution,h,LeftRaw,RightRaw]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp [contribution,h,LeftRaw,RightRaw,raws,Finset.sum_add_distrib]

theorem derivedIncoming (g : Links C) :
    rawSlots g + ∑ v ∈ g.derived, g.incoming v = 2*g.derived.card := by
  classical
  rw [←g.rawIncoming, ←g.totalIncoming]
  simpa only [raws,derived] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun v => g.parent v = none) g.incoming)

theorem manyRaws (g : Links C) (f : Fin 22 → Fin n) (inj : Function.Injective f)
    (raw : ∀ b, g.parent (f b) = none) : 22 ≤ g.raws.card := by
  classical
  have sub : Finset.univ.image f ⊆ g.raws := by
    intro i hi
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hi
    simpa [raws] using raw b
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

end PCX150.Links
namespace PCX150
/-- The root has no reader. All other retained resolution lines have one or more. -/
structure ReadBudget where
  axioms : Nat
  derived : Nat
  axiomReads : Nat
  otherReads : List Nat
  linesBound : axioms + derived ≤ 51
  axiomCount : 22 ≤ axioms
  minRaw : 27 ≤ axiomReads
  slots : axiomReads + otherReads.sum = 2 * derived
  count : otherReads.length + 1 = derived
  live : ∀ r ∈ otherReads, 0 < r

private theorem sumWithoutFirst (rs : List Nat) (live : ∀ r ∈ rs, 0 < r) :
    (rs.map Nat.pred).sum + rs.length = rs.sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := live r (by simp)
    have predStep : r.pred + 1 = r := by cases r <;> simp_all
    have tail := ih (fun x hx => live x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem ReadBudget.surplus (b : ReadBudget) :
    b.derived ≤ 29 ∧ (b.otherReads.map Nat.pred).sum ≤ 3 := by
  have hsum := sumWithoutFirst b.otherReads b.live
  have hslots := b.slots
  have hraw := b.minRaw
  have hlen := b.count
  have hl := b.linesBound
  have ha := b.axiomCount
  omega

private def sharedCounts (reads : List Nat) : List Nat := reads.filter (fun n => decide (2 ≤ n))

private theorem sharedCharge (rs : List Nat) :
    (sharedCounts rs).length ≤ (rs.map Nat.pred).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : 2 ≤ r
    · simp [sharedCounts, h] at ih ⊢
      omega
    · simp [sharedCounts, h] at ih ⊢
      omega

private theorem allDouble_of_tight (rs : List Nat)
    (tight : (rs.map Nat.pred).sum = (sharedCounts rs).length) :
    ∀ n ∈ sharedCounts rs, n = 2 := by
  induction rs with
  | nil => simp [sharedCounts]
  | cons r rs ih =>
    have bound := sharedCharge rs
    by_cases h : 2 ≤ r
    · have predStep : r.pred + 1 = r := by cases r <;> simp_all
      have cons : sharedCounts (r :: rs) = r :: sharedCounts rs := by simp [sharedCounts,h]
      rw [cons] at tight ⊢
      simp only [List.map_cons,List.sum_cons,List.length_cons] at tight
      have rt : r = 2 := by omega
      have tail : (rs.map Nat.pred).sum = (sharedCounts rs).length := by omega
      intro n hn
      rcases List.mem_cons.mp hn with eq | mem
      · exact eq.trans rt
      · exact ih tail n mem
    · have cons : sharedCounts (r :: rs) = sharedCounts rs := by simp [sharedCounts,h]
      rw [cons] at tight ⊢
      simp only [List.map_cons,List.sum_cons] at tight
      apply ih
      omega

theorem ReadBudget.shared_cases (b : ReadBudget) :
    (sharedCounts b.otherReads).length ≤ 2 ∨
      ((sharedCounts b.otherReads).length = 3 ∧
       ∀ r ∈ sharedCounts b.otherReads, r = 2) := by
  have bound := b.surplus.2
  have charge := sharedCharge b.otherReads
  by_cases small : (sharedCounts b.otherReads).length ≤ 2
  · exact Or.inl small
  · exact Or.inr ⟨by omega, allDouble_of_tight _ (by omega)⟩

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
namespace Links
variable {n : Nat} {C : Fin n → Cl}
def inputs (g : Links C) (i : Fin n) : List (Fin n) :=
  match g.parent i with
  | some (j,k) => [j,k]
  | none => []

inductive Used (g : Links C) (root : Fin n) : Fin n → Prop where
  | rootLine : Used g root root
  | input {i j} : Used g root i → j ∈ g.inputs i → Used g root j

theorem later (g : Links C) {i j} (mem : j ∈ g.inputs i) : i.val < j.val := by
  cases h : g.parent i with
  | none => simp [inputs,h] at mem
  | some pair =>
    obtain ⟨u,v⟩ := pair
    have edge := g.rule _ _ _ h
    simp only [inputs,h,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl
    · exact edge.1
    · exact edge.2.1

theorem rootFirst (g : Links C) {root i} (hi : Used g root i) : root.val ≤ i.val := by
  induction hi with
  | rootLine => rfl
  | input _ mem ih => exact Nat.le_trans ih (Nat.le_of_lt (g.later mem))

noncomputable def fill (g : Links C) (root : Fin n) (raw : Cl) (i : Fin n) : Cl := by
  classical
  exact if Used g root i then C i else raw

noncomputable def retain (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3) :
    Links (g.fill root raw) := by
  classical
  refine ⟨fun i => if Used g root i then g.parent i else none,?_,?_⟩
  · intro i h
    by_cases alive : Used g root i
    · simpa [fill,alive] using g.ax i (by simpa [alive] using h)
    · simpa [fill,alive] using ax
  · intro i j k h
    split at h
    next alive =>
      have e := g.rule i j k h
      have a : Used g root j := .input alive (by simp [inputs,h])
      have b : Used g root k := .input alive (by simp [inputs,h])
      simpa [fill,alive,a,b] using e
    next => contradiction

theorem retainParent (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3) (i : Fin n) :
    (g.retain root raw ax).parent i = open Classical in
      if Used g root i then g.parent i else none := by rfl

theorem rootUnseen (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3)
    (i : Fin n) : root ∉ (g.retain root raw ax).inputs i := by
  classical
  intro mem
  by_cases alive : Used g root i
  · have h := (g.retain root raw ax).later mem
    have first := g.rootFirst alive
    omega
  · simpa [inputs,retainParent,alive] using mem

theorem nonrootRead (g : Links C) (root : Fin n) (raw : Cl) (ax : raw ∈ PHP 4 3)
    {i : Fin n} (derived : (g.retain root raw ax).parent i ≠ none) (ne : i ≠ root) :
    ∃ u, i ∈ (g.retain root raw ax).inputs u := by
  classical
  have alive : Used g root i := by
    by_contra bad
    simp [retainParent,bad] at derived
  cases alive with
  | rootLine => contradiction
  | @input u j used mem =>
    exact ⟨u,by simpa [inputs,retainParent,used] using mem⟩

end Links
end PCX150
namespace PCX150.Links
variable {n : Nat} {C : Fin n → Cl}
/-- Convert finite physical indegrees to the non-root rows of the read budget. -/
noncomputable def readList (g : Links C) (r : Fin n) : List Nat :=
  (g.derived.erase r).toList.map g.incoming

theorem physicalBudget (g : Links C) (r : Fin n) (derivedRoot : g.parent r ≠ none)
    (unread : g.incoming r = 0) (live : ∀ i, g.parent i ≠ none → i ≠ r → 0 < g.incoming i)
    (small : n ≤ 51) (many : 22 ≤ g.raws.card) (slots : 27 ≤ rawSlots g) :
    ∃ b : ReadBudget, b.derived = g.derived.card ∧ b.otherReads = g.readList r := by
  classical
  have rootMember : r ∈ g.derived := by simpa [derived] using derivedRoot
  have sizes := g.rawAndDerived
  have erase := Finset.sum_erase_add g.derived g.incoming rootMember
  have others : (g.readList r).sum = ∑ i ∈ g.derived.erase r, g.incoming i := by
    simp [readList]
  refine ⟨⟨g.raws.card,g.derived.card,rawSlots g,g.readList r,by omega,many,slots,?_,?_,?_⟩,rfl,rfl⟩
  · rw [others]
    have total := g.derivedIncoming
    omega
  · simp only [readList,List.length_map,Finset.length_toList]
    exact Finset.card_erase_add_one rootMember
  · intro k hk
    obtain ⟨v,mem,rfl⟩ := List.mem_map.mp hk
    have hv : v ∈ g.derived.erase r := by simpa using mem
    obtain ⟨ne,yes⟩ := Finset.mem_erase.mp hv
    exact live v (by simpa [derived] using yes) ne

theorem chargePositive (g : Links C) {i v : Fin n} :
    0 < g.contribution i v ↔ v ∈ g.inputs i := by
  cases h : g.parent i with
  | none => simp [contribution,inputs,h]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    by_cases a : v=j <;> by_cases b : v=k <;> simp [contribution,inputs,h,a,b]

theorem incomingPositive (g : Links C) (v : Fin n) :
    0 < g.incoming v ↔ ∃ i, v ∈ g.inputs i := by
  classical
  constructor
  · intro h
    by_contra! none
    have zero : ∀ i, g.contribution i v = 0 := fun i =>
      Nat.eq_zero_of_not_pos (by rw [g.chargePositive]; exact none i)
    simp [incoming,zero] at h
  · rintro ⟨i,hi⟩
    have pos := g.chargePositive.mpr hi
    have le : g.contribution i v ≤ g.incoming v :=
      Finset.single_le_sum (f := fun u => g.contribution u v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

end PCX150.Links
namespace PCX150
open PEqualNP.ProofComplexity
theorem oldestEmpty {n : Nat} (f : Fin n → Cl) (has : ∃ r, f r = ∅) :
    ∃ r, f r = ∅ ∧ ∀ i, r.val < i.val → (f i).Nonempty := by
  classical
  let empties : Finset (Fin n) := Finset.univ.filter (fun i => f i = ∅)
  have member (i : Fin n) : i ∈ empties ↔ f i = ∅ := by simp [empties]
  obtain ⟨j,hj⟩ := has
  have nonempty : empties.Nonempty := ⟨j,(member j).2 hj⟩
  let r := empties.max' nonempty
  refine ⟨r,(member r).1 (Finset.max'_mem _ _),?_⟩
  intro i later
  apply Finset.nonempty_iff_ne_empty.mpr
  intro empty
  have hi : i ≤ r := Finset.le_max' empties i ((member i).2 empty)
  exact (Nat.not_le_of_lt later) hi

theorem fillRoot {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl) :
    g.fill r raw r = C r := by
  classical
  simp [Links.fill,Links.Used.rootLine]

theorem fillEarlier {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl)
    (positive : raw.Nonempty) (older : ∀ i, r.val < i.val → (C i).Nonempty) :
    ∀ i, r.val < i.val → (g.fill r raw i).Nonempty := by
  classical
  intro i lt
  by_cases live : g.Used r i
  · simpa [Links.fill,live] using older i lt
  · simpa [Links.fill,live] using positive

theorem fillClean {n : Nat} {C : Fin n → Cl} (g : Links C) (r : Fin n) (raw : Cl)
    (ok : ¬Taut raw) (clean : ∀ i, ¬Taut (C i)) : ∀ i, ¬Taut (g.fill r raw i) := by
  classical
  intro i
  by_cases live : g.Used r i
  · simpa [Links.fill,live] using clean i
  · simpa [Links.fill,live] using ok

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
def placeholder : Cl := Finset.univ.image (fun j : Fin 3 => (((0 : Fin 4),j),true))

theorem placeholderFacts :
    placeholder ∈ PHP 4 3 ∧ placeholder.Nonempty ∧ ¬Taut placeholder := by
  refine ⟨Or.inl ⟨0,rfl⟩,?_,?_⟩
  · exact ⟨((0,0),true),Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  · rintro ⟨v,_,neg⟩
    simp [placeholder] at neg

theorem rawNonempty (c : Cl) (h : c ∈ PHP 4 3) : c.Nonempty := by
  rcases h with ⟨i,rfl⟩ | ⟨i,j,k,_,rfl⟩
  · exact ⟨((i,0),true),Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  · exact ⟨_,Finset.mem_insert_self _ _⟩

structure Prepared {n : Nat} (D : Fin n → Cl) (g : Links D) (r : Fin n) : Prop where
  emptyRoot : D r = ∅
  olderNonempty : ∀ i, r.val < i.val → (D i).Nonempty
  rootDerived : g.parent r ≠ none
  rootUnread : g.incoming r = 0
  othersRead : ∀ i, g.parent i ≠ none → i ≠ r → 0 < g.incoming i
  budget : ∃ b : ReadBudget, b.derived = g.derived.card ∧ b.otherReads = g.readList r

theorem prepareGraph {n} {C : Fin n → Cl} (g : Links C) (existsEmpty : ∃ r, C r = ∅)
    (clean : ∀ i, ¬Taut (C i)) (len : n ≤ 51)
    (many : ∀ {D : Fin n → Cl} (h : Links D) r, D r = ∅ → 22 ≤ h.raws.card)
    (pay : ∀ {D : Fin n → Cl} (h : Links D) r, D r = ∅ → (∀ i, ¬Taut (D i)) →
      27 ≤ rawSlots h) : ∃ (D : Fin n → Cl) (dg : Links D) (r : Fin n), Prepared D dg r := by
  classical
  obtain ⟨r,emp,earlier⟩ := oldestEmpty C existsEmpty
  obtain ⟨ax,nonempty,ok⟩ := placeholderFacts
  let D := g.fill r placeholder
  let dg := g.retain r placeholder ax
  have er : D r = ∅ := (fillRoot g r placeholder).trans emp
  have rd : dg.parent r ≠ none := by
    intro raw
    have no := rawNonempty (D r) (dg.ax r raw)
    simpa [er] using no
  have ur : dg.incoming r = 0 := by
    apply Nat.eq_zero_of_not_pos
    rintro pos
    obtain ⟨i,hi⟩ := (dg.incomingPositive r).mp pos
    exact g.rootUnseen r placeholder ax i hi
  have reads (i) (derived : dg.parent i ≠ none) (ne : i ≠ r) : 0 < dg.incoming i :=
    (dg.incomingPositive i).mpr (g.nonrootRead r placeholder ax derived ne)
  refine ⟨D,dg,r,er,fillEarlier g r placeholder nonempty earlier,rd,ur,reads,?_⟩
  exact dg.physicalBudget r rd ur reads len (many dg r er)
    (pay dg r er (fillClean g r placeholder ok clean))

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
theorem physicalContract
    (hard : ∀ xs : List (Fin 48), xs.length ≤ 8 → ¬∀ q : PP, isMarked (runMoves xs 0) q)
    (deny : ∀ {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}, Prepared D g r → False) :
    ¬ (∃ π : List (Clause (Fin 4 × Fin 3)), IsRefutation (PHP 4 3) π ∧ π.length ≤ 51) := by
  rintro ⟨π,ref,small⟩
  obtain ⟨rows,proof,size,pure⟩ := cleanRefutation ref
  obtain ⟨root,read,⟨reas⟩⟩ := indexedRefutation proof
  let C := fun i : Fin rows.length => rows[i.val]
  let g := asLinks reas
  obtain ⟨hr,er⟩ := List.getElem?_eq_some_iff.mp read
  have existsEmpty : ∃ i, C i = ∅ := ⟨⟨root,hr⟩,er⟩
  have clean (i : Fin rows.length) : ¬Taut (C i) := pure _ (List.getElem_mem _)
  have many {D : Fin rows.length → Cl} (dg : Links D) (r : Fin rows.length) (emp : D r = ∅) :
      22 ≤ dg.raws.card := by
    obtain ⟨f,inj,props⟩ := distinctSources dg r emp
    exact dg.manyRaws f inj (fun i => (props i).1)
  have pay {D : Fin rows.length → Cl} (dg : Links D) (r) (emp : D r = ∅) (cleanD : ∀ i, ¬Taut (D i)) :
      27 ≤ rawSlots dg := by
    rw [slots_eq]
    exact rawLowerFromGame hard dg r emp cleanD
  obtain ⟨D,dg,r,prep⟩ := prepareGraph g existsEmpty clean (by omega) many pay
  exact deny prep

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)

end PCX150
namespace PCX150
private theorem filterMapLength {α} (xs : List α) (f : α → Nat) :
    (xs.filter (fun i => decide (2 ≤ f i))).length =
    ((xs.map f).filter (fun k => decide (2 ≤ k))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : 2 ≤ f a <;> simp [h,ih]

/-- Order the shared vertices from earliest to latest in the derivation. -/

def orderedCuts {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) : List (Fin n) :=
  (ds.filter (fun i => 2 ≤ f i)).sort (· ≥ ·)

theorem cutLength {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).length = ((ds.toList.map f).filter (fun k => decide (2 ≤ k))).length := by
  rw [←filterMapLength]
  let xs := ds.toList.filter (fun i => decide (2 ≤ f i))
  have unique : xs.Nodup := ds.nodup_toList.filter _
  have setEq : xs.toFinset = ds.filter (fun i => 2 ≤ f i) := by ext i; simp [xs]
  have card : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup unique
  simpa [orderedCuts,←setEq] using card

theorem cutMembers {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) (v : Fin n) :
    v ∈ orderedCuts ds f ↔ v ∈ ds ∧ 2 ≤ f v := by simp [orderedCuts]

theorem cutNodup {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).Nodup := by simp [orderedCuts]

theorem cutOrdered {n : Nat} (ds : Finset (Fin n)) (f : Fin n → Nat) :
    (orderedCuts ds f).Pairwise (fun i j => j.val < i.val) := by
  have order : (orderedCuts ds f).Pairwise (· ≥ ·) := by
    unfold orderedCuts
    exact?
  have unique := cutNodup ds f
  generalize he : orderedCuts ds f = xs at order unique ⊢
  clear he
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    obtain ⟨front,tail⟩ := List.pairwise_cons.mp order
    obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp unique
    apply List.pairwise_cons.mpr
    refine ⟨?_,?_⟩
    · intro y hy
      have ne : y ≠ x := by intro eq; subst y; exact fresh hy
      exact lt_of_le_of_ne (front y hy) (fun eq => ne (Fin.ext eq))
    · exact ih tail uniq

end PCX150
namespace PCX150
variable {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}
noncomputable def sharedIndices (g : Links D) (r : Fin n) :=
  orderedCuts (g.derived.erase r) g.incoming

theorem isShared (v : Fin n) :
    v ∈ sharedIndices g r ↔ v ≠ r ∧ g.parent v ≠ none ∧ 2 ≤ g.incoming v := by
  simp [sharedIndices,cutMembers,Links.derived,and_assoc]

theorem cutSplit (pr : Prepared D g r) :
    g.derived.card ≤ 29 ∧ ((sharedIndices g r).length ≤ 2 ∨
      ((sharedIndices g r).length = 3 ∧ ∀ v ∈ sharedIndices g r, g.incoming v = 2)) := by
  obtain ⟨b,bd,br⟩ := pr.budget
  have eq : (sharedCounts b.otherReads).length = (sharedIndices g r).length := by
    rw [br]
    exact (cutLength _ _).symm
  refine ⟨bd ▸ b.surplus.1,?_⟩
  rcases b.shared_cases with small | ⟨large,doubles⟩
  · exact Or.inl (eq ▸ small)
  · refine Or.inr ⟨eq ▸ large,?_⟩
    intro v mem
    obtain ⟨ne,hd,many⟩ := (isShared _).mp mem
    apply doubles
    rw [br]
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨v,?_,rfl⟩,by simpa using many⟩
    simpa [Links.derived,ne] using hd

theorem offCut (pr : Prepared D g r) (v : Fin n) (hd : g.parent v ≠ none)
    (nr : v ≠ r) (unshared : v ∉ sharedIndices g r) : g.incoming v = 1 := by
  have pos := pr.othersRead v hd nr
  have small : ¬2 ≤ g.incoming v := fun h => unshared ((isShared _).mpr ⟨nr,hd,h⟩)
  omega

end PCX150
namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}
def natParent (g : Links C) (k : Nat) : Option (Nat × Nat) :=
  if h : k < n then (g.parent ⟨k,h⟩).map (fun p => (p.1.val,p.2.val)) else none

def natClause (C : Fin n → Cl) (outside : Cl) (k : Nat) : Cl :=
  if h : k < n then C ⟨k,h⟩ else outside

theorem natEdge (g : Links C) (outside : Cl) {i j k : Nat}
    (edge : g.natParent i = some (j,k)) :
    i < j ∧ i < k ∧ j < n ∧ k < n ∧
      IsResolvent (natClause C outside j) (natClause C outside k) (natClause C outside i) := by
  unfold natParent at edge
  split at edge
  next hi =>
    cases e : g.parent ⟨i,hi⟩ with
    | none => simp [e] at edge
    | some pair =>
      obtain ⟨u,v⟩ := pair
      obtain ⟨rfl,rfl⟩ : u.val=j ∧ v.val=k := by simpa [e] using edge
      obtain ⟨a,b,r⟩ := g.rule _ _ _ e
      exact ⟨a,b,u.isLt,v.isLt,by simpa [natClause,u.isLt,v.isLt,hi] using r⟩
  next => contradiction

theorem natAx (g : Links C) (outside : Cl) (ok : outside ∈ PHP 4 3)
    {i} (leaf : g.natParent i = none) : natClause C outside i ∈ PHP 4 3 := by
  by_cases hi : i < n
  · have hp : g.parent ⟨i,hi⟩ = none := by simpa [natParent,hi] using leaf
    simpa [natClause,hi] using g.ax ⟨i,hi⟩ hp
  · simpa [natClause,hi] using ok

theorem natDerived (g : Links C) (i : Fin n) :
    g.natParent i.val ≠ none ↔ g.parent i ≠ none := by simp [natParent,i.isLt]

theorem natRoots (g : Links C) (v : Nat) :
    g.natParent v ≠ none ↔ ∃ i : Fin n, i.val = v ∧ g.parent i ≠ none := by
  constructor
  · intro h
    by_cases hv : v < n
    · exact ⟨⟨v,hv⟩,rfl,(g.natDerived ⟨v,hv⟩).1 h⟩
    · simp [natParent,hv] at h
  · rintro ⟨i,rfl,h⟩
    exact (g.natDerived i).2 h

end PCX150.Links
namespace PCX150
open PEqualNP.ProofComplexity
/-- A leaf records a physical source, so two copies of an equal clause can use different labels. -/
inductive LabeledTree (clause : Nat → Cl) : Cl → Type where
  | leaf (id : Nat) : LabeledTree clause (clause id)
  | resolve {C D R : Cl} (left : LabeledTree clause C) (right : LabeledTree clause D)
      (rule : IsResolvent C D R) : LabeledTree clause R

namespace LabeledTree
def cost {f R} : LabeledTree f R → Nat
  | .leaf _ => 0
  | .resolve l r _ => l.cost + r.cost + 1

def leaves {f R} : LabeledTree f R → List Nat
  | .leaf i => [i]
  | .resolve l r _ => l.leaves ++ r.leaves

theorem leafCount {f R} (t : LabeledTree f R) : t.leaves.length = t.cost+1 := by
  induction t with
  | leaf _ => rfl
  | resolve _ _ _ ih jh =>
    simp only [leaves,List.length_append,cost]
    omega

theorem toResTree {f R} (t : LabeledTree f R) {F : Set Cl}
    (available : ∀ i ∈ t.leaves, f i ∈ F) : ResTree F R t.cost := by
  induction t with
  | leaf i => exact .ax (available i (by simp [leaves]))
  | resolve l r rule ih jh =>
    exact .res (ih (fun x hx => available x (by simp [leaves,hx])))
      (jh (fun x hx => available x (by simp [leaves,hx]))) rule

/-- Substitute exactly the designated physical line. Other equal clauses are kept as leaves. -/

def splice {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    LabeledTree f R :=
  match t with
  | .leaf k => if h : i = k then h ▸ proof else .leaf k
  | .resolve l r rule => .resolve (l.splice i proof) (r.splice i proof) rule

theorem spliceCost {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    (t.splice i proof).cost = t.cost + t.leaves.count i * proof.cost := by
  induction t with
  | leaf k =>
    by_cases eq : i = k
    · subst k
      simp [splice,cost,leaves]
    · simp [splice,cost,leaves,eq,Ne.symm eq]
  | resolve l r rule ih jh =>
    simp only [splice,cost,leaves,List.count_append,ih,jh,Nat.add_mul]
    omega

theorem spliceLeaves {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    ∀ k ∈ (t.splice i proof).leaves,
      (k ≠ i ∧ k ∈ t.leaves) ∨ k ∈ proof.leaves := by
  induction t with
  | leaf j =>
    by_cases h : i = j
    · subst j
      intro k hk
      exact Or.inr (by simpa [splice] using hk)
    · simp [splice,leaves,h,Ne.symm h]
  | resolve l r _ ih jh =>
    simp only [splice,leaves,List.mem_append]
    intro k hk
    rcases hk with left | right
    · rcases ih k left with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inl mem⟩
      · exact Or.inr mem
    · rcases jh k right with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inr mem⟩
      · exact Or.inr mem

end LabeledTree
end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
def portList (pair : Option (Nat × Nat)) : List Nat :=
  match pair with
  | none => []
  | some (j,k) => [j,k]

inductive Fragment (f : Nat → Cl) (parent : Nat → Option (Nat × Nat))
    (boundary : Nat → Bool) : Nat → Bool → Type where
  | leaf (i : Nat) (force : Bool) (reason : parent i = none ∨ force = false ∧ boundary i = true) :
      Fragment f parent boundary i force
  | node (i j k : Nat) (force : Bool) (openAt : force = true ∨ boundary i = false)
      (edge : parent i = some (j,k)) (step : IsResolvent (f j) (f k) (f i))
      (left : Fragment f parent boundary j false) (right : Fragment f parent boundary k false) :
      Fragment f parent boundary i force

namespace Fragment
def expanded {f p b i t} : Fragment f p b i t → List Nat
  | .leaf _ _ _ => []
  | .node u _ _ _ _ _ _ l r => u :: l.expanded ++ r.expanded

def tree {f p b i t} : Fragment f p b i t → LabeledTree f (f i)
  | .leaf u _ _ => .leaf u
  | .node _ _ _ _ _ _ rule l r => .resolve l.tree r.tree rule

theorem costCount {f p b i t} (g : Fragment f p b i t) : g.tree.cost = g.expanded.length := by
  induction g with
  | leaf => rfl
  | node _ _ _ _ _ _ _ _ _ ih jh =>
    simp only [tree,LabeledTree.cost,expanded,List.length_append,List.length_cons,ih,jh]
    omega

/-- Every occurrence other than the root came through exactly one parent slot.
    A physical line may appear more than once in either list. -/

theorem occurrenceBalance {f p b i t} (g : Fragment f p b i t) (v : Nat) :
    g.expanded.count v + g.tree.leaves.count v =
      [i].count v + (g.expanded.flatMap (fun u => portList (p u))).count v := by
  induction g with
  | leaf => simp [expanded,tree,LabeledTree.leaves]
  | node i j k force op edge rule l r ih jh =>
    simp only [tree,LabeledTree.leaves,expanded,List.count_append,List.flatMap_append,
      List.flatMap_cons,edge,portList,List.count_cons,List.count_nil,Nat.zero_add,
      List.cons_append] at ih jh ⊢
    omega

end Fragment
theorem canExpand {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      IsResolvent (f j) (f k) (f i)) (b : Nat → Bool) (i : Nat) (force : Bool) :
    Nonempty (Fragment f p b i force) := by
  have aux (m : Nat) : ∀ i, bound-i = m → ∀ t, Nonempty (Fragment f p b i t) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro u eq t
      by_cases cut : t = false ∧ b u = true
      · exact ⟨.leaf u t (Or.inr cut)⟩
      · cases hp : p u with
        | none => exact ⟨.leaf u t (Or.inl hp)⟩
        | some pair =>
          obtain ⟨j,k⟩ := pair
          obtain ⟨hj,hk,bj,bk,step⟩ := rules u j k hp
          obtain ⟨l⟩ := ih (bound-j) (by omega) j rfl false
          obtain ⟨r⟩ := ih (bound-k) (by omega) k rfl false
          have op : t = true ∨ b u = false := by cases t <;> cases hb : b u <;> simp_all
          exact ⟨.node u j k t op hp step l r⟩
  exact aux _ i rfl force

end PCX150
namespace PCX150.Fragment
theorem leafReason {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.tree.leaves, p v = none ∨ b v = true := by
  induction g with
  | leaf u force reason =>
    intro v hv
    have hv' : v = u := by simpa [tree,LabeledTree.leaves] using hv
    subst v
    exact reason.imp_right And.right
  | node _ _ _ _ _ _ _ l r ih jh =>
    intro v hv
    rcases List.mem_append.mp hv with a | a
    · exact ih v a
    · exact jh v a

theorem boundaryExpansion {f p b i t} (g : Fragment f p b i t) (v : Nat) (cut : b v = true) :
    g.expanded.count v = if t = true ∧ i = v ∧ p i ≠ none then 1 else 0 := by
  induction g with
  | leaf u force reason =>
    rcases reason with raw | ⟨nf,_⟩
    · simp [expanded,raw]
    · simp [expanded,nf]
  | node u j k force op edge rule l r ih jh =>
    by_cases eq : u = v
    · subst u
      have forced : force = true := op.resolve_right (by simp [cut])
      simp [expanded,ih,jh,forced,edge]
    · simp [expanded,ih,jh,eq,Ne.symm eq]

theorem openedDerived {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.expanded, p v ≠ none := by
  induction g with
  | leaf => simp [expanded]
  | node u j k force op edge rule l r ih jh =>
    intro v hv
    simp only [expanded,List.cons_append,List.mem_cons,List.mem_append] at hv
    rcases hv with rfl | hl | hr
    · simp [edge]
    · exact ih v hl
    · exact jh v hr

end PCX150.Fragment
namespace PCX150
open PEqualNP.ProofComplexity
abbrev Rooted (f : Nat → Cl) (p : Nat → Option (Nat × Nat)) (b : Nat → Bool) :=
  (i : Nat) × Fragment f p b i true

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}
def nodes (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.expanded)

def tips (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.tree.leaves)

def starts (fs : List (Rooted f p b)) := fs.map (fun z => z.1)

theorem balance (fs : List (Rooted f p b)) (v : Nat) :
    (nodes fs).count v + (tips fs).count v =
      (starts fs).count v + ((nodes fs).flatMap (fun k => portList (p k))).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.occurrenceBalance v
    simp only [nodes,tips,starts,List.flatMap_cons,List.map_cons,List.count_append,
      List.flatMap_append,List.count_cons,List.count_nil,Nat.zero_add] at ih h ⊢
    omega

theorem cutRoots (fs : List (Rooted f p b)) (v : Nat) (cut : b v = true)
    (proper : ∀ g ∈ fs, p g.1 ≠ none) : (nodes fs).count v = (starts fs).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.boundaryExpansion v cut
    have d := proper ⟨i,g⟩ (by simp)
    have t := ih (fun z hz => proper z (by simp [hz]))
    by_cases eq : i = v
    · subst i
      simp [nodes,starts,d,List.count_append] at h t ⊢
      omega
    · simp [nodes,starts,d,eq,Ne.symm eq,List.count_append] at h t ⊢
      omega

theorem noncutNotTip (fs : List (Rooted f p b)) {v : Nat} (derived : p v ≠ none)
    (uncut : b v = false) : (tips fs).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hv
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  rcases g.2.leafReason v hg with empty | cut <;> simp_all

theorem physicalDerived (fs : List (Rooted f p b)) {v : Nat} (hv : v ∈ nodes fs) : p v ≠ none := by
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  exact g.2.openedDerived v hg

end Rooted
end PCX150
namespace PCX150
/-- A unique incoming slot is preserved when a list of line indices is replaced by
    its expanded occurrences, provided the unique reader has been expanded once. -/
theorem countParentsSingle (lines : List Nat) (ports : Nat → List Nat) (v u : Nat)
    (sole : ∀ x ∈ lines, (ports x).count v = if x = u then 1 else 0) :
    (lines.flatMap ports).count v = lines.count u := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := sole x (by simp)
    have tail := ih (fun y hy => sole y (by simp [hy]))
    by_cases eq : x = u
    · subst x
      simp_all [List.flatMap_cons,List.count_append,Nat.add_comm]
    · simp [List.flatMap_cons,List.count_append,h,tail,eq,Ne.symm eq]

theorem countParentsZero (lines : List Nat) (ports : Nat → List Nat) (v : Nat)
    (none : ∀ x ∈ lines, v ∉ ports x) : (lines.flatMap ports).count v = 0 := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := none x (by simp)
    have tail := ih (fun y hy => none y (by simp [hy]))
    simp [List.flatMap_cons,List.count_append,tail,List.count_eq_zero.mpr h]

/-- Conservation over the forest of fragments. The roots list has one copy of
    each cut line and the conclusion. A non-cut derived line ends no fragment. -/

theorem oneExpansionPerLine (nodes tips roots : List Nat) (ports : Nat → List Nat)
    (derived : Nat → Prop) (balance : ∀ v, nodes.count v + tips.count v =
      roots.count v + (nodes.flatMap ports).count v)
    (casesFor : ∀ v, derived v →
      nodes.count v = 1 ∨
      (tips.count v = 0 ∧ roots.count v = 0 ∧ ∃ u, u < v ∧ derived u ∧
        ∀ x ∈ nodes, (ports x).count v = if x = u then 1 else 0)) :
    ∀ v, derived v → nodes.count v = 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    rcases casesFor v hv with done | ⟨tip,seed,u,lt,hu,sole⟩
    · exact done
    · have incoming := countParentsSingle nodes ports v u sole
      have earlier := ih u lt hu
      have h := balance v
      omega

end PCX150
namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}
theorem soleReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Fin n, u.val < v.val ∧ g.parent u ≠ none ∧
      ∀ x, g.contribution x v = if x = u then 1 else 0 := by
  classical
  have pos : 0 < g.incoming v := by omega
  obtain ⟨u,slot⟩ := (g.incomingPositive v).mp pos
  have hu := g.chargePositive.mpr slot
  have le := Finset.single_le_sum (f := fun x => g.contribution x v)
    (fun x _ => Nat.zero_le _) (Finset.mem_univ u)
  change g.contribution u v ≤ g.incoming v at le
  have one : g.contribution u v = 1 := by omega
  have nonzero : g.parent u ≠ none := by
    intro bad
    simp [contribution,bad] at one
  refine ⟨u,g.later slot,nonzero,?_⟩
  intro x
  by_cases eq : x = u
  · simpa [eq] using one
  · rw [if_neg eq]
    have e := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun j => g.contribution j v) (Finset.mem_univ u)
    change _ + _ = g.incoming v at e
    have xmem : x ∈ (Finset.univ : Finset (Fin n)).erase u := by simp [eq]
    have b := Finset.single_le_sum (f := fun j => g.contribution j v) (fun j _ => Nat.zero_le _) xmem
    omega

theorem portCount (g : Links C) (x v : Fin n) :
    (portList (g.natParent x.val)).count v.val = g.contribution x v := by
  cases h : g.parent x with
  | none => simp [natParent,x.isLt,h,contribution,portList]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    simp only [natParent,dif_pos x.isLt,h,Option.map_some,contribution,portList]
    have comp (z : Fin n) : (z.val == v.val) = decide (v = z) := by
      by_cases yes : v = z
      · subst z; simp
      · have no : z.val ≠ v.val := fun h => yes (Fin.ext h.symm)
        simp [yes,no]
    simp only [List.count_cons,List.count_nil,comp]
    by_cases a : v = j <;> by_cases b : v = k <;> simp [a,b] <;> omega

theorem soleNatReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Nat, u < v.val ∧ g.natParent u ≠ none ∧
      ∀ x, (portList (g.natParent x)).count v.val = if x = u then 1 else 0 := by
  obtain ⟨u,lt,hd,only⟩ := g.soleReader v single
  refine ⟨u.val,lt,(g.natDerived u).2 hd,?_⟩
  intro x
  by_cases hx : x < n
  · have cnt := g.portCount ⟨x,hx⟩ v
    rw [only] at cnt
    simpa [Fin.ext_iff] using cnt
  · have ne : x ≠ u.val := by intro eq; subst x; exact hx u.isLt
    simp [natParent,hx,ne,portList]

end PCX150.Links
namespace PCX150.Links
variable {n : Nat} {C : Fin n → Cl}
noncomputable def physicalList (g : Links C) := g.derived.toList.map Fin.val

theorem listMember (g : Links C) (v : Nat) :
    v ∈ g.physicalList ↔ g.natParent v ≠ none := by
  unfold physicalList
  rw [List.mem_map,g.natRoots]
  constructor
  · rintro ⟨i,mem,eq⟩
    exact ⟨i,eq,by simpa [derived] using mem⟩
  · rintro ⟨i,eq,mem⟩
    exact ⟨i,by simpa [derived] using mem,eq⟩

theorem listNodup (g : Links C) : g.physicalList.Nodup := by
  exact g.derived.nodup_toList.map Fin.val_injective

theorem countFlatMap {α} (xs : List α) (f : α → List Nat) (v : Nat) :
    (xs.flatMap f).count v = (xs.map (fun x => (f x).count v)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.count_append,ih]

theorem physicalPorts (g : Links C) (v : Fin n) :
    (g.physicalList.flatMap (fun x => portList (g.natParent x))).count v.val = g.incoming v := by
  classical
  rw [countFlatMap]
  have sum : (g.physicalList.map (fun x => (portList (g.natParent x)).count v.val)).sum =
      ∑ i ∈ g.derived, g.contribution i v := by
    simp [physicalList,List.map_map,Function.comp_def,g.portCount]
  rw [sum]
  unfold derived
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g.parent i = none <;> simp [contribution,h]

end PCX150.Links
namespace PCX150
private theorem occursAtMost {xs ys : List Nat} (h : ∀ x, xs.count x ≤ ys.count x) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have positive := h a
    have mem : a ∈ ys := by
      by_contra bad
      have zero := List.count_eq_zero.mpr bad
      simp [zero] at positive
    have tail : ∀ x, xs.count x ≤ (ys.erase a).count x := by
      intro x
      have old := h x
      by_cases eq : x = a
      · subst x
        simp at old
        rw [List.count_erase_self]
        omega
      · simpa [List.count_erase_of_ne,eq,Ne.symm eq] using old
    have len := ih tail
    rw [List.length_erase_of_mem mem] at len
    have pos := List.length_pos_of_mem mem
    simp only [List.length_cons]
    omega

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {b : Nat → Bool}
/-- If every uncut live internal node has exactly one incoming slot, expansion
    partitions the physical rules without charging any physical line twice. -/
theorem partitionCost (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (present : ∀ v, p v ≠ none → v ∈ physical)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none)
    (cut : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u < v ∧ p u ≠ none ∧
        ∀ x ∈ nodes fs, (portList (p x)).count v = if x = u then 1 else 0) :
    (nodes fs).length = physical.length ↔ ∀ v ∈ physical, p v ≠ none := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hv
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb rootsDerived).trans (cut v hv hb))
    | false =>
      obtain ⟨zero,u,lt,d,only⟩ := single v hv hb
      exact Or.inr ⟨noncutNotTip fs hv hb,zero,u,lt,d,only⟩
  have charge : ∀ v, (nodes fs).count v ≤ physical.count v := by
    intro v
    by_cases mem : v ∈ nodes fs
    · have hd := physicalDerived fs mem
      rw [once v hd]
      exact List.count_pos_iff.mpr (present v hd)
    · simp [List.count_eq_zero.mpr mem]
  constructor
  · intro eq v hv
    by_contra bad
    have absent : v ∉ nodes fs := fun h => physicalDerived fs h bad
    have charge' : ∀ x, (nodes fs).count x ≤ (physical.erase v).count x := by
      intro x
      by_cases same : x = v
      · subst x
        simp [List.count_eq_zero.mpr absent]
      · simpa [List.count_erase_of_ne,same,Ne.symm same] using charge x
    have h := occursAtMost charge'
    rw [List.length_erase_of_mem hv] at h
    have pos := List.length_pos_of_mem hv
    omega
  · intro proper
    apply Nat.le_antisymm (occursAtMost charge)
    apply occursAtMost
    intro v
    by_cases mem : v ∈ physical
    · rw [once v (proper v mem)]
      exact List.nodup_iff_count_le_one.mp unique v
    · simp [List.count_eq_zero.mpr mem]

end Rooted
end PCX150
namespace PCX150.Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}
/-- Expand one fragment per selected root, preserving their physical labels and order. -/
noncomputable def chooseForest {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : List (Rooted f p b) :=
  xs.map (fun i => ⟨i,Classical.choice (canExpand rules b i true)⟩)

theorem chooseStarts {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : starts (chooseForest rules b xs) = xs := by
  simp [starts,chooseForest,List.map_map,Function.comp_def]

/-- A non-root with unit indegree is expanded once, no matter how the fragments
    were selected by the kernel's existential unrolling lemma. -/

theorem ownership (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (allRoots : ∀ z ∈ fs, p z.1 ≠ none)
    (cuts : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u<v ∧ p u ≠ none ∧ ∀ x, (portList (p x)).count v = if x = u then 1 else 0) :
    ∀ v, (nodes fs).count v = physical.count v := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hd
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb allRoots).trans (cuts v hd hb))
    | false =>
      obtain ⟨zero,u,lt,hu,only⟩ := single v hd hb
      exact Or.inr ⟨noncutNotTip fs hd hb,zero,u,lt,hu,fun x _ => only x⟩
  intro v
  by_cases hd : p v ≠ none
  · have low := List.count_pos_iff.mpr ((proper v).2 hd)
    have high := List.nodup_iff_count_le_one.mp unique v
    have one := once v hd
    omega
  · have no : v ∉ nodes fs := fun h => hd (physicalDerived fs h)
    have other : v ∉ physical := fun h => hd ((proper v).1 h)
    simp [List.count_eq_zero.mpr no,List.count_eq_zero.mpr other]

end PCX150.Rooted
namespace PCX150.Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}
/-- Identical multiplicities let us count each parent slot directly in the physical list. -/
theorem countPhysical (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v) (v : Nat) :
    ((nodes fs).flatMap (fun k => portList (p k))).count v =
      (physical.flatMap (fun k => portList (p k))).count v := by
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  have out : ((nodes fs).flatMap (fun k => portList (p k))).Perm
      (physical.flatMap (fun k => portList (p k))) := perm.flatMap (fun _ _ => .refl _)
  exact (List.perm_iff_count.mp out) v

/-- For every marked derived line there is exactly one forced opening.
    The remaining occurrences on the frontier are exactly all physical reads. -/

theorem cutReads (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none) {v : Nat} (cut : b v = true) :
    (tips fs).count v = (physical.flatMap (fun k => portList (p k))).count v := by
  have bal := balance fs v
  have atRoot := cutRoots fs v cut rootsDerived
  have charge := countPhysical fs physical same v
  omega

end PCX150.Rooted
namespace PCX150.Rooted
open PEqualNP.ProofComplexity
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {N : Nat}
/-- Build the partition at every selected shared rule and at the empty conclusion. -/
theorem markedFamily
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < N ∧ k < N ∧
      IsResolvent (f j) (f k) (f i))
    (physical roots : List Nat) (unique : physical.Nodup) (distinct : roots.Nodup)
    (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (relevant : ∀ v ∈ roots, p v ≠ none)
    (read : ∀ v, p v ≠ none → v ∉ roots → ∃ u, u < v ∧ p u ≠ none ∧
      ∀ x, (portList (p x)).count v = if x=u then 1 else 0) :
    ∃ fs : List (Rooted f p (fun k => decide (k ∈ roots))),
      starts fs = roots ∧ (nodes fs).length = physical.length ∧
      (∀ v, (nodes fs).count v = physical.count v) ∧
      ∀ v ∈ roots, (tips fs).count v =
        (physical.flatMap (fun k => portList (p k))).count v := by
  let b := fun k : Nat => decide (k ∈ roots)
  let fs := chooseForest rules b roots
  have start : starts fs = roots := chooseStarts rules b roots
  have allRoots : ∀ z ∈ fs, p z.1 ≠ none := by
    intro z hz
    apply relevant
    rw [←start]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have one (v) (mem : v ∈ roots) : (starts fs).count v = 1 := by
    rw [start]
    have pos := List.count_pos_iff.mpr mem
    have low := List.nodup_iff_count_le_one.mp distinct v
    omega
  have same := ownership fs physical unique proper allRoots
    (fun v _ hv => one v (by simpa [b] using hv)) (by
      intro v hv cut
      have absent : v ∉ roots := by simpa [b] using cut
      exact ⟨by rw [start]; exact List.count_eq_zero.mpr absent,read v hv absent⟩)
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  refine ⟨fs,start,perm.length_eq,same,?_⟩
  intro v hv
  exact cutReads fs physical same allRoots (by simp [b,hv])

end PCX150.Rooted
namespace PCX150
open PEqualNP.ProofComplexity
variable {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}
noncomputable def boundaryRoots (g : Links D) (r : Fin n) : List Nat :=
  r.val :: (sharedIndices g r).map Fin.val

theorem boundaryMember (i : Fin n) :
    i.val ∈ boundaryRoots g r ↔ i = r ∨ i ∈ sharedIndices g r := by
  change (i.val ∈ r.val :: (sharedIndices g r).map Fin.val) ↔ _
  rw [List.mem_cons,List.mem_map]
  constructor
  · rintro (eq | ⟨v,hv,eq⟩)
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr ((Fin.ext eq : v = i) ▸ hv)
  · rintro (rfl | mem)
    · exact Or.inl rfl
    · exact Or.inr ⟨i,mem,rfl⟩

theorem boundaryDistinct (g : Links D) (r : Fin n) : (boundaryRoots g r).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
    exact ((isShared _).mp hi).1 (Fin.ext eq)
  · exact (cutNodup _ _).map Fin.val_injective

theorem graphFamily (pr : Prepared D g r) :
    let roots := boundaryRoots g r
    let f := Links.natClause D placeholder
    let p := g.natParent
    ∃ fs : List (Rooted f p (fun k => decide (k ∈ roots))),
      Rooted.starts fs = roots ∧
      (Rooted.nodes fs).length = g.derived.card ∧
      ∀ i : Fin n, i.val ∈ roots → (Rooted.tips fs).count i.val = g.incoming i := by
  dsimp only
  have proper (i : Nat) := g.listMember i
  have read (i : Nat) (hd : g.natParent i ≠ none) (absent : i ∉ boundaryRoots g r) :
      ∃ u, u < i ∧ g.natParent u ≠ none ∧
        ∀ x, (portList (g.natParent x)).count i = if x=u then 1 else 0 := by
    obtain ⟨v,rfl,hv⟩ := (g.natRoots i).mp hd
    have ne : v ≠ r := fun eq => absent ((boundaryMember v).2 (Or.inl eq))
    have un : v ∉ sharedIndices g r := fun h => absent ((boundaryMember v).2 (Or.inr h))
    exact g.soleNatReader v (offCut pr v hv ne un)
  have req (v : Nat) (m : v ∈ boundaryRoots g r) : g.natParent v ≠ none := by
    rcases List.mem_cons.mp m with eq | rest
    · subst v; exact (g.natDerived r).2 pr.rootDerived
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp rest
      exact (g.natDerived i).2 ((isShared _).mp hi).2.1
  obtain ⟨fs,start,len,_,tips⟩ := Rooted.markedFamily (f := Links.natClause D placeholder)
    (fun _ _ _ e => g.natEdge placeholder e) g.physicalList (boundaryRoots g r)
    g.listNodup (boundaryDistinct g r) proper req read
  refine ⟨fs,start,?_,fun i hi => (tips i.val hi).trans (g.physicalPorts i)⟩
  simpa [Links.physicalList] using len

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity LabeledTree
def Permit {f R} (raw : Nat → Prop) (other : List Nat) (t : LabeledTree f R) : Prop :=
  ∀ i ∈ t.leaves, raw i ∨ i ∈ other

private theorem permitSplice {f R raw other i} {t : LabeledTree f R} {p : LabeledTree f (f i)}
    (old : ∀ k ∈ t.leaves, k ≠ i → raw k ∨ k ∈ other)
    (inside : Permit raw other p) : Permit raw other (t.splice i p) := by
  intro k hk
  rcases t.spliceLeaves i p k hk with ⟨ne,mem⟩ | mem
  · exact old k mem ne
  · exact inside k mem

private theorem permitMono {f R raw xs ys} {t : LabeledTree f R}
    (h : Permit raw xs t) (sub : ∀ x ∈ xs, x ∈ ys) : Permit raw ys t := by
  intro k hk
  exact (h k hk).imp_right (sub k)

/-- Apply the numerical tree bound to any three cut fragments with two named shared roots. -/

private theorem threeCost {f raw a b} {x : LabeledTree f (f a)} {y : LabeledTree f (f b)}
    {z : LabeledTree f ∅} (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weights : ∀ {A B i j k}, ResTree (PHP 4 3) A i → ResTree (insert A (PHP 4 3)) B j →
      ResTree (insert B (insert A (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hx : Permit raw [] x) (hy : Permit raw [a] y) (hz : Permit raw [b,a] z) :
    38 ≤ x.cost+y.cost+z.cost := by
  apply weights (A := f a) (B := f b)
  · apply x.toResTree
    intro k hk
    rcases hx k hk with h | h
    · exact source k h
    · simp at h
  · apply y.toResTree
    intro k hk
    rcases hy k hk with h | h
    · exact Or.inr (source k h)
    · have eq : k = a := by simpa using h
      simp [eq]
  · apply z.toResTree
    intro k hk
    rcases hz k hk with h | h
    · exact Or.inr (Or.inr (source k h))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl <;> simp

/-- Expand each of the three candidate shared nodes in turn; each duplicated
    fragment increases the physical step count by exactly its own cost. -/

theorem afterThreeCopies {f raw a b c} (A : LabeledTree f (f a)) (B : LabeledTree f (f b))
    (C : LabeledTree f (f c)) (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weight : ∀ {P Q i j k}, ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
      ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E)
    (twoA : B.leaves.count a + C.leaves.count a + E.leaves.count a = 2)
    (twoB : C.leaves.count b + E.leaves.count b = 2) (twoC : E.leaves.count c = 2) :
    let total := A.cost+B.cost+C.cost+E.cost
    38 ≤ total+A.cost ∧ 38 ≤ total+B.cost ∧ 38 ≤ total+C.cost := by
  dsimp only
  have removeA {R} (t : LabeledTree f R) (rest : List Nat)
      (ht : Permit raw (rest ++ [a]) t) : Permit raw rest (t.splice a A) := by
    apply permitSplice _ (permitMono hA (by simp))
    intro k hk ne
    simpa [ne] using ht k hk
  have removeB {R} (t : LabeledTree f R) (rest : List Nat)
      (memA : a ∈ rest) (ht : ∀ k ∈ t.leaves, raw k ∨ k = b ∨ k ∈ rest) :
      Permit raw rest (t.splice b B) := by
    apply permitSplice _ (permitMono hB (by simpa using memA))
    intro k hk ne
    simpa [ne] using ht k hk
  have sa := threeCost source weight (removeA B [] hB) (removeA C [b] hC)
    (removeA E [c,b] hE)
  have sb := threeCost source weight hA (removeB C [a] (by simp) (by simpa [Permit] using hC))
    (removeB E [c,a] (by simp) (by simpa [Permit,or_comm,or_assoc,or_left_comm] using hE))
  have sc := threeCost source weight hA hB (permitSplice
    (t := E) (i := c) (p := C) (fun k hk ne => by simpa [ne] using hE k hk) hC)
  simp only [spliceCost] at sa sb sc
  have ca := congrArg (fun n : Nat => n * A.cost) twoA
  have cb := congrArg (fun n : Nat => n * B.cost) twoB
  simp only [Nat.add_mul,Nat.two_mul] at ca cb
  rw [twoC,Nat.two_mul] at sc
  omega

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
theorem satOfTree {F : Set Cl} {C : Cl} {n : Nat} (tree : ResTree F C n)
    (a : V → Bool) (model : ∀ D ∈ F, ClauseSat a D) : ClauseSat a C := by
  induction tree with
  | ax h => exact model _ h
  | res _ _ step left right =>
    obtain ⟨v,_,_,rfl⟩ := step
    cases h : a v with
    | false =>
      obtain ⟨l,mem,val⟩ := left
      have ne : l ≠ (v,true) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩
    | true =>
      obtain ⟨l,mem,val⟩ := right
      have ne : l ≠ (v,false) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩

private theorem uniqueSign {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Two nonempty clauses can refute by themselves only if one resolution step suffices. -/

theorem refuteTwo {A B : Cl} {n : Nat} (tree : ResTree ({A,B} : Set Cl) ∅ n)
    (na : A.Nonempty) (nb : B.Nonempty) : IsResolvent A B ∅ ∨ IsResolvent B A ∅ := by
  classical
  have noBoth (a : V → Bool) (sa : ClauseSat a A) (sb : ClauseSat a B) : False := by
    have sat := satOfTree tree a (by
      intro D hd
      rcases Set.mem_insert_iff.mp hd with eq | mem
      · simpa [eq] using sa
      · have eq : D = B := Set.mem_singleton_iff.mp mem
        simpa [eq] using sb)
    simpa [ClauseSat] using sat
  have opposite (l) (hl : l ∈ A) (m) (hm : m ∈ B) : l.1 = m.1 ∧ l.2 ≠ m.2 := by
    by_cases eq : l.1 = m.1
    · refine ⟨eq,?_⟩
      intro same
      exact noBoth (fun _ => l.2) ⟨l,hl,rfl⟩ ⟨m,hm,same⟩
    · let a : V → Bool := fun v => if v = l.1 then l.2 else m.2
      exact (noBoth a ⟨l,hl,by simp [a]⟩ ⟨m,hm,by simp [a,Ne.symm eq]⟩).elim
  obtain ⟨u,hu⟩ := na
  obtain ⟨v,hv⟩ := nb
  have h := opposite u hu v hv
  have oneA : A = {u} := by
    ext l
    constructor
    · intro hl
      have p := opposite l hl v hv
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.trans h.1.symm) (uniqueSign p.2 h.2))
    · intro hl
      exact (Finset.mem_singleton.mp hl).symm ▸ hu
  have oneB : B = {v} := by
    ext m
    constructor
    · intro hm
      have p := opposite u hu m hm
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.symm.trans h.1) (uniqueSign (Ne.symm p.2) (Ne.symm h.2)))
    · intro hm
      exact (Finset.mem_singleton.mp hm).symm ▸ hv
  obtain ⟨u,us⟩ := u
  obtain ⟨v,vs⟩ := v
  change u = v ∧ us ≠ vs at h
  obtain ⟨rfl,neq⟩ := h
  rw [oneA,oneB]
  cases us <;> cases vs <;> simp_all [IsResolvent]

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity LabeledTree
private theorem otherLength (xs : List Nat) (c : Nat) :
    (xs.filter (fun k => decide (k ≠ c))).length + xs.count c = xs.length := by
  induction xs with
  | nil => rfl
  | cons k ks ih =>
    by_cases eq : k = c
    · subst k
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] at ih ⊢
      omega
    · simp [eq,Ne.symm eq] at ih ⊢
      omega

private theorem oneModel (u : Cl) (hn : u.Nonempty) :
    ∃ a : V → Bool, ClauseSat a u := by
  obtain ⟨l,hl⟩ := hn
  exact ⟨fun _ => l.2,l,hl,rfl⟩

private theorem otherLabel {f c} {e : LabeledTree f ∅}
    (three : e.leaves.length ≤ 3) (twice : e.leaves.count c = 2) (nc : (f c).Nonempty) :
    ∃ k ∈ e.leaves, k ≠ c ∧ ∀ u ∈ e.leaves, u = c ∨ u = k := by
  let other := e.leaves.filter (fun k => decide (k ≠ c))
  have hlength : other.length ≤ 1 := by
    have eq := otherLength e.leaves c
    change (e.leaves.filter _).length ≤ 1
    omega
  cases h : other with
  | nil =>
    obtain ⟨a,sa⟩ := oneModel (f c) nc
    have only : ∀ x ∈ e.leaves, f x ∈ ({f c} : Set Cl) := by
      intro x hx
      by_contra bad
      have ne : x ≠ c := by rintro rfl; simp at bad
      have mem : x ∈ other := List.mem_filter.mpr ⟨hx,by simpa using ne⟩
      simp [h] at mem
    have contra := satOfTree (e.toResTree only) a (by simpa using sa)
    simpa [ClauseSat] using contra
  | cons k ks =>
    have rest : ks = [] := by
      have hh : other.length = ks.length + 1 := by rw [h]; rfl
      have small : ks.length = 0 := by omega
      exact List.length_eq_zero_iff.mp small
    subst ks
    have km : k ∈ other := by simp [h]
    obtain ⟨km',ne⟩ := List.mem_filter.mp km
    refine ⟨k,km',by simpa using ne,?_⟩
    intro u hu
    by_cases eq : u = c
    · exact Or.inl eq
    · have mem : u ∈ other := List.mem_filter.mpr ⟨hu,by simpa using eq⟩
      exact Or.inr (by simpa [h] using mem)

theorem shortEnd {f raw a b c} (A : LabeledTree f (f a)) (B : LabeledTree f (f b))
    (C : LabeledTree f (f c)) (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weights : ∀ {P Q i j k}, ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
      ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E) (nc : (f c).Nonempty) (proper : ∀ k ∈ E.leaves, (f k).Nonempty)
    (two : E.leaves.count c = 2) (small : E.cost ≤ 2) :
    38 ≤ A.cost+B.cost+C.cost+1 := by
  have three := E.leafCount
  obtain ⟨k,hk,ne,only⟩ := otherLabel (by omega) two nc
  have setTree : ResTree ({f c,f k} : Set Cl) ∅ E.cost := E.toResTree (by
    intro u hu
    rcases only u hu with rfl | rfl <;> simp)
  have allow : raw k ∨ k ∈ [b,a] := by simpa [ne] using hE k hk
  have allowedJoin (rule : IsResolvent (f c) (f k) ∅) :
      Permit raw [b,a] (LabeledTree.resolve C (.leaf k) rule) := by
    intro u hu
    simp only [LabeledTree.leaves,List.mem_append,List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hC u hu
    · exact allow
  rcases refuteTwo setTree nc (proper k hk) with rule | rule
  · have h := threeCost source weights hA hB (allowedJoin rule)
    simp only [LabeledTree.cost,Nat.add_zero] at h
    omega
  · have allowed : Permit raw [b,a] (LabeledTree.resolve (.leaf k) C rule) := by
      intro u hu
      simp only [LabeledTree.leaves,List.mem_append,List.mem_singleton] at hu
      rcases hu with rfl | hu
      · exact allow
      · exact hC u hu
    have h := threeCost source weights hA hB allowed
    simp only [LabeledTree.cost,Nat.zero_add] at h
    omega

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
abbrev TreeLower := ∀ {P Q : Cl} {i j k : Nat},
  ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
  ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k

theorem forbidFour {f raw a b c}
    (A : LabeledTree f (f a)) (B : LabeledTree f (f b)) (C : LabeledTree f (f c))
    (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E)
    (twoA : B.leaves.count a+C.leaves.count a+E.leaves.count a=2)
    (twoB : C.leaves.count b+E.leaves.count b=2) (twoC : E.leaves.count c=2)
    (nonempty : (f c).Nonempty) (proper : ∀ k ∈ E.leaves, (f k).Nonempty)
    (tiny : A.cost+B.cost+C.cost+E.cost ≤ 29) : False := by
  obtain ⟨ha,hb,hc⟩ := afterThreeCopies A B C E source weight hA hB hC hE twoA twoB twoC
  have last : E.cost ≤ 2 := by omega
  have no := shortEnd A B C E source weight hA hB hC hE nonempty proper twoC last
  omega

theorem forbidThree {f raw a b}
    (A : LabeledTree f (f a)) (B : LabeledTree f (f b)) (E : LabeledTree f ∅)
    (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hE : Permit raw [b,a] E)
    (tiny : A.cost+B.cost+E.cost ≤ 29) : False := by
  have no := threeCost source weight hA hB hE
  omega

theorem forbidTwo {f raw a} (A : LabeledTree f (f a)) (E : LabeledTree f ∅)
    (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hE : Permit raw [a] E)
    (tiny : A.cost+E.cost ≤ 29) : False := by
  let B : LabeledTree f (f a) := .leaf a
  have pB : Permit raw [a] B := by simp [B,Permit,LabeledTree.leaves]
  apply forbidThree A B E source weight hA pB
  · simpa [Permit] using hE
  · simpa [B,LabeledTree.cost] using tiny

theorem forbidOne {f raw} (E : LabeledTree f ∅) (i : Nat) (pure : raw i)
    (source : ∀ v, raw v → f v ∈ PHP 4 3) (weight : TreeLower)
    (hE : Permit raw [] E) (tiny : E.cost ≤ 29) : False := by
  let A : LabeledTree f (f i) := .leaf i
  have pA : Permit raw [] A := by simp [A,Permit,LabeledTree.leaves,pure]
  apply forbidTwo A E source weight pA
  · intro v hv
    exact Or.inl (by simpa using hE v hv)
  · simpa [A,LabeledTree.cost] using tiny

end PCX150
namespace PCX150.Fragment
/-- Each leaf of an expanded physical rule occurs strictly earlier in the
    derivation (the input list uses the reverse of chronological order). -/
theorem leafOrder {f p b i t} (g : Fragment f p b i t)
    (forward : ∀ i j k, p i = some (j,k) → i < j ∧ i < k) :
    ∀ v ∈ g.tree.leaves, i ≤ v ∧ (p i ≠ none → t = true → i < v) := by
  induction g with
  | leaf u forced reason =>
    intro v hv
    have eq : v = u := by simpa [tree,LabeledTree.leaves] using hv
    subst v
    refine ⟨Nat.le_refl _,?_⟩
    intro derived yes
    rcases reason with raw | ⟨no,_⟩
    · exact False.elim (derived raw)
    · simp [yes] at no
  | node u j k force op edge rule l r ih jh =>
    intro v hv
    have e := forward u j k edge
    have strict : u < v := by
      rcases List.mem_append.mp hv with a | a
      · exact Nat.lt_of_lt_of_le e.1 (ih v a).1
      · exact Nat.lt_of_lt_of_le e.2 (jh v a).1
    exact ⟨Nat.le_of_lt strict,fun _ _ => strict⟩

theorem permitsEarlier {f p b i} (g : Fragment f p b i true)
    (forward : ∀ i j k, p i = some (j,k) → i < j ∧ i < k)
    (proper : p i ≠ none) (other : List Nat)
    (boundary : ∀ k, i < k → b k = true → k ∈ other) :
    ∀ k ∈ g.tree.leaves, p k = none ∨ k ∈ other := by
  intro k hk
  rcases g.leafReason k hk with raw | cut
  · exact Or.inl raw
  · exact Or.inr (boundary k ((g.leafOrder forward k hk).2 proper rfl) cut)

end PCX150.Fragment
namespace PCX150
open PEqualNP.ProofComplexity
namespace LabeledTree
def onEmpty {f C} (t : LabeledTree f C) (h : C = ∅) : LabeledTree f ∅ := h ▸ t
@[simp] theorem onEmptyCost {f C} (t : LabeledTree f C) (h : C = ∅) :
    (t.onEmpty h).cost = t.cost := by subst C; rfl
@[simp] theorem onEmptyLeaves {f C} (t : LabeledTree f C) (h : C = ∅) :
    (t.onEmpty h).leaves = t.leaves := by subst C; rfl

end LabeledTree
namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}
theorem splitHead {fs : List (Rooted f p b)} {r : Nat} {xs : List Nat}
    (start : starts fs = r :: xs) :
    ∃ (g : Fragment f p b r true) (tail : List (Rooted f p b)),
      fs = ⟨r,g⟩ :: tail ∧ starts tail = xs := by
  cases fs with
  | nil => simp [starts] at start
  | cons z zs =>
    obtain ⟨i,g⟩ := z
    change i :: starts zs = r :: xs at start
    obtain ⟨eq,rest⟩ := List.cons.inj start
    subst i
    exact ⟨g,zs,rfl,rest⟩

theorem emptyTail {fs : List (Rooted f p b)} (h : starts fs = []) : fs = [] := by
  cases fs <;> simp_all [starts]

theorem totalCostCons (g : Fragment f p b i true) (tail : List (Rooted f p b)) :
    (nodes (⟨i,g⟩ :: tail)).length = g.tree.cost + (nodes tail).length := by
  simp [nodes,g.costCount]

theorem tipCountCons (g : Fragment f p b i true) (tail : List (Rooted f p b)) (v : Nat) :
    (tips (⟨i,g⟩ :: tail)).count v = g.tree.leaves.count v + (tips tail).count v := by
  simp [tips,List.count_append]

end Rooted
end PCX150
namespace PCX150
open PEqualNP.ProofComplexity Rooted
private theorem noNode {f p b} : (nodes ([] : List (Rooted f p b))).length = 0 := rfl

private theorem noTip {f p b} (v : Nat) : (tips ([] : List (Rooted f p b))).count v = 0 := rfl

theorem exclude0Cut {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {r : Nat}
    (rule : ∀ i j k, p i = some (j,k) → i < j ∧ i < k)
    (source : ∀ i, p i = none → f i ∈ PHP 4 3) (weight : TreeLower)
    (emp : f r = ∅) (nonempty : ∀ i, r < i → (f i).Nonempty)
    (derived : ∀ i ∈ [r], p i ≠ none)
    (fs : List (Rooted f p (fun i => decide (i ∈ [r]))))
    (startsAt : starts fs = [r]) (small : (nodes fs).length ≤ 29)
    (free : ∃ i, p i = none) : False := by
  obtain ⟨E,tail1,rfl,start1⟩ := splitHead startsAt
  have fin := emptyTail start1
  subst tail1
  simp only [totalCostCons,noNode,Nat.add_zero] at small
  have pE : Permit (fun k => p k = none) [] E.tree := by
    apply E.permitsEarlier rule (derived r (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  let Z := E.tree.onEmpty emp
  have zLeaves : Z.leaves = E.tree.leaves := LabeledTree.onEmptyLeaves _ _
  have zCost : Z.cost = E.tree.cost := LabeledTree.onEmptyCost _ _
  have pZ : Permit (fun k => p k = none) [] Z := by
    intro k hk; exact pE k (zLeaves ▸ hk)
  obtain ⟨i,hi⟩ := free
  apply forbidOne Z i hi source weight pZ
  rw [zCost]; omega

theorem exclude1Cut {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {r a : Nat}
    (rule : ∀ i j k, p i = some (j,k) → i < j ∧ i < k)
    (source : ∀ i, p i = none → f i ∈ PHP 4 3) (weight : TreeLower)
    (emp : f r = ∅) (nonempty : ∀ i, r < i → (f i).Nonempty)
    (derived : ∀ i ∈ [r,a], p i ≠ none)
    (fs : List (Rooted f p (fun i => decide (i ∈ [r,a]))))
    (startsAt : starts fs = [r,a]) (small : (nodes fs).length ≤ 29)
    (ord1 : r < a) : False := by
  obtain ⟨E,tail1,rfl,start1⟩ := splitHead startsAt
  obtain ⟨A,tail2,rfl,start2⟩ := splitHead start1
  have fin := emptyTail start2
  subst tail2
  simp only [totalCostCons,noNode,Nat.add_zero] at small
  have pE : Permit (fun k => p k = none) [a] E.tree := by
    apply E.permitsEarlier rule (derived r (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pA : Permit (fun k => p k = none) [] A.tree := by
    apply A.permitsEarlier rule (derived a (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  let Z := E.tree.onEmpty emp
  have zLeaves : Z.leaves = E.tree.leaves := LabeledTree.onEmptyLeaves _ _
  have zCost : Z.cost = E.tree.cost := LabeledTree.onEmptyCost _ _
  have pZ : Permit (fun k => p k = none) [a] Z := by
    intro k hk; exact pE k (zLeaves ▸ hk)
  apply forbidTwo A.tree Z source weight pA pZ
  rw [zCost]; omega

theorem exclude2Cut {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {r a b : Nat}
    (rule : ∀ i j k, p i = some (j,k) → i < j ∧ i < k)
    (source : ∀ i, p i = none → f i ∈ PHP 4 3) (weight : TreeLower)
    (emp : f r = ∅) (nonempty : ∀ i, r < i → (f i).Nonempty)
    (derived : ∀ i ∈ [r,a,b], p i ≠ none)
    (fs : List (Rooted f p (fun i => decide (i ∈ [r,a,b]))))
    (startsAt : starts fs = [r,a,b]) (small : (nodes fs).length ≤ 29)
    (ord1 : r < b)
    (ord2 : b < a) : False := by
  obtain ⟨E,tail1,rfl,start1⟩ := splitHead startsAt
  obtain ⟨A,tail2,rfl,start2⟩ := splitHead start1
  obtain ⟨B,tail3,rfl,start3⟩ := splitHead start2
  have fin := emptyTail start3
  subst tail3
  simp only [totalCostCons,noNode,Nat.add_zero] at small
  have pE : Permit (fun k => p k = none) [b,a] E.tree := by
    apply E.permitsEarlier rule (derived r (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pA : Permit (fun k => p k = none) [] A.tree := by
    apply A.permitsEarlier rule (derived a (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pB : Permit (fun k => p k = none) [a] B.tree := by
    apply B.permitsEarlier rule (derived b (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  let Z := E.tree.onEmpty emp
  have zLeaves : Z.leaves = E.tree.leaves := LabeledTree.onEmptyLeaves _ _
  have zCost : Z.cost = E.tree.cost := LabeledTree.onEmptyCost _ _
  have pZ : Permit (fun k => p k = none) [b,a] Z := by
    intro k hk; exact pE k (zLeaves ▸ hk)
  apply forbidThree A.tree B.tree Z source weight pA pB pZ
  rw [zCost]; omega

theorem exclude3Cut {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {r a b c : Nat}
    (rule : ∀ i j k, p i = some (j,k) → i < j ∧ i < k)
    (source : ∀ i, p i = none → f i ∈ PHP 4 3) (weight : TreeLower)
    (emp : f r = ∅) (nonempty : ∀ i, r < i → (f i).Nonempty)
    (derived : ∀ i ∈ [r,a,b,c], p i ≠ none)
    (fs : List (Rooted f p (fun i => decide (i ∈ [r,a,b,c]))))
    (startsAt : starts fs = [r,a,b,c]) (small : (nodes fs).length ≤ 29)
    (ord1 : r < c)
    (ord2 : c < b)
    (ord3 : b < a)
    (twice : ∀ i ∈ [a,b,c], (tips fs).count i = 2) : False := by
  obtain ⟨E,tail1,rfl,start1⟩ := splitHead startsAt
  obtain ⟨A,tail2,rfl,start2⟩ := splitHead start1
  obtain ⟨B,tail3,rfl,start3⟩ := splitHead start2
  obtain ⟨C,tail4,rfl,start4⟩ := splitHead start3
  have fin := emptyTail start4
  subst tail4
  simp only [totalCostCons,noNode,Nat.add_zero] at small
  have pE : Permit (fun k => p k = none) [c,b,a] E.tree := by
    apply E.permitsEarlier rule (derived r (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pA : Permit (fun k => p k = none) [] A.tree := by
    apply A.permitsEarlier rule (derived a (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pB : Permit (fun k => p k = none) [a] B.tree := by
    apply B.permitsEarlier rule (derived b (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  have pC : Permit (fun k => p k = none) [b,a] C.tree := by
    apply C.permitsEarlier rule (derived c (by simp))
    intro k lt cut
    simp only [List.mem_cons,List.not_mem_nil,or_false,decide_eq_true_eq] at cut ⊢
    omega
  let Z := E.tree.onEmpty emp
  have zLeaves : Z.leaves = E.tree.leaves := LabeledTree.onEmptyLeaves _ _
  have zCost : Z.cost = E.tree.cost := LabeledTree.onEmptyCost _ _
  have pZ : Permit (fun k => p k = none) [c,b,a] Z := by
    intro k hk; exact pE k (zLeaves ▸ hk)
  have noAa : A.tree.leaves.count a = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (A.leafOrder rule a mem).2 (derived a (by simp)) rfl
    omega
  have dbla := twice a (by simp)
  simp only [tipCountCons,noTip,Nat.add_zero] at dbla
  have noAb : A.tree.leaves.count b = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (A.leafOrder rule b mem).2 (derived a (by simp)) rfl
    omega
  have noBb : B.tree.leaves.count b = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (B.leafOrder rule b mem).2 (derived b (by simp)) rfl
    omega
  have dblb := twice b (by simp)
  simp only [tipCountCons,noTip,Nat.add_zero] at dblb
  have noAc : A.tree.leaves.count c = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (A.leafOrder rule c mem).2 (derived a (by simp)) rfl
    omega
  have noBc : B.tree.leaves.count c = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (B.leafOrder rule c mem).2 (derived b (by simp)) rfl
    omega
  have noCc : C.tree.leaves.count c = 0 := by
    apply List.count_eq_zero.mpr
    intro mem
    have later := (C.leafOrder rule c mem).2 (derived c (by simp)) rfl
    omega
  have dblc := twice c (by simp)
  simp only [tipCountCons,noTip,Nat.add_zero] at dblc
  apply forbidFour A.tree B.tree C.tree Z source weight pA pB pC pZ
  · rw [zLeaves]; omega
  · rw [zLeaves]; omega
  · rw [zLeaves]; omega
  · exact nonempty c (by omega)
  · intro k hk
    exact nonempty k ((E.leafOrder rule k (zLeaves ▸ hk)).2 (derived r (by simp)) rfl)
  · rw [zCost]; omega

end PCX150
namespace PCX150
variable {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}
theorem sourceOrder (pr : Prepared D g r) (i : Fin n) (derived : g.parent i ≠ none)
    (ne : i ≠ r) : r.val < i.val := by
  have all (k : Nat) : ∀ j : Fin n, j.val = k → g.parent j ≠ none → r.val ≤ j.val := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro j eq hd
      by_cases same : j=r
      · simp [same]
      · obtain ⟨u,mem⟩ := (g.incomingPositive j).mp (pr.othersRead j hd same)
        have lt := g.later mem
        have hu : g.parent u ≠ none := by
          intro hp
          simp [Links.inputs,hp] at mem
        exact Nat.le_trans (ih u.val (eq ▸ lt) u rfl hu) (Nat.le_of_lt lt)
  have lo := all i.val i rfl derived
  have diff : i.val ≠ r.val := fun h => ne (Fin.ext h)
  omega

theorem portBound {x v : Nat} {p : Nat → Option (Nat×Nat)} (N : Nat)
    (bounded : ∀ i j k, p i = some (j,k) → j<N ∧ k<N) (mem : v ∈ portList (p x)) : v<N := by
  cases h : p x with
  | none => simp [h,portList] at mem
  | some pair =>
    obtain ⟨j,k⟩ := pair
    obtain ⟨a,b⟩ := bounded x j k h
    simp only [h,portList,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl <;> assumption

theorem rawOrOlder {v : Nat} (pr : Prepared D g r) (h : r.val < v) :
    (Links.natClause D placeholder v).Nonempty := by
  by_cases hv : v < n
  · simpa [Links.natClause,hv] using pr.olderNonempty ⟨v,hv⟩ h
  · simpa [Links.natClause,hv] using placeholderFacts.2.1

end PCX150
namespace PCX150
open Rooted PEqualNP.ProofComplexity
theorem impossiblePrepared {n : Nat} {D : Fin n → Cl} {g : Links D} {r : Fin n}
    (pr : Prepared D g r) (weight : TreeLower) : False := by
  let f := Links.natClause D placeholder
  let p := g.natParent
  have empty : f r.val = ∅ := by simpa [f,Links.natClause,r.isLt] using pr.emptyRoot
  have nonempty : ∀ i, r.val < i → (f i).Nonempty := fun i lt => rawOrOlder pr lt
  have source : ∀ i, p i = none → f i ∈ PHP 4 3 := fun _ h => g.natAx placeholder placeholderFacts.1 h
  have rule : ∀ i j k, p i = some (j,k) → i < j ∧ i < k := fun _ _ _ h =>
    ⟨(g.natEdge placeholder h).1,(g.natEdge placeholder h).2.1⟩
  have rootProps (v : Nat) (h : v ∈ boundaryRoots g r) : p v ≠ none := by
    rcases List.mem_cons.mp h with eq | mem
    · subst v; exact (g.natDerived r).2 pr.rootDerived
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
      exact (g.natDerived i).2 ((isShared _).mp hi).2.1
  have later (i : Fin n) (hi : i ∈ sharedIndices g r) : r.val < i.val :=
    sourceOrder pr i ((isShared _).mp hi).2.1 ((isShared _).mp hi).1
  have ordered := cutOrdered (g.derived.erase r) g.incoming
  change (sharedIndices g r).Pairwise _ at ordered
  obtain ⟨size,casesN⟩ := cutSplit pr
  have limit : (sharedIndices g r).length ≤ 3 := by rcases casesN with h|⟨h,_⟩ <;> omega
  have useTwo (length : (sharedIndices g r).length = 3) :
      ∀ i ∈ sharedIndices g r, g.incoming i = 2 := by
    rcases casesN with h|⟨_,dbl⟩
    · omega
    · exact dbl
  obtain ⟨fs,start,cost,counts⟩ := graphFamily pr
  have small : (nodes fs).length ≤ 29 := cost ▸ size
  have free : ∃ i, p i = none := ⟨n,by simp [p,Links.natParent]⟩
  generalize he : sharedIndices g r = xs
  revert he
  cases xs with
  | nil =>
    intro eq
    have boundary : boundaryRoots g r = [r.val] := by simp [boundaryRoots,eq]
    revert fs
    rw [boundary]
    intro fs start cost counts small
    apply exclude0Cut rule source weight empty nonempty (by simpa [boundary] using rootProps) fs start small
    exact free
  | cons a tail =>
    cases tail with
    | nil =>
      intro eq
      have boundary : boundaryRoots g r = [r.val,a.val] := by simp [boundaryRoots,eq]
      have lta := later a (by rw [eq]; simp)
      rw [eq] at ordered
      revert fs
      rw [boundary]
      intro fs start cost counts small
      apply exclude1Cut rule source weight empty nonempty (by simpa [boundary] using rootProps) fs start small
      exact lta
    | cons b tail =>
      cases tail with
      | nil =>
        intro eq
        have boundary : boundaryRoots g r = [r.val,a.val,b.val] := by simp [boundaryRoots,eq]
        have lta := later a (by rw [eq]; simp)
        have ltb := later b (by rw [eq]; simp)
        rw [eq] at ordered
        have step0 : b.val < a.val := (List.pairwise_cons.mp ordered).1 _ (by simp)
        revert fs
        rw [boundary]
        intro fs start cost counts small
        apply exclude2Cut rule source weight empty nonempty (by simpa [boundary] using rootProps) fs start small
        · exact ltb
        · exact step0
      | cons c tail =>
        cases tail with
        | nil =>
          intro eq
          have boundary : boundaryRoots g r = [r.val,a.val,b.val,c.val] := by simp [boundaryRoots,eq]
          have lta := later a (by rw [eq]; simp)
          have ltb := later b (by rw [eq]; simp)
          have ltc := later c (by rw [eq]; simp)
          rw [eq] at ordered
          have step0 : b.val < a.val := (List.pairwise_cons.mp ordered).1 _ (by simp)
          have step1 : c.val < b.val := (List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 _ (by simp)
          revert fs
          rw [boundary]
          intro fs start cost counts small
          apply exclude3Cut rule source weight empty nonempty (by simpa [boundary] using rootProps) fs start small
          · exact ltc
          · exact step1
          · exact step0
          · intro v hv
            have dbl := useTwo (by rw [eq]; rfl)
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
            rcases hv with h | h | h
            · subst v; exact (counts a (by simp)).trans (dbl a (by rw [eq]; simp))
            · subst v; exact (counts b (by simp)).trans (dbl b (by rw [eq]; simp))
            · subst v; exact (counts c (by simp)).trans (dbl c (by rw [eq]; simp))
        | cons d tail =>
          intro eq
          rw [eq] at limit
          simp only [List.length_cons] at limit
          omega

end PCX150
namespace PCX150
open PEqualNP.ProofComplexity
theorem finishFromBounds
    (hard : ∀ xs : List (Fin 48), xs.length ≤ 8 → ¬∀ q : PP, isMarked (runMoves xs 0) q)
    (weight : TreeLower) :
    ¬ (∃ π : List (Clause (Fin 4 × Fin 3)), IsRefutation (PHP 4 3) π ∧ π.length ≤ 51) :=
  physicalContract hard (fun pr => impossiblePrepared pr weight)

end PCX150

namespace PCX150.Orbits
abbrev Pt := Fin 24

abbrev Endpt := Fin 36

abbrev Act := Fin 48

structure Board where
  cell : Endpt → Pt → Prop
  opposite : Endpt → Endpt
  direct : Endpt → Act
  port : Endpt → Act

def Ready (B : Board) (s : Set Pt) (e : Endpt) : Prop :=
  (∀ p, B.cell e p → p ∈ s) ∨ (∀ p, B.cell (B.opposite e) p → p ∈ s)

def Step (B : Board) (s : Set Pt) (a : Act) : Set Pt :=
  {p | p ∈ s ∨ ∃ e, B.cell e p ∧ (B.direct e = a ∨ (B.port e = a ∧ Ready B s e))}

structure Renaming (B : Board) where
  pt : Equiv.Perm Pt
  ed : Equiv.Perm Endpt
  op : Equiv.Perm Act
  cell : ∀ e p, B.cell e p ↔ B.cell (ed e) (pt p)
  mate : ∀ e, ed (B.opposite e) = B.opposite (ed e)
  direct : ∀ e, op (B.direct e) = B.direct (ed e)
  port : ∀ e, op (B.port e) = B.port (ed e)

def identity (B : Board) : Renaming B :=
  ⟨Equiv.refl _,Equiv.refl _,Equiv.refl _,fun _ _ => Iff.rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

def combine {B : Board} (f g : Renaming B) : Renaming B where
  pt := f.pt.trans g.pt
  ed := f.ed.trans g.ed
  op := f.op.trans g.op
  cell e p := (f.cell e p).trans (g.cell _ _)
  mate e := (congrArg g.ed (f.mate e)).trans (g.mate _)
  direct e := (congrArg g.op (f.direct e)).trans (g.direct _)
  port e := (congrArg g.op (f.port e)).trans (g.port _)

def Below (B : Board) (s t : Set Pt) : Prop :=
  ∃ f : Renaming B, ∀ p ∈ s, f.pt p ∈ t

theorem belowSubset {B : Board} {s t : Set Pt} (inc : s ⊆ t) : Below B s t :=
  ⟨identity _,fun _ h => inc h⟩

theorem belowTrans {B : Board} {s t u : Set Pt} (a : Below B s t) (b : Below B t u) :
    Below B s u := by
  obtain ⟨f,hf⟩ := a
  obtain ⟨g,hg⟩ := b
  exact ⟨combine f g,fun p hp => hg _ (hf p hp)⟩

theorem preserved {B : Board} {s t : Set Pt} (f : Renaming B) (incl : ∀ p ∈ s, f.pt p ∈ t)
    (a : Act) : ∀ p ∈ Step B s a, f.pt p ∈ Step B t (f.op a) := by
  have group {e : Endpt} (c : ∀ p, B.cell e p → p ∈ s) : ∀ p, B.cell (f.ed e) p → p ∈ t := by
    intro p h
    have hit := (f.cell e (f.pt.symm p)).2 (by simpa using h)
    simpa using incl _ (c _ hit)
  intro p h
  rcases h with old | ⟨e,cell,direct | ⟨port,ready⟩⟩
  · exact Or.inl (incl p old)
  · exact Or.inr ⟨f.ed e,(f.cell e p).1 cell,Or.inl ((f.direct e).symm.trans (congrArg f.op direct))⟩
  · refine Or.inr ⟨f.ed e,(f.cell e p).1 cell,Or.inr ⟨(f.port e).symm.trans (congrArg f.op port),?_⟩⟩
    rcases ready with left | right
    · exact Or.inl (group left)
    · exact Or.inr (by simpa [f.mate e] using group right)

theorem fromFrontier {B : Board} (cap : Nat → Nat → Set Pt) (size : Nat → Nat)
    (next : ∀ d < 8, ∀ i < size d, ∀ a : Act, ∃ j < size (d+1), Below B (Step B (cap d i) a) (cap (d+1) j))
    {actual : Type} (marked : actual → Set Pt) (go : actual → Act → actual)
    (safe : ∀ s a, marked (go s a) ⊆ Step B (marked s) a)
    (miss : ∀ d ≤ 8, ∀ i < size d, ∃ p, p ∉ cap d i)
    (start : actual) (initial : ∃ i < size 0, Below B (marked start) (cap 0 i))
    (as : List Act) (len : as.length ≤ 8) : ¬ ∀ p, p ∈ marked (as.foldl go start) := by
  have visit (xs : List Act) (d : Nat) (s : actual) (lim : d+xs.length ≤ 8)
      (atState : ∃ i < size d, Below B (marked s) (cap d i)) :
      ∃ i < size (d+xs.length), Below B (marked (xs.foldl go s)) (cap (d+xs.length) i) := by
    induction xs generalizing d s with
    | nil => simpa using atState
    | cons a xs ih =>
      obtain ⟨i,hi,f,embedding⟩ := atState
      have h : d < 8 := by simp at lim; omega
      obtain ⟨j,hj,nextState⟩ := next d h i hi (f.op a)
      have lift : Below B (marked (go s a)) (Step B (cap d i) (f.op a)) :=
        ⟨f,fun p hp => preserved f embedding a p (safe s a hp)⟩
      have remain : (d+1)+xs.length ≤ 8 := by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lim
      have finish := ih (d+1) (go s a) remain ⟨j,hj,belowTrans lift nextState⟩
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finish
  obtain ⟨i,hi,f,inc⟩ := visit as 0 start (by simpa using len) initial
  simp only [Nat.zero_add] at hi inc
  obtain ⟨p,absent⟩ := miss as.length len i hi
  intro full
  exact absent (by simpa using inc (f.pt.symm p) (full _))

end PCX150.Orbits
namespace PCX150.Bands
structure Part where
  destination : Nat
  distance : Nat
  down : Bool
  deriving Inhabited, DecidableEq

def readBit (p : Part) (r : Nat) : Option Nat :=
  if p.down then some (p.distance + r) else
  if p.distance ≤ r then some (r-p.distance) else none

def applyPart (p : Part) (m : Nat) : Nat :=
  p.destination &&& (if p.down then m >>> p.distance else m <<< p.distance)

def roll (ps : List Part) (m : Nat) : Nat :=
  ps.foldr (fun p t => applyPart p m ||| t) 0

theorem testPart (p : Part) (m r : Nat) :
    (applyPart p m).testBit r = (p.destination.testBit r &&
      ((readBit p r).map (fun x => m.testBit x)).getD false) := by
  by_cases b : p.down = true
  · simp [applyPart,readBit,b,Nat.testBit_and,Nat.testBit_shiftRight,Nat.add_comm]
  · by_cases d : p.distance ≤ r <;>
      simp [applyPart,readBit,b,d,Nat.testBit_and,Nat.testBit_shiftLeft]

theorem rollBit (ps : List Part) (m r : Nat) :
    (roll ps m).testBit r = true ↔
      ∃ p ∈ ps, p.destination.testBit r = true ∧ ∃ x, readBit p r = some x ∧ m.testBit x = true := by
  induction ps with
  | nil => simp [roll]
  | cons p ps ih =>
    change ((applyPart p m ||| roll ps m).testBit r = true) ↔ _
    rw [Nat.testBit_or,Bool.or_eq_true,testPart,Bool.and_eq_true,ih]
    simp only [List.mem_cons]
    cases h : readBit p r with
    | none => simp [h]
    | some k => simp [h]

def routes (ps : List Part) (r src : Nat) : Prop :=
  (∃ p ∈ ps, p.destination.testBit r = true) ∧
  ∀ p ∈ ps, p.destination.testBit r = true → readBit p r = some src

instance (ps : List Part) (r src : Nat) : Decidable (routes ps r src) := by
  unfold routes
  infer_instance

theorem rollCorrect {ps : List Part} {r src : Nat} (h : routes ps r src) (m : Nat) :
    (roll ps m).testBit r = m.testBit src := by
  apply Bool.eq_iff_iff.mpr
  rw [rollBit]
  constructor
  · rintro ⟨p,mem,y,x,hx,val⟩
    rw [h.2 p mem y] at hx
    have e := Option.some.inj hx
    simpa [e] using val
  · intro bit
    obtain ⟨p,mem,y⟩ := h.1
    exact ⟨p,mem,y,src,h.2 p mem y,bit⟩

end PCX150.Bands
namespace PCX150.OrbitCert
open PCX150.Orbits
abbrev PermID := Fin 144

def asPoints (s : Nat) : Set Pt := {x : Pt | s.testBit x.val = true}

def flipEnd (e : Endpt) : Endpt := Fin.ofNat 36 (e.val ^^^ 1)

def dr (e : Endpt) : Act := Fin.ofNat 48 e.val

def pa (e : Endpt) : Act := Fin.ofNat 48 (36+ports[e.val]!)

def board : Board := ⟨fun e p => (seg e).testBit p.val = true,flipEnd,dr,pa⟩

theorem endValues : ∀ e : Endpt,
    (flipEnd e).val = e.val ^^^ 1 ∧ endEdge (flipEnd e) = endEdge e ∧
    (dr e).val = e.val ∧ (pa e).val = 36 + ports[e.val]! := by decide +kernel

theorem stepToMove (s : Nat) (a : Act) : Orbits.Step board (asPoints s) a ⊆ asPoints (move s a.val) := by
  intro p h
  rcases h with old | ⟨e,inGroup,dir | ⟨port,act⟩⟩
  · exact moveGrows _ _ _ old
  · change dr e = a at dir
    rw [← dir,(endValues e).2.2.1]
    exact directGain s e _ inGroup
  · change pa e = a at port
    rw [← port,(endValues e).2.2.2]
    have ready : enabled s (endEdge e) := by
      rcases act with m | m
      · exact makesActive s e (incFromPositive s e m)
      · have f := makesActive s (flipEnd e) (incFromPositive s (flipEnd e) m)
        rw [(endValues e).2.1] at f
        exact f
    exact portGain s e ready _ inGroup

theorem moveToStep (s : Nat) (a : Act) : asPoints (move s a.val) ⊆ Orbits.Step board (asPoints s) a := by
  intro p hit
  change (move s a.val).testBit p.val = true at hit
  unfold move at hit
  by_cases sm : a.val < 36
  · rw [if_pos sm,Nat.testBit_or,Bool.or_eq_true] at hit
    rcases hit with old | new
    · exact Or.inl old
    · let e : Endpt := ⟨a.val,sm⟩
      exact Or.inr ⟨e,new,Or.inl (Fin.ext (endValues e).2.2.1)⟩
  · rw [if_neg sm] at hit
    have accumulate (ls : List Nat) (acc : Nat)
        (ok : ∀ b ∈ ls, b < 36) (prior : acc.testBit p.val = true → p ∈ Orbits.Step board (asPoints s) a) :
        (ls.foldl (fun x b => gain s a.val b x) acc).testBit p.val = true →
        p ∈ Orbits.Step board (asPoints s) a := by
      induction ls generalizing acc with
      | nil => exact prior
      | cons b bs ih =>
        apply ih (gain s a.val b acc) (fun k hk => ok k (List.mem_cons_of_mem _ hk))
        intro m
        unfold gain at m
        dsimp only at m
        split at m
        · next active =>
          rw [Nat.testBit_or,Bool.or_eq_true] at m
          rcases m with m | m
          · exact prior m
          · have hcond := Bool.and_eq_true_iff.mp active
            let e : Endpt := ⟨b,ok b (by simp)⟩
            refine Or.inr ⟨e,m,Or.inr ⟨?_,?_⟩⟩
            · apply Fin.ext
              change (pa e).val = a.val
              rw [(endValues e).2.2.2]
              simpa [Nat.add_comm,e] using eq_of_beq hcond.1
            · rcases Bool.or_eq_true_iff.mp hcond.2 with c | c
              · left
                have sub : Inc (seg e) s := (incIff _ _).2 (by rw [Nat.and_comm]; exact eq_of_beq c)
                exact fun x hx => sub _ hx
              · right
                have sub : Inc (seg (flipEnd e)) s := by
                  apply (incIff _ _).2
                  rw [Nat.and_comm,seg,(endValues e).1]
                  exact eq_of_beq c
                exact fun x hx => sub _ hx
        · exact prior m
    exact accumulate (List.range 36) s (fun _ h => List.mem_range.mp h) (fun h => Or.inl h) hit

def rowP : Array Nat := #[0xbdab49ca307b9ac5a928398a418820,0x8c1ee6b2f6ad2724a16a31c6229001,0xad2f694d6a4a0e68c1ee6b08508062,0x5a92839ab4bda537ba306342021443,0x7ba30635285a8c7bdab49c843004a4,0x4a16a31dee8c18dad2f694c0110c85,0xb5e72ad2116b1ee290620816a4a0e6,0x845ac7bad79cab4188a4005285a8c7,0x9cad7a54a418820845ac7b94b39928,0x2906208272b5e956b21173ce652d09,0x6b21173c6229001b5e72ad10931d6a,0x188a4005ac845cf9cad7a54c74254b,0xa5653bd94b399282142018a307b9ac,0x52ce64a29594ef60808510dee8c18d,0x94e95b5c850806252ce64a2116b1ee,0x2142018a53a56d73994b425ac845cf,0x3994b4242021443a5653bd9cf63630,0x808510ce652d0994e95b5d8d73e11,0x73d8d8c10931d6a10c01292f6ad272,0x424c75a9cf6363000443216b4bda53,0x635cf84443004a4424c75aad79cab4,0x10c012918d73e1131d0952e72b5e95,0x31d0952c0110c8573d8d8c29594ef6,0x443214c74254b635cf84653a56d7]

def colP : Array Nat := #[0xbdab49ca307b9ac5a928398a418820,0xb5e9594e1173d8d52d0931c8510c01,0xacef2b51ed8b20e49d665206128082,0x9d657a59af645d03a4cb4282301444,0xa4ad3bd5cc8362f419475a440204a3,0x95276add8e6c1f1320ea4ac0209065]

def rowA : Array Nat := #[0xbeeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xb2baafbada689e69648a382179f4503ce34c2ca2481c675c6da6585d65544d21440c2040,0xbeeb69a27b2baa696475c6da6588e28607de5d65544d241138f30d1440c20402ca2481c6,0xa689efbadb2baa696471d69b61941138f30d1440c20408e28607de5d65544d22ca2481c6,0xb2baa9a27beeb669644503ce34c8a382179f2ca2481c671d69b6191440c20405d65544d2,0xa689ecaeabeeb6696441138f30d71d69b6191440c20408a382179f2ca2481c65d65544d2,0xbeeb6caea9a5929a278e28607de5d65544d275c6da6582ca2481c64503ce34c105083001,0xb2baafbad9a5929a278a382179f2ca2481c64503ce34c5d65544d275c6da658105083001,0xbeeb66964b2baa9a275d65544d28e28607de75c6da65828b2091871050830014503ce34c,0x9a592fbadb2baa9a2759751549328b2091871050830018e28607de75c6da6584503ce34c,0xb2baa6964beeb69a272ca2481c68a382179f4503ce34c59751549310508300175c6da658,0x9a592caeabeeb69a2728b2091875975154931050830018a382179f4503ce34c75c6da658,0xbeeb69a279a592caea75c6da6585d65544d28e28607de1440c204041138f30d28b209187,0xa689efbad9a592caea71d69b6191440c204041138f30d5d65544d28e28607de28b209187,0xbeeb66964a689ecaea5d65544d275c6da6588e28607de10508300128b20918741138f30d,0x9a592fbada689ecaea59751549310508300128b20918775c6da6588e28607de41138f30d,0xa689e6964beeb6caea1440c204071d69b61941138f30d59751549328b2091878e28607de,0x9a5929a27beeb6caea10508300159751549328b20918771d69b61941138f30d8e28607de,0xb2baa9a279a592fbad4503ce34c2ca2481c68a382179f1440c204071d69b619597515493,0xa689ecaea9a592fbad41138f30d1440c204071d69b6192ca2481c68a382179f597515493,0xb2baa6964a689efbad2ca2481c64503ce34c8a382179f10508300159751549371d69b619,0x9a592caeaa689efbad28b2091871050830015975154934503ce34c8a382179f71d69b619,0xa689e6964b2baafbad1440c204041138f30d71d69b61928b2091875975154938a382179f,0x9a5929a27b2baafbad10508300128b20918759751549341138f30d71d69b6198a382179f]

def colA : Array Nat := #[0xbeeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xbafb6bb2aa299e59a48608e27de6da75c6585545d64d23ce45034c2482ca1c60c2144040,0xbedbacaaba67a269258e27de86075c6586da5d64d255445034c3ce2ca1c62481440400c2,0xb6fbaab2b9e9a249a57de8e286065875c6da4d25d655434c4503ce1c62ca2480401440c2,0xbadbebaaca27a659268607de8e26da65875c5544d25d63ce34c4502481c62ca0c2040144,0xb6ebeaaec9e8a649667de8608e26586da75c4d25545d634c3ce4501c62482ca0400c2144]

def inverseRow : Array Nat := #[0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]

def inverseCol : Array Nat := #[0,1,2,4,3,5]

def applyP (rq cq j : Nat) : Nat :=
  let inner := (colP[cq]! >>> (5 * j)) % 32
  (rowP[rq]! >>> (5 * inner)) % 32

def applyA (rq cq j : Nat) : Nat :=
  let inner := (colA[cq]! >>> (6 * j)) % 64
  (rowA[rq]! >>> (6 * inner)) % 64

def PF (o : PermID) (x : Pt) : Pt := Fin.ofNat 24 (applyP inverseRow[o.val / 6]! inverseCol[o.val % 6]! x.val)

def PB (o : PermID) (x : Pt) : Pt := Fin.ofNat 24 (applyP (o.val / 6) (o.val % 6) x.val)

def EF (o : PermID) (x : Endpt) : Endpt := Fin.ofNat 36 (applyA inverseRow[o.val / 6]! inverseCol[o.val % 6]! x.val)

def EB (o : PermID) (x : Endpt) : Endpt := Fin.ofNat 36 (applyA (o.val / 6) (o.val % 6) x.val)

def AF (o : PermID) (x : Act) : Act := Fin.ofNat 48 (applyA inverseRow[o.val / 6]! inverseCol[o.val % 6]! x.val)

def AB (o : PermID) (x : Act) : Act := Fin.ofNat 48 (applyA (o.val / 6) (o.val % 6) x.val)

theorem fullP : ∀ o p, PB o (PF o p)=p ∧ PF o (PB o p)=p := by decide +kernel

theorem fullE : ∀ o e, EB o (EF o e)=e ∧ EF o (EB o e)=e := by decide +kernel

theorem fullA : ∀ o a, AB o (AF o a)=a ∧ AF o (AB o a)=a := by decide +kernel

def pairs : Array Nat := #[230,32,328,130,361,163,428,98,526,160,559,129,494,296,556,358,525,327,626,164,724,97,757,64,692,362,754,295,723,262,758,560,691,493,658,460]

def fstP (e : Endpt) : Pt := Fin.ofNat 24 (pairs[e.val]! % 32)

def sndP (e : Endpt) : Pt := Fin.ofNat 24 (pairs[e.val]! / 32)

theorem segmentPair : ∀ (e : Endpt) (p : Pt), (seg e).testBit p.val = true ↔ p=fstP e ∨ p=sndP e := by decide +kernel

def permLine (o : PermID) (e : Endpt) : Prop :=
  ((PF o (fstP e)=fstP (EF o e) ∧ PF o (sndP e)=sndP (EF o e)) ∨
   (PF o (fstP e)=sndP (EF o e) ∧ PF o (sndP e)=fstP (EF o e))) ∧
  EF o (flipEnd e) = flipEnd (EF o e) ∧ AF o (dr e) = dr (EF o e) ∧ AF o (pa e) = pa (EF o e)

instance (o : PermID) (e : Endpt) : Decidable (permLine o e) := by unfold permLine; infer_instance

theorem boardSmall : ∀ o e, permLine o e := by decide +kernel

theorem boardRenames : ∀ (o : PermID) (e : Endpt),
    (∀ p : Pt, (seg e).testBit p.val = (seg (EF o e)).testBit (PF o p).val) ∧
    EF o (flipEnd e) = flipEnd (EF o e) ∧ AF o (dr e) = dr (EF o e) ∧ AF o (pa e) = pa (EF o e) := by
  intro o e
  have line := boardSmall o e
  refine ⟨?_,line.2⟩
  intro p
  apply Bool.eq_iff_iff.mpr
  rw [segmentPair,segmentPair]
  have inj : Function.Injective (PF o) := fun a b h => by
    simpa only [(fullP o a).1,(fullP o b).1] using congrArg (PB o) h
  rcases line.1 with ⟨h,j⟩ | ⟨h,j⟩
  · rw [←h,←j,inj.eq_iff,inj.eq_iff]
  · rw [←h,←j,inj.eq_iff,inj.eq_iff,or_comm]

def symmetry (o : PermID) : Renaming board where
  pt := ⟨PF o,PB o,fun x => (fullP o x).1,fun x => (fullP o x).2⟩
  ed := ⟨EF o,EB o,fun x => (fullE o x).1,fun x => (fullE o x).2⟩
  op := ⟨AF o,AB o,fun x => (fullA o x).1,fun x => (fullA o x).2⟩
  cell e p := by
    change ((seg e).testBit p.val = true) ↔ ((seg (EF o e)).testBit (PF o p).val = true)
    rw [(boardRenames o e).1 p]
  mate e := (boardRenames o e).2.1
  direct e := (boardRenames o e).2.2.1
  port e := (boardRenames o e).2.2.2

def levels : Array (Array Nat) := #[#[0],#[192],#[1472,212,12480,204,82112,225,12583104,2621632,195],#[4032,1512,13760,1484,165312,1490,50624,12584384,1312192,1475,12500,82132,164052,12583124,1310932,798912,12528,5255360,3158208,8663232,12495,49356,135372,5243084,3145932,8650956,2621644,41164,10567872,82117,8732864,4800704,82115,73953,8650977,4718817,12583107,2621635],#[16320,13800,165352,1530,50664,12584424,1312232,1515,13793,177600,13778,62912,800192,13808,5256640,10499520,3159488,8664512,12596672,2635200,13775,13780,165324,50636,136652,10487244,3147212,8652236,12584396,198092,2622924,42444,1312204,21964,10651072,165317,3311040,12748224,1476032,165315,50642,1495,3147218,12584402,1312210,21970,239058,8701376,12633536,2672064,1361344,50644,12625344,12604864,12584387,12584404,12780992,1312195,1406400,5255380,10498260,3158228,8663252,4731092,12595412,2633940,1323220,5325012,10567892,3227860,4800724,12665044,2703572,1392852,4882644,12746964,2785492,1474772,12624084,12603604,12779732,1331412,798975,3158256,8663280,5255375,3158223,8663247,5292236,5378252,10621132,3281100,4853964,2756812,1446092,5263564,3342540,3186892,8691916,8671436,2662604,10567875,8732869,8732867,8732897,4800707,4800737,8847585,8671457,12779715,2662595],#[16353,802752,16368,5259200,16335,177640,62952,5256680,10499560,3159528,8664552,12596712,2635240,10651112,165357,3311080,12748264,1476072,165355,50682,3147258,12584442,1312250,22010,239098,8701416,12633576,2672104,1361384,12625384,12604904,12584427,12584444,12781032,1406440,62945,5256673,10499553,3159521,8664545,12596705,2635233,964032,177648,5420480,3323328,177615,10499538,3159506,8664530,12596690,2635218,62960,62927,62932,800255,10499568,3159536,2635248,5256655,10499540,3159503,3159508,8664527,12596692,2635220,15218127,10651084,3311052,8816076,12748236,2786764,1476044,10536396,8701388,12633548,2672076,1361356,3282380,1447372,10528204,10507724,3343820,3188172,3167692,8693196,8672716,12625356,12604876,1508812,2643404,2663884,1353164,10651095,3311045,1476037,15369669,3311060,12748227,12748244,1476035,8701394,12633554,2672082,1312215,239063,3167698,3384786,12604882,12821970,1570258,4957650,12633556,2672084,1361364,12625347,12604867,12604884,12780995,12781012,1406415,6124992],#[802815,13909967,12645864,11961832,3311085,185837,15369709,3311100,1476075,1570298,8713697,15906240,8041935,10548720,16577999,2684372,1029631,15414735,15443415,1570271,16610767,6125055],#[1015807,16700909,16580559,16578047,8369663,15709695,16774623],#[16744447]]

def witness : Array (Array Nat) := #[#[0x440064010c0188042006000f8010003d003e00f000f0038001c00dc0068036001800b000d002b003200a800c0026001000940038024000c0050001001300020048000000000000000000000004714303ef3ae36d32c2eb2aa2692281e71a61651240e30a20610206],#[0x70e021c1838007060c00190029f055700780c1c28384060a0c101818302340a6415ec01803010a02100028004000600080408001001002000000000000000000017bbcdeb20c06f6ad2728c1e0705ac5a928398a408c0205],#[0x61000202038107060e001c2030306060a0c10201840206060c080830006000a00100818102000600080008109001274500000400080000000316b38bdaa0082809ca307b9a0081805a928398a400c0205,0xc38007160d261a0c34006960c2c14582c186030b06144c30985130b0018002c0052b867b0c9219b43010924124e040408000000001800016717b56869824789205785c76818659544485010006205,0xd26184ccc286120126004d5c2801201220044008000f7b110e20345060a011400283410602010400500010000000000000008ec4ad26090a30785c16b1601888a4a087184061140105,0x4d809a0036006938c2712013200655c20018012e005c1880096002d022000a880b0e1692192030083000600509c0800000020000000e2f6ad26290e30791c56818258d49414e4300201804105,0x1c7d88d071e003e0078f0d001d0038285c508831706230a1dec3878c0e160230005ab8331061e103900084004018080810000000000000410726c16e0b0ea7a4e5183dc009dac32ca4028291a00205,0x1451a89f5032a04d411281e00460088f0d839d202e008528b4087302c223030503140e400215b430103480c4a255c1000001800000000e2f6ad26391620809e1710e06818b51d20309022906105,0xc235843b00d600eec89d11391834446488c0c291e103ca07838f27120c240234043800d000ec0900121f855d0902146c20000000a00000026717b1401184620541404c6290a2183dcd62d4941cc405,0xc6398c4420d600eee8dd0c831b3446d06cc0ca99f103ea04d88d001a0c260238044130d020ec4940129e835d05020c641000001400000002670505ec1184021d4141cc0290a2183dcd62d4941cc405,0xe940528325004a0c9001215a02a400e8019012a02440028001015140628485000a128901124824004800000000000000569394600789c7385a3618c05894528523410831040005],#[0x20802f008000b801f802d007c001401e80040078000c01600020056000401500145226a449480000c4118820000620d2728c1e0180400b9ac5a920180400a0e6290030080105,0x1830006080a0414182800508080c1018104010602041000200020202041c00380030606514800084000800100005252728c1e0085c16898358d400852140ce2308000940405,0x4c00900110020003c007000d001800280040001001600e800a80093b28005000008001000000004098a388a00101e0705a162d401006032468284070100105,0x210040007c00f001d0038006c00d0019061a006000b80160210105018181073aae0051500080010020000030ce5183dc0101a06116128d4010120414e43002400c0105,0x9809280250248009001180220832103c18c830f022c0058001452e021200240938027360600b81001c00080000002418aa5a1a60382408c1ee6b160080401040a324a80100305,0xb4016012b005604a80150029064604a0014010a001475580018414062800b96001400080000000314601785c0281a062d4419040081204002238cc400c0205,0x32006200c0017832a0648106c208831a062000a008c00170008042400580333a284948d81880010000004030826491620106010bdcd62d40104010240829c8608c0105,0x1a8034083e0c7409880300056009408f011300380048002803808160cb801b803608128e516800400080e0000041d0d329c00080c01145214420082007b9ac5a9280100305,0x435066a0cb42108321026400c8016002602400080003033a08160c2c09c8039420600e97801c000800000004184132c8c0380401445033ca0081c06b16a0a4280100305,0xce401c8437026e0cd801b0433064e10540998027022a00a418a00143aaa4948003880010000000050460f735801056108d404908010501090e030c600940005,0x2100413314010001f803e575000f401e003b7b651ad43450608002a01480408000000001000008e047b9a26016a48501384221808628481184010004105,0x49312c012002380462c7aae5c022804400860cee15abdb049084ccc3cb0608270804500410000000000800128e7289201781cd60566509211810721881008620002505,0x4d0098012c025163f2c8c0d1019e42347b62b261b5787960d1464212599484024e2d54100800000000100800966691e22801e97202468d89580aa2900838cc30004105,0x27b0b5009cc0d09a613412690012c023804000a0ba920552790733400dc91b0d963f144e1804280000014028000252728a808100491986718449801e871da660561000a405,0xb27b4b5069ec2d49a6934226920134024804200a2be460cda911763604e491c9f081810521410280005000028000228149ca28100691986710449801e871da660561000a405,0xcd61fac5758c6b1ed643ac19183030346060c011801480060000000000009aa3658293548b0a880192438a09880908084,0x36a0654335a194c06a0054575a014c7218d437b4d0e98346860d011a01480068001000000000008e047b9a06096a48501380201888628481184011040105,0x66ad5d58da21a86f6821d006bc0c7602f001db09c3d381a3c307008f001c01546060000000000000109005344e200cf0305e10380220cad62caa204091a04105,0x728c6d1005363591ab43600640017a00f4aab009000207870f4e06920c240159ec300000000002000088a324600200a8004a123dc611c606b06b1040a3a4c105,0xfd62baa00a8f6e436106ba0c8202fc01f1e1c61391a84309801100ae725064600000000008000110e5004c38040f38802338032042d2b16a208090a06205,0x36b8657335c195806b8057575c0159edd43ba01aa015434a06140128014800a18a0000000000000e047b9a06096a480c0284201888838481180011040005,0x24d848b09d4cc6c185836a6036002c0353312e605d24ba4178174025c00bab822704dee83c10000000c0004000a66a90224815e371da86096350d2102007000c22888105,0xbc01753ab005c00b6016802c83544950946215819ae8164605ce2baba700301a509c0800000020180000964189e0279883705a16016238c062a829400202004105,0xbf0d753adaba51b46036802cbda100b0211051db0923d3a90bc606809900aa1050b420000000400000114891340e120cef315c10008168d8b50525400401802205,0xe100c201806d1b1a601b6016cda9a4b0109090c03a4005601340068f0e9e9d810cdeb8b410000000e0004000cc921c6021888100481181e5719a262d49400e0300a105,0xc601893b09fad3c3a0370c2c08490e8eae91259243138aec248646c0b90036015cb40800000020180000c8b1240a278c0971c88280826a4c362167500203004105,0x31cd634cc52006f005d81409160423074500c8c048f4ea7a45022028000f0c8d5d1e195c9c2800002820000000ce4a04524494624186740062809ee69d86580202808105,0x659b08c182000e300c4018406fc35d18a89ea940d80648174028400fae99312e1a50b4280e0000200000009a403c604795c3685815814310c2612428100202808105,0xf0f189e623cae788e20e44883cfa78562074407880110732876500ca423c6478b8f0c1e143c0878000000000010730a9320ca0904912a0102bc80105cd1b06702c4a0a40605,0x77b8627d8ef076670b801995cf9ede217832f0999a4331cca2e6428cc41302281851f499800000000000208e5180de0701ac580c150922090602a0a2004272084105,0x666eb6c2ac1acbdb60f961d1c065163d3f5678795cd18990f4a01a00338613022116b86478000000000800520d2701942504084cc128c0021a02f3b8c50346c0ac4405,0x1fab3d40e17052f83da7b6e1f3045287490c745cfc0232b9b00d40890034b11e8e3e7450607000000001000062080118861016679447003c0109c4e0b58602d492a02405,0x76a62c81da0034806700cb0ae0aab87ae14aa029c999811506aa625030a000000000010078f3e8e0dc4050311182c88a3900032a1804,0xd77d4331de63dbe0f9882f99a88362a15c1ebc331485008a1b589dd7572a505430a80000000200000082274ae0a195e2719a1611020096a4a0e0018012906105,0xd919840359fae3bcc616446624310c82787d85280682b4e7159b54011a816c32515c8000001c00100000c9310c103788004902640420700a2685803ad462906105,0x8fc6a18d0361fae3d429578c2d08cb4864190803517150454e060eebb113816e30515c8800002002000000c8311c062019e07146708420201a260560429273148105,0x186830b860a0c0e0d34196810d01da003698560cac4ad805b1236006c7eb86d700000010000000041ee6a0020902000c05004206016738541498c520c4005,0x18e8b1ba84a0c0e0d35346410d4c59003718570cae4ae405c9337026e7a5064a00000200000000041e8039a20900108c05080016056738140498c520c4005],#[0xb40804180030004000404046ee5408b8117821ab7336e0010000193a2b000190b232968181038e0dd48202834282081810084,0x18002c00500090010001c0030022356e00dc002900180100008a185148114138b0a888190120809880108084,0xc07001102200040087800f001a1020184456e003004480090105001c00141021c003000000005241e170da03818058940481003002018002188200140405,0x5c00b0115002a045000a030e0226004db370137003000dc102218900000008ee15950204840b81808103028009888008084,0x38006c00d0019061e1028184980e00260c500031a3727244adc082980180080810a72686018d88ad3494018b883028120090084,0x3c007408d801a002004300058021080c008000f8015063082dc20290008388002a736938010b08101818808e0d9d149400a8204,0x83c0c78f07011c0038004419114a02840101800b0317004431b818340010008003b10706a840a881e22a0010d8d24991900b8304,0x5c80a10042002400c7c00f959206244a48a1b8137256e00dc0092182181000086e5d4c0213910b01888212910801888108004,0x290050009c01300250048008c34281783b7e00dc000100118000008a9a5950104840b8b088102028a01880808084,0x356802d0d5800b0015802a0d0a001403706ee005cb810e8200800000821902008600098d9514c38008082030102898104,0x6600c80188030005e10ecede806e0c4400dc040100180000008919d248104038b0a888102018189080808084,0x11e1a3d1c6ee8f6800d00370023000d1ed801b47b5006aa810e821a8000000821018286800e0d9511c980080840380830a0104,0x35b58f6a0ca801523b53b6a00dc000a01000004b52a610a39a51010831859041043,0x7400e401c04240ef000d0efc002b02f000dc001300900000008a91d220302048c0b808101828989080808084,0x1a9a84248f6a00900039db5466a10b0016043b007676b800188008000001933a08a80860292905b8082051a4b104018104,0xc108216003806551ed00178025001000f035633180084846004198008000012908a1e981808090165d008204c238903028104,0x396b6a00c0013042c007c00b4ed7003d42311bb8004a00100000831912a23820908191bdd010a88cac11800b0184,0x35353bf000c4377002706551e8d1da803f423066dc005200100008009912b0a020809191dd301088acc39180088184,0xd4d4efc00320050002d821042c476a1ab402047860084cc616810800840000211e98c00083039093e3008281dad0904820104,0x35b500751ed8019802900180ca80209dae0084cc617020800800000210d80188082819091d2808004c038903020104,0xfc01e803b006a01e0ee1002e008400dc002138200000008329921010484010388820183098a800808004,0x82010001f003c08761bb8edd8178336e00dc01b2001000000008185148211140b8b088111100a89880900084,0x90011c02300450088010c19c456b36281e140070112088400b8100380100800118b70eae03858524891c010302902280a018084,0x9a0130025804a6fdc012419c9b14087e0c503c280353a7e4e495021001000000098706a60105852c9b0c010380322a000808184,0x9e01391fc043d0246c108d8a1dc2005c4edc20a1801810080092512b281888c82938c01880a3a03010088104,0x288050065601240218125422a10b8209031860840108282180100800020e35991818303002aa5010104ac03808020084,0x1500298052009c01100938334062684551a1042e007adfb8b492002010008016ae3d9820a88329983820d089cb4010080104,0x5600aa012802281260656845401fa3f8086a4edc2099801820080125ad31901880a82910b01888c9403820090204,0x2c005747f0012c0230129086a0080021042e60840c6150088010100002a6358900083018899ad0101049c0b820828204,0xb201491fc01230f0a0c54190304208847709501081900800020bd1181808404a99124010383132b00a820084,0x2d004c008e04a002d83340656c10808fa34200840c615018801c100002163c0288083038891a30182859d0c810820104,0x2e005700aa014c028033a00b6110820a841f3a7e00b950213010000001886032d810504a40a9b81008028a1002018084,0x2e0059009e013402404780668845418b94a0086a01e1541b80080800018886359038282a2911b008504942080a018084,0x2d005800ac01500289b14024601e018b17a0006a11e1502080280000019028635808504a410988283800ba3002018104,0x8860d0c0a18043001a01806d60cac06c01eb03562117362e0174100c8030000008891a3ac04818188746b8301010862da5008084,0x2f815e00bc10bc197c260362c01740070060025c00b8101180380000290b60991818585028c94038303282120a010084,0x1781a481450fdc01106d635b400d6018508b802d868460dc007900100000b288a1b94010a086a1463810988b05d4980a8084,0x11400a380460020d4d00301b1300da1ab403180621b590909682080080000321bcac0000848141690880838030605ad020184,0x6b68d4d002f845106a20520024001102c8019108bc51800dc6c61781080100000132881f1e8082026258d08180809049413830284,0x6402c601880b0843c0fdd15b402e802e068460dc0092801000001200d9d14828c089a039101098890031980a0004,0x19c033006506bc0cf421f9d3d00dc48dc009980100000808911c94018b888b02028189080129a10088084,0xda0034125d266e017409b806906d248dc01b9001800000004c1919038b08828200038b088282000080004,0xd405940988030422c8d08035842e066a48dc00a280200000819532121828b080b0181028c8882141b8098104,0x36306006d2059c0330133006410d400a806d085c8f09601880181800010e29d98008281512120808484018b932010084,0x6806f0845800b0435066a01b9600e0080000d1051630a2fb1c40820828b303083,0x16c00d805a8035035f08f0005c1bc062206d001b9601200080000011008d8d01848413aa2a01808080a1b1a810104,0x16b00d601a41b0016d00da01bc00c0442068401b96022bb0000000190883830285854c21a1000080801098a018104,0x1194225034e00ca05380253523065a04b63d19e373a5c64dc00c900100008809a3a32b810809eb63db01088852cac20088184,0xdac22a835236260198025801a00e0d48d8a147861bdc74b96820800800000311a9a000082816a62d8808500482041b830104,0xd3b81b59d7806a6019c026001b0f5a01c4196c7b662847adce09880118000828869831008a08e258d2010808481341b8a8084,0xd3b81b5045606a8053c026c7b50038d48c039006e3a6a78dcd8c00018000082080169a800a88e0d850010808184943b0a0084,0x7200e201c01b0833e087e64dc01b1d42025c48dc9c9180180000800a5a514818a88943303818a880911020080084,0x8da115c0368057003a36b4356847300e6d41a12131428f0c74b968009808200003b1281a0008284f4eaa08084016418d95038304,0x45c06b201b00ad0058003d1cd9a9aa3b5362601d403a036e8f0ccc616c018008480002a0410c800838198fc738083016b60d95028204,0x7400e605c4031014100ec0da421b23c2008437b800f9001830000285a5130010a08910219818c889c039100a8004,0x3a847300e0018c0200077086a8eec1b48142085c7edc0100802838000026359b8008b0919110082888d1499840080204,0x1b6845b00da056c010b5368e6c01dc03b3f048484c10968208008000002a339080008381e1d991008300504808c028204,0x8ea0dd00b9006406f010d8034033500f078dca103001000000201051ca830a89a08299810c089b811100a0004,0x1100796a6ad6d508c017800f001b9782380000000019000a8b03820212131a8000808898104018104,0x1ec63364c3615f33dcd87b2370c3578624087630dc04400000001000898a5d29084c28a880891823b0a09880801084,0x305757cefb3e26e0dc333662cecf948625007832dc0438000000100809a28b3958252080b8891834c0a89880801084,0x46ec3d8c370ccd7bd9c0d6400f8f9486282a7ac7b80448000000290009a3544bd0210120c8891843d9309880802904,0x1fee0ddcc36236c1f29336e32dc314800001000870aaba0996692824a1c41050443,0x3fdcaf95ef907783d8cc15e3ed06b33b7630dc045000000110000a09b1290054b0a88889101c2098b880801084,0x176f40ea0d60189982bb0d84f7a370e34f00403fdc4e8804580000081800123a4081c03e292b2891880da3514880801904,0x63dc66c182bc0d48de8baf4f630627008232dc0510000000100009d004c1200aa088a08a9803b0809880801084,0x63dcc36237a99b183ac05e0f9486b15f7e30dc046000100028000901d3cb082120a08889381b40989080802884,0x18c83d90c3b15e5c2ec7b9642e06120ab80c4804dc046800000008008925d1a8a04c28a880a0903b18988090800884,0x18c75799116885c0caf49327ca031293991784050828400000000808922db940882d288341b8a049131081a1800904,0xc7662ec9ec82170f668ddc249a0f907ca0314168f2a7e04fc04780000000900922c5b54d82900abd1e8a064c3b081a1800904,0xaf28f643df00ef07eca3ae249b0f8e59846121d42041e0508bc500000008800ac218b48814ee08ba02099459bb08050100a84,0x18762bc985e863109ce137121707ec8313009081d605093c480000100800ba648900a9adb0b03428a1d148108024180b84,0xc76606939eb3d90bae43e2062727344dc0657c29e012205093c780005800800a9ed81888924d0a05324b91e4040803b100a84,0x63158ecb0ec85eb07549cd9f2818481f14108137202f0befd485000080010011886e2dcb238b9b834308a54a829000c201184,0x93c5ef89fb33d8eb339c2707c70d663094c9297898cdac1b4104800000110080a2b53d9005cd40ea9ac9026208439b1801084,0x192d306d84e6e7383581fb3324e9ef8a4e006381d64708106000001018280b645901b838888a8a38d03132849242001884,0xcb71836a7e18ce6ed9575ec0d3324c1f100b11ec7014444eca4d800010020080b6902e3990c188d980c5113b084a810102084,0x3e2b25a65b879e1da506b1184b0874a4d127802c8a4fc105800080010081882d2d9305cd448b23128398884623a001184,0x347384e63710fd82ec481609ec035839c4318811cc939b09e8d3c5a7804f0780070280021187f05601debec98e5b04514c3b090802a04,0x30f585e83714fd8afc583629e98c93bb270c4c01d493a301d8d3c5e7804ef800070280020791f051865eb9ce8e5b04514c3b090802a04,0x217a30f484e6c1cd3deb9bd00ee49d8b512eeb81d64e88050800000030002e5d480120219b9c18a1880914139088803284,0x46f569eb0bd587a817824f052860dfa93f767ebefc110800000038003005d4c220109111a2a0881a19990a8a803b04,0x19ee3fdcafb98f73dee87dc32dc61b86b70c6e02dc01baa0190080000121add020acc0282000109bb0181000080004,0x2ef85ff002e401c9ecb3c96737dec8c3df4b44c7b86c68008000010009b1ba823a3100808009292a19595080c8c104,0x39f07fb8efc1e4b61971b455f5063a10f0f79065b8000000080001ba8530c882380030021a10a8101800104004,0x67b55f6bdf887f0377431d803b0d84030861ba800000000002011489808c10280001a093b0102000081804,0x73806eec3f857de02f401eb1ee0d841909ed109000000300008914c0100b0008119a0a9039918801a9a004,0x7fb95f5bdf889f0730837c003f0c84030865b80800000800010a0289c8841000080190abb0201000081804,0x43f8319a613122500c91bbeae409c7c1f8087edfe0544000001800810c8d58311b8ab431021ad2c88104001a3a1084,0x57c43781eea254e85cc613061d043d61841b089c4800000810018aa08911a11508c980219104298bb008101884,0x59c6378073c3ed6309a939512130420a841aec9c5000000810080920991999252080c8419903b2891008101884,0x69a29399bf68de08ba4013a04e1b3944841b089c40000008140009908b3a0a1400908852b9021c993008102884,0x24e74a9f1d5582140f230928be061d2ce13b841b089c3800000918000b20894103a988c0a0211183b58d4808281084,0x30949f7807c34d1819a39e214d2ec260841b089c5800008818000a3882110b29889088399183548aa008401084,0x69a3073e178004f1874c3097de293f44841afc9c6000180820000980d2abb1121090b0322a0499894008103884,0x43f885cca19476f2fd083f0613006830c008f018ecb4d98000080000881b5d19121bc0c080138a2b292c8808201084,0x57c07948f6945528ba49f493a900d200a473818c8c0912d2237803c8800800807002d25a009e1ef046ce1235bd184840009393284,0x22a944f84fd6a15406a00531bbcc790ddcbac281441b08b480080010018009280e31095980b08829a189150ca010403884,0x44f83fd503e13f5465500aac22d76498c90df015e0b458080010080014a80bab5082588c28521a149c389810083104,0x8bd6a5593b5a0ea7784015a07c30c0387e1908b4618000081000081a251ab9030888983b091214940808102884,0x42700af09fad8f240f801f0016d8202ec2507e1b089d0800000800000bc005a2a35189208841918b94891008302884,0x315b88b614f08610cc21784190809e00000002c12da83d30906360dc924c132a003,0x18d057a6c99d238a0e717a0fb04b1f44420c8404f465e00000002800a11581b8ba8510014880919ab2308114188a04,0x7fb4f2107ed61db17b4c61163e1984190809f00000002001008913c84a040988b1100c2a11b9008b298004,0x7bec1f892389fed3cb6190587680ef577a330809e80000001800093089383981300a2008291508c8042a180084,0x1fed11da7be033c103b04c25984e9db15b8eb662ec61d800000080000100991880dcca9b80020b1088500443b2a004,0x1fed3df0f7dc471a4720ef040ec1359d42577e050861d80000008000010189088259508a80011914984003b2a08804,0x15e261c503883f11e538ca69d4c0a9abbd737a72f465e8010180080001bb00121081b905d001888cc0301a8a892004,0x46d441d69dac0aa30e383821904bb1abbd767e32fce1e90001800000081589bb5001910a3889a80300801caa014084,0x42f661ed09d983b12f601ec49d803b0def3fde67bc3f78000000000005d4c00010119898991189880101008bb2a004,0x43f863f109dd83b92f801f04ddc0bb9ec2318433083610000000000005d004c1010980080089898108808803b2a004],#[0x2f814e1c1404344a589141cac0000028c9200001e49c10818a10008208208000003,0x1e1c2439e40aa817802a80400032a220000164ea18210218020408420000003,0x24387c706090d12f00478725895d02be040003b28918000000891248383028402000081018100800000004,0xf0e8d12aa059c4bd81141c1004000d19c200441057028030c07a18809898081003,0x33200205d4a2e015e02000400053138000022ee228220a08010620610000003,0x12d04d18800105d022638d000400000458c10200223aa22000020c10010c3,0x44e4000485018f1d0e38d002200000090808c00a0b70c4000040c3002043,0x3b208c41847438e3b1c3c3850700000000902c1800802c0120021aa01001003,0x3b20d04d98483103c0c3e38280c0100000584218204100f1210203a100010c3,0x6b1c8c421c71d90461c2838f03100004109010b60904204ac01662a4200a043,0x611c4e407c7098e471c2438f0310000480500e42090420b120166a681009083,0x1d904e1cc2384c7090e471ccc240011008c400d0a0e00967a2ab60984288b00b083,0x6b1d0e391870a0e1f1ccc2574090080000a1c0220841c2184080280ca0020c3,0x2289c6136626d04c0018303000c0c181001000800000001a09090102020004038081818003028000004,0x13818104000800140880010000c90241001000a18000002c09090103830002018082828002018000004,0x2289a31000064a40003c30e00082a38100880180000020a8180c0083001300800182808010938020084,0x4513841c601054a2d81131c001814090306000a508b008039200430a18059402103,0x302100020140a703300c0024100a0080001aa041810803e200084100cb206143,0x129000102a50083c30e00202a381001219000007cc9a08808008418408008400003,0x741c64401822d813a1c00249002488000001273610a00810408200618200003,0x1d0a3a0e11261040c08030504028c389000894000000000939328081800180810082000100808000004,0x820e439c8a2d816c128e38140a060600049113010031400210a18059201043,0x182828100127438100961000004a082608601818010410051401043,0x11c391c7060900128c39c81d3100c004848a81b8c90088134d0451419043,0x441d0a00090020e450183184004009362020926202840165809a60a083,0x8e40f0819103a2056409c8201000000821521000c248410003050000043,0x7499d10300856418870002271042396c0a000800000109a9a00020280c080838083000008118010084,0xe88438e621cc639d071d14501c64105470089108080980a9083080400130022890080a08013881880c,0xc638ac81d0e00124038c0300100410c80aa80186b88201104205340b043,0x28147228c43a1070402211c26380011a1084005062c009657499211246291009083,0x851c6010487238e66120c240011010c8011820e00a2892cc212a83a510140c3,0xd4398871d9415288e388471000400041a22008201001200601401201003,0x820c2384c7300e471c24389c41048640011b1b0092726a8209842888208083,0x428e611d083854a300e7f029c396c090080000e7d58008212410208200082203103,0x1ac700091228d438f0320000800480e32120810cb80269b641011043,0x1a08000a8f1d0e3818725890a02760558030000000000b020004008381912a8a0000001800101008184,0x451189b50e871c76385070000000048281600601a01200211801001003,0x11468200c40280a1400298c88983a9103100222,0x8a0a0e461c0c392c4b0090000902098188028d820820020a0c2003,0x4e1c0450188350e00148e38344900900000a626208028858208011009040043,0x450188350e68209c391c700002000006a1001068818001250400008003,0x1880a0e461c0c39580300000009020081880a8d92000010020c2043,0x13280c50008098e061d0a05e0090080004e1001208204d2800800a08b0c3083,0x809940628263818742817802ba04ec0809000008084010081800989038b010008080800280880204,0xb46268c4018a040e0018ce261c080000086d0200201242e04801043182149083,0x5830e46202c3800643814212f004c0018800000012a0080840181002119888000001038203028004,0x261a4c346000c5c020040e80c600010240c10802a98819202081040051003,0x188040c161c842580300080004e024100228a0dc802288303113083,0x161c0c391871d8c08189625084b0000010a0018419046091a0104004210a043,0x188040e471c2c39084a0000080d00206110410da40104008308b043,0x13c7040e471c103180300182000506c100470a04a4043186810a1083,0xc411871d8c061cc01974090100000e1403208a1c21840801008b003083,0x1a0c3a140c78e00129624ec0bb00001018428801848c98801042003088043,0x3a948f1c0038e80a8006408886e88c8664405c02,0x1e103a2471d8108031e38c801c00000008a30a180238932000020c2040103,0x6b1c0c423c70010471c7638000521a000002331408430a08008220610000003,0x132804518071d93062000347c7420124941164086001a29904000aca820028b,0xc38ec9bc814b128c39e00901800004b005808801848018012099041083,0x601cf005e40830e461c3e39740a160000054a03c1022a210a200180e10010c3,0x8c39186000e00187638000b020000043094010010601620419468041003,0x44211238188278c1f1c2c382063000000225258019241002401068330088043,0x11863a94461c003800610200030812042032c02022230ca09009a003,0xd63a2471d8c461c2c382063000001012258019241002a01060290088043,0x3499990001c8e38000a008000042093010010401408611848041003,0x9e30207090e471c10319c4d00820001402902800a2436080210a10c0083,0x6b1c26513c6000f461c3e38ec60003000012cc0801242801201058a90048083,0x50008868c0620003804082238000812c400020800a22060a6a8082003,0x1328cc40003290e0d18363010040084000036a1820608008c08418028400003,0x521c0c340038d8c00181e24002201840170ea91611c40654a1944b00840c043,0x26514873b8e131c041020722410510180280522a18024420802410502cb,0x10384c7068c1b1800195001000000498a08008a112d48000020400420c3,0xc13280c35d463310082200197009020000483a04208c3823ea2001a058042003,0x828ee381868108521c1039381e0082002e90612322a044b80a289008213143,0xa80548703076620003828090100000c822a208a0804ba10804810003043,0xf081390081c0039500901000008820220800904b0104025100c2043,0x2070e9327100039500100000008820800820924a2000040c0082043,0x3a28cc40f48000e501cde25500b01000010820561800905e010a04a90084043,0x71d0e6f12103954080080000500118008128830082012c80c1083,0x3e200428b48040c0018a43984080000090d508000104208400104b5a810b083,0x1d8e1e1c1039840808103a20044624044ae85262,0x1c26519882a011b181a302809610000088c1a208610055610202220002043,0x3310521ca8042c08408001c0c2428090380000d022c208a0808ba38806c20003083,0x2143630b443f810f12fc0584080000010561400010430440010514d00c9083,0xe8a000e1b18a038006001000108360240164040461105a04804a003,0x85230e521c003818480182020c804400208004301a88b420213043,0x4c74081081c0039500901000008820220800b04c0104024d00c2043,0x2438007040e49120c2550090180000a020220800908d018402650042103,0xa0504c7000e1b181a315001200000088608008611254600002140102043,0x487040e001c0c2550010000000d020800820928c200003040043083,0x1d8e1e1c1039840808003a20044624044ae85262,0x1988000e461c0c2550090100000982042080090ca0108028500420c3,0x383460994501d0205d4604110018b80550090020000001884802401000108093802008018ab002818084,0x1d0e081c003954089000480c808aa61105706422,0x46388870b8e00242c381002010000004263a10208028810218018200003,0x761cea300060b0e36121e2400220280016ca51141144045642944b00880b043,0x13771cec385c7420636122c39381a03800024a0d341945059d619451020209043,0xc1e3034600127d026c25f00801a00076128000020810d218403186585103,0x118e761c10459470b8e1b182c38003d01000140f2a242924149081125a198208043,0x19070a9406224638346001040024180200184800a4110490980c9003,0x40e131c1e308c7010c67123631680b0080002274a8018408a50608401001580103,0x771c6c419070b0e061cd22400450100004c208982964b62221144a00e40b003,0x6440e86040e06182e39084c0000090d00108210410da40104008314b083,0xa2308c71d0c1b1210396c0b0080000512e8018614410618200081201083,0x511c7a41d07288c061c44381863010001042402619051130001440405509003,0x626004d947320e171c74385876028000003022608000049208010051040003,0x4c40009811024200048008124000000480820aa90218002098018010003,0xc4c187230e231c9625084d0000010880204190420d18010400430ca043,0x2420e8502088d8c42120c39600c2000000ca4080204060c1200410053543043,0x189a38e231c1039803400820005024100229204b6022882c10d1083,0xe4500090d8c081c0c4560098000000ca4200084040c1200410053543043,0x1130628004d0848009081c0c3960062800001e80084308258d32000000420c2043,0x9031472281044188820000004360800208c848002698019691003,0xf184e211c6118e02181039680a020000019330010418c484202010053400c3,0x15103a28ca380889e90001e44383c60022001009a800012680f8221241003588043,0x328e3a1c2e38207400020818122a850220404822,0x1c423818880123a181a3234492108000c0c0c008401042410202291143003,0x87918e471c003a34490108000c020c008201042210603691083003,0x118e121c10380870080018200440200c4a82d062,0x4820783111528004408790080001408c800a89126360a0936c1295003,0x6c6078c601c0438009010c0818fc056809801000000022ac3800181808088818101000800093000204,0xa358e0026d439780c20000004009a220218809600411440041003,0xa81140628245000a00000001200820010400030014524c004b003],#[0x1c00080630c0c0000042984000002e0208210808000010600000003,0xde18343060635080008180105aa0000104a000008200010408818000003,0xec02a800006a800e8020000000504000008010c1800003041001083,0xc04000858047008c002801028000004041608000018008408008400003,0x42c00303250048002805011600001081828000020010208008600003,0x298015802a0034004c0090007000c000a0010050010800000004840b8302820001810100000000800000004,0xd08140800080aa150220220440a24088c42,0x2a0c2c00303250048002805010600001081828000020010208008600003,0x1d020b00980028070a0002231800100888088002,0x1b0337060606100c60303014d0074093000c38002100000003028081918180808010000000000200004,0xd2009806c02e8aa80801,0x13044c08e2120c046807e00bc01700338042007400e000880000005d48000800080004038310000002820180800104,0x671088c100024000a04010321000230180802,0x116001007802ea8a80801,0x3884000c000c0010110028040000021183b02202,0x606480c0018100200040220001321100802,0x80c0c64200053a0418000403cc1000001428610828810000008008000003,0x3a84680866102020040801c002a0008231000802,0x1802c205020a48140028000000004600001050010001050010008003,0x58000c0c20180063a049a013003700008000028810868610401000000030003,0x60c0ce21518100692006204200002d9801002,0x4604bc08e814002000110331000220000802],#[0xc000000a0100000a001,0x500180010000a8000040000000800100002,0x320008000800030000040000000080800002,0x40018000800088000020000000101000002,0x10000400c04000008801,0xe000400404000008801,0xe0064003000000a00000400000040000802]]

def pointer (d i a : Nat) : Nat :=
  let word := (witness[d]!)[i]!
  let bits := word % 8
  let idx := (word >>> (3 + a * bits)) % (2 ^ bits)
  (word >>> (3 + 48 * bits + 15 * idx)) % 32768

def cap (d i : Nat) : Set Pt := asPoints ((levels[d]!)[i]!)

def size (d : Nat) := levels[d]!.size

def one (d i : Nat) (a : Act) : Prop :=
  let w := pointer d i a.val
  let m := move ((levels[d]!)[i]!) a.val
  let j := w%128
  let o := Fin.ofNat 144 (w/128)
  j < size (d+1) ∧ ∀ p : Pt, m.testBit p.val = true →
    ((levels[d+1]!)[j]!).testBit (PF o p).val = true

instance (d i : Nat) (a : Act) : Decidable (one d i a) := by unfold one; infer_instance

def check (d : Nat) : Bool :=
  (List.range (size d)).all (fun i => (List.range 48).all
    (fun a => decide (one d i (Fin.ofNat 48 a))))

open PCX150.Bands
def paths24 : Array Nat := #[0xb5e72ad2116b1ee290620816a4a0e6,0xad2f694d6a4a0e68c1ee6b08508062,0x8c1ee6b2f6ad2724a16a31c6229001,0xacef2b51ed8b20e49d665206128082,0xb5e9594e1173d8d52d0931c8510c01]

def codes24 : Array Nat := #[0,5,4,37,44,300,3,43,35,299,355,2403,2,42,34,298,354,2402,19,339,275,2387,2835,19219,26,346,282,2394,2842,19226,154,2714,2202,19098,22682,153754,1,41,33,297,353,2401,25,345,281,2393,2841,19225,10,330,266,2378,2826,19210,83,2643,2131,19027,22611,153683,202,2762,2250,19146,22730,153802,666,21146,17050,152218,180890,1229466,17,337,273,2385,2833,19217,153,2713,2201,19097,22681,153753,81,2641,2129,19025,22609,153681,665,21145,17049,152217,180889,1229465,1226,21706,17610,152778,181450,1230026,5322,169162,136394,1217738,1447114,9835722,209,2769,2257,19153,22737,153809,1233,21713,17617,152785,181457,1230033,1617,22097,18001,153169,181841,1230417,5329,169169,136401,1217745,1447121,9835729,9809,173649,140881,1222225,1451601,9840209,42577,1353297,1091153,9741905,11576913,78685777]

abbrev GenID := Fin 5

def fs (g : GenID) (p : Pt) : Pt := Fin.ofNat 24 ((paths24[g.val]! >>> (5*p.val)) % 32)

def pieces (g : GenID) : List Part :=
  match g.val with
  | 0 => [⟨63,6,true⟩,⟨4032,6,false⟩,⟨798720,2,true⟩,⟨3194880,2,false⟩,⟨4259840,1,true⟩,⟨8519680,1,false⟩]
  | 1 => [⟨3145731,2,true⟩,⟨12582924,2,false⟩,⟨262160,1,true⟩,⟨524320,1,false⟩,⟨4032,6,true⟩,⟨258048,6,false⟩]
  | 2 => [⟨65,1,true⟩,⟨130,1,false⟩,⟨780,2,true⟩,⟨3120,2,false⟩,⟨258048,6,true⟩,⟨16515072,6,false⟩]
  | 3 => [⟨2396745,2,true⟩,⟨532610,3,true⟩,⟨9586980,2,false⟩,⟨4260880,3,false⟩]
  | 4 => [⟨5592405,1,true⟩,⟨11184810,1,false⟩]
  | _ => []

theorem atomic24 : ∀ g p, routes (pieces g) p.val (fs g p).val := by decide +kernel

def rev24 (w : Nat) : Nat → Pt → Pt
  | 0,p => p
  | d+1,p =>
    let z := (w >>> (3*d))%8
    if z=0 then rev24 w d p else rev24 w d (fs (Fin.ofNat 5 (z-1)) p)

def go24 (w : Nat) : Nat → Nat → Nat
  | 0,s => s
  | d+1,s =>
    let z := (w >>> (3*d))%8
    let m := go24 w d s
    if z=0 then m else roll (pieces (Fin.ofNat 5 (z-1))) m

theorem eval24 (w d s : Nat) (p : Pt) :
    (go24 w d s).testBit p.val = s.testBit (rev24 w d p).val := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [go24,rev24]
    split
    · exact ih p
    · rw [rollCorrect (atomic24 _ p)]
      exact ih _

theorem finals24 : ∀ o p, rev24 codes24[o.val]! 9 p = PF o p := by decide +kernel

def verify24 (d i a : Nat) : Bool :=
  let w := pointer d i a
  let j := w%128
  let o := Fin.ofNat 144 (w/128)
  let x := move ((levels[d]!)[i]!) a
  let y := go24 codes24[o.val]! 9 (levels[d+1]!)[j]!
  j < size (d+1) && x &&& y == x

def quickCheck (d : Nat) : Bool :=
  (List.range (size d)).all (fun i => (List.range 48).all (fun a => verify24 d i a))

theorem depth0 : quickCheck 0 = true := by decide +kernel

theorem depth1 : quickCheck 1 = true := by decide +kernel

theorem depth2 : quickCheck 2 = true := by decide +kernel

theorem depth3 : quickCheck 3 = true := by decide +kernel

theorem depth4 : quickCheck 4 = true := by decide +kernel

theorem depth5 : quickCheck 5 = true := by decide +kernel

theorem depth6 : quickCheck 6 = true := by decide +kernel

theorem depth7 : quickCheck 7 = true := by decide +kernel

theorem allQuick : ∀ d : Fin 8, quickCheck d.val = true := by
  intro d
  have disj : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 ∨ d.val=5 ∨ d.val=6 ∨ d.val=7 := by
    have := d.isLt
    omega
  rcases disj with h|h|h|h|h|h|h|h
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth0
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth1
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth2
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth3
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth4
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth5
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth6
  · exact Eq.mpr (congrArg (fun n => quickCheck n = true) h) depth7

theorem cert : ∀ d : Fin 8, check d.val = true := by
  intro d
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro a ha
  apply decide_eq_true
  have v := List.all_eq_true.mp (List.all_eq_true.mp (allQuick d) i hi) a ha
  have av : (Fin.ofNat 48 a).val = a := Nat.mod_eq_of_lt (List.mem_range.mp ha)
  unfold one
  dsimp only
  rw [av]
  have v' := Bool.and_eq_true_iff.mp v
  refine ⟨of_decide_eq_true v'.1,?_⟩
  intro p hp
  have hit := congrArg (fun m : Nat => m.testBit p.val) (eq_of_beq v'.2)
  rw [Nat.testBit_and,hp,Bool.true_and,eval24,finals24] at hit
  exact hit

theorem stepFront {d i : Nat} (hd : d<8) (hi : i<size d) (a : Act) :
    ∃ j < size (d+1), Below board (Orbits.Step board (cap d i) a) (cap (d+1) j) := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp (cert ⟨d,hd⟩) i (List.mem_range.mpr hi)) a.val (List.mem_range.mpr a.isLt)
  have actEq : Fin.ofNat 48 a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  change decide (one d i (Fin.ofNat 48 a.val)) = true at ok
  rw [actEq] at ok
  obtain ⟨range,hits⟩ := of_decide_eq_true ok
  let o := Fin.ofNat 144 (pointer d i a.val / 128)
  exact ⟨_,range,symmetry o,fun p h => hits p (stepToMove _ a h)⟩

theorem absent : ∀ d : Fin 9, ∀ i : Fin (size d.val), ∃ p : Pt,
    ((levels[d.val]!)[i.val]!).testBit p.val = false := by decide +kernel

theorem hard (xs : List (Fin 48)) (short : xs.length ≤ 8) :
    ¬ ∀ p : PP, isMarked (xs.foldl (fun s a => move s a.val) 0) p := by
  apply fromFrontier (B := board) cap size (fun _ hd _ hi a => stepFront hd hi a)
    asPoints (fun s a => move s a.val) moveToStep _ 0 _ xs short
  · intro d hd i hi
    obtain ⟨p,hp⟩ := absent ⟨d,by omega⟩ ⟨i,hi⟩
    exact ⟨p,by intro m; change _ = true at m; simp [hp] at m⟩
  · refine ⟨0,by decide,belowSubset ?_⟩
    intro p hp; change (0 : Nat).testBit p.val = true at hp; simp at hp

end PCX150.OrbitCert

namespace PCX150.SmallChart
abbrev Sample := Fin 60

abbrev Var := Fin 12

abbrev Tag := Fin 22

abbrev Key := Fin 48

structure Domain where
  val : Sample → Var → Bool
  tag : Sample → Tag

structure Aut (B : Domain) where
  s : Equiv.Perm Sample
  v : Equiv.Perm Var
  a : Equiv.Perm Tag
  bit : ∀ x q, B.val (s x) (v q) = B.val x q
  label : ∀ x, B.tag (s x) = a (B.tag x)

def Aut.unit (B : Domain) : Aut B :=
  ⟨Equiv.refl _,Equiv.refl _,Equiv.refl _,fun _ _ => rfl,fun _ => rfl⟩

def Aut.thenDo {B : Domain} (f g : Aut B) : Aut B where
  s := f.s.trans g.s
  v := f.v.trans g.v
  a := f.a.trans g.a
  bit x q := (g.bit _ _).trans (f.bit x q)
  label x := (g.label _).trans (congrArg g.a (f.label x))

def acted {B : Domain} (f : Aut B) (u : Set Sample) : Set Sample :=
  {x | f.s.symm x ∈ u}

def branch (B : Domain) (u : Set Sample) (q : Var) (b : Bool) : Set Sample :=
  {x | x ∈ u ∧ B.val x q = b}

def plain (B : Domain) (u : Set Sample) : Prop := ∃ a, ∀ x ∈ u, B.tag x = a

structure Chart (B : Domain) where
  state : Key → Set Sample
  wt : Key → Nat
  root : Key
  start : state root = Set.univ
  rich : ∀ k, ¬ plain B (state k)
  next : Key → Var → Bool → Option Key
  proper : ∀ k q b, match next k q b with
    | none => plain B (branch B (state k) q b)
    | some j => ∃ f : Aut B, branch B (state k) q b = acted f (state j)
  subadd : ∀ k q, wt k ≤ ((next k q false).map wt).getD 1 + ((next k q true).map wt).getD 1

theorem actedChain {B : Domain} (f g : Aut B) (u : Set Sample) :
    acted g (acted f u) = acted (f.thenDo g) u := rfl

theorem branchAct {B : Domain} (f : Aut B) (u : Set Sample) (q : Var) (b : Bool) :
    branch B (acted f u) q b = acted f (branch B u (f.v.symm q) b) := by
  ext x
  have eq := f.bit (f.s.symm x) (f.v.symm q)
  simp only [Equiv.apply_symm_apply] at eq
  change (_ ∧ B.val x q = b) ↔ (_ ∧ B.val (f.s.symm x) (f.v.symm q) = b)
  rw [eq]
  rfl

theorem actedPlain {B : Domain} (f : Aut B) {s : Set Sample} (h : plain B s) : plain B (acted f s) := by
  obtain ⟨a,ha⟩ := h
  refine ⟨f.a a,?_⟩
  intro x hx
  simpa [ha _ hx] using f.label (f.s.symm x)

theorem actedRich {B : Domain} (f : Aut B) {s : Set Sample} (h : ¬ plain B s) : ¬ plain B (acted f s) := by
  rintro ⟨a,ha⟩
  apply h
  refine ⟨f.a.symm a,?_⟩
  intro x hx
  apply f.a.injective
  rw [Equiv.apply_symm_apply,←f.label]
  exact ha _ (by simpa [acted] using hx)

def Classified {B : Domain} (c : Chart B) (s : Set Sample) : Prop :=
  plain B s ∨ ∃ k, ∃ f : Aut B, s = acted f (c.state k)

theorem classifyBranch {B : Domain} {c : Chart B} {s : Set Sample}
    (h : Classified c s) (q : Var) (b : Bool) : Classified c (branch B s q b) := by
  rcases h with ⟨a,h⟩ | ⟨k,f,rfl⟩
  · exact Or.inl ⟨a,fun x hx => h x hx.1⟩
  · rw [branchAct]
    have hi := c.proper k (f.v.symm q) b
    cases e : c.next k (f.v.symm q) b with
    | none =>
      rw [e] at hi
      exact Or.inl (actedPlain f hi)
    | some j =>
      rw [e] at hi
      obtain ⟨g,hg⟩ := hi
      exact Or.inr ⟨j,g.thenDo f,by rw [hg,actedChain]⟩

theorem chartAll {B : Domain} (c : Chart B) (qs : List (Var × Bool)) :
    Classified c (qs.foldl (fun s q => branch B s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : Classified c s) :
      Classified c (xs.foldl (fun t q => branch B t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (classifyBranch h _ _)
  apply walk
  exact Or.inr ⟨c.root,Aut.unit B,by rw [c.start]; rfl⟩

inductive Tree
  | leaf
  | node (v : Var) (no yes : Tree)

def leaves : Tree → Nat
  | .leaf => 1
  | .node _ l r => leaves l + leaves r

theorem leafPos (t : Tree) : 1 ≤ leaves t := by
  induction t with
  | leaf => decide
  | node q l r h k => simp only [leaves]; omega

def rawValid (B : Domain) : Tree → Set Sample → Prop
  | .leaf,s => plain B s
  | .node q l r,s => rawValid B l (branch B s q false) ∧ rawValid B r (branch B s q true)

theorem rawLower {B : Domain} (c : Chart B) (t : Tree) (k : Key) (f : Aut B)
    (good : rawValid B t (acted f (c.state k))) : c.wt k ≤ leaves t := by
  induction t generalizing k f with
  | leaf => exact False.elim (actedRich f (c.rich k) good)
  | node q l r hl hr =>
    let u := f.v.symm q
    have one (b : Bool) (sub : Tree) (ih : ∀ j (g : Aut B), rawValid B sub (acted g (c.state j)) → c.wt j ≤ leaves sub)
        (ok : rawValid B sub (branch B (acted f (c.state k)) q b)) :
        ((c.next k u b).map c.wt).getD 1 ≤ leaves sub := by
      cases e : c.next k u b with
      | none => exact leafPos sub
      | some j =>
        have hg := c.proper k u b
        rw [e] at hg
        obtain ⟨g,he⟩ := hg
        have hi : branch B (acted f (c.state k)) q b = acted (g.thenDo f) (c.state j) := by
          rw [branchAct]; change acted f (branch B (c.state k) u b) = _
          rw [he,actedChain]
        exact ih j _ (hi ▸ ok)
    exact (c.subadd k u).trans (Nat.add_le_add (one false l hl good.1) (one true r hr good.2))

end PCX150.SmallChart
namespace PCX150.Chart48
open PCX150.SmallChart
abbrev G := Fin 5

abbrev ID := Fin 144

def vars : Array Nat := #[0xba9876210543,0xba9543876210,0x876ba9543210,0xb9a867534201,0xab9786453120]

def samp : Array Nat := #[0xebbdf6e78cf2d74c70bafaeab6c9e6a689648a37de8606da75c65859751549341138f30d1440c20402ca2481c6,0xe78efadb7d74c70cf2b6cbeeaaba689649e68608e279f75c6586da5535d25942ca2481c64503ce34c105083001,0xefad74cf2e78df6c31beea689e6b6caea9258e275c6da8607de6194503ce34c5d65544d22472c62880c1140102,0xebbe39db7d35cb3c318e28607de75c6da658beeb6caeaa689e69645974d255441134c3ce28b1c62481050400c2,0xbeeb6caeaa689e6964efae78df6d74cf2c708a382179f71d69b6195545d64933ce45030d2482ca1870c2144001]

def tags : Array Nat := #[0x2b3a46507b5cb62927414c418801,0x2959ca1173dac52d093988518440,0x2b28d2707b16e6a9262a0e410c20,0x2b49ca304a0e6291ee6b16a18820,0x1ee6b16aad2728c128398a418820]

def rm : Array Nat := #[4296015872,0x4000080000002,2155872258,309238177792,12890144768,0x4001080000002,0x4001080800002,281479272726593,9183121115218432,282575562080321,3231711235,282578784354369,282575564177473,4503917454958720,282853662261313,0x8400100104048,0x80018100100060,0x81000100100061,4503986174435456,4503676940984450,0x81010100100061,0x814001080800082,4785384918097921,0x9400100104049,0x8100c100100061,0x88400100104068,0x8101c100100061,0x8480311504008,281789586743361,0x8100c100112061,4785384918098113,0x2a00001500c30c,4516905440780430,0x844030488861012,4503989410865283,0x3384484428a005,7116327023042761,0x49100c3005120e1,0x4884883005140e8,0x33384484428a005,0x3384484428a3c5,0x49948c3005160e9,7683709651673549,0x2afc0015fcc30c,0x30ac5ac5e8a28f,0x3bcc4b5578e3cd,0xf30aefaefebaebf,0xfffffffffffffff]

def weight : Array Nat := #[2,3,3,4,2,4,5,5,5,5,3,6,6,6,7,7,7,6,7,7,7,8,8,8,7,8,8,9,9,8,9,11,9,12,10,13,13,13,13,14,14,17,17,15,19,23,29,43]

def words : Array Nat := #[0,1,2,3,4,5,17,25,33,41,10,26,34,42,19,35,43,44,37,81,209,273,337,153,281,345,353,297,202,266,330,154,282,346,354,298,83,275,339,355,299,300,1617,2129,2641,1233,2257,2769,2833,2385,665,2201,2713,2841,2393,2401,1226,2250,2762,2826,2378,666,2202,2714,2842,2394,2402,2131,2643,2835,2387,2403,9809,18001,22097,22609,19025,5329,17617,21713,22737,19153,19217,17049,21145,22681,19097,19225,5322,17610,21706,22730,19146,19210,17050,21146,22682,19098,19226,22611,19027,19219,42577,140881,173649,181841,153169,153681,136401,169169,181457,152785,153809,180889,152217,153753,136394,169162,181450,152778,153802,180890,152218,153754,153683,1091153,1353297,1451601,1222225,1230417,1447121,1217745,1230033,1229465,1447114,1217738,1230026,1229466,11576913,9741905,9840209,9835729,9835722,78685777]

def lab : Array Nat := #[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21]

def cols : Array Nat := #[0xa20a200cfa28a00,0x5100cfa20492480,0xcf510510145140,0x488488333514028,0x844333488861012,0x33384484428a005,90657122719368468,0x281c3c142300861,0xc3c281281c0028a,5912485265682627,0x2afc001500c30c,0xfc002a02a030c30]

def bound : Array Nat := #[0xfc00000fc00008fc0ff00fc000000003f00fc00000fc00000fc000000003f000003f00fc00000fc000,0xfc00100fc001000403f000403f00fc00100fc00100fc001000403f00fc00111fd60000fc00107fd8c0,0xfc00200fc00258000ff000803f00fc00200fc00200fc002000803f00fc00200fc00200fc002060003f,0xfc00300fc0032c040ff00fc0030bfc1820a00600000c03f00fc00300fc00300fc003000c03f00fc003,0xfc00400fc00408fc0ff0500000000014000fc00400fc00400fc004001003f0000140050000000fc004,0xfc00500fc005001403f001403f00fc00500fc00500fc005001403f00fc00511fc3410afc00107fcf81,0xfc00600fc00600140ff001803f00fc00600fc00600fc006001803f00fc00611fc2830afcb030600f81,0xfc00700fc0078a0c0ff00fc007001c03f00fc007710024200fc00700018020d0c03f00fc00700fc007,0xfc008002003f00fc0080804e400ffdc0300fc00815056400efe10300fc00800fc00800fc008002003f,0xfc00900fc009002403f00fc009002403f00fc00902049400cfdfc300fc0093904f4000fc00907fe383,0xfc00a00fc00a3d100ff0008082020800200fc00a0208002000808200fc00a00fc00a00fc00a011003f,0xfc00b00fc00b79180ff00fc00b002c03f00fc00b71001830cfc0070002383091803f00fc00b00fc00b,0xfc00c00fc00c00240ff00fc00c003003f00fc00c1e0c9400cfc04700fc00c390408200fc00c0102383,0xfc00d00fc00d003403f0104b010bfc10809fc2890614e0000fc00d08fdcc600fc00d003403f00fc00d,0xfc00e00fc00e2e340ff00fc00e003803f00fc00e20041830cfc04c000050809190c00bfc00b00fc00e,0xfc00f8d0c2421f003077c01687170c9c200fc00f00fc00f00fc00f863007f683003f00fc00f00fc00f,0xf0418300fc0100905ac300fc010004003f00fc01000fc0100cfcb4c20249405c259000bfe34c00fc010,0x860000700fc0118a0c44200fc011004403f00fc01171007c700fc011630d802722003f00fc01100fc011,0xfc01200fc012004803f0114b010bfc08d09fdf4d06147810afc00d08fdb0d00fc012004803f00fc012,0xfc01300fc013272c0ff052c0bf00fc01300fc013270014753004c705009c700fc013132c03f00fc013,0x860000b00fc014791844200fc014005003f00fc014710234c0cfc011630e3838e3403f00fc01400fc014,0x15fc24e00fc0156934ec0005403f00fc01500fc01512fdbce783514000fc01511fd7d05b04d884d04bc8,0xfc01600fc01609480ff12fd45402182430a0058e005803f00fc01600fc01610fe2d40618783010034e,0xfc0178d0c0078a0c3077c0030f89309c200fc017710000f00fc01786318022c4003f00fc01700fc017,0xf0404c00fc0180125ac300fc018006003f00fc0182004b4c00fc018202620372210c40bfc01100fc018,0x860000f8d0c7c71f003117c00e131f2c9c200fc01900fc01900fc019205007f5a3803f00fc01900fc019,0xf0400e00fc01a2e35ac300fc01a006803f00fc01a20040100cfc01820245088e350c40bfc01400fc01a,0xfc01b084800408fc4965a351484f048d506fd41a00fc01b00fc01b006c03f3f355486804c5504fe29a,0xfc01c00fc01c28540ff00fc01c84501820a022d9515024200fc01c00023590d0d451000e11101022d7,0x6a0d68f00fc01d0f30b8700fc01d00600bf00fc01d5c0cb0f00fc01d203060772203ca181001100fc01d,0xfc01e00fc01e7b580ff4502359012c2870a00f59005807f00fc01e00fc01e55020590a2c0470100719,0xfc01f007c03f00fc01f5121cd100fc01f2e205d16f215d100fc01f4e201d183211d100fc01f6c200d1,0xfc0205e11bd9533810a055084700fc020530d1598b30151530205d430c85700fc020816803f00fc020,0x37363d400fc021013599436214980cfc39f182019800fc021008403f00fc021893509400fc0213d34094,0xfc02200fc0223d6c0ff8351451130c25c0a01b208b51bd10a0c4dc0501f6000fc022095800a011025e,0xfc0231b48016094811612fcb215c34c5a3a3459a008c03f00fc02300fc02310fc1617a348da5f3435a,0xfc024012061d186141105415571f404d700fc0244f2141d00fc02450606112c40fd7384001700fc024,0x92061d00fc0251860b91282001d00604d100fc0254f20b9d00fc0252e6061172204dd136001100fc025,0x92141d0120b9d1f1095f3f38b191f384d900fc02600fc02600fc0260f8407f5a38159383801900fc026,0x14fc0231b4845b0948a5b12fc0e336489db19491db009c03f00fc02700fc02710fcca36449c5b444a15b,0xfc028605801e7b5811e4511c6684386606e38da0008c07f00fc02800fc02855109e68c391207f39920,0x9200240120025186095f2d563a01f6941c00fc0294f2002600fc0290f8461148558a0386a29c00fc029,0xfc02a0e69fe0436a3e005415641f402245e400240d6876000fc02a8a699203c680a08c689a000fc02a,0xfc02b219c0ff00fc02b0c585620c108682358c6204582220410fe812586e2085812208117e81b584a2,0xfc02c5e6c0223d6c1220d8499f57219693521169058441f73211e955209e900fc02c086d362016db22,0xfc02d3f8c2623f6cfe81b6a1698469ea912544ea008cb6200fc02d006c0283c691e98c690694c5402a,0x3d8c02c5e6c26d3d6c6ed248c0ec436c66d246cdad328c3ac536ccad326d4ed00fc02e099d0eb1b9c92b,0xb9c52e219cbee419d46e029c1ae0d9c5ae239cc6e009c06e059c26e129c6ee019c02e099c16e1b9c4ae]

def bits (s : Nat) : Set Sample := {p : Sample | s.testBit p.val = true}

def geo : Domain :=
  ⟨fun r v => cols[v.val]!.testBit r.val,fun r => Fin.ofNat 22 lab[r.val]!⟩

def vs (g : G) (v : Var) : Var := Fin.ofNat 12 ((vars[g.val]! >>> (4*v.val)) % 16)

def rs (g : G) (r : Sample) : Sample := Fin.ofNat 60 ((samp[g.val]! >>> (6*r.val)) % 64)

def ls (g : G) (k : Tag) : Tag := Fin.ofNat 22 ((tags[g.val]! >>> (5*k.val)) % 32)

theorem gInv : ∀ g : G, (∀ q : Var, vs g (vs g q)=q) ∧
    (∀ r : Sample,rs g (rs g r) = r) ∧ (∀ k : Tag,ls g (ls g k)=k) := by decide +kernel

theorem gRule : ∀ g : G, ∀ r : Sample,
    geo.tag (rs g r) = ls g (geo.tag r) ∧
    ∀ v : Var, geo.val (rs g r) (vs g v) = geo.val r v := by decide +kernel

def gen (g : G) : Aut geo where
  s := ⟨rs g,rs g,(gInv g).2.1,(gInv g).2.1⟩
  v := ⟨vs g,vs g,(gInv g).1,(gInv g).1⟩
  a := ⟨ls g,ls g,(gInv g).2.2,(gInv g).2.2⟩
  bit r v := (gRule g r).2 v
  label r := (gRule g r).1

def assemble (w : Nat) : Nat → Aut geo
  | 0 => Aut.unit geo
  | d+1 =>
    let t := (w >>> (3*d)) % 8
    let prev := assemble w d
    if t=0 then prev else prev.thenDo (gen (Fin.ofNat 5 (t-1)))

def backward (w : Nat) : Nat → Sample → Sample
  | 0,r => r
  | d+1,r =>
    let t := (w >>> (3*d)) % 8
    if t=0 then backward w d r else backward w d (rs (Fin.ofNat 5 (t-1)) r)

theorem backApply (w d : Nat) (r : Sample) : (assemble w d).s.symm r = backward w d r := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    simp only [assemble,backward]
    split
    · apply ih
    · exact ih _

def orient (o : ID) := assemble words[o.val]! 9

def slot (k : Key) (q : Var) (b : Bool) : Nat :=
  (bound[k.val]! >>> (14*(2*q.val+b.toNat))) % 16384

def index (code : Nat) : Key := Fin.ofNat 48 (code%64)

def turn (code : Nat) : ID := Fin.ofNat 144 (code/64)

def mono (code : Nat) : Tag := Fin.ofNat 22 (code/64)

def node (k : Key) := bits rm[k.val]!

def next (k : Key) (q : Var) (b : Bool) : Option Key :=
  let d := slot k q b
  if d%64=63 then none else some (index d)

def pointTest (k : Key) (q : Var) (b : Bool) (r : Sample) : Prop :=
  let d := slot k q b
  let keep := (rm[k.val]!.testBit r.val && (geo.val r q == b))
  if d % 64 = 63 then keep = true → geo.tag r = mono d
  else keep = rm[(index d).val]!.testBit (backward words[(turn d).val]! 9 r).val

instance (k : Key) (q : Var) (b : Bool) (r : Sample) : Decidable (pointTest k q b r) := by
  unfold pointTest; dsimp only; split <;> infer_instance

theorem allSteps : ∀ (k : Key) (q : Var) (b : Bool) (r : Sample), pointTest k q b r := by decide +kernel

theorem allCost : ∀ (k : Key) (q : Var), weight[k.val]! ≤ ((next k q false).map (fun (j : Key) => weight[j.val]!)).getD 1 +
    ((next k q true).map (fun (j : Key) => weight[j.val]!)).getD 1 := by decide +kernel

def witnessRow (k : Key) (a : Tag) : Prop :=
  ∃ r : Sample, rm[k.val]!.testBit r.val = true ∧ geo.tag r ≠ a

instance (k : Key) (a : Tag) : Decidable (witnessRow k a) := by unfold witnessRow; infer_instance

theorem spread : ∀ k a, witnessRow k a := by decide +kernel

def chart : Chart geo where
  state := node
  wt k := weight[k.val]!
  root := 47
  start := by
    ext r
    have h : ∀ p : Sample, rm[47]!.testBit p.val = true := by decide +kernel
    exact iff_of_true (h r) trivial
  rich k := by
    rintro ⟨a,ha⟩
    obtain ⟨r,inside,ne⟩ := spread k a
    exact ne (ha r inside)
  next := next
  proper k q b := by
    let d := slot k q b
    have facts := allSteps k q b
    by_cases hom : d%64=63
    · simp only [next,show slot k q b % 64 = 63 from hom,ite_true]
      refine ⟨mono d,?_⟩
      intro r h
      have both : (rm[k.val]!.testBit r.val && (geo.val r q == b)) = true := by
        have hl : rm[k.val]!.testBit r.val = true := h.1
        simp [hl,h.2]
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_pos hom] at e
      exact e both
    · simp only [next,show ¬slot k q b % 64 = 63 from hom,ite_false]
      refine ⟨orient (turn d),?_⟩
      ext r
      have e := facts r
      change (if d%64=63 then _ else _) at e
      rw [if_neg hom] at e
      change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
      rw [backApply,←e]
      simp [node,bits]
  subadd := allCost

theorem rootWeight : chart.wt chart.root = 43 := by decide +kernel

end PCX150.Chart48
namespace PCX150.Chart48
open PCX150.SmallChart
set_option maxRecDepth 10000
def alongCode : Array Nat := #[21542142465,38789383680,56036622346,68971138567,73015430152,303041801,94842913043,107776907011,111687505156,4749596165,129337398018,142270930716,146064540701,9179301150,163831546660,167554327832,13556327961,17870299674,176180175643,189702736390,202635619626,206262110251,26594969900,224196888370,227751244559,30971343888,35285970961,236377747730,250065074187,253574589196,43960118285,271624047421,275063258681,48336027450,52651102523,283690209852,293185860110,296591691587,61308080196,65616823605,305212311094,77599294007,319053580308,322446105877,82884304406,340612551757,343934324297,87259762506,91575294539,352561732428,362174817303,365463214163,100232272212,104540558631,374083376680,116406047273,388044954712,391313709344,121804577313,126120315682,399941323811,409601333279,412839387230,134773875039,139085373531,421462761820,150900713821,425811923749,156302791718,160614590307,434435598436,172455716183,448408332902,451679053614,182169921583,186485652272,460306660401,469966677549,473204731500,195139219309,199450717801,481828106090,211266058091,486177260339,216668128308,220979934577,494800942706,232821060423,504464031032,507752429940,242521487989,246830298688,516373116737,258695785282,520718873662,264044311871,268356108409,529342546298,280250973048,289851142469,533724820038,301813417852,543268818248,546674657661,311391046270,315701821264,555297308753,327684283730,559643065678,332915834447,337227632770,568266740099,349239936129,358722200405,572648547414,370801923973,577010228825,380230328154,384542137222,585633913991,396669847650,406031926880,590010943329,418229084809,431166686565,594424392807,440426392936,444738201994,603048077963,457035189360,466229496430,607426612079,478594429069,491531369587,500607646070,611857431159,513090025614,526024216187,539278869119,616303133568,551895466383,564830506884,582078138760,599325052300]

def invName : Array Nat := #[0,1,2,3,4,5,10,7,8,9,6,14,12,13,11,15,16,18,17,19,36,29,30,28,24,25,27,26,23,21,22,31,37,38,35,34,20,32,33,40,39,41,50,43,44,61,67,68,60,59,42,57,58,54,53,55,56,51,52,49,48,45,62,63,70,69,66,46,47,65,64,71,88,83,84,76,75,77,94,95,100,99,93,73,74,92,91,87,72,89,90,86,85,82,78,79,97,96,101,81,80,98,102,116,117,114,113,107,108,109,122,121,124,106,105,120,103,104,119,118,115,111,110,123,112,125,126,135,134,133,131,130,137,129,128,127,136,132,139,138,142,141,140,143]

def follow (o : ID) (g : G) : ID := Fin.ofNat 144 ((alongCode[o.val]! >>> (8*g.val)) % 256)

def inverse (o : ID) : ID := Fin.ofNat 144 invName[o.val]!

theorem followBoard : ∀ (o : ID) (g : G) (r : Sample),
    backward words[(follow o g).val]! 9 r = backward words[o.val]! 9 (rs g r) := by decide +kernel

theorem invertBoard : ∀ (o : ID) (r : Sample),
    backward words[(inverse o).val]! 9 (backward words[o.val]! 9 r) = r := by decide +kernel

theorem zeroBoard : ∀ (r : Sample), backward words[0]! 9 r = r := by decide +kernel

theorem followAct (o : ID) (g : G) (s : Set Sample) :
    acted (gen g) (acted (orient o) s) = acted (orient (follow o g)) s := by
  ext r
  change ((assemble words[o.val]! 9).s.symm (rs g r) ∈ s) ↔
    ((assemble words[(follow o g).val]! 9).s.symm r ∈ s)
  rw [backApply,backApply,followBoard]

theorem zeroAct (s : Set Sample) : acted (orient 0) s = s := by
  ext r
  change ((assemble words[0]! 9).s.symm r ∈ s) ↔ r ∈ s
  rw [backApply,zeroBoard]

theorem invertAct (o : ID) (s : Set Sample) : acted (orient o) (acted (orient (inverse o)) s) = s := by
  ext r
  change ((assemble words[(inverse o).val]! 9).s.symm ((assemble words[o.val]! 9).s.symm r) ∈ s) ↔ r ∈ s
  rw [backApply,backApply,invertBoard]

theorem composeAct (o p : ID) (s : Set Sample) :
    ∃ u : ID, acted (orient o) (acted (orient p) s) = acted (orient u) s := by
  have go (w d : Nat) : ∃ u : ID, acted (assemble w d) (acted (orient p) s) = acted (orient u) s := by
    induction d with
    | zero => exact ⟨p,rfl⟩
    | succ d ih =>
      obtain ⟨u,hu⟩ := ih
      simp only [assemble]
      split
      · exact ⟨u,hu⟩
      · rename_i h
        let g := Fin.ofNat 5 (((w >>> (3*d))%8)-1)
        exact ⟨follow u g,by rw [←actedChain,hu]; exact followAct u g s⟩
  exact go _ _

theorem nextName (k : Key) (q : Var) (b : Bool) :
    plain geo (branch geo (node k) q b) ∨ ∃ (j : Key) (o : ID), branch geo (node k) q b = acted (orient o) (node j) := by
  let d := slot k q b
  have facts := allSteps k q b
  by_cases hom : d%64=63
  · left
    have h := chart.proper k q b
    change (match next k q b with | none => _ | some j => _) at h
    rw [show next k q b = none by simp [next,show slot k q b % 64 = 63 from hom]] at h
    exact h
  · right
    refine ⟨index d,turn d,?_⟩
    ext r
    have e := facts r
    change (if d%64=63 then _ else _) at e
    rw [if_neg hom] at e
    change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
    rw [backApply,←e]
    simp [node,bits]

def named (s : Set Sample) := plain geo s ∨ ∃ (k : Key) (o : ID), s = acted (orient o) (node k)

theorem namedBranch {s : Set Sample} (h : named s) (q : Var) (b : Bool) : named (branch geo s q b) := by
  rcases h with ⟨a,mono⟩ | ⟨k,o,rfl⟩
  · exact Or.inl ⟨a,fun r hr => mono r hr.1⟩
  · rw [branchAct]
    rcases nextName k ((orient o).v.symm q) b with mono | ⟨j,p,eq⟩
    · exact Or.inl (actedPlain _ mono)
    · obtain ⟨u,hu⟩ := composeAct o p (node j)
      exact Or.inr ⟨j,u,by rw [eq,hu]⟩

theorem allNamed (qs : List (Var × Bool)) :
    named (qs.foldl (fun s q => branch geo s q.1 q.2) Set.univ) := by
  have walk (xs : List (Var × Bool)) (s : Set Sample) (h : named s) :
      named (xs.foldl (fun t q => branch geo t q.1 q.2) s) := by
    induction xs generalizing s with
    | nil => exact h
    | cons a tail ih => exact ih _ (namedBranch h _ _)
  apply walk
  exact Or.inr ⟨47,0,by rw [zeroAct]; exact chart.start.symm⟩

end PCX150.Chart48

namespace PCX150.Sparse
abbrev Point := Fin 60

abbrev Query := Fin 12

abbrev Label := Fin 22

abbrev Box := Sum Label (Fin 2)

inductive TestTree where
  | leaf
  | cut (v : Query) (no yes : TestTree)

def leaves : TestTree → Nat
  | .leaf => 1
  | .cut _ t u => leaves t + leaves u

def half (bit : Point → Query → Bool) (s : Set Point) (v : Query) (b : Bool) : Set Point :=
  {p | p ∈ s ∧ bit p v = b}

def Valid (bit : Point → Query → Bool) (term : Box → Set Point) : TestTree → Set Point → Prop
  | .leaf,s => ∃ i, s ⊆ term i
  | .cut v t u,s => Valid bit term t (half bit s v false) ∧ Valid bit term u (half bit s v true)

theorem coverExists (bit : Point → Query → Bool) (term : Box → Set Point)
    {t : TestTree} {s : Set Point} (h : Valid bit term t s) :
    ∃ f : Finset Box, f.card ≤ leaves t ∧ ∀ p ∈ s, ∃ i ∈ f, p ∈ term i := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    exact ⟨{i},by simp [leaves],fun p hp => ⟨i,by simp,hi hp⟩⟩
  | cut v t u ht hu =>
    obtain ⟨a,ha,ca⟩ := ht h.1
    obtain ⟨b,hb,cb⟩ := hu h.2
    refine ⟨a ∪ b,(Finset.card_union_le _ _).trans (Nat.add_le_add ha hb),?_⟩
    intro p hp
    cases m : bit p v with
    | false =>
      obtain ⟨i,hi,hit⟩ := ca p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_left _ hi,hit⟩
    | true =>
      obtain ⟨i,hi,hit⟩ := cb p ⟨hp,m⟩
      exact ⟨i,Finset.mem_union_right _ hi,hit⟩

def box (tag : Point → Label) (A B : Set Point) : Box → Set Point
  | .inl i => {p | tag p = i}
  | .inr i => if i = 0 then A else B

noncomputable def liveTags (tag : Point → Label) (s : Set Point) : Finset Label := by
  classical
  exact Finset.univ.filter (fun k => ∃ p ∈ s, tag p = k)

theorem ofLive {tag : Point → Label} {s : Set Point} {i : Label}
    (hi : i ∈ liveTags tag s) : ∃ p ∈ s, tag p = i := by
  classical
  unfold liveTags at hi
  exact (Finset.mem_filter.mp hi).2

noncomputable def residual (tag : Point → Label) (s A B : Set Point) (x y : Bool) : Finset Box := by
  classical
  exact ((liveTags tag {p | p ∈ s ∧ (x = true → p ∉ A) ∧ (y = true → p ∉ B)}).map
      ⟨Sum.inl,Sum.inl_injective⟩) ∪
    (if x then {Sum.inr 0} else ∅) ∪ (if y then {Sum.inr 1} else ∅)

theorem cheapLower (bit : Point → Query → Bool) (tag : Point → Label)
    {t : TestTree} {s A B : Set Point} (h : Valid bit (box tag A B) t s) (k : Nat)
    (hk : ∀ x y : Bool, k ≤ (residual tag s A B x y).card) : k ≤ leaves t := by
  classical
  obtain ⟨f,hf,cover⟩ := coverExists _ _ h
  let x := decide ((Sum.inr 0 : Box) ∈ f)
  let y := decide ((Sum.inr 1 : Box) ∈ f)
  have subset : residual tag s A B x y ⊆ f := by
    intro u hu
    simp only [residual,Finset.mem_union] at hu
    rcases hu with (lab | fst) | snd
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp lab
      obtain ⟨p,⟨ps,pa,pb⟩,eq⟩ := ofLive hi
      obtain ⟨b,mem,hit⟩ := cover p ps
      cases b with
      | inl j =>
        change tag p = j at hit
        have ji : j=i := hit.symm.trans eq
        simpa [ji] using mem
      | inr j =>
        fin_cases j
        · exact False.elim (pa (by simpa [x] using mem) (by simpa [box] using hit))
        · exact False.elim (pb (by simpa [y] using mem) (by simpa [box] using hit))
    · by_cases hx : (Sum.inr 0 : Box) ∈ f
      · have e : u = Sum.inr 0 := by simpa [x,hx] using fst
        simpa [e] using hx
      · simp [x,hx] at fst
    · by_cases hy : (Sum.inr 1 : Box) ∈ f
      · have e : u = Sum.inr 1 := by simpa [y,hy] using snd
        simpa [e] using hy
      · simp [y,hy] at snd
  exact (hk x y).trans ((Finset.card_le_card subset).trans hf)

end PCX150.Sparse
namespace PCX150.Scoring
open PCX150.Sparse
def bitset (m : Nat) : Set Point := {p : Point | m.testBit p.val = true}

def tags : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,0xc0000000000,52776558133248,0xc00000000000,844424930131968,0xc000000000000,0x30000000000000,0xc0000000000000,0x300000000000000,0xc00000000000000]

def label (p : Point) : Label := Fin.ofNat 22 (#[0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,3,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,20,20,21,21][p.val]!)

def present (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tags[k]! != 0 then n+1 else n) 0

def apart (a b : Nat) := a ^^^ (a &&& b)

theorem tagBits : ∀ (k : Label) (p : Point),
    (tags[k.val]!).testBit p.val = decide (label p=k) := by decide +kernel

theorem tagSmall : ∀ k : Label, tags[k.val]! < 2^60 := by decide +kernel

theorem tagHit (m : Nat) (k : Label) (h : m &&& tags[k.val]! ≠ 0) :
    ∃ p ∈ bitset m, label p = k := by
  classical
  by_contra no
  apply h
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and]
  by_cases sm : n < 60
  · let p : Point := ⟨n,sm⟩
    have e := tagBits k p
    change (tags[k.val]!).testBit n = _ at e
    rw [e]
    by_cases bit : m.testBit n = true
    · have ne : label p ≠ k := fun eq => no ⟨p,bit,eq⟩
      simp [ne]
    · simp [show m.testBit n = false by cases z : m.testBit n <;> simp_all]
  · have low := Nat.testBit_lt_two_pow (lt_of_lt_of_le (tagSmall k)
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 60 ≤ n)))
    simp [low]

theorem presentBound (m : Nat) : present m ≤ (liveTags label (bitset m)).card := by
  classical
  let test := fun k : Nat => m &&& tags[k]! != 0
  let ls := (List.range 22).filter test
  have fold (ws : List Nat) (n : Nat) :
      ws.foldl (fun v k => if test k then v+1 else v) n = n+(ws.filter test).length := by
    induction ws generalizing n with
    | nil => simp
    | cons a as ih =>
      cases h : test a <;> simp [h,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have size : present m = ls.length := by simpa [present,ls,test] using fold (List.range 22) 0
  let target := (liveTags label (bitset m)).image Fin.val
  have subset : ls.toFinset ⊆ target := by
    intro k hk
    have hit := List.mem_filter.mp (List.mem_toFinset.mp hk)
    have kt := List.mem_range.mp hit.1
    let v : Label := ⟨k,kt⟩
    have ne : m &&& tags[v.val]! ≠ 0 := by simpa [test,v] using hit.2
    have witness := tagHit m v ne
    have live : v ∈ liveTags label (bitset m) := by
      unfold liveTags
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,witness⟩
    exact Finset.mem_image.mpr ⟨v,live,rfl⟩
  have h := Finset.card_le_card subset
  have nd : ls.Nodup := List.nodup_range.filter _
  rw [size,←List.toFinset_card_of_nodup nd]
  exact h.trans (Finset.card_image_le)

theorem apartSet (m a : Nat) (p : Point) :
    p ∈ bitset (apart m a) ↔ p ∈ bitset m ∧ p ∉ bitset a := by
  change (apart m a).testBit p.val = true ↔ m.testBit p.val = true ∧ ¬ a.testBit p.val = true
  simp only [apart,Nat.testBit_xor,Nat.testBit_and]
  cases m.testBit p.val <;> cases a.testBit p.val <;> decide

theorem countResidual (s a b : Set Point) (x y : Bool) :
    (residual label s a b x y).card =
    (liveTags label {p | p ∈ s ∧ (x = true → p ∉ a) ∧ (y = true → p ∉ b)}).card + x.toNat + y.toNat := by
  classical
  cases x <;> cases y <;> simp [PCX150.Sparse.residual,Finset.union_singleton,Finset.mem_map,Finset.card_insert_of_notMem]

def basic (s a b : Nat) := min (present s) (min (1+present (apart s a))
       (min (1+present (apart s b)) (2+present (apart (apart s a) b))))

theorem numericalLeafCover (val : Point → Query → Bool) (s a b : Nat) (t : TestTree)
    (v : Valid val (box label (bitset a) (bitset b)) t (bitset s)) : basic s a b ≤ leaves t := by
  apply cheapLower val label v
  intro x y
  rw [countResidual]
  cases x <;> cases y
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset s := by ext; simp
    rw [eq]
    unfold basic
    exact (min_le_left _ _).trans (by simpa using presentBound s)
  · have eq : {p | p ∈ bitset s ∧ (false=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart s b) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s b)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (false=true → p ∉ bitset b)} = bitset (apart s a) := by ext p; simp [apartSet]
    rw [eq]
    have z := presentBound (apart s a)
    unfold basic
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
    omega
  · have eq : {p | p ∈ bitset s ∧ (true=true → p ∉ bitset a) ∧ (true=true → p ∉ bitset b)} = bitset (apart (apart s a) b) := by
      ext p; simp [apartSet,and_assoc]; aesop
    rw [eq]
    have z := presentBound (apart (apart s a) b)
    unfold basic
    simp only [Bool.toNat_true]
    omega

end PCX150.Scoring

namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut)
def renamed {B : Domain} (f : Aut B) : TestTree → TestTree
  | .leaf => .leaf
  | .cut q l r => .cut (f.v q) (renamed f l) (renamed f r)

theorem sameLeaves {B : Domain} (f : Aut B) (t : TestTree) : leaves (renamed f t) = leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [renamed,leaves,hl,hr]

theorem smaller {bit : Point → Query → Bool} {base newer : Box → Set Point}
    {t : TestTree} {s d : Set Point} (h : Valid bit base t s) (sub : d ⊆ s)
    (relax : ∀ i, ∃ j, ∀ p ∈ d, p ∈ base i → p ∈ newer j) : Valid bit newer t d := by
  induction t generalizing s d with
  | leaf =>
    obtain ⟨i,all⟩ := h
    obtain ⟨j,hj⟩ := relax i
    exact ⟨j,fun p hp => hj p hp (all (sub hp))⟩
  | cut q l r hl hr =>
    constructor
    · exact hl h.1 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))
    · exact hr h.2 (fun _ hd => ⟨sub hd.1,hd.2⟩)
        (fun i => (relax i).imp (fun _ h p hp => h p hp.1))

theorem moveTree {B : Domain} (f : Aut B) {t : TestTree} {s : Set Point}
    {old newT : Box → Set Point} (good : Valid B.val old t s)
    (go : ∀ i, ∃ j, ∀ p ∈ s, p ∈ old i → f.s p ∈ newT j) :
    Valid B.val newT (renamed f t) (SmallChart.acted f s) := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,full⟩ := good
    obtain ⟨j,hj⟩ := go i
    refine ⟨j,?_⟩
    intro p hp
    simpa using hj (f.s.symm p) hp (full hp)
  | cut q l r hl hr =>
    have step (b : Bool) : half B.val (SmallChart.acted f s) (f.v q) b =
        SmallChart.acted f (half B.val s q b) := by
      change SmallChart.branch B (SmallChart.acted f s) (f.v q) b = _
      rw [SmallChart.branchAct,Equiv.symm_apply_apply]
      try rfl
    constructor
    · rw [step]
      exact hl good.1 (fun i => (go i).imp (fun _ h p hp => h p hp.1))
    · rw [step]
      exact hr good.2 (fun i => (go i).imp (fun _ h p hp => h p hp.1))

theorem transferTree {F : Set PCX150.Cl} (vCode : PCX150.V → Query) (bit : Point → Query → Bool)
    (A : Point → PCX150.V → Bool) (correct : ∀ p v, bit p (vCode v) = A p v)
    (term : Box → Set Point) (raw : ∀ C ∈ F, ∃ i, ∀ p, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C → p ∈ term i)
    {C : PCX150.Cl} {n : Nat} (h : PCX150.ResTree F C n) (s : Set Point)
    (f : ∀ p ∈ s, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C) :
    ∃ t : TestTree, leaves t = n+1 ∧ Valid bit term t s := by
  induction h generalizing s with
  | ax hc =>
    obtain ⟨i,hi⟩ := raw _ hc
    exact ⟨.leaf,rfl,i,fun p hp => hi p (f p hp)⟩
  | @res C D R i j _ _ hr ihC ihD =>
    obtain ⟨v,pc,pd,rfl⟩ := hr
    have left : ∀ p ∈ half bit s (vCode v) false, ¬PEqualNP.ProofComplexity.ClauseSat (A p) C := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,true) := by
        rintro rfl
        change A p v = true at yes
        have val : bit p (vCode v) = false := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    have right : ∀ p ∈ half bit s (vCode v) true, ¬PEqualNP.ProofComplexity.ClauseSat (A p) D := by
      intro p hp sat
      obtain ⟨l,hl,yes⟩ := sat
      have ne : l ≠ (v,false) := by
        rintro rfl
        change A p v = false at yes
        have val : bit p (vCode v) = true := hp.2
        rw [correct,yes] at val
        contradiction
      exact f p hp.1 ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,hl⟩),yes⟩
    obtain ⟨l,lc,lv⟩ := ihC _ left
    obtain ⟨r,rc,rv⟩ := ihD _ right
    exact ⟨.cut (vCode v) l r,by simp only [leaves,lc,rc]; omega,lv,rv⟩

end PCX150.Sparse
namespace PCX150.Sparse
open PCX150.SmallChart (Domain Aut acted)
structure Triple where
  points : Set Point
  a : Set Point
  b : Set Point

def admissible (g : Domain) (s : Triple) (t : TestTree) :=
  Valid g.val (box g.tag s.a s.b) t s.points

def restricted (g : Domain) (s : Triple) (q : Query) (b : Bool) : Triple :=
  ⟨half g.val s.points q b,s.a,s.b⟩

structure Embed (g : Domain) (hard easy : Triple) where
  turn : Aut g
  keep : hard.points ⊆ acted turn easy.points
  accepts : ∀ i, ∃ j, ∀ p ∈ hard.points,
    turn.s.symm p ∈ box g.tag easy.a easy.b i → p ∈ box g.tag hard.a hard.b j

theorem embedTree {g : Domain} {hard easy : Triple} (f : Embed g hard easy) {t : TestTree}
    (h : admissible g easy t) : admissible g hard (renamed f.turn t) := by
  let pre : Set Point := {p | f.turn.s p ∈ hard.points}
  have inc : pre ⊆ easy.points := by
    intro p hp
    have w := f.keep hp
    change f.turn.s.symm (f.turn.s p) ∈ easy.points at w
    simpa using w
  have localGood := smaller h inc (newer := box g.tag easy.a easy.b)
    (fun i => ⟨i,fun _ _ hi => hi⟩)
  have eq : acted f.turn pre = hard.points := by
    ext p
    change f.turn.s (f.turn.s.symm p) ∈ hard.points ↔ p ∈ hard.points
    simp
  change Valid _ _ _ hard.points
  rw [←eq]
  apply moveTree f.turn localGood
  intro i
  obtain ⟨j,hj⟩ := f.accepts i
  exact ⟨j,fun p hp ha => hj _ hp (by simpa using ha)⟩

structure Rule (g : Domain) (K : Type) where
  item : K → Triple
  weight : K → Nat
  base : ∀ i, admissible g (item i) .leaf → weight i ≤ 1
  kw : K → Query → Bool → Nat
  fork : ∀ i q, weight i ≤ kw i q false + kw i q true
  child : ∀ i q b, let s := restricted g (item i) q b
    (∀ t, admissible g s t → kw i q b ≤ leaves t) ∨
    ∃ j, Nonempty (Embed g (item j) s) ∧ kw i q b ≤ weight j

theorem soundRules {g : Domain} {K : Type} (rule : Rule g K) :
    ∀ t i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
  have count (n : Nat) : ∀ (t : TestTree), leaves t = n →
      ∀ i, admissible g (rule.item i) t → rule.weight i ≤ leaves t := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro t eq i good
      cases t with
      | leaf => exact rule.base i good
      | cut q l r =>
        have pos (u : TestTree) : 0 < leaves u := by
          induction u with
          | leaf => decide
          | cut v a b ha hb => simp only [leaves]; omega
        have left := pos l
        have right := pos r
        change leaves l + leaves r = n at eq
        have each (b : Bool) (sub : TestTree) (lt : leaves sub < n)
            (valid : admissible g (restricted g (rule.item i) q b) sub) :
            rule.kw i q b ≤ leaves sub := by
          rcases rule.child i q b with cheap | ⟨j,⟨emb⟩,hw⟩
          · exact cheap sub valid
          · obtain hg := embedTree emb valid
            have z := ih (leaves sub) lt (renamed emb.turn sub) (sameLeaves _ _) j hg
            exact hw.trans (by simpa [sameLeaves] using z)
        exact (rule.fork i q).trans (Nat.add_le_add (each false l (by omega) good.1) (each true r (by omega) good.2))
  exact fun t => count (leaves t) t rfl

end PCX150.Sparse

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
def quickGen (g : Nat) (m : Nat) : Nat :=
  match g with
  | 0 => ((m <<< 6) &&& 4032) ||| ((m <<< 2) &&& 0x330330330000000) ||| ((m <<< 1) &&& 0x800800800aaa000) ||| (m &&& 844631138893824) ||| ((m >>> 1) &&& 0x400400400555000) ||| ((m >>> 2) &&& 0xcc0cc0cc000000) ||| ((m >>> 6) &&& 63)
  | 1 => ((m <<< 6) &&& 258048) ||| ((m <<< 3) &&& 4194304) ||| ((m <<< 2) &&& 0xc0cc0cc0c900000) ||| ((m <<< 1) &&& 0x8008008000002a) ||| (m &&& 0x30030030000000) ||| ((m >>> 1) &&& 0x40040040000015) ||| ((m >>> 2) &&& 0x303303303240000) ||| ((m >>> 3) &&& 524288) ||| ((m >>> 6) &&& 4032)
  | 2 => ((m <<< 6) &&& 16515072) ||| ((m <<< 4) &&& 0x3c03c03c0000000) ||| ((m <<< 3) &&& 1040) ||| ((m <<< 2) &&& 2340) ||| ((m <<< 1) &&& 563087425929216) ||| (m &&& 0xc00c00c00000000) ||| ((m >>> 1) &&& 281543712964608) ||| ((m >>> 2) &&& 585) ||| ((m >>> 3) &&& 130) ||| ((m >>> 4) &&& 0x3c03c03c000000) ||| ((m >>> 6) &&& 258048)
  | 3 => ((m <<< 12) &&& 0xfff000000000) ||| ((m <<< 2) &&& 3195660) ||| ((m <<< 1) &&& 0xaaa000000820820) ||| ((m >>> 1) &&& 0x555000000410410) ||| ((m >>> 2) &&& 798915) ||| ((m >>> 12) &&& 68702699520)
  | 4 => ((m <<< 12) &&& 0xfff000000000000) ||| ((m <<< 2) &&& 12782640) ||| ((m <<< 1) &&& 45802332290) ||| ((m >>> 1) &&& 22901166145) ||| ((m >>> 2) &&& 3195660) ||| ((m >>> 12) &&& 0xfff000000000)
  | _ => m

def useWord (w : Nat) : Nat → Nat → Nat
  | 0,m => m
  | d+1,m =>
    let z := (w >>> (3*d))%8
    let t := useWord w d m
    if z=0 then t else quickGen (z-1) t

def permute (o m : Nat) := useWord words[o]! 9 m

def parts (g : G) : List Part :=
  match g.val with
  | 0 => [⟨4032,6,false⟩,⟨0x330330330000000,2,false⟩,⟨0x800800800aaa000,1,false⟩,⟨844631138893824,0,true⟩,⟨0x400400400555000,1,true⟩,⟨0xcc0cc0cc000000,2,true⟩,⟨63,6,true⟩]
  | 1 => [⟨258048,6,false⟩,⟨4194304,3,false⟩,⟨0xc0cc0cc0c900000,2,false⟩,⟨0x8008008000002a,1,false⟩,⟨0x30030030000000,0,true⟩,⟨0x40040040000015,1,true⟩,⟨0x303303303240000,2,true⟩,⟨524288,3,true⟩,⟨4032,6,true⟩]
  | 2 => [⟨16515072,6,false⟩,⟨0x3c03c03c0000000,4,false⟩,⟨1040,3,false⟩,⟨2340,2,false⟩,⟨563087425929216,1,false⟩,⟨0xc00c00c00000000,0,true⟩,⟨281543712964608,1,true⟩,⟨585,2,true⟩,⟨130,3,true⟩,⟨0x3c03c03c000000,4,true⟩,⟨258048,6,true⟩]
  | 3 => [⟨0xfff000000000,12,false⟩,⟨3195660,2,false⟩,⟨0xaaa000000820820,1,false⟩,⟨0x555000000410410,1,true⟩,⟨798915,2,true⟩,⟨68702699520,12,true⟩]
  | 4 => [⟨0xfff000000000000,12,false⟩,⟨12782640,2,false⟩,⟨45802332290,1,false⟩,⟨22901166145,1,true⟩,⟨3195660,2,true⟩,⟨0xfff000000000,12,true⟩]
  | _ => []

theorem paths : ∀ (g : G) (r : Sample), routes (parts g) r.val (rs g r).val := by decide +kernel

theorem genAsRoll (g : G) (m : Nat) : quickGen g.val m = roll (parts g) m := by
  fin_cases g <;> simp [quickGen,parts,roll,applyPart,Nat.and_comm,Nat.or_assoc]

theorem genExact (g : G) (m : Nat) (r : Sample) :
    (quickGen g.val m).testBit r.val = m.testBit (rs g r).val := by
  rw [genAsRoll]
  exact rollCorrect (paths g r) m

theorem wordExact (w d m : Nat) (ok : ∀ k < d, (w >>> (3*k))%8 ≤ 5) (r : Sample) :
    (useWord w d m).testBit r.val = m.testBit (backward w d r).val := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih =>
    let t := (w >>> (3*d))%8
    have hr : ∀ k < d, (w >>> (3*k))%8 ≤ 5 := fun k h => ok k (by omega)
    have lim : t ≤ 5 := ok d (by omega)
    simp only [useWord,backward]
    by_cases h : t=0
    · rw [if_pos h,if_pos h]
      exact ih hr r
    · rw [if_neg h,if_neg h]
      let g := Fin.ofNat 5 (t-1)
      have ge : g.val = t-1 := Nat.mod_eq_of_lt (by omega)
      have bit := genExact g (useWord w d m) r
      rw [ge] at bit
      exact bit.trans (ih hr (rs g r))

theorem digits : ∀ (o : ID) (k : Fin 9), (words[o.val]! >>> (3*k.val)) % 8 ≤ 5 := by decide +kernel

theorem actionBit (o : ID) (m : Nat) (r : Sample) :
    (permute o.val m).testBit r.val = m.testBit ((orient o).s.symm r).val := by
  rw [orient,backApply]
  exact wordExact _ _ _ (fun k h => digits o ⟨k,h⟩) _

theorem actionSet (o : ID) (m : Nat) :
    bits (permute o.val m) = acted (orient o) (bits m) := by
  ext r
  change (_ = true) ↔ (_ = true)
  rw [actionBit]

end PCX150.Scalar

namespace PCX150.Chart48
abbrev Sample := Fin 60

abbrev Var := Fin 12

abbrev Tag := Fin 22

abbrev Key := Fin 48

end PCX150.Chart48
namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def cubePart0 : Array Nat := #[0,0xcf510510145140,0xa20a200cfa28a00,0x5100cfa204924bf,0xa20a200cfa28a3f,0xcf51051014517f,0x5100cfa20492480,0xaeff305dfb6db7f,0x5df5dff305d75ff,0xf30aefaefebaebf,0xfffffffffffffff,63]
private def cubePart1 : Array Nat := #[0,0x488488333514028,0x33384484428a005,0x844333488861012,0x33384484428afc5,0x488488333514fe8,0x844333488861fd2,0x7bbcccb7779efed,0xb77b77cccaebfd7,0xccc7bb7bbd75ffa,0xfffffffffffffff,4032]
private def cubePart2 : Array Nat := #[0,0x281c3c142300861,90657122719368468,0xc3c281281c0028a,90657122719626516,0xc3c281281c3f28a,0x281c3c14233f861,0x3c3d7ed7e3ffd75,0xd7e3c3ebdcff79e,0xebdebd3c3f3faeb,0xfffffffffffffff,258048]
private def cubePart3 : Array Nat := #[0,5912485282197699,0x2afc001500c30c,5912485265682627,0xfc002a02a030c30,0x2afc0015fcc30c,0xfc002a02aff0c30,0xfd503ffeaff3cf3,0xfeafea03fffcf3c,0x3ffd5fd5fcf3cf,0xfffffffffffffff,16515072]

private def cubeValue (w : Nat) : Nat :=
  cubePart0[w % 16]! &&& cubePart1[(w >>> 4) % 16]! &&&
  cubePart2[(w >>> 8) % 16]! &&& cubePart3[(w >>> 12) % 16]!
private def banksCodes : Array Nat := #[0x4113312331254235423433353334231523142313222522242223112211110000,0x5226122641625122441635262241511125224115443233563141633253323426,0x3127423723192318312831292229222722281334333746323631343133466226,0x9111282256223546245148324732522325153145115131718332733237264118,0x5611336323548226722692264613112491226115362322453926382622712424,0x222a3984333a1339198219181726651681112922493239315362531383163535,0x52282518733423592942239482463175314711713958717378335318312a9725,0x9741583722473a2622a1952924275722811528674a3233a61376934992235229,0x4734353776375911822347499151a22653826729419471241127a12294263148,0x3986298211471175531a133a93569622529128243a312a1158763946a3163935,0x3648291773399339235a59422a42157623a43187942337293a23935313933a46,0x44694753242a2729811871183943782698269651861513a692299228522a2972,0x2447419949184719912947643399285517239726287162a62872317731782277,0x6834931938376618591597111629a622255729187171917153592377793253a2,0x6856a22357248722972252486913551852857916392854292829429918466a32,0xa916958298239428372a736967959373935813a33a863a76114a118711a51984,0x3a4319767a269a2699512a7153795867a61533a9922a36787962a155a73115a6,0x1a2317282a449a11974556773a29227a8458a2297863272a9627195839733949,0x95497184931aa37676189915591759721929674988344a198174767372832747,0x11a88954295788568a229a22581869924a9246a46599a319617984845873a129,0x117797519723982828751729469939489393937815893aa67175765871989955,0x8915a37393698962581a2a1a8864257759575a72698267a21973997619a6a2a6,0x479397245729957318769843398315a339793a733a49aa16aa26967599715399,0x4aa25775a82329a45a7158585a551a2854789448a2673a2a9429962995584889,0x44998744295a555a4759476975768a3488398179939472a35747891372894794,0x914a287455a425a9584928892a8495a22aa2174876a2192a83a4738986749359,0xa2732a589a46164a2847a93479391837544a167859749a155a4499449a429972,0x951aaa32a1a2a5926a927782796476842477882928577483a48677432a2a61a9,0x69185918a3a2a3848a5613996773885399279278527a924a7a1379196a199818,0x1a763a833a79a91513a9a962377a5a8269a299a69a23172a738a46a9394a71a5,0x9a7229a998a2a3598a39247a81a9a39453a98a13a7232a89a772a6298a719a24,0x99751a2a927a981a72a9a8197a92a786a2799a8638a9a189a9391a2987a69a17,0x6aa29858977197282878547a5a58577866a949993978a9531aa668a3a9557178,0x9837997398839a4339893aa3197984795a575a47a3a38992167a1778994715a9,0x9929585a964a886988598849957874897a43788696784aa387735a2a1a7395a3,0x8a64a9648a446a59a6747959a2a3794979699a554aa4799494787784aa235a75,0x95a49a4498845889995793796a69697964a94a6aa5a67993a593a3a48818944a,0x7783174aa743867918897589584aaa34783878392977557a59a4955a99829974,0xa569889384a3a684a6a287821a4998298894a1a4a44967a46889aa429891a483,0x28a849a9a7373a7871a8791859796aa69918a58474a3a473a4a66a9367a3aa24,0x9a7147a72a78992aa92947a89a279a379a7698a63a8983a9a9928a9293a79a28,0x28a979a2a379a389489a48a94a794a89478a79a6277aa179728a71a9a919a771,0xa88288a277a673a97a82a278a8867a86a9728a7282a9917aa8297a38297a7a29,0xa47987958a757958a73a99581a4aa993987319899aa67678177a91aa9a1a8a29,0x88589a5789945a5a2a8aaa17a3a8aa64aa928599a89498a45879a1a87aa29775,0x1978aa5378837869aa4387a34aa8777348aa1aa318a9577799a39a833aa98498,0xaa447967aa19a2a984892aa99748967758785aa5a9a1a859a92a6a5a677986a9,0x6789a38a7a5979734a7a947a4a8a874977491a79a5a3a9a627aaa9699747a3a7,0x9949a4a58a3a99957a2a68999a745aa459a9a6a45a8999849aa28a6974a9a774,0x76977984aa72aa868974aa812a9aa7836999985a5a4a588737aa8478aa399579,0xa81aa4a3a689a7a66aa3679887848873a7a289597599a1a984877a9477a46aa4,0x9a75197aa9739a7398a39399479989189729787628778aa68884a5a4a8a27aa1,0x67a8a7738a7319a9984a8a949a47a994995a994a88a45a799a589a48a589a775,0xa7475a87967a76a9a7847a845a78885aa869a84985a9a7587a93a893859a77a3,0x58a999a49a848a4979a3597a875a6a897a697a49677a577a57a7a959a949a489,0x75a9a5796a97796a8a74a974a67984a97a6874a8957a6a7968a977a5a9958a59,0x69aa1a7aa9a39aa31aa98a1889a29a29a8377a37a88487a469a96a9888a3776a,0x86aaa6a9aa48aa93aa836aa89a5aaa945a9a5a8aa8a49aa45aa9aa758aa55aa8,0xaa69a75a7a5a7a4a68aa6a7a6a8a75aaa47aaa57aa4757aaa94a6aa7a85aa84a,0x17aaa58aa5a7a4a9a8a594aa1a9a18aa7aa5a9a5a6a859aa8a6aa68a8a4aaa59,0x7978a83a99789a2aa5a8a7a3a76a8aa3a7a4a57a85aa7aa4aa74a49a74aa9a6a,0x78897899a873aa29a72a8898799988788887889758a72aa7a2a895a99878a958,0x778998798999a91a8aa297787979798978888a84889988798798a5997a7378a3,0xaa2aa8a6799867a9786a9979988999899788a3a997774a9a4aa9877977798789,0xa5a98aa4aa84aa58a9a47aa3aa73a8a39a4a4aaaaaa2a1aaaaa62aaaa3aaaa1a,0x9a7788a798a9a9787a6aa6a7a86a58aa5a7a5aa76aa9aa951a8a1aa8aa49a74a,0x7a997a79777aa779a789a999a989a977888aa899a879a8788a987a7878a988a8,0xa88988a9a778997a9a789a9887a977a9999a998a9a79978a99a989a98a99977a,0xaaa35aaa778aa997a89899a798a877a88a79877a7a898a97a97987a779a9889a,0xaa997a7aaa7789aaa87a8aa89aa9aa6aa6aaa4aaaaa51aaaaa5aaa4a6aaaaaa4,0x8aa9a77a87aa7aa98aa7a97aa9a988aaa8a9aa789a7aa7a97aa7a8a7a9a88a8a,0xaaa89aaaaa7aaaa9a99aa89aaa98a8a8a7a87aa89aa799aa9aa88a9a8a7aaa79,0xaaaaaa9aa7aaa9aa]
def banks (i : Nat) : Nat := cubeValue ((banksCodes[i/16]! >>> (16*(i%16))) % 65536)


private def nodesField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def nodesClassData : Array Nat := #[0x2aaaaaaaaaaaaa8009f,35,0x3feaa955540000000a3,4398046478438,0x2aaaaaaa955555550a7,41,41,4398046380137,4398046494826,4398046445675,44,4398046503020,45,45,45,45,45,45,45,45,45,45,45,45,45,45,45,4398046249069,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,4398046503022,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47,47]
private def nodesClass (i : Nat) : Nat := nodesField (nodesClassData[i/32]!) 6 (i%32)
private def nodesFirstData : Array Nat := #[0x46c6c6c6babaa81d1c9c9c929291918a8a8a85050504848484848000140202024000,0x5dbb15b274c992a54a0c183060c183060c18204040810000000000003802,0x6c00000000000002600000000000000000419060c0300c0300c0300c0300c0300be2fd000,0x4142f0bc2f0bc2f0bc2f0ba2e8ba1384a1284a018060180601806018060180000000881724389e19d002,0x2368da368d9663e8ce1b06c1b0520200400001405000,0x7f6c30000000000000000000000000002000,0x7fffffe4e1e1615d545444aaa89e119191919191919191919191918c8c8281804013,0x2c94aa54e271385a1b8d46a35188401008018040200000000000000039d5fafd4a9143a04800,0x41208a651a5cbc5e2d96c68341a0d068341a0d068341208c460d0683400000058a84c160c804,0x7a1e87a1e87a1e87a188080200401000000000000000000000000000000000004ff05a1084210845000,0x482412090452150a8542a150a7934592c15dadcce6732994c81f0f000000000000000000483d,0x8040201008040100800000000000000000000000000000000000000000000003ad5daec800,0x4b2aebae8a230c30c30c30c30c30c30c28a20410410200003002,0x4631739cd6b5ac6316b5ad6b5ad6b5ad4a184000282a,0x575d73cd34d348fbef0c30c30c3000000000000000000000303b,0x6db6db6db6db6db6ba9861861861861861861861630a10203066,0x76eee6444443bbbb0000000000000000209d,0x5ef7bded28b108421084210842108420a421063028ab,0x5b6db6b6db6db6db6c00000018c2,0x77df7df7df7d75d6db6db6dadd6db6534d12cb2ca38e000030cf,0x444444410000000000000000000000002112,0x6d6db2460000000000000000191a,0x575d75d75d75d75d75d75d755555555555534d34d34d01003120,0x41ec5ad6318c6318c6318c6318c6318c63184200294b,0x7ef3e7b45408101e364c993264c993264c993264c993264c993241c0395b,0x6baeba659638df7d934d34d34d34b2cab2cb0c300000000031d9,0x7676766cdad655d4d2d2d2d2d2d2d1d1bcbcbcb9373707070707070484828280420e,0x200802008020080200800601806018060180601804010000000000000006899e6799e6798adf57d5000,16,0x5ef7bde94a5294a5294a529400000000000000002812,0x555554cccccccccc44444444444400002029,0x55555555555555554cccccc8000000002033,0x5b6590c30c30c30c30c30c30c30c30c2fbefbef3cf3cf380303d,0x44444419999888800000000000000000206a,0x55555280000000001072,0x596596595d75d75d755555555550000000000000000000003074,161,0x7ffffffffd55540010a1,164,0x46318c2108421083def7b18c631084210529400028a8,0x6fbefbefbefbefbefbee69a69a69a30c30c30c300000000030b9,240,0x5b200000000000000000000018f0,0x75dddccaaaa99999999888888880000020f5,0x6665554cccc9999999999999999998002103,0x6baeabaebaebaebaebaebaebaebae1041041040820820800310f,0x7ffffffaaaa000001144,0x55555555500000001147,329,329,0x54ccccc44444000000000000000000002149,0x5ddddddcccc9111111088880000000002153,0x4444444443bbbbbaaaaaaaaaaaaaa800215e,0x7ffd52aaaaaa00001167,0x6edbb76eddbb766cd9b366cd9af5ebd7af468d1a3468d1a03060c180396a,477,0x5145145145145145144d34b2cb2cb2cb249249248000000031de,0x462e739ce739ce735ad4210842000000000000002a07,0x5b6c9236d2492400000000001a18,0x61c23468d1a3448912244891210204081020408102000000000000003a1d,0x4924924900000000000000001a7e,0x69a699e79e79e79e79e79a8a28a28a28a2818618618618603282,0x4cccc91111111111110888888880000022b6,0x540000000000000012bf,0x421081ce739ce739ce7294a5294a5294a00000002ac1,0x66cd9728c183060c182850a142850a142850a14000000000000000003ad1,0x555553333333333222222222000000002337,0x4a952a54a952a54a952a54a952a54a060c00000000000000000000003b41,0x423c29a9a9a8a8a7010101010080808080808080808080808000000000000000438b,0x2504a0941282504a0941282504a0941282504a0040080100200400801002004008010020000000083b03e07d800,0x6baebaebaebaebae9a69a69a69a0208208208208208200003025,0x7800000000000000105a,0x7ffffffffffffbefbefbefbefbefa0000000000000000000305d,0x55555111111111111111111111110000209c,0x4a952a54a952a54a952a54a952a54a952a54a952a54a94000000000038a6,0x5554aaaaaaaa000010f0,0x4d9b366cd9b366cd9b366cd04081020408102040810204000000000038f2,0x55555554aaaaa000113f,0x7fff00000943,0x46464646464646464646461212121212121212121212120000000000000000004144,0x5d75d75d75d75d75d75d706186186186186186186186000031d0,0x55552aaaaaaaa00011fe,0x7bf7efdfbf60408102040810204081020408102000000000000000003a00,0x6c0000000000000000000000000000000000000000000000327b,689,0x7fff55555554000012b1,0x5b6db6db6db40000000000001ab4,0x414141414141414141414141414141414141414141413e3e3e3e3e000000000042b9,0x50a142850a142850a142850a142850a142850a142850972c000000003b3b,0x74e9d22c58b162c48912242850a14283060c183060c18200000000003b8b,0x4f9f3e7cf9f3e7cf9ef1e1d3a74e9d3a74e8810204081000000000003bff,6597069775961]
private def nodesFirst (i : Nat) : Nat := nodesField (nodesFirstData[i/32]!) 11 (i%32)
private def nodesSecondData : Array Nat := #[0x68db4d844a29108844241105045884521f278783a1f0f0183e1e038180a880f0ec0602004805,0x6ab7faddbb96ee5b47dfad184f9eb92a4842610a84883464b95242003805,0x2221a056038c6889721a86800222699802c86a1a06603ccf1745cf8ae293230591444a8f23812a3c5001,0x4fd3f3aa8d2124b0ee368fc310a6298a829836378da1f06c1a862068140007e09822a920a82a0a2c500d,0xc62c89c2408a2207c1b0681782e0981a0600a0061cb8a92972348d234970fc23234218404f8cd4fd001,0xc90008621951cfd1f476e4b40c9b24a32468ba2c831e0779dc6599063186549323c89a2207619503c,0x2528e1ec9494b549ec53553432983cb305939ccc2386e1642d8701785c110420e032890b833001435036,0x25cfe3269721e6ba5c489bc1c866431584f8f8629ce21444fe2ecb19e806800ecdb8e5db8a8396e5d003,0x29e89a029525495154701ba809924610a400ee388962406c950d21b1203a0de2d89600444b2c590f5007,0x292a32608c1b21e06e982045e2f2987afddee390431013f2971c26c8b62284a00699a3d593b3e6b05017,0x284991fa4a12b1921e7e964539043f8fe5392a410ff8e14e760004a1204abeea127e8c22e8820c5cd0de,0x47308254931fc2f5c107e6f79d6116338b7a9ea0a72859e0769d860176518be2c8601000122ddf405007,0x1ae194ea878a51ca1e791e2769d869198648d42508a190420b8007619220e1b19122250836c595635081,0x8e0a8208b9c432e089b22436c38ac0e1853a0899ee4d8f62384e0901201800be94cbf8f66d11a30d038,0x24c5a91a0036c7d9aa2d1c1665052b30c799aa4d0cc12d9d4bd233f3b0d0b36bba9e8e2306f93629d078,0x54523b187e9dc649521e062005d825d4f5153b16364bd29a8595a56152380d23402812a088482284d0a2,0x285d13013cc613bdca62087594b1a2c85d8d00848ebdad6a521a861ba6c9805c14a438f82b0240050b3,0xe2368b02283ca70b446add954f91b3aa9815a55934479003e8da2e0b40b8045983c09000158171b50c0,0x1ce6d164498e4318c40852d3fc6706b8ab3a6c9415a538982483809001694670c192599605614849d0c7,0x438ae8f8380781483e148380dc2a1f83c0d804668883083c210780e0890e3ceb9000e583ecf87e0dd12f,0x56148500f8380100030d7f06bcce5b70c42b4a6a08741c86f9b668180550e82a098238660f83a0dd12f,0x7403077000400420e8003bf1f77235999c03391e7934980ba50268fc48200f074381909c94e,0x30abfa7a809b46799461984480ea298821183f053eaf83567219a148011fbf4d39fe2f046b204834514f,0x4ad635913a0812c2d07bfad6346cd2ca9fa76729ae5d9383b8bc2e8b22b0601584000b5000558f7514e,0x113013e2c3964f8b2cc3b2c7b4bcf53ccce2e8911ec7596c4f9364a914350a61f010030081c000f55173,0x284f61eb1d2e6ef723cb44337c3d2d5c92478e4492a66a847c3c0dd8c81047bba0ea1b004a12,0x2bd107c36b40daaf6bb4164b14496858b61f9b4d22a579f05901681b4822634801647c36ca8d,0x1492844ec9191a18e28400414752d8d9f9741aa008003194baa6caa94e25437c5232e7a6dcdad34f652cc191d81b,0x5872a48316c5312c28f336cdab1cb8ac8abaaa879ee6a992640fe3e8f43c0a426082198441082200516f,0x4e72f440861c9e774dc5ecb8f4f12e494962186d99e07801b03c8d23309622087986590d02c8a020d063,0x13a480d62c83f9f5cf6e4e12b2e0b22162204f8be273c4db2fbfeb7a8a6d93a2e88c00739aa4d12b5085,0x6d99f67b9564d8de335744f102d6629643f0dc006595cd5d0ca328a1afc06b18ce1941cd31cb128c5072,0x173247deeafa36356f5534dca722b80d2ae27899c6413e4a008849d8238119762cd432e111e3aed082,0x1d66e1b259162036ff2e8d82184350a7c7eebba06596ed953ece128c04f43b28620e5795a20008005084,0x24c861a4661946496851020061000070fb86476756b4bcf7314731bc28fd3c4c52ecb9ad89aa3e6650be,0x617249da140119250f30cb32747374cef1ec64e691c006c38c6177057b5bd3b44d0f3f4f331ca925d0a4,0x4ed2ac9f22c61174410bc29043daf3b9ad0b2ac62c6729c46b9885e9764d92c4a8e42d8ac2582c0050d8,0x16857126460f8358ce318c02a0a61683c0d8300a81c006b379d712646b17c38ee91f905f375d6742d0d1,0x5312b49b2148107c18f03baeab9adb2f8bcaeab729e9d26e8aa1c7b9dc5f0841805c1602a0980c0051b8,0x3be6688e13d914ecdb33c9ce4b4462e252cae8491fc640e605800b9a8c829aa68e191535f062e6a9d126,0xd62f096240801a84c0e8380d834088014dd3543c67180b12646b13bbe24034005672fcaf0e430f95115,0x4f6793a9b4d2451b87425eed7612c962a7522651a6e36198b0551f0c83c12078340e0300498b,0xb60057a426155c56154d273dccf304b11f44f1043109bfefbbecf9bccee3a6e8394e437adbb56d2d135,0x1293d418d0803152a0bb102210533fc6d154230388e230013fbe0a8a26588de235c76ec74f10fe385149,0x34cc92873e470e4dc91237cd685d79dd51fc77083b8e5382e032ac1aa69da26638661400135cbefad15d,0x1745a8634c4df2f4b913c2505b586b94c2d05c0d8340c00187d931f3ac40088fe3a4cc0c20dcdb2a512f,0x29e809f86898e4b91a348b4248480a8200052915c3eecb2e210497b52b1541b02bf0ebba8e9368a85149,0xc62e8b62d0ae288721905e170561484c120460880e00521434d51dc10f5ba6e7332c9afebcaf0b35159,0x4d4ccbc7c745c4434140bf3cbb35b4b3ae2c2ba7a11b9b181595120d0c85810041c1,0x69e3e15edcd04f4ec13f3ebe3db9b3b02c251e9c93928a098908078403020080425f,0xfdb9ae629494beed3b1894a4850c9107404fbbdee9b72d2b48cf31cc42f2afabca9a9aa528aa1d1f7,0x4b90e3fefd3109b98362c93161cb61d24c42beae2720044c869c66e58b625132e45cf0b94dca08695167,0x41ef0b8cd7b38c8a6e90887083b6ae2a08f2392ac0ed7b54c5aa0899f67612a3509808801243f6ef51e9,0x4a242ff5bab1552a92350a953a84aa4f2187c1e00cd62add2691ab43de8e16a3456e92004a74,0x3e5569f4620902158c39d9eb85980400bc5a251104da539178ad55a7d281db1ca570ac754ae0,0x40afdba6e6366d8312c32c0af2b4ab25489220819f27a9ba689886197e5b94c448dc2e08c0981e00523e,0x394e4b44b2aba9c9ba3a8c6268980033e6542d04beabb2ca70172ea38ecfb36bb19cce240829b46ad228,0x260a59cc6dc291409fac158954a7161eabbe50642eb448037fa5bf592c74ca3d0234892bca4c,0x13488300045dc8d3292813c6dafcfa64b8439ecb1718c451d0e57236d76b83c9d4e055214ab0,0xf417177aad9523dd5d6aad187db2801a6ccc5e06fc7db6daec84d45e0d007db71a0bd4aca98,0x50e3f1b5f2a9369a490ec7404af556a31c68af9589a49230e86431960ac48228741604004af2,0x268bc56cc62add61993ddeaec4a1585d9eb0c55e2ba57a50f23484c21e2ed6c240c000cf4aa7,0xac421f0b01ee550a4cddfaa34b9f0f66e2308401729cc99bed66aa3c7d666eb65aabb44cabf,0x2002c00c3dfe833195495f8fb6833598cb6229d3c9a4c2391a8a3e1e4de66301585c2712cac8,0x2c4f8712e58e69307f30172b8589788600b54d9c2d561ac962993d9e0e73a84bf9aab83d4adb,0x164909747d09bac74c1e0acf3792cd3897479e0b2401f8ec0153a2d0e6f0c722d1449c4c4afc,0x1898121007be3433ab2a2825960f075334339e1d99960a007b6eeccd29a221874348,0x3c36b02eadabaaaa2923928988868481009f98dd5451b7331206850484010080438b,0x483dd94f31e64f4e5a50be2a5a4c413b38b6302da8a81b80615a595352c13ebdc38d,0x56f56d5754d494f480ebba4deb64d01e21558359d5d52c3b0dbb6e4a8a99030003883c0a3a1ed3aad0f0,0x2f68d1ea5e1745693c1b04600777b3ebf6458919c4c71f5dd3e99a5e8d9ae69334811a13df3ec9a9d05b,0xfc3ecaf2b4ab2747d19c5f10c370bc2b0741701b1ec3308c1afa769d27419e6297e559481a022005212,0x55f5754121c04e939ca466b8ad5d4b400e538ede372c8801a6e8995e49835514dd354c5252dba2e2d0f9,0x36cdab64d12997edf778ddf75dd5615675053b48d21455073e4f73c4a11d3fcbf0040061354d4b51d115,0x5c36fdb56bda75555153d49505334bd2b4a5231fbdae93063d06c0f03207810006db8a5553f46cfbd0f9,0x30cbd2c67719c370711e43efebd2dc310b62647c1a863188589001b80127c771a40f00bd2f1bc2e6d21f,0x51e873b94c62230b81b417e900a80397c4e06d765969ccd65b05541b09bc7be522672a92ca82,0x46d1842d07be0f22f2bc2eab32c4afabc860011e3def0350cfaf4b8ad8b287725453063c8e738ccdd22f,0x616c33096c8e411a8a3b12e5a271347c00fbfd7e5dee46cf0b8298ca62510662b0b82b05ca7d,0x5ceacff74b85c0da6cb3d6a00d1e4af372aad4d98ca633118675db68f2388bedcae3409dcacb,0x4fa5f2a8f446210c85405a4aa3d94401eef378bb9c4ab52a4b1989c4a18e1598c7c1dbdb4a91,0x1cce251208c85a05007abc3dfbd5ae752790c7e3b188ac4a210e86c1fc9e0e96fb3f93bc4a88,0x27538944089001f9f67aba983a5cda4d2591be5ece6641505bebe9f1f8b85bc49de6de66ca7d,0x383bddbebb439acbe3f1989b0d66b11484c1609017c3b5d4e772389b8d2662993a98494ac1,0x5eaf378bbdd2e564a24f66d3599cb2370e75389b8da6ab4190c460ae56c2d140502005004ad7,0x1a0cc5a29948a2009a4b22d1484b5da8c445208d4652c95036199d4ca612b9448e3f198c4b3c,0x50a832f7dbd1e6e9642711689431286e00b3d86bb389bcb2150980bd9e8ed63ab958a64d4b0e,0x3d1dae3661b0d4622c15cac50249208441198c04a1e0e8480107793c5e0ac8b43e1509814b5f,0x6965e3e36261dad9d54e3c3a342ba5a412110d0a080603020068bff7f7726be6438c,0x22a09544c3c1393847c52e804a49a30980443eb9b82d209a1601514ec846c641c3de,0x74c176e56ab4a8478d35df0ab2a4c88f1a2efa53234501ceedc9115bbc09,514067925052506]
private def nodesSecond (i : Nat) : Nat := nodesField (nodesSecondData[i/32]!) 11 (i%32)
private def nodesWeightData : Array Nat := #[0x229a6cb8db8e391c8dc9524cc7,0x114904134da6dc8d349a4db6cc9,0x1e5e1d5e1e1dde2266080d119559dd9dd04,0xd1959dddd9d5e1e22222661e1c8d51d05,0x2622666262666aa640890d559d519958107,0x33cda0d37249657a4d2d96fd8c9,0x135321427956e5b77db6ceeccc8,0x1d19e199d9e59e65e219996269014d89107,0xb6932dc764b25ae48e38cc40ca,0x266a6aae2aee8d59e666af2f6f080cd1906,0x1b88a36a4936d05ba6cb69368cb,0x222667625e2aaeea6f72eef33b337404909,0x118d9d19111111155565991180dd584890d,0x2dae424b2e08ee9f6db389558cf,0x2cb4bada656bf50539238f5d4cd,0x10d1d5959dc148cd194ddd561d9d955990c,0x2e95d52da0c8d3ae4b659edb4cc,0x236e28c98e1b8369b8e58da48cd,0x24ae6960b97cd5b2da95b6db0cb,0x811151d90d119189514e18cc8185cd8d0c,0x90d5510c0d08948d0d5118d1591619910d,0x2d0b49ac65c4daf65d65ba59ccc,0x262f46dcb3480b737e8dbacd8cb,0x848d5554d4d958ddd9d999e261611c0d0b,0x1205c31414452491c92f8efc4cb,0x9604091d9c9161966591da15584c96210a,0x98d00949894019551e1859110d89910d0a,0x1d1849f29490d6ba529cdcf8ca529d0a42100730549,0x1ddddd9a2222a2626aaa666aaaaab2ed0f,0x21deec0515a21eef2ef5a222aaa2eeeed10,0x2aaea95519e22af1559dde2eaeaec116110,0x88888d11919a15cccd195808c8cd11d13,0x255c08d5dd9da1de5ea6a6a6a915dea8911,0x2aee6a4232ade2099dda1e1e22ea72af10f,0x1f32626aaaaa8409d9d5de266226266690f,0x1de6ad59e22565da2e819de1e21e9e2190e,0x100924164b4d269b564b1b8cd5,0x29da2e266a2666662601415a11649115510,0x865e2155da1de625e6222266e26a22d0e,0x19a6d4d151114155d59a991dd9819d55d10,0x1d59d5d9d9d5a0000898d0c9da44088cd13,0x84482492d36536934d26dc90d6,0x29c580884911951d91915d9da219dd61d10,0x18d12515eaa159112a610d1e5a000cddd10,0x1e2919cd9e2c06a219e1e66629b331a1d0d,0x1da5dd5dd52265a6ee64199e71e5f75950e,0x121e25ddddde1e04cdd5e008150cc890911,0x2eb76db69b477640a700605a8d3,0x24b24b2cb7c92490496596d94d3,0x14c134606594896c25259246cd4,0x3192d71d6c0255b54dbc9e590d0,0x1599996015a491dd99d5de4c915199ddd0e,0x11950d155d150d58111111924d55541110f,0x129269c4944896136ca48a70d2,0x115555551599118995d8a595159c0a1a10e,0x1019159999555a21a59a5e62e5ade1a5d0d,0x1de19d9a1e665e0011a999a199e1e26250c,0x21520d6665558194d11158d95a21119dd0e,0x199594cd95cd0d8dccc209155155511990f,0x195d6220519559801a1155a19d5d999610d,0x558d51e1188cd21e969595e6559a1ad0c,0x2a290059d99b2309995dede221deee1d50b,0x199e18991d71665961c11150d9c95995d0d,0x18d80495840c8ccd559218914da5cd9110f,0x2e32519659dda69c816161d96158615150c,0xe05410515a1d55654e665c90951555110d,0x15992564da5159965d5555554900a62290c,0x160a0e5e5e59dd9ab225202ceaaeaa2210a,0x1d8c0d20dd9e159d9e559a1e9191c1d990a,0x339d6359def5bdef7bce75adef7ce739cdfbc41814a,0x221a61e1e20119999a04155519dddc1551e,0x1ce0802029107290c63a5cd635ae7bdce7c1d084156,0x199dddddc4d9dddd99e0448819d961de11c,0x19d9dc4c0449d5599d9d555dd9de419591c,0x1dcd16e26a662e9172f6bbb776c16eee918,0x1cd6b9ad684e93a58d6b5b06b5ad684043892829955,0x32eeeeef2eeeee18221aeb23331a37b6d16,0x19962f32f6eef061e9aef2ec5a66ef116,0x12ee732aeaeef2ac4005e19b332f7333116,0x1aea5293a52949a10e739d4a52b6a012973a127354d,0x25174a31a4e5294e5201d266c9b294a5394a673b94e,0x3635b73748021f733733b33335005999514,0x1cf7b5ef28c8a6bdef7bdef83e0f0296b4c1f084151,0x22000cc732d8d8322d6ca3084a5164a5284a319454e,0x405555c589cc8e15dd1ddd9e1e222c9d18,0x1cf6c22f7944c431ce439ef735ce70c42180e85a151,0x1a6ad5f9e3332eec041e2599695deef2d14,0x1d9a3ab1eeb3b7733333730c21285501913,0x10832d0c731c849d2a5a5cb439ce6ba20614a81a150,0xb2d549ecc730cf33129aa37334110da90f,0xd248626565e2f51d71d69eeb0529a910e,86346256651]
private def nodesWeight (i : Nat) : Nat := nodesField (nodesWeightData[i/32]!) 6 (i%32)
def nodes (i : Nat) : Nat := (nodesClass i <<< 0) ||| (nodesFirst i <<< 6) ||| (nodesSecond i <<< 17) ||| (nodesWeight i <<< 28)

private def layouts : Array Nat := #[0x644104000000,17619096698880,17619096715264,70408472690704,70408472690688,70408472625152,70441775398912,17665217265664,90211352704,90211090560,90211090432,39732707344,39732707328,39732641792,39728513024,70374112888832,70374112954368,70374112954384,70374112886784,73032269824,73031221248,73036464128,73032533120,73036727424,73031222272,73035415552,73031222400,73031483520,73032270848,70373055922176,70373055926272,70373055938560,74766792785920,74766792802308,74766792802564,74766792802560,74766792802304,70369012613120,70369012633664,70369012629760,70369012613184,70369012613376,70369012633600,70369012615488,70369012701504,70369012617280,70369012633856,70369012629824,70369012629568,70369012617536,70369012613440,70369012615232,70373041524756,70373041588309,70373039144960,70373041592384,70373039214661,70373039214596,70373039149056,70373039144977,70373039165444,70373039230997,70373041590272,70373039161348,70373039144961,70373039165440,70373039233109,70373039210496,70373039147072,70373039161344,70373041242112,70373041524757,70373039145024,70373039214656,70373039144964,70373039495252,70373039229008,70373039226880,70373039161408,70373039165456,70373039230976,70373039233104,70373041592400,70373041590341,70373039230993,70373039144981,70373039149072,70373039210500,70373039210512,70373039214592,70373041590288,70373041508352,70373041524740,70373041504256,70373039161345,70373039144976,70373041520644,70373041569797,70373039147076,70373039161360,70373039407120,70373039230977,70373041520641,70373039149057,70373041590276,70373039147008,70373041520661,70373041586176,70373041588308,70373039163472,70373041586180,70373041520640,70373039161365,70373041504261,70373039210497,70373039147088,70373039233088,70373039167568,70373039161361,70373039423492,70373039212624,70373039216720,70373039149060,70373041520660,269829199,269766735,269505862,269571392,269766991,269571398,268718406,273958217,273962311,269833543,273958214,268452161,269484096,269500673,272630016,273961295,273958212,268435776,274027855,269763849,269833545,268435520,273962304,273962313,274027846,269766665,269762825,273960969,273957193,273940804,268718089,268763200,269750281,268718409,268713984,268702016,273956937,269828352,269550912,269815872,269746246,268718080,268764480,268435456,269502729,268703808,274028870,269500681,269833551,269833537,274026575,268455936,269833542,269832518,269504774,268452105,268439808,269500672,282416199,274026822,268702022,268702790,268456006,268439616,269549568,268435526,274027844,273962308,269502721,269500737,269751364,268701764,268436480,273962319,273765702,268718153,269812800,268714054,268702025,268437760,268699712,273962055,269766982,268718337,269762822,268701702,268697664,274026569,268439814,268452096,268697670,268439622,273958208,274026566,268701760,274093385,269832521,269484288,273695040,269746176,273945921,273694784,269500480,268435712,273961286,269571407,268435718,269488128,269502720,268523846,274026831,269504838,269899081,269833549,269898052,268849156,269899078,268702017,268701700,269828416,269764864,269570310,269762816,272896068,274093382,268703812,269833536,274026502,268784975,269500417,268439552,269500416,269815814,269828102,273698822,278151168,268435462,269746432,272716096,269766661,273940800,269504521,269766985,274026825,269746438,268767561,268701696,268451904,269828096,268767296,269751360,268783616,272629760,269746240,269815878,268697856,269750336,269766726,273961225,269746441,268697865,274010377,269505871,269815808,269815817,273957129,268713993,278155273,269762569,269750278,268435465,269747273,269750598,269750272,268697600,273940548,268697668,273942857,268783680,272912448,268718336,268451840,273961216,268439558,274022720,268439556,268505088,269811712,268714048,269746505,273958153,268698944,268698948,268715332,268703044,269829449,273958221,269833540,268784964,274089289,269766980,268436804,274027849,268719433,268436800,269747264,269747529,268502336,268714313,269816905,268714057,269484352,274027840,268435464,268697606,269484032,268714246,269763593,269832512,273944832,268701766,273961289,273960960,269766976,268783942,269833541,269768006,269766918,268703040,278156614,269832527,269763905,268435713,268783872,269763840,269833472,268783686,268522822,272912710,268698880,269766912,272908614,268457286,269566208,268718345,269762886,269751625,269766662,268456262,269811782,268521536,273944902,269832516,273956928,274010438,268715337,268501312,272782662,269766921,269767945,269833216,269504512,268451849,274006281,272961860,273945670,268698688,269570374,268697604,269747200,269766656,269768000,272912704,268521472,268457024,268500992,278220806,272651264,273940550,278138880,268701952,274006086,273957120,274026816,268767552,269750592,269817152,268768320,268505408,277173312,269816832,273962048,273940489,273957184,272650240,274022729,268452160,273695049,272908617,272715840,272651520,274024448,273956864,273940480,273698816,272892160,272908608,272978240,274024713,273956873,272646473,268456192,268718144,268783936,269828169,268439872,273700096,268517440,273694976,272695296,273944576,269830400,272695360,272646464,273678336,269762560,268452864,268521792,269484041,269484297,268435524,273940745,269746496,269811968,268832832,273764617,272646208,272629824,272959744,268765504,273941760,269812032,269817156,273944582,269767680,272781577,268582912,272633856,273697097,274028873,268452102,269816896,272974144,269504582,268702726,269812736,278201664,269485056,268846080,268698624,268715008,268451913,269488393,272630080,268697862,269813056,268701769,268784966,269762630,268453193,268764160,268501056,269504768,268702982,268439878,268440576,269488454,268456960,268454208,272646400,272695616,277151744,268763136,269549824,269816900,278222150,278135808,277876736,268850176,278024192,268702720,276890624,278200640,278135040,273940736,268714240,277152832,272634880,277939456,278201344,5576021,5264721,5330389,5625173,5592541,5600629,5469655,5756373,5600759,5756405,6157813,7673725,14112117,5723509,5592917,5601109,5732181,13980757,5593045,5726037,8213845,5731669,5339095,6125525,5600597,7722837,14112629,6117335,6125399,5338583,6247765,5592405,5600599,6116821,5594452,6249845,5625181,6124887,6124885,6116823,6100305,7722327,6125013,5600725,5592407,6116949,5332861,5633375,5592341,5723477,5600533,5756277,7853533,5338581,7853429,5756413,5330423,14114269,5330933,6280663,5731703,5725557,5594485,6157821,6125053,6157591,5594453,1168660,1085508,1167685,1,16388,349265,5592437,4457733,5596541,4097,98340,1052672,82017,14112085,14112597,14114133,5625693,1398597,5723988,6248277,6149463,5592533,5594455,6116701,6149469,5588309,13983061,7691605,5723605,5602647,7689557,5592535,5338455,13981013,1331473,5592413,5592925,5625685,4577117,6125012,1398085,5328213,5723217,5263685,13981045,1385621,5594581,7689589,1336593,1332308,5330391,6125015,5854583,6116725,6116695,64,5596501,1312001,4096,81984,6116689,6640983,4277508,90176,4160,17408,5602645,7692101,5725525,5592469,6639636,1398101,5591061,1048580,5723479,7673695,7722871,4543607,5592342,265557,7724381,1381908,0,5657941,5592149,13981141,7692117,7689565,7690069,6643161,268368,6243669,6249813,65872,6116693,9783637,6115669,1589265,16078677,13989207,14638421,13981533,13989206,1064960,5591125,4259840,1066048,1332293,9786449,5592404,1064964,4214785,4194368,8732736,5594583,5731671,5609045,1377296,4456453,345093,5723221,4542484,5598550,65,1197060,131072,13983573,1380612,1380420,349268,5572949,17412,14111829,5594461,14014301,14014293,4473108,5328901,5526869,4472836,1065024,13983063,9787733,13981029,5608789,9786709,263424,9787743,4198400,328722,266322,2,7697750,5662054,5596503,5592662,9852245,14111093,5596502,5657957,9721168,17476,4457728,267521,5526852,1053952,4539653,5602641,5658965,5723607,5724501,5592409,5725527,4210752,1397841,65540,344129,262208,5594965,4476928,9786448,5625169,5593425,5600593,9852244,13981525,5921109,6117205,5588244,65860,81985,262228,13981009,9785681,13990995,9787729,5593941,5592913,278528,5600341,13991254,5594454,5591377,6641236,9715984,6642001,7673685,4,14013781,4543824,1048576,1065232,266244,8388608,2048,5330261,5363029,5592661,5625429,5858645,5887319,9524309,5326164,4195412,5572180,6124821,5334361,13981021,4260176,5332309,1393748,1065028,4259920,4195396,17472,262212,9794901,6641045,1398613,5596565,13989333,9792853,17409,1065988,5592669,5723485,5592406,1065216,278784,4527189,81920,1066304,1136192,5592148,1064969,1048592,9852310,5596581,5596486,5592565,1048832,1402213,1311744,7689591,7690103,271426,353317,5395540,1311760,5854545,5521668,5242880,1066052,7722325,6772085,5592919,6673749,6640981,2445652,7689559,4543557,6378517,348501,5588566,364821,16640,5326405,1118468,65600,1398161,256,13981014,5600598,1398230,4457732,352272,356352,4543957,4523013,65604,4547605,271442,1048577,352321,5527109,5592645,1377685,1328212,4195328,1381969,4216133,1092,5571908,5522500,1332309,4194304,5587268,1328468,4198401,5854805,353601,528449,1049664,1024,1398357,4260869,1066085,1377872,5592677,9700368,5124,1050176,5592660,352577,1088,266324,5510487,1119300,5854553,1066564,1394260,1049156,1114113,70720,1381445,1115152,1115137,5120]
private def layoutIndex : Array Nat := #[0x80200802008020080200802004010000000000,0x40100401008010040200401008020080200402,0xc0300c0400c0300c0300c0300c0300c0300c03,0xc0400c0400c04010040100300c0300c0300c03,0x1806014050140401004010040100400c0400c03,0x24090200801c0701c0701c07018060180601806,0x2c0b02c0b02c0b02c0c02c0b02c0a0280a02809,0x340d0300c0300c0300b02c0b0300b0300c02c0b,0x48100401104010040110400f0400f03c0f03c0e,0x5c130501304c130501405016050130541505013,0x50190501904c140601405014050140501505014,0x50130501b06c1a0501904c18050140501404c1a,0x501404c1404c1c05014050140501b0501405019,0x501405014050140501405014050180501405014,0x781d0741d0741d0741d07414050130501a05014,0x741d0741f07c1d0741d0741d0741d0741d0741d,0x802208822080200802008420080200741d0741d,0x802208020080200802008022080230802008820,0x9c25094290a0270942609425080200902008020,0x94270a02509425094250942d0b0280942b0a82a,0xa4300942f0b8250a42509425094250942509425,0xcc250a42709428094320c425094290942509425,0xd83d0f03b0e8360e4360e0370d8350d02509425,0xe8440d8430e842104400fc360f8360d8360d836,0xd83a11c400d8360d845118450d836114360d844,0xd836128431244810c360d8360d8360d83610036,0x154540e853148510f85013c4e1343a0e84c0d84b,0xd8360d8450d84115c360d8360d8431283615845,0x164450d8361004a10036114400d8361603610036,0x17843104360d83a16c360d8400e8361745c16c5a,0x18836100611805f0d85817c5f158360d83610436,0x194360d86410c3f1144d1344d118360d83618c5f,0xe8361743a0d83610c360d83f0d8660d8361143a,0xd8400d8400d83b0d8360d8360d8360d8360d836,0xd8450d8361405f0d836104670d8360d8360d857,0x1144d14041134360d8360d8361a04a0e8360e839,0xd8360d8360d8360d8690d83610c360e8360fc36,0xd8400d8360d85f0d8361a8360e8360d8490e840,0xd8430d8361ac360d8360d836154361603610036,0xd8360d86312836138360d83619c3616c3a14036,0xe85f0fc430e86d100451006717c3a1b0581703f,0xd8360d85f1bc360d8430d86e19c3a0d86e0d836,0xd8361a8360d8361c4360d85f0d84a1284a12870,0x128450d8360fc5f10c3f17c4a18c4a0d83a0d836,0xd84c0e83a0d8360fc460d8571c8570d83610036,0xd8730d8360d8360d8360d84a0e836134360d836,0x18c581585618c5f158431d04317c630d8560d84a,0xd8360d8401c8401586317c560d86318c750d856,0xd8360d8360d8360e8360e8400d8360d86717c36,0xd8430d836100360d83a100360d8760d8360d836,0x1b4741a0360fc360d84015c570d8360d87719845,0xd8361e4360d8360e83a13c3a0d87818c7418c36,0x1e8770f8680d8361804a0d85f180360d86311436,0xd86719c3a0d8361804a1ec360fc360d83f16036,0x20882204801fc7e1f47c0d857180570d8670e836,0x2449023c8e2348c22c8322889220872188521083,0x2689f2789d2709b268902649825c962549424c92,0x29cab2a8a92a08f29c88298a5290a028ca2284a0,0x250802d8b52d0b32c8b12c0902bcae214ad2b0ac,0x308c1300bf2f8a72f4bc2ecba2e47e2e0942dcb7,0x32ca4328c9320c73189024cbf200c529cc4244c3,0x2007d2c0802b0b529ca7348d1340cf33880334cc,0x36cda3549e3649e360a735cb0234d6344d5350d3,0x38ce22ac912d4d22c0b5384e037cde260b0374dc,0x3bc813b8ed3b0b72b4eb3a8e93a0e7398e5390a7,0x3e8b439cb429cbb3e4f83dcf63d4f43ccf23c4f0,0x2dd033f90229101400ff3f8ce364fd3f0fb2b0fa,0x3650a4290942107411062c09f2c105220e7410b5,0x29d15450b344cd6449114410f2ad0e39d0d4310b,0x37d1e22d1d4711b2410a3ed1a4651845ca741116,0x4a1274992546d2448d2246d22439212552047ca7,0x4b52c2792b2c0da4a8df29117438d23fcdf37d29,0x4c5134c0fe4a51337c943e8fa2052f294a54b8a5,0x369384c4ff4dd314d8ff4d49e4d1333c91f43932,0x4ed3b26cab499244893a2453924131368d14c4fe,0x518d5514a65113c50d425053b5013f4f90a4f53c,0x535174914c52d4a491395153f245494fc9152147,0x545264995037c832ace3374d22352430d4f53891,0x4a91f37cdc29d533fc8839ce729c8255153548df,0x525175595637cff554da29ca738ce329ca73f8af,0x2348856d5a56558358d355cae368a74a505278df,0x54160574903548157d5e5748537d5c238bd38c91,0x5a8b0361695a1675988259564285632856258494,0x354b55bcb55b9583416d354d02d566340945b16b,0x2ecd52ed58209745cce33d9722d1715c0fe22d11,0x250d229d1729c9129ca72ed762ecb5560e325975,0x3397a5e4da450a7279784c57729ca74a92a34917,0x45cff37cdf204a754cd4338b75ecda45ca738cda,0x450ff60981471226011b5fca74657e5f8bb5f57c,0x37cdf278a7374bd4c4a729d866155129d8460d1b,0x62d36628a74a8df6250e3e1884950525187348a7,0x278df4dcaf644a76418129d8f4398e438a76358c,0x38d96279953e9945aca764d0e4a92a40d2a64952,0x4d8ce368fa578fa4451128c9f6699966197410a7,0x518984e0a76059e6759a3f8a7670fe3f99b50533,0x68c935699f5c90b4d15b56498689a14298a6819f,0x6adaa689a94a99f6a12f69da667d3469498691a4,0x6a9176c9b16c1a0690af6bda3695ae42dad4a5ac,0x4552942db74a9b6689b56d10b6bc98249b36895a,0x258de24d29644af2452a62ca76e8df6892a6e5b8,0x499a26fdbe29c96485bd6b9bc245a554dab455bb,0x3c8a7355c126ca754c9e4a92a4a92a55d2629dc0,0x29ca729d81605c3708a7438ff29d2a414a72790e,0x3fc9129ca729ca74cca7235c5714a729ce34c5c4,0x438e3624a7450912f4b029d5329dc64c4a754d31,0x4a90e71d0538c9e29d2a45d2a35553450df52553,0x54ca74a9144a91f47cf229d2a7211754d88278f2,0x244dd29cfe29ca72791745d17704d5278da7252a,0x29cda29ca7695cd4a89e29ca7245cc411cb561ca,0x54c9e29ca7244a729d2a279cf738df29d0e24549,0x62517278df45dd3291d2359052c1527452a74117,0x43ca7751884c553278d5278d2414df4a8f23c92a,0x29c9e368df4a8a7235d629dd5548a74a89e45ca4,0x29d3175d2a29d3129dcd4c5d73f9d743d7c29ca7,0x29ca731131711824c5a243dd9761c44a8ff7059f,0x774a729ddc4ccbc76cb0368a729cd229dda29cbb,0x4a8df29d5829db3374e7778d13f8fe29ca739cb4,0x358da4a9e3789e129c9f3c8c34a9e037de04a9df,0x470da54d8929cdf344a76509e45d3729ca729de4,0x4a8a7798a739cfe705e529d532f52335ca729ca7,0x244934a8a029ca754ca779da429dc24c49129d0b,0x29ca738c8d29d2a29ca72cca738d5129c91498ab,0x4cca729ca77a8a729cd945d1737de977d374a9e8,0x4a92a7b0a729ca73f92a2789137ca3359eb29cfe,0x4e0d729dee29ded38d53244bd29cd245cdf4a89e,0x39caf35cd17c114744fe7bcb92dc91369ef2ec91,0x39df57d0863f8a74cce729df3219f238df129cbb,0x2d4913555829cbd3f991244a73fcd53755339cd1,0x29cfe5f10f26df9244a77e0a77dca7691f6710a7,0x7f117205df38dfb355f8438dd2ad17228d538dfa,0x29ca7368da4389130c9e4a93730d8826c9e45cdf,0x311e129d5229ca729cff29ca7801ff650e37f9fd,0x358e329ca729ca74c4a7310a731203809ee77e01,0x4c4b429ca738ca77b0a743cda29d4f29c9129d37,0x2c0e739ca77e4a7818a78188a41605810d24a92a,0x548df29d2a29de054994549df26c9e3591737d58,0x4a9df4a8a729d2a81cda5609e29d3729de054958,0x828fe29ca729ddf824a74e0a72ecfe4c4a78212a,0x85e168561484e128461083e0e8320d830a782ca7,0x89e268962488e228862087e1e8761c86e1a86618,0x8de368d6348ce328c6308be2e8b62c8ae2a8a628,0x83e408fe3e83e308f63c8ee3a8e6338ce3886e36,0x9364c8c24b92a49922478663f91a459124390a41,0x8862b96e5a9665895e569565494e529465093e4e,0x992638ae629861a8f2608c63697e5e88a1b9765c,0x9a66e8b26d9b26b9aa699a2368b62f99e6699664,0x862739da5e9d674866499ce558ae729c6709ba6f,0x8f65c92a7e9f67c9ee7a9e6789de2b8ae739ce31,0xa1684a0e2b8ae82a062b8b22ba027f862729c24e,0x8ae2ba2686a227ba1e7b956249c22b8a66da1a86,0x8e2929ca648de9189290a3e8ea3689a328ba2a8a,0x97224a663d9fa9997298a5e96a56948e26f9c293,0x93a2ba82709a69fa7a4a83e24a769ca6e9a8626e,0xa9a709c23d866739b664a96a4a8e649f63da8aa1,0xabeaeab6acaae5c86a24aaaa9aa22b9be2b8aea7,0xae6b88aeb7adab593a38ad232aceb2a9eb1a9ab0,0xafebeaf62baf2bbaea2c8b293a9e5c8924e97291,0xb124e8b2559ee18b0e70b0a2bb06199c24ea66c0,0xb3a0f8927092a29b36ccb2ecab26c8b1e2bb1ac5,0xb62d79b6d68f693972d5a4ed4b4ed2adad1b42cf,0xb92e3b8a2bb86e092adfb7a7bb760fb72dbb6ad9,0x8b26dbbe6dbbaedbb26dbae1abaae9ba2e7b9ae5,0xbe2e09c25cbdef69ce87a4ef5bd28fbcef2bc6f0,0x8b302c07009a62497291afeffbfafdbf2fbbeaf9,0x8ab0998a87c2307a8706c1704c0e70b5a2c89291,0xc4b11bdb10c3e65c3b0dc3309c2f0a99a3dc26a2,0x9c319c6317c5a3dc565c8f63dc52a7bea709c313,0xc9b25c9323afb22c871cc1b20c7f1ec771cc6f1a,0x8ae2bcb270cae1aca72aca7289ca4e83e30a8727,0xcd331cbe2b8ae2b8af33ccb31cc32fcbb2d83f26,0xcfeedbb73ecf73ccef3ace738bfaa1cdf369cb35,0x86b44d0e3d8b2a79b74296a6bd06949bea4bc340,0xafb4dd322b8af4bd2b49d22b9d1f46d16389d22b,0xd4357a6756d5754a6753b6aed86b52d4750d3f4e,0xd862b9fb609c308d7f5ed735dd735bd6b5996b58,0xdab69da3679c360d9b659c364d8e558e362b8308,0xdce2ba8694d1694dca388af71dc36fdbb6ddb36b,0x94f7bdea94de68c893788df77dda86dd745dd2c4,0xe1f86d7f85e1383e0b81e037fdfb6fa437da3b7c,0xe4b82e037ae4790e3f8ee365ae338be2b36e2788,0xaff9ce6f9ae675fe6397e5b95e5386cd783e4f92,0xe8ba5e93a3a87a2a62c4e87a0e7ea1e7b5fa8f9d,0x3aaa87a9ea39de9fa6]
def refLayout (i : Nat) : Nat := layouts[(layoutIndex[i/16]! >>> (10*(i%16))) % 1024]!
private def payload0 : Array Nat := #[0,0,0,0,0,0,45056,45057,45058,45056,45056,126978,45056,45056,114689,491520,229378,0,401411,45059,503811,491520,0,0,491523,0,0,229379,0,0,0,0]
private def payload1 : Array Nat := #[485345382406,485344333830,485338042377,485338042378,485338042374,360785039367,360789233672,485347102726,322137296903,485348102152,188994359302,188995358731,180241,322126811140,322126761988,322135150613,188989116437,188992262165,360796573716,322132004885,322126761989,322141491227,189000650758,462870,462871,180246,180247,189003796500,344089,485352722451,180250,485359685651]
private def payload2 : Array Nat := #[189006942228,189006942228,344092,188983824389,307225,180252,344093,180253,307230,462879,180255,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,137439117318,137442263060,61444,61445]
private def payload3 : Array Nat := #[61444,0,0,0,0,41038454898728,35399164936231,41996235751465,46149676,49542495244333,50642006745133,51689966309430,52991343370294,53940527996982,85605840793686070,57239076655156,58338593382463,59438109204516,57733177,58781754,64935672586301,65073214,69333724610621,69333725659197,73882082267188,17242796100,72364098,73412679,75558984,76607562,75,76]
private def payload4 : Array Nat := #[12365,16438,176191,32,54,455368245307,61,455367213101,0x6a05e040342805f,455369310263,562743476281,562744524870,0x6a05f000432805f,605695246410,455371391049,0,86,0,84934744,270664917078,229462,0,0x59410030505d0f014,0,0,0,98391,127064,274519,0,274523,0x3f04e0005b410000505c0f006]
private def payload5 : Array Nat := #[0,0,87158873,0,0,0,0,0,0,94,0,86,368719,0,80,0,21573566468,127064,0,0,0,0,95,274523,82,0,99676165,137439117318,137439117318,0,188502,0]
private def payload6 : Array Nat := #[85,0,0,0,137442263060,0,0,0,0,0,103174635615,88,0,88,0,0,0,0,0,0,94,0,0,0,0,0,0,0,0,0,0,0]
private def payload7 : Array Nat := #[0,0,21573566468,0,127064,0,0,0,0,0,0,0,0,0,0,368719,0,0,0,0,0,0,0,0,0,0,0,450641,32853,0,0,0]
private def payload8 : Array Nat := #[0,0,0,0,323685,426086,426087,0x2606f340894f089,352375,426091,524398,286833,0x46074460853f0856f086,0x3f069260876108868087,0x3f06a260876108880087,155752,258155,0x46069260886108768088,286828,258157,0x460692608761087,286832,0x4606f260886108768088,286838,258167,155763,155762,155765,286842,352377,0x4f078260883f0884f08c,213115]
private def payload9 : Array Nat := #[213116,454781,213118,369499660431,155775,155776,0,0,0x620a0410ac280a9,0,421066469528,467092,544919,0,0,421118898359,421144039650,421097902262,0x5005470ba280ba,0,467135,0x79000620b4870be6d006850bc72096,580050387089,0,0,0,0,0,0,164040,421094781085,0]
private def payload10 : Array Nat := #[0,0,0,0,0,0,0,0,0,290993,0,0x8e0d8410db470e2,0x8e0dc850a9280a9,0,610086846678,290989,0,0,0,0,291022,0,0,0x410e4470e2280a2,571453112489,0,164046,0,421094781107,544937,0,21479497954]
private def payload11 : Array Nat := #[0,0,0,0x610363f0816e09b5a0e84709245098,0x3f03661081810997f099000360408147096450966e102,0,0x3f036610818109e7f095870e81303413088,0x8d0a9150e900087550a2000fb,0,0x8d0a55a0fa450a6,0,86251,305124081898,0x7f0af130ec45091,0x8d0a26e0a2130fb850a2550a2000fb,0,0,0,0,0,0,0x5a0345a088810db6e0ba5a102,0,472623894754,577787,472640942320,0x8d0c16e092850f10002000083850cb550bd8d0f1,545010,577686,0,33554563,545010]
private def payload12 : Array Nat := #[33554563,0,0,520336,0,0,520391,258102,450704,0,0,0,242,0x61036610846e0c2850f3850a94509100102,545000,0,0,242,0,0,0,0,0,0,0,528532,135,0x8d094550f000087,577684,348351,0,0]
private def payload13 : Array Nat := #[0x3f0878d0a16e0a9130f40403f13082470c345092,0,0x8d0c76e0a20403f13082470c3,368876,553196,605768048805,472632000647,0x7f097150f24709c,0x810e26e098150f2,0x6103d610868d0e26e0a0150f2,0x8d0cb7f0a9150f20403d0408685096,0x3f03f770828d0cc6e0a7150f20003f2b08247096,0x61020610838d0ca6e091150f213088550c98d0fb,86258,0x8d0a26e0ae5a0f7470a93f0fb,0x470ce550c6000f6,450739,365329412252,0,282778,577687,0,0,0,0,554238824605,545619726576,0,520343,0,0,0]
private def payload14 : Array Nat := #[0,577782,0,554220941538,0,0,33006,450712,0,33006,282824,33006,0,0,450720,554228068602,0x6103d610868d0e26e0cb130fb850a2,0x6103d61086130ee,0x6103d610866e0c45a0f255096,416676188294,0,348401,249,0,0,0x3f02d610875a0f8,86264,0,0,472627892457,577705,472635146491]
private def payload15 : Array Nat := #[0,545634406640,0,0,0,90448613548,291018,291018,605760803018,0,291018,0x77020770836e09f550bb,0x7702077083810db550916e0ea,33010,0,49662848684211,291018,472667943114,0,0,0,397375,554235850928,554235781294,554235781285,450739,472683729065,528560,386688905435,0,0,0x8d0d56e0c0870fe000fc]
private def payload16 : Array Nat := #[545008,450779,0,0,0x5a03f610827f0963f0f2,0,472683663529,0,0,577710,0,0,545008,416659271815,0,545008,0,0,0,0,0,0,0,0,0,0,305118839034,0,250,0,450802,0]
private def payload17 : Array Nat := #[605776269515,0,0,0,0,0,365343203586,545634230522,0,0,290996,0x810b17f0d95a0ea,0,0,520357,0,0x810e45a0f245096,348402,0,553201,282817,0x3f0393f08a810e47f0da130ed45096,0,0,0,0,0,605763854501,472628175098,0x8d0d97f0b55a0fa,605763924141,450766]
private def payload18 : Array Nat := #[0,472683663526,0,368890,0,577701,0,0,16438,0,0,0,0,0,0,0,499962,78066,0x810a9550eb00087,0,0,78066,0,0x770467708b6e0db470b3550d700100,0,0,544932,0,0,0,258288,0]
private def payload19 : Array Nat := #[0,450802,0,554288050323,0,0x470dd4509d000ea,0,0,0,0,0,0x6102d3f087810987f0e2,0,0,528555,0,0,0x810b56e0dd850ee,368880,0x3f03f77082130ee,0,580068049151,0,0,0,472676040839,0,282791,472676331739,0,0,0]
private def payload20 : Array Nat := #[472683663586,0x3f036610816e0cf130fb450bf,554288304290,0x6102d5a087810b06e0a20402d00087850a2450b0,78075,544930,90458587388,251,520381,251,0x6e0c50402d00087850a2,78075,528610,472616554722,291042,78075,0,0,0x5a0345a0888d0cd6e0ba550a2,0,78075,90458587388,0x5a0345a0888d0d06e0ba550a2,0,577703,0,0,0x5a0495a08e6e0b3,290973,0,0,0]
private def payload21 : Array Nat := #[0x7f0914709d450de000ec,282830,282830,282830,282830,0,290995,0,0,0x770497708e450df8d0ee,0,0,0,0x5a037770897f096470ab550de8d0ee,0,0,0,0,86267,0,282830,472634388637,282794,544932,472683663507,577707,544938,545630998754,0,0,520356,282796]
private def payload22 : Array Nat := #[0,450818,0,0,554280702097,554239525122,605776269515,0,397366,545630998754,0,0,368880,368880,0x8d0e57f0d00004a0008d850b1,0,0,0,0,605775388897,0,368878,282802,0,0,0,0,0,0,0,49495344967842,0]
private def payload23 : Array Nat := #[282802,0,571481804972,0,472606077080,290993,528610,0x8d0e27f0db150f20002d04087,528610,90448359596,290990,472606331099,90448359596,90448359596,554288050330,472606331037,90448613548,0,0x6e0b7550fa00036040814709f,545674252465,472606077147,0,90448359604,291008,472606077107,365335957682,450818,554231169282,258285,0,0,0]
private def payload24 : Array Nat := #[0,290996,90451247349,0,0,0,450818,348418,0,348418,0,0,0,0,0,0,0,0,0,0,0x7f09b470e4000ed,0,0,235,78057,0,0,237,0,0,577717,0]
private def payload25 : Array Nat := #[520354,0x3f02d770877f0928d0ec,0x5a0886e0b6450a6,0,0,0,554218901723,554218836147,499970,0,0,545630998754,0,0x5a0345a0888d0e66e0ba87103450a2,0x810e26e0db550ed0402d00087,0x6e0a40402d00087470a2,0,472611320027,0x810ba6e0d2550ed1303413088,472611319987,0x810e20402d00087470e2,0,86258,0x7f0e0550ed4709c,348402,86253,0,0,0,0x8d0b0850fd0002d04087850a9,0,0]
private def payload26 : Array Nat := #[0,450740,472634642651,0,0,0x3f02d610876e0b0450e2,291025,0,282810,0x3f02d610876e0e2450e2,0,0,0x3f03761089810b76e0e3151014509f,0x5a0345a088810db6e0ba5a102,0x5a0886e0b6450a2,386817872052,0,554288050402,545638338786,0,0,472683663586,0,0x3f0343f0887f0a2850e4450ba,282816,0x5a0345a0886e0ba450a9,0,0,553200,90442858733,365326008557,0]
private def payload27 : Array Nat := #[0,545019,580068081915,0,554238759091,0x5a0345a0886e0ba450e2,554290139313,0,0x92e73b2e74914b1418d1414b4918d090696a1111a06970111,0x9283671ac192e77d1726c16d1b069491137806b14111,0x4816f14172632e72d14b5f168792838311135069,0x91702512844168632e73e1285f168792e7,0x2d281672816632e7d1ac4d1ac6c32e6406b6c1138906b66113,0x2d19a4814b141727d1752d14b2a1726c1754e1163506f,0x4e3526633d631f63a2f86c1836c11157069,0x1a351662f27d1882a2196c1836c11157069,0xc128091733b32e1432f0b14b5f1d26c17a0906b8f112,0xc1280918d4e1ab441672e163141285f1ac5b2e4801133b06b2d111,0x916e3b1670e1574432f351af2d14b5f19c6c17d4e1163506f2d111,0xc128092ed3b1b0191eb0b1355f1d25b32e6a1111a069,0x441995f19b6c1822d111,310107411113,0x2d349441995f19c2d111,464179818909,0x214b2d2ed3b18d142520b14b4d2ed5b18d190652a104,0x66157481633b1691432e6317a2a184492735f06b831137906b4d110,0x214b1e3293b279141c30b14b4d2ed5b32e2e111,249700921887,0x413d1e2e43b1af0f139442e4631af0b12a3a1855b18d5f06b491163b06f8d113,0x481631a2ca442e41f1282a3145f06b8d113,0x2d33d4e1ae67128141d1632ed3e14c3a173492eb1906e8c10a,373133]
private def payload28 : Array Nat := #[0x214b4818a1a2524434e351672e14c4d2ed491a0,0x214b481891a178142822e1ae1414c3a2867927b5f06b8d113,0x413e2d1c34e18d67128662263533d1f14c2a2ed5b18d2e11137069,0x1e2e41a1724417a7d32f5f06b8d113,0x2d32e1a16a1432e2a1865f06b8d113,0x214b2d2f83b1714417a7d32e5f06b2a105,0x214b2d1ca1a295192e23a1ab791b95f06b8d113,0x214b2d1c64e1ec3a3145b18d51111,0x481636732e67128142f8352ed3e1353a2355b18b7a06d8d113,0x3b3294417a353215f06b2a105,0x1a283671285b18d,0x481631a321633295f06b8d113,0x1a17319336631743a1735b2c61906e8c10a,253780640487,0x3b1ae3532f3a1865b18d,0x671714417a353525f06b8d113,0x214b092191a2334434e5b190440672a106,0x481ae672ee67157142f35f2ed,0x9357671283e15a3a2355b21f,0x93521a1670e14c7d34e7932e,0x661572d2f81a1764417a5b196440662a105,0x1e2cd1a33d5b18d511111a069,0x3b3294417a2e351,0x4e1af671281f15a3a2355b194,39551611283,0,0x1e1a21a352142f32d14c2a1865f06b8d113,0x2d1ca141ca2a0363a1855f06b8d113,0x4e34e2e34e2a036491a2,0x413e1e2cd4e2350f13e442cd2e2352a0363a1875b18d491163b06f,0x1e2e4442e42a1875f06b8d113,0]
private def payload29 : Array Nat := #[0x481f8671ac0e14b192e27d33d0b1264d2046c18f5f06b831057806b8d113,0x92e26733d0e14c44188631640b1262a2046c1903a06b491137806b81113,0x481676719c2514b142e2352260b1265f2796c1912d111,0x92a4672522514c4418d631830b1263a2796c18e831065d06714111,0x6c14b2d34d671d24914b1434d2e204791a21e06f491137806b2a116,438940717885,0x2d1e76719c2514c4418d7d2d30b1263a33d6c1981b0692a111,0x4832f4e1e70e14c142e2631640b1265f2ed6c197491135b06d,0x92ed671d10314c6632e631642a1ae6c32e6a1107806b,0x92f619357631643a2046a1107806b,0x4418d3a2830906981111,425575371495,0x2d1eb442632a349,0x4e0200014c091ac4e17a03128191bf632e72e13b7928383111350692a111,0x2d18d4e18d442a96329b2a1ac5b34d3c06b2e10a8906e48113,0x6c13d091a81a1af0312a19282351682e13a3a1ae6c2a47d1168906f,0x414c091ae3b1af2a14b191be7d1bb3a16e6c18d831166306f,0x128091e01a2524914c192e47d1a72a1ae792838311135069,0x128092ed3b33d0314c192e4351682e13e2a1ae791b36a10d78069,0x1a252632864d254492a18311135069,0x481df191ca351683e1395f176791b54910e5b06a,0x1a18d632e72d14b6c3598311135069,0x191cd7d1ba791b48311135069,537336975796,39402398028,0x6c3598311135069,0,0xc1492d1ae3b2830e128441e0352524e14c5f1ce491aa2e111,0xc128091783b1a66633d351672e14c4d2e25b1a92e111,0x932f441fd2a03d4d2812d111,0x9351441a55f1cf492192d111,0x93523b1676332e1f14b493452e111]
private def payload30 : Array Nat := #[0x3b32e3518d493592e111,373161,131406,0,0x214c481e43b1734417a7d33d141283a2ed6c1d15f06b801133b06b8d113,0x2d32e3b17a4417a2e32e2a2736c2735f06b6a1135b06b2a10b,0x214c2d2333b279141c3631670b14b2a2264934e2e111,0x2157092653b1ae4417a3516e2e14b2a271792793c0728111a,0x481ae672e767128192153528b3e1352a2ed6c1e47a06d8d113,0x6c138092bb67128663292e3211f1355f2047932e8311135069,0x3b2044417a3534e792555f06b2a10b,0x92a23b34d671280b12f491a1,0x1a32e442cd491a02e11137069,0x672ed632f63a1ab5b2201906e8c10a,0x2d3171a33d491a0511111a069,180454924934,0x4e34e2a03f491a2,0x414b0932e672e7192797d19e3e1584932e7d10b6307114111,0x4832e671ac192ed7d2735f17a4932e4406b8310b7806b8f113,0x4832e672ed441a46319f2a2e76c16d7d10a3706e,0x4e361441ae632e33a32e14111,0x1e34e671ac192f65f2048310b7806b,0x3b2e2632ed491137806b,254289417006,0,0,0x481fa142bb2a349,0x481f8671a90e14b1927b633013e12b4d204791a15f06b6f108630778d113,0x4832e3b34e661a3352545f169791a01906b831186307770113,0x9282671a94814b1932e2e2a93e1585f1ae4929b8310c63074,0x2d34d3b2e21434d2e204791a21e06f83118630772a116,0x2d2a44e2264416d352865f1af5b1e40906f831186307714116]
private def payload31 : Array Nat := #[0x4d1280929b4e3290f1351932e7d2ed7934e0906970111,0x631ab3a2047d11863077,108228112814,0x3b2e2632ed8311863077,0x3b34d4932e8311863077,249700922189,0x1e365671a90e1351434f352fc3e15f3a176492578310c63074,0x352865b1d48311863077,0,0x127481b91a2ed44168201352a33d792e2,112059498856,0x1272d1b81a33d03135442a2632a45b18d511111a069,335671300941,108148269794,0x4e3522e1b3491b3,0x215f1e2ce1a1761402d441682e334201353a337792f65c0796611d,0x2d18d4e32e2514b141663534d5f29b792a93c06b48113,309618516325,0x916e671ae2514c441ae2e29b2d14b3a32e492a96f11d63079,0xc14b2d2041a27b661a95f1b95b1731e07714115,0xc14b2d34e661673a32e5b314,129689350574,0xc1574834d1a2f66334a2014b2a34e5b32914111,0xc14b1e233662795b2a9,0x2d3524418d3a32e,0x9349671ae48157191762e2f81f1352a2cd493146f11d63079,112443495149,0x2d34e1434e3a28a,373382,0x2d235142353a1651e06f2a116,0x1e176441765b173,238007]
private def payload32 : Array Nat := #[0,0x2157481ae6718d142e7631672a3066c3214911137069,0x2d2820e157141d27d34d2d14b4d2046c34d5f06b6f1073506f8d113,0x3a1746c11a3506f,129526588059,0x483551434e6c0364d1a2,0x4913e662cd2e2b46c0364d248791664911e35078,0x1281e2a44e166031291418b2e18c4d1ac5b2a46406b7d1136306d70105,0x4832e663297d34d5f17a7932e8311135069,0x48282671ae4814c142812e2f42d14b3a252791e214111,0x128091df1a33d03135661c17d1e54d2e76c18d5110e5706a,0x92924e1ac66020191d12e29b3e1283a29b5b2993606b14113,0x92813b283031376617c631ac3e1284d17b5b1e6640778011184115,0x92841a1ae660206617e631ac5f2265b1e74e111,0x2d2820e135191d22e2a03e1283a2ed5b1ef6c11457069,0x6716c66020191d3631ac4e111,0x2d2826718d66020191d2631ac3e1284d17f5b1e98011137069,0x1a204351ed4d17a492b014111,0x1a18d7d34d4e111,0x92823b1ec251281432b5f32f5b1ec,0x48288672331434e4d0204d17a,0x93550e15719176351ef5f3298311435069,0x1e2824e2f2191c33a351,0x12a4e352351e75b1e74e111,0x4d1482d1d5671756602066180631ac0b1364d17f5b1f12e11e1a06f,0x4e34e351f04d0205b1e84e111,228147442154,0,228155773313,129226723698,537740571249,0x2d1674e252251581416b7d1f42d1283a33d7917f]
private def payload33 : Array Nat := #[0x2d1674e2524812b1416b7d1dc2d1283a33d5b226,0x2d1a94e1f80e1586621f631732d1285f2ed5b27b640778b1136306b4d118,0x414c1e1731a2080312d6625d631738b1136306b,0x672826714b6634d7d2043e1574d34d491d21906f8b1136306b2d116,0x1e2e71416b14111,0x414c1e2ed672f8031354427b2e2357917a5111a37072,0x2d1ae6732e442542e2352a2e77917a8b1136306b,217734,129233928555,0x2d252672820e14c7d3088b1136306b,0x1e34e4e1ae0e14b142cd7d1106306b,0x482f21a2e4792e48b1136306b,0x413d09176661d4631736a1123b06c,217734,0x4e02d2d32e1a3454429b,0x4d1571e176672f803135662cd2e2353a3497917a5111a37072,0x2d349662bb3a282,597289218155,39044965095,129239585139,0x1e1753b3593a2c6,0x92e26733d0e14c142e2351682d12b3a1734925a491137806b,0x671ac632ed5f1736c2c6,0x9283671ac4814b441ae7d2712d12b5f1ae492a06c11a63072,0x1280315a4421f351e35f1755b2a1,313821462635,0x1e3573b35744357633575110470104,0x1291e34d3b34d4d1ef6c1ef,0x481b914166353593c06b48113,0x4832e6732e4429e632ac2a1ac5b34e1b0711410b,0x2d18d6732e4429b632a93a34d491bf7a06e1410a,0x1292d1954e1924914c442a2632a46c1e7671135d06b]
private def payload34 : Array Nat := #[0x1292d1934e1960f135442a4632a22a1ac6c1ea5c06684105,0x1e3214e18d4d1ed6c1125d06b,0x3b2352a1287d3612a1ac5b34e3c06b1410b,194143015537,335861207885,0x2d2c6192f24d1e73c06b48113,292765012642,0x934e1a34e0f12f1934d,0x1a2eb0f128632b3491ac,0x2d2ee1a1a0632f43e128792b0,0x6732e792a0671135d06b,0x3b3570e15a4435763357,0x442a45f2a43c06b48113,297,0x1e34d3b2356c1ef,0,0x93521a1a26714c632b0792b0671135d06b,442670370923,0,443051987443,0x482554e16a6333d49167,0x4827b3b1af442547d2a149167491163b06f,0x1582d21f1a173192ed7d1ca2a1a91b07714118,0x158091d8672040f14c191ab6327b801133b06b,0x916b672e7191d72e1da3a34e4932e1b07784118,0x4833d671ae2514c191ab2e2f84e1282a1d1792ed1907714118,0x4827c3b1742a1a91b0772a108,0x4e1712a1a91b07714118,0x1581e3273b2ed0f1357d1ca2a1a91b0757011b,0x6c15f482794e18d143062e1d92a2ed491671b0772e1113706984118,0x1e34d663292e3211f1352a2e77932e1b076831113506914117,39035581217]
private def payload35 : Array Nat := #[0,0x93591a1752515a3521f,0x916b3b34e2514b633171b07784118,0x4827b4e2f24421a6327e1b07714118,0x1582d2201a178192ed3a1aa1b07714118,335899145021,0x4e2ed191ab1907714118,0x4832e6733d3a34d1907684117,0x4e2541928b1b07714118,0x4e02d0932d4e33d19271353641907714118,0x91db4e2f91928b1b07714118,0x1e3643b1762a1a91b0757011b,0x48317672352e16b2e1161a06f,116088979736,0x1e1694e2522d128793055f06b8d113,0x1e1ae3b211632045f32e6c2a97d11f5b07b,0x1e1783b213351ad,39546315346,129474077204,39105872686,112461320933,112120550221,443167404392,0x482641a33d49169511111a069,194060067662,320338,0x4e3492e24149241,0x2d33d1a17a6712819255632ed3e14c5f173492eb511133506b,0x212d092101a2794916b51111,112057205479,0x4e34d4916b49111,0x14f1e31e3b1762a03f5f1735b1f50907a7011c]
private def payload36 : Array Nat := #[0x4e33d441737d21f,0x4e1670e158661f47d16a5b33d,0x1a172441737d259,0x3b173441737d25b,0x14c4e172441737d25a791a7,0x92060e135142e96332e1f14b3a217791b06c11157069,0x2d1ae4e2e725135143017d21f1f14b2a2f8791df,0x4833d671ae4814c192862e2f81f14b2a2f3791e0,0x6c14a2d1c36718d0e14c142e97d16a1f14b3a2165b33d4911137069,310091428332,0x3b17367141441737d25f,0x2d1ae6732e7d25e,512362,0x3b286192867d25f3a2e2,0x3b20403140441737d25c,278899,0x14c0920e3b178192867d25d3a2e2,254257123690,0x2d1ae6732f2514b2e2cc,0x6734d7d16a2e111,0x7d16a4911137069,0x4155092e4671b103128192622a1a879352,112061596019,537250685201,193801044737,159276814936,278899,0x2d1ae1a3522514b,39201293034,103046,0x4e2ed44173792f6,0x3b32f2e28d49352]
private def payload37 : Array Nat := #[406171,103046,0x672357d16a2e1161a06f,0x6734e2e28d5b334,103008,0x1e16b672e767128192152e3013e1352a2e95b21f7a07066115,0x48208672f25f21a7927e3c07770115,299371,0x21521e2eb4e1b1141a90b1285f21b3c07770115,0x3b329141a93c07770115,0x1e2eb4e2f2442f43c07770115,257823277333,0x481f5192e23a2ed3c07770115,0x3b366671495b220,0x1a1732012e4d20449221,0x1a1682012c4d2045b224,0x3b1ae1f12e4d222792794e111,0x3b1ae192a20b12c3a223792794e111,0x2d32e4e2e71432e2e32e2a2347924b5f06b8d113,0x1a16f352a42e12c2a228792794e111,0x2d2823b16a0e14b4417e3e14c5f2a97924d5f06b8d113,0x214c1e23d1a279662520b1582a22b792793c0734e11181119,0x3b1723e12e4d2047924c,0x1e1691a16e0e1571429b2e2e24e14b2a229792524e111,0x1a2830e14b192753527b1f1582a22a792796f111,0x214c1e2441a2862e02d192e21412c2a230792495f06b8d113,0x1a16f0b12e2a22c792794e111,0x934d3b167661ae631672a231792524e111,0x4e1ae0e14b3e14c4d204492f8,0x201402a22f792794e111,292945109741,0x14d2d2824e1ae0e14b4417e631e02d14c2a1ad792015f06b8d113]
private def payload38 : Array Nat := #[0x3b1734417a3534e2014b3a2ed792555f06b8d113,0xb1404d2047924f,496249,0x481a5672790e14b141d32d1582a1dd792575f06b8d113,0x1e1693b3212d12879250,496249,0x481f8672e70e14b141ca2d1582a1ad7927c5f06b8d113,0x201412a232792796f111,0x481f86733d5f2a9792575f06b8d113,0x1e2e44e2f2442e45f06b8d113,0x1e23b672f22e1412a1e1792535f06b8d113,0xe14b3e15a2a22d7924a,0x67254141ca3a28b792ce5f06b8d113,0x2d32e4e33d1432e5f06b8d113,443167330820,0x1e1693b34e481572e2f63e1357924e7a06d8d113,496249,0x4e2ed4417a792555f06b8d113,0x1e23b2a22779253,0x1a351631f8792d34e111,0x2d2824e252142f35f06b8d113,180925993558,112448684877,129458414126,238219,0x1e248141d22a2305f06b8d113,0x21522d2f34e2f9141d01414c2a2347927f5f06b8d113,129459610194,0x14e1e3206732f48157192752e2361f14c2a23679254,408134668563,408134668563,389227]
private def payload39 : Array Nat := #[129229026095,0x1a2f27d1137c06b,295726,0x671ac143612a2ed491137806b,0x6719d142377d2814d2547923a491137806b,0,129390301554,129697534322,39044223347,129233949102,123443,0,0x916b1a16e6714b14239352522a29b5b33d6407a4d11c,39035761234,0x916b1a3214812863317,320299,86678655822,217764,0,0,172408,172408,0,0,0x671eb2e34979263,0x2d2791a365142573e1356407b8411f,129646215928,193896702362,0x2d32e3b1676714c142ed3518d4d21e492c9,0x2d16f4e2e70e15f142e72e32e5f21d49207,112210604392,0x2d16f1a34e3e14b4920f]
private def payload40 : Array Nat := #[193658598222,335793111400,0x1e225672f25f21c,0x1e3571a2352e1f9,0,0x4e3492e1fa49206,0x6c14b482ad3b2e74914b662a0351ae6c2821e06f6a1111a0692a116,0x13c2d1b6671b67d1af4d1af,0x413509332672e24914b191f9632ed5b1fa090681410f,0x3b2d35b1f86a1111a069,0x672816332f493596a1111a069,0x414c483573b3611932f7d2543a16e7934e0906970111,0xc15a2d21867215442a435235,0x481ae4e2e71432e2e32e4d2386c212,39428854292,249801511443,299656,237944,0x5b252491163b06f,0x6613b2d2921a1ae4913d662ad2e2ad2e13b5f1ae6c2921e06f4e1163506f2a116,0x671af4913c441e42e29b3a29b5b2996711d89079,193955422565,0x1e2834e1a925158441ae352652d14b3a2796c2718311b7c07514111,0x916e1a16e0e157142a22e2a21f1572a2a2492a24e1162d116,0x92821a1af19282351af2e13a3a1be4929a2e11e5b078,0x1e2824e2791933d2e29b4d2ca6f11f7c07b,0x2d2820e135192e22e2a02d14b3a2ed492a64e1163506f,108227961646,0x482824e1ae4814b1933d2e2a53e14c5f1ae4929c1b06914111,0x916e672e74814b442d32e2b23e1572a2e24929b8011d8d111,0x6718d351af2d14b4d207492af,0x12a2d2801a1784913f191a8352032e13f3a1a85b203]
private def payload41 : Array Nat := #[0x12a1e28b1a33d4913e191bd2e2a42e13d3a2e45b1af4e1165706f,0x4e02d1e2834e2e7441ae2e29b2d14b3a1c2492a8801208907c,0x4828a671ac4814b142812e2ad2a1d2492a03c06b6c11a6307248113,0x916e6732e4814b192523a33d,0x916e4e32f6634e3e1574d34e492b22d111,0x916e6732e4814b192523a33d,408472862993,0x3b20449140441ae2e29f2a34e,0x3b32f4421f351af3a2f4492a44e1163506f,0x916e3b16b6634e2d14b3a252,0x1e2821a28149141441ae2e2ab2e13d2a34e,0x4e32149143191c4351af6c23f4e1163506f,0x49144191ca351af3e1393a1c6492af801163506f,0x12a482881a295192e72e1423a1a8492a7,0x1e2863b32e49145191c8351af3e1393a1c9492a2801165b06f,0x12a4e32b192f82e2a43a2f8492a44e1163506f,0x3b16b2d14b3a2f2,0x928c3b286191a82e29d5f1ae,0x12a1e28b1a33d4913e191c12e2a42e1463a1c75b1af4e1165706f,0x1e2834e33d1933d2a352801216307d,0x916e4e32f4432f3e14c3a1c3,0x1e2821933d2a352,0x928e672331434e3a2826f1227c07e,292508836685,0x12a1a2f2191c03a2f85b2996711d89079,0x1e2824e2f2191c34d34a4e1226307e,0x1a2527d292492a14e1163506f,0x191ca351af3e1393a1cb492af801165b06f,0x9351192e73a2e7,0x92824913d1434e5f1ae,0x482881434e3a282,108228112814]
private def payload42 : Array Nat := #[0x6734e49147351af492a3,0x13b482961a176441ae2e2b33a32e492a9090694e1218907d81111,217519,0x672ed1933d7d35c5f1ae1b06914111,0x1e2941a33d142163a2f35b1af4e1165706f,198271279771,0x916e1a34e2e2ac3e14c2a3575b361360694d111,0x916e1a3521432b2a32b,389550,0x1e2824e179191c32e2b16f1236307e,0x191cc2e2a23a1cc492a24e1163506f,0x4e352192f82e2a43a2f8492a44e1163506f,0x4e3217d292492ae4e1163506f,537474286143,292680868482,198276584098,0x1e2923b2354814b4929b6f1217907d,0x4829667329441ae2a1750906f14116,238328,0x1a2e77d3656c34d4e1163506f,0x9282143493a1c3,537782567570,0x4913e191cb2e2b45b1af,198276584099,0,0,299696,0,112058561028,0,335459828153,0x6c14f092ca4e18d6712866226352d31f1582a2ed6c16c2e11137069]
private def payload43 : Array Nat := #[112058560883,112054419820,320338,107257,0,0,0x158483053b33d6332e3a34e5b1f66a1111a069,278899,0x1e2351a32e491284435e2e3453a34e491672e111,112059498867,0,344,0x4e3497d2bb491fa,0x12b1e2d61a2ed442864932f,0x12b4824e3b33d0314c6332f3a34e6c1e76a1111a069,0x916b4e18d442c03533d3a34e491672e11137069,0x673526328e7933d,315906,0,254289433208,0x4e3492e2b86c1eb,0x6719c192e72d12b3a33d6c2691b0698410d,0x6c14b483011a29b03135661c17d2e24d2e76c16d4e1125706c,0x4832e671ac1426f7d26d4d1ae6c16d491137806b,0x7d1725f176491135b06d,37375,0,0x1e2bb0e135142ed6332e1f14b3a217493216c11157069,310091506513,129747890741,129581343414,112058561321]
private def payload44 : Array Nat := #[0x491574d2524928e,0x21357d0366624863172201535f1767931e7d1205b07c,425854472889,0x4832e4e1ae142732e3142a1a91b07781115,0x4832e4e1ae142726327d2a1a91b07781115,0x1e34e4e18d142746327a792836f11137069,0,0x2d1de1a1ec141dd6327c1f14b2a1d31b07781115,0x1e2663b2333a2a20907314119,0x481f01a34d0312f662c52e2571f14b,0x1a176662041e07081115,0x672ed2a1a91b07781115,0x2d23e1423c6327e,0x192ed1b07781115,39492620939,344,0x9288672523a2371b07781115,0x1521e267672f92a14c3a2811b07781115,0x1584e34e4914c7d3453a359792834e111,0,110711,0x7d1582d3051a33d351f80b14c6c34e511111a069,0x3b1790b15a4926c,0,0,82559,0x792ee491163b06f,193939612312,0,335456342861,194127389501,129528603435]
private def payload45 : Array Nat := #[0,335894844045,0x2d32e0e135142e76332e4d3295b2786c11157069,0x661512d32f4e18d25128662263526a1f14c2a2f0792e76f11137069,0x1e270672332a284,0x1e3413b33d63283671111a069,335899058449,0x7d1531e3216718d14036142ed3516d4e1284d2c15b2d34911137069,112052097389,0x2d32f1a34e2d157,193959719506,320082,0,0x1e3573b3574435763357,13216440759,0x1e29b3b2a9141657d32e201355f34d5b2ad,0x214c671af1432e2e32e3a2ac5b29e,0x313c141b92e1b8,0,112555385646,0x141ef6334e1f12f7934d,254107902766,12604,0,0x1e2a61923563357,0x4803409365671af25154192cd632ce6711d89079,0,0xc135141653534920135,86581138258,0x9352672e767128,39546237729,254251647492]
private def payload46 : Array Nat := #[0x1a2f27d1137c06b,0xc140482fe1a33d6c16c511111a069,319865,0x4e0362d2404e2f21423d,107157,422717,254257848968,0x2d02d0932d4e32e7d265,0,0x3b1790b1333a272,0x3b2367d2683a275,0x4816f4e2e725135142f02e2f42d14b5f29b49301,0x12c2d30d1a33d03135792835110e5706a,112061399410,0x12c482c21a178192f03a1a7,238011,0,562927194217,0x6c14c092051a2ed0f14c191787d2f32a33d491ae,0x6728b031287d2604d1ae492ee,0x1e34e671672e3523a1ec7932e,0x2d1ae4e282251352e2f34e14c2a2f8791df,0x3b34e7d2e33a34e4932e,0x2d1ae4e33d2514b2e2cc5b28b,0x3b2836712c2e2c9792ee,0x1a167251282e3527932e,0x4833d4e33d4814c442ea7d2764e14c2a2f35b295,0x4832e1a167193387d2cb1f1572a2ed792838311135069,0x93521a167671281935e7d34e4e14c2a2f67932e,0x1a32e2e3527932e,0x4833d4e16d19362353433a175491ac671135d06b,60447773390]
private def payload47 : Array Nat := #[0x352524911137069,0x483511a1670e14b193617d34e1f1572a2f66c34d4e111,0x1a2836714c7d34e4e14c6c34e,189056,217682,0xf14b7d2cd4d1ae5b34e,0,217742,0x2d1ae3b177251352e2cc1f1582a2f8492f6,0x4e02d4e33d2512d442aa2e2ce4e14c792f9,0x482821a3524814c7d2cf1f156,0x9209442ea2e2d0,0,0x1a1b119302791b1,0x414b1e2d3673031916f2a18d6c1c20906981111,0x414c1e33d672e50f14c4433d7d2e50b15c3a1fa491be5c0698110d,0x7d12c1e2d23b1df142e72e1b4201356c1ca,0x21411e33d4e2ff0906981111,0x2d2574e301191ec2e199,0x4832d1a35e661676334e3a32e6c2790906981111,0x41281e3371a2ed191684d2ee491ae,0x7d128142527d2e7,0x4d1281e277673071932e2a18d7934e0906981111,0x4d128483454e2fa4416d632302a18d7934e0906981111,0x2d31467314141ae7d2e74d2e7491ae,0x6c12b2d2c34e2260f14c142814d1e75b34e,0x4d1281e33d3b2750f14c6616b7d2ec2a18d6c2520906981111,0x4834c673297d2e8201353a32e6c33d0906981111,0x214b1e2d44e242192ca7d2e70b15f6c2f8,0x214b1e2d44e2076632f7d2e7,0x6612b1e29b672c51432e2e19c201354d2e26c1c55c06c48112,0x4d14c1e33d6730a0f14c442524d2825b3520906981111]
private def payload48 : Array Nat := #[0x662e74d32e491ae,0x192045f34e491ae,0x412b1e33d6724e142ca4d1e75b34e0906981111,0x414b1e33d1932e2a18d6c2520906981111,0x1581e2d61a2ed0f14c192ed2a33d5b34e,0x7d14c1e2d74e3014416b7d282201356c2f3,0x4d128673091932e2a18d7934e0906981111,0x1350f14c442ed7d2f8491ae,0xc12867308442ca7d2e75b2e4,0x214b443217d2e72e1574d2f6,0x7d14c1e2d74e242192ca7d2820b15f6c2f3,107245,0x12d1e2e01a2ed0f14c663292a02d,0x6614b1432f7d2e7,0x12e1e2d81a2ed44173,0x6c12e1e2d93b1df,0x214b1e2dc6632f7d2e7,0x1e29b6730d351bc,0x414b1a3392a18d,0x6c14b1e2db672610f14c192e77d2f02a18d4932f1b06a8410e,0x14b67314191734d32f491ae,0x414b483451916f2a18d492520906981111,0x4d1581e33d673050f14c1432b3a1f65b34e0906981111,0x6c14c1a2ed0f14c191787d2f32a33d491ae,438940717799,0x192832a18d6c32e,0x412e1e33d6730b5c06a8110e,0x4d12d1e33d673040f14c192524902d3a1f60906981111,0x4d12e1e1b04e35c191ae0906981111,0x4d1281932e2a18d5b3520906981111,335584338749,0x212e1e2d91a2ed19174]
private def payload49 : Array Nat := #[0x214c1e2d74e2076632f7d282,9371224289825511,0x6632e7d2ed4d2e7,0x2135092154e3011432e7d2e7201354d2f66c2f8,0x414c1e2d36730a1932f4d2826c1c20906981111,0x41286730c03155661b1352e43a3526c1a8,0x41351e2db3b2160f14c1933d7d2f62a18d7932b1b06a8410e,0x6730f6632e7d2e76c32e,0x6730e03155662e77d32e4d32e6c1a8,9371245828625127,0x929e3b3660f14c442f2492525c06b81110,107147,0x6334d5f34d7934d,0x212f2d2c36724e0f14c192f27d2f74d1e75b34e1e06d48113,0x1e2dd4e2422e209,0x1e2ce1a28b6c1ca,0x21351e2d11934e7d2e72e1574d2f6,0xf14c4417949252,242143,0xc128662ee7d2e7,39565189889,0x6c14b48348141752a18d,0,0x1e2df673124416a7d32e2e1575f1755b2ad,107245,299438,438471897934,0x7d14c142ee7d2820b15f,0x1e2dd4e2422e245,0x21281e2de1a338191677d2ee201573a32e6c1b10906981111,0x4d14b1e337661722a19a491ae,0x1e33d3b366143523a1f60906981111]
private def payload50 : Array Nat := #[8908763468,0x1e3561a28b6c1ca,0x415a1e2da672d1,123709,0x414c483451932f4d282492520906981111,299731,0x215a1e2d26730d632a3,0x4d14b67314441743a177491ae,0x1e2e01a2ac0f14c192f92a02d2a33d,0x6612e1e2d367311661773a1f70906981111,0x1e2d367313143493a1fb0906981111,0,0x6c14c031556c282,0x135441763a349491ae,0x7d14c193527d282,38765334801,322036430,0,38765334801,0x414e1e2e1673157d2f73a1ff,242227,319865,107157,107257,112061596019,37714,0,0x671b025128792f8,0x1e2b71a1b2142be,86636733154,0,0x3b32e6316f2e111]
private def payload51 : Array Nat := #[254257017199,335793111411,0,0x48244672f22a243,422484,0,129640973049,112581817026,0,86539108671,0x2a12d19178632bc4d1fd6c33d,0x1e1d4191ff632bd,0x92ff193527d32e,0,0,0,0x2d1701906f2d116,278905,172882,0,0,0x916f5f2e7360694d111,0x916f4d2351906f2d116,249990255186,0,0x2e2ca6a1111a069,0,0,0,0,443099,309903770361]
private def payload52 : Array Nat := #[103061,295549,0,82553,314424090897,0,184953,0,0x93454e16767158143182e3211f1353a35e6c32d8311135069,0x493522e11137069,299858,512344,0,0x2d2791a3653e135,238229,112581599654,184959,0x2d32e1a34e3e14b79319,194127311694,8493,295434,108148269804,320303,253793456497,242041,0,335402865269,172556,0x2d344672f92a28b,0x7d15b483003b1764d1711907b4d11f,443269132938,320082]
private def payload53 : Array Nat := #[0x3b16f6332e4e111,254251647347,335899058449,295435,443006972553,0x92a13b2355f31b492d7,242425,0,0x6734e6328a4e111,0x4832e1a34e2513563304,0x4832e3b34e2514b63317,320338,301,422717,0,184840,107257,0x92eb3b1b20312a5f2f4,0x3b2e7632e649349,112061596019,108155609826,0x1e3464e2f944287,112517837160,443006820996,443179836036,112061596008,0,0,188851,0,39446770425,496270]
private def payload54 : Array Nat := #[0x6734e1402d632836c352,0x672817d19d492c86c1138906b,0x4d14c2d2e349150142c67d2f94d1d06406b66113,464145387627,367323528860359,443197,0,0,112454635894,107245,464205091457,0x12a48349192e72a26b791b20906981111,0,0,0x3b2f97d2db4931e,0,0x1e28d3b3522d14c4931d,496270,112464159525,0,129597809481,0x4159672f90f1342a0363a281,0x672f60f1352a0363a28149248,442917556885,242510,0,0,443197,0,0,442775999222,295478]
private def payload55 : Array Nat := #[443167404841,0x7d1621e2884e32f2d1572a20c,320082,0x2d1f03b34d0e14b3a34f49257,0x3b2f26c1138906b,0x1e322671ac0e14b143617d34c2012f2a2516c2c46f1097806b,0x1e31f672333a1d5,0x1a32e6c1ec6f11137069,0x1e3453b18d0e14b7d3594e12d5f328491fc4e111,0x1e3231a33d6c1ec4e1111a069,0x41411e3243b33d6332e671111a069,253795627817,129745658218,335402865269,442777117196,0x934e4e2e74e128,422717,0x3b32f6328a4e111,0x1a2526328a4e111,242425,129528603474,0x1e325672f95f289,335895040645,112061596164,108169241334,335805497995,123730,102964,335899058449,0x1e3571a23519235633334e128,0,108034233114]
private def payload56 : Array Nat := #[0x1e31c1a33d7932e511111a069,253795627379,335792935282,422484,0,0x3b2ee6c11157069,0xc1351402d6633d7d3345f3643a07d70121,0,85946811030,408934597174,0,106873,39505208146,0x1a2e72e349792e8,112061399789,0,0,0,0xf14c2a2ee5b34e,108053054201,8937419125,405877,8937419125,103066,51857699662,0,103066,0,107257,537219445394,279374,0]
private def payload57 : Array Nat := #[0x412f2d2571a34f1934d7d1f02013579219,0x483466732919176,39564952381,107147,0x1e33d5c06f48116,0x4d14c483451434e4902d3a283793590906981111,0x4135483481a3392a15f14235353414902d3a283793491e06f81116,292450386663,0x7d14c193523528d,82514,91006616196354321,0x2d352360694d111,103158,82221,0,0,228430557944,0,0x1928e3a28e511243707f,0,112464269791,0,0,0x1a32e2e32c7932e,0x1e349671670e1351935e7d3594e15d2a3186c2354e1163506f,0x1e3591a2836714c2e3524e1586c34e,309914272076,0x2e32b2e1161a06f,0x6c1581a2f90f14c443622a33d4932f,0,0,0x48338663403533d5b2e76f10d37069]
private def payload58 : Array Nat := #[425594319220,129238229741,0,0,189010,512829,0x6720d2e1774911137069,0x3b32e7d2353e13e801165b06f,129526588153,39436284656,0x6633f7d2f95f28f,0,0x3b334352e75b2e74911137069,0,39546102610,320338,0x1e3524e2e7031304e128,242425,0x2d0341e3593b175671281f1324d2fb6c326,39546315162,0x2d0341e3593b235671281f1324d2fc6c327,320242,0x3b32f7d2926c3594e111,0x1a2527d2924e111,0x3b2f6632f65f17879344,0,193959481676,0x4e2f91402d192921414c,112555450664,320246,0x1a2826335149320,0x1a33d7932f511111a069]
private def payload59 : Array Nat := #[0x4e2ed141b11f13d,0,0,0,0x4832f1a34967157,335543661190,335802352049,0x3b2f6632f65f286,0,0x671756316f2e1161a06f,309860606327,0,0x482521a3494e157,184974,0x3b2e76332e49349,0x3b1765f3293607d2a121,0,0,0,0x2e3595b19a491163b06f,0x2d0362d2f24e2481433b633174407e2d122,0x5b19a491163b06f,185155,0,0x1433a493350907f14124,0x93454e32e1935f,406265,193898885766,0,0x93376335e5f1b11b0792a11d,0,107059]
private def payload60 : Array Nat := #[0x4135093301a3100f158141ee6334f4d32e793451b06c14112,0,443001,103066,86413275439,0,0x192b04d28a79359,0x414c4d28a7934e,0,185053,0,0,0xc14c1e3433b367141e86c2547a06b4d113,422545,0xc1354834c4e361661ac633651f12f4d3336c2551e0722a11a,443001,0x1e2f2141eb2a2c87a06b4d113,524098523411,443007,0,499819,238037,0,0x1932f2a2961b0692a111,0,0,107249,0,249990255186,172874,0,0]
private def payload61 : Array Nat := #[0x1a3675f1d65112537080,320242,0x934a3b34e48157,0x2d3514e2e7031303e128,0x1e3654e1af0e14b1f15a2a2d549331,39342678866,443179836043,253795627377,0x6c1600934b4e2350f15c1935d6333c6c34d4911e3b06f,0,0,0x1a2827d34a493201e0802a125,0,0,0,0x7d34a2e1161a06f,512842,0,0x4e17a6714c193612e3571f1572a233493578311135069,0x4e29649321511111a069,0x93521a16e0e1582e35249320,39505208137,299656,112161014323,242134,189266,0,0,0,0x4835a1a33d193036c1754e1165706f,107342,422717]
private def payload62 : Array Nat := #[443006665494,319865,193703551826,443179836043,335894987410,0,0x7932f511111a069,299858,37504,389877,0x142541f14a4d35b792fd5c07e66123,0,0x1a2800e1551f155,0,0x2e34e5b33d4911137069,0x1a2f619178491df,299766,426095645430,64735187687,0x1a2827d3527932f,299442,0x157483364e1752a14b443387d3575f17779167491163b06f,0x673652e34e2e161492962e1161a06f,64735261517,512850,0x483371a2f80f1283a3595b235,341,0x92b244353352544d340,0x3b32e6333d4910e5b06a,0x3532e5b33d4911137069,108261684046,194059318057]
private def payload63 : Array Nat := #[198454915901,0,0x3b32e6332e2013a3a35d4910d5b069,315919,0x631ae4d35c5b33d4911137069,0x21351e3293b32e443520b14b5f1766c3574911137069,198347632971,0,194059129204,0x632524911137069,0,512431,0x2135093613b332443550b1575f176492352e1161a06f,0x2d3392e2355f3605b33d491165d06f,90879232504279371,194059424553,0x3b28a7d34e4911137069,194059129206,184971,39449916150,292951552660,129626292979,0,373454,0x661571934e7d32f0b14c,406100,0x493594911137069,0,0x3b3342e349493654911137069,108228039017,443122,0x1e3511434e3a282]
private def payload64 : Array Nat := #[0,0x93511906f2d116,0x662476c0364d2486c2f2,0x192f93a2f36c33e,0,327762636415736,0,0x1554914c5f3527928d,0,496473,0x2d0343b2926714c,0x1a2f40f12a792eb,292453585613,0x31353a3495b16a,217684,0,254300713294,238229,108228112814,17527263975,443064427257,0x932e663654d2351906f2d116,309922681678,254198297334,0x6c1570f1584d32f79352,438978269559,0x483420f14b3a235,389686,0x2d3514e2e7031301f14b,0x483510e157663297d2351f1355f32a6c34d4e1163506f,253793530665,0x2d3501a16e0e1577d34e1f1576c34e4e111]
private def payload65 : Array Nat := #[194163876690,443179987593,112061596457,0x4e2350f15c6c34d,254189822225,0x4e1777d3596c3654e111,0x483513b34e48157,242230,112467198817,0x4e3497d3656c3654e111,299858,335861179182,0x3b2827d34e49352,0x3b2826332f49352,0,0,0x2d02d093651a18d6715e193477d2351f1353a35e6c3594e1163506f,0x2d02d2d33d1a3653e135,238229,0x3b2f6632f63a295,0x2d02d092cb2e1fe,0x3b2f91402d1433d2e32f2014c,0,0,193964622675,0,0,0,0x4e1704e1163506f,0,194052940107,254298]
private def payload66 : Array Nat := #[0x2d02d1e35766034192353534d,0x93494e2e7031301f135,0x4e282031304e14c,0x3b2e4632e42012a,0x2d034031301f132,45363,0,45390,0,82681,0,0,0,0,172628,0x4e2967932f491163b06f,0x2d2524e19a0e14c,0,442802,0,0x481794d3634920f,0,0x4e34e7d35579282,86294106870,0,0x4835c4e235663615b1ae491163b06f,0,315823,0,0,426000044897,82354]
private def payload67 : Array Nat := #[422717,242326,112466563832,0x4e02d4832e3b349251355f2b55b35f,0x4e02d4828a3b3595f2b0,0x92ef3b1b25f29c,17542914706,0x415a483336735c4d1af,0,0x414e093576733d5f254,0,0x4e02d672de2514c,0,39047090548,194071712399,0x93491a16e0e157193612e3571f1573a361493574e1163506f,0x1a2e77d3656c2354e1163506f,39536665426,443179836052,0x4e34e6c2964e1163506f,112061419894,0x4e2350f15c6c235,0x93496732e0e1350b130,0x1a19a4e1163506f,0x3b1b1633373a35e,0x3b2ee4e1163506f,0x2d0341e3653b1750e1351f1325f34179342,0,319864,0,39536878162,0x1a3514e1163506f]
private def payload68 : Array Nat := #[0x4e1777d3596c3654e1163506f,0x4e3524e1163506f,0x2d0341e3653b2350e1351f1323a35f5b364,0,0x93493b34e48157,0,112467198817,0x4e3497d3656c3654e1163506f,0x1a2822e3496c34e,0x1a295192f73a2f7,106906,0,0,242327,0x93526728c0e1581f155,422544,107345,0x2d0343b2966714c1f13249356,0,279399,189257,198450647890,0,0x1a2f94436279236,0,335579566965068,0x93651a365031310b130,0,0,0,217936,0x2d034093570e14c1f1323a366]
private def payload69 : Array Nat := #[0,0x2d0341e3653b365031301f132,0,0x583d14436c8f3d16763d7663d066131963d1a368043682863d42613,0x3263d6d63d6a63d6b63d073682f368373680f63d1163d,0x3d63d646378640a496cb817390163d366373040a025060d4fc2736d,0x4d5327e5210a4853a40a3b3a5014853663d470691a514255063f7d5423d1,0x5e3724436885506594262f06b2c5143b3a70854619368735060f40a2137b423a6,0x3d52f44368895dc496235c5db3b3a3143681636e470691a3bf0c5db3606946623423a1,0x6c3687e3bf716e81c38a5c368220695d6e8015326f45d525db0706b034132138f423d1,0x436e8873bf0c069676264a368400693b3aa143682f7e547069356e8025db3f45d57069423ab,0x5e3be44368897397d06b1c3892f06b5c6e53b3a00840c6f587470691a81d25568213cb423a2,0x437397a738713ad6762d2c3d17006b3b3d414368097b247069376cb0706b026e5213795706b423a9,0x5e40c5f52f7981d2e06b1c38b2f06b3c6e53b3a10136f193684706937739010670f56821390423a3,0x583b45f40a45069898401c37c2f06b4a7383006f3b3d6063b40940a2706a378400706b036cb2139b423d1,0x5e3733f069758407c5461c39c3b3ac183c90506916840575460706b0f7380906f214cd423a4,0xe06966865755468d40a0206f138302c5068883014368366cb357390706b048406142a423a8,0x3d4178737289738020691c3995a5463b3a614368093b71a7391806d0f840214cf423a7,0x535327e3d18e50638506803d14b532014591207716514574590e6260d5b142626,0x5e5878340c7c5684936c804bf4206b816e50158712077365688440c03368123be7b3be,0x4d438723c6636135806b386e52c3c44206b816e501587120771b7d58440c03368123bd7b3be,0x3306b5e81d5f62c8d3d1136132c4dc5d63d4e3e2707393e51c4163d277d5,0x66420723cb79568397d51e5877f40c4e3db12077165de1106b5745a003b321368453be,0x4d3d45f62d8f3d15806b496cb803d13b6c22b06b4e3e1120776f6e5503dc0f5200d83027738,0x4d3d22606b723ca8806b866e5393d11e568766e52d7381b3ad73739207393f6cb29368,0x747398b738633ad5806b136e52c3c56206b813d5066e5093d157568033680581f296cb,0x4d3da723d02b5461e48540069765034e3de12077097382706f503e4037ec615085706965840,0x5378e723c745072856e81c40a4a688420695b5c70145d120776f546290695746904739054d929368,0x5e8635f51f7c6e82a40a2c3ce42069813d8066d0096cb8440c024101073f45375,0x7d68846069645c76340a2a546230691e5e95b45d4e3dd12074166e8503e6204d92136811725,0x250694d3d9723cc8540a1406e2b8402c3cd813d31440c12077516cb575910a06f008304152011726,0x4d578723c87606d8f8401c6cb2c3cf813d14e3df12077197381106f503e3003b40d40a370692250c]
private def payload70 : Array Nat := #[0x4d5764442c7306c828401c7385a5202206f813d64e3e712077196cb8440c0040a0d5781a0692950c,0x74856444300a7383c4234006f813d74e3e03154647069503e525508217ec5706962865,0x4d4e4724da8806b718285806b2b8282c4da814e44e3e82f4dc503e83e7564165340756,0x43368647d5635060a5142c50d5b3e9085b13640a573eb03368467d545506,0x4d5386d4207c568135de804bf4206b763ea33617367d58440d033680d3b335069626cb,0x4336887644450697c6cb0a63d776475d52108780343d18d06b526e8025382163d60613,0x435066d81d854131c5684a4bb5b3ec0306b2d81d1b3d1507800474c12739,0x433685474c4506963739660791c6e84c3f25b3ef030692d5e916546735a3070690f6480d5467b40a,0x4d3b77a3688d7390a5464106977646763eb1863056840573e93e7d51906f4163f11738,0x6653b7e3b2450698d8402b5064c3fd2206f5b3ee1584336739574fc0253b0d3b23506929840,0x53780646134506a858403954668488420693b77a153fa51739574fc003b0466b9226e8,0x4d53b7e40a7b06a8f8401c6cb4c3fc5b4fc07520197381106f573ed0053b0d40a5b06a42840,0x536527a368450697c89e1d81d3b8300881e197d7738670c8301181d,0x7d8303406f7287a637d51d7d51606f2c87a7f8302e3f916754576b6003b9213683506942825,0x6c4bf545766006b795140a40a2c40a4006969514085064f5324b06f5263d1f532125067b4fc,0x7d589444208e5681c3682c3b3400698c3be015de564c66b06b844323e66a417d56552e,0x243d1544e46006b8d6cb5950c1e4208606d78578075de314b48506b8443320617617d529532,0x58626544388d63d0a4e44a368400697f5541836d0506f1b5e85552c205d2106376541d,0x7d495544367c63738649777565d3680863d1645484434027d51036d1a06f605e8,0x6642f544378c072896e8387251e6cb5d3681440a1968829069505c70040146546370696541e,0x664258378e8c0728a840596c11e5545d36807738164551106f5283520626285461a0697b6a5,0x6c4de543696006b85825387265c87a8881e337d51006f37815025ea10754626b9,0x58418754181c3783a3787643a0306b2d7d51006b4f7d5553ae0706b1f7d51906b3f7d5453ae,0x3d517723ad853ad1c3792f06b6843f5006b7f43f0151756506735060b3791906b2643f3506b4543f,0x3d81d5f81d893682b3d11e40c7f44a08739317390240c123d16544a,0x533ad5f513635061406b0a5b03a3817f43d015140951c5740a043d11251c29514,0x3d517723ad85506594262f06b3a37b7f43f0151756506735063e4261906b2137b4543f,0x3d51c5f5146340a1c4bf2f06b3a5b08c3f00151356506375063e51c123d160514,0x3d40e5f40e7151459423774232206f7f3ae01518095180b3c9213c94543b,0x58532837268640c1406b1348e2f06b3a4cd7f3ae065326f7263040c0706b0b37f123d14544c,0x3d40c46069755328d3691406b1c37d2f06b3a3867f3ae0152c565062706f1a413253711906b213876543c,0x3d41175413893682a3702f06b4c4137f4410151c16522573d10f63d123d165449]
private def payload71 : Array Nat := #[0x3d5315f534676135a45d400698c44933506164032706f5263d004852640a65443,0x3d51346069547d5896131406b1c38c0d06e3a3847f3ae0151f094043540a0706b0b38e123d145445,0x533ad5f417793bf1406b1c3885106d3a385764070152f565062706f375dc0706b0b3883606d2138560407,0x3d54e755540a485805ee7f44b2d7d54f7d52706f1a6370706b007383f7d53506f65449,0xe0693d412833ad825460206e1c38d3a37e7f43e0006901533165417107d35368043d11906b2139345448,0x3d4145f4161c37a5a5687f447064025406b0981d2706f506e50706b0081d0d40c65444,0x533ad754197c6cb1406b385872f06b3a3966b40b065381b4b7845680706b04780124bf426e5,0x533ad5f86f896cb1406b1c397774267f4450151f1b86f555060706b0b3976142645445,0x58544543b060069896e81406b384642f06b3a3917f3ae173b0165446906f1a6e83e626213823706945446,0x533ad5f81f896cb1406b1c6e53a3c58f06b7f442187371b81f553ad0706b0b6e5213c57c06b45442,0x533ad5f54a797391406b1c3923a3838c43f0306f01540095173736d0706b0b392213836543f,0x533ad5f553637391c6e84c51c5b78e0306914865165468440a240711f5e9214d14543d,0x5853b5f52045069898401c37c2f06b3a39d3006f8c44c0653b095202706f378400706b0b39e1906b2139b453ae,0x3d41a723ad897391c394160663a3988c440015170954b1a7380b394090662139865440,0x584105f54445069638401c3823a395220697f44f014061651827078526e80706b0b39a1906b214d9453ae,0x3d4155f40e450698d840594232f06b3a7382206f7f44a015541640520546213c9370694544e,0x533ad75825718251c752806477f8670306f018051b86f737d50b754214da4078e,0x8b8561c3812f06b1e8967f4511583e1655820899417cf,0x758702f06b7f5de3084021870,0x5f540594312f06b3a39f7f43f0954050899233ff4544d,414793,456918095936,0x8263d1c3802c8247f4521583e358500b89927865,0x3d54e7541c637391c39c1e7397f453018031b88e354dc0706b00828214da65450,0x4385679739015550986f1288e27866,0x3d7a85f7a8717541c39d3a39d3006f0140609406307540706b0b4df1906b214df453ae,546615612493,0x1c39b2f06b0706b2139b,503611705446,0x1c39c2c825378990706b65450,0x5e5896d41f7c568135de804c65b45a01587367d58440c033680d4e47b3be,0x5e5898b4b8636130c077386e54a4214206b5b45b015871b7d58440c03368123bd7b3be]
private def payload72 : Array Nat := #[0x1706f5e5878352c8d36d0c077676372c4a85b456014613463d84481033684164940756,0x1706b5e45f644578f6e520073135685a4b55b5880146312077517398440c0b40c103c147587,0x7d6236456986637137d55a5322206f5d66a0146812077196cb8440c0040a0d5782950c,0x6c739646b23840a2c68840069765c70145e120761b546270695746700738615063506f7b3c0,0x1706f5e4608352c8d7380c075398401e46b5b45c00069067544f54684688033684164a226c1,0x7475b8340c826cb5940a210696867d766e7014581207734840574660e7261906f4683011520,0x5e46b6d51645075856e81c40a68738420695b5c70145d6f54629069574690e725054d929368,0x5e462644597b0778d8402b5061e46c2206f5b465016b1367398440c0f726235ef3706922867,0x758158981d0a7d71e822788761440c120770989e5746d123c111726,0x748996486f826cb2b4fc1e8965b88a1484019850208992886f116cb,0x6c73d647508d8501c6cb2c4ad69739016b1120770989957464005d1103bb7b3c3,0x586df546df8d4dc0c077388281e4685b59101468120773482857591007560d756,0x5e46a6446a45077638280c0771d8281e46a5b46a0146a120771b8285746a0c3c2123c2453c2,0x7d40c83830635060a5143a6275d490014eb3640a303f1033680586f42520,0x7d40c724a64507782739496e58706b1e4ed3b4221866b346137347c3e5871240c350697b3c1,0x744a76456c8e3ad0a7395c63d5b6b12d617096e56906b736910e5ef61867654c4,0x7d830648307c3ad0a3d1778677f83017628166e52706b737020086f21368116cb,0x74752834817163d2a6376a4807647d1306f155e85136d8453b033680d4e43506942649,0x5e5918340c45077826cb5940a2c596765610762709637735600e7261906f4683011520,0x7d40c724aa4507779739396e58b06b1e4ee7647b014ef343ad7347e0278e6406b3f726115ef,0x7d40c724ac45077637397407a1c6e81e4ec7647f03069066ce165467355f070690f6483f78040613,0x5e58a724a5760708f8401c6cb1e6b55d63d17532197381106f5765600578416262250c,0x744a9724a945077717541c7d54a8303006f7687a14830197d54b06f7387a208252882529368,0x6c739724ad896cb2a85080813187cf36899576b10b74d0d409475d1,0x2d06b536b6546178f5de1c53b3a36d7f5e9040694e8565650a1a3680c63d2862645752,0x664af2606b54630866e5484b31e5686957904069336b92f52e35587207390549c454fc,0x435026440a897397d06b2b6e15c6e53b4b90840c3663f470695585925568055df224b1,0x434fc7a5ea896cb134e15a3d18f06b6b6ea040693383034726375320b6e5125847c06b454fe,0x438593406f7a7397c5063861768637814e00151c5685b84546007392640a27865,0x436b95f51c7c6e86761377546420698c869087393174c1a3680340a3f7383706965865,0x43500835d28f8401365c5c7394b63d063b03177d8206f3763f0f546125ef37069275cf,0x1f06f435a6834a2865064963d1e739816b1040694e867345ef8453b0b8403f5d2454ff]
private def payload73 : Array Nat := #[0x43505834a3387d51e7384006f814e21878e56508848400c546054853506945503,0x5386354541896e82b88e1e6cb4b63d184fd2f73f69069848640b40a3f5e03706945504,0x1f069535d0834948f40a4963d5c6cb8c75b063b536532307260c8400549e454fd,0x834877c8965a899816b56f841036cb45856,0x245f45f514855d21d40a5c438816262e521363696e5322052c1e06f1041329506,0x4d5616d40a7c5961c5325a830883d10753234830733d10348e1048927514,0x324187e7d58e5ea133be5c4e4883d12d57856420305891c06b0c697104c37b5de,0x666d5446cb7c4fc0a7381e5323b4d92d40a6d06b2f7dc7062d0046e5f06b464f4276e5,0x4d36b836cb8950f7d06b3850c5c5783b4bf4d06d1750c36578356230706f004701252f7b7d5,0x4d36b5f7397c50e7d06b1c6485c4353b4cf084172f6b91a4b707069004721060245613,0x664787a8408e617495211606f4a56c3b7a81553b120692f5cf525ef004741041347739,0x4d47a7c510397ec410693a7543b81d187ec28069197541a81d0481d1906f464f611738,0x1706f4d479445067c5122006e38867777ee3b4bc0f06e17867567ee1a4bc25568464fa11739,0x5363d835464506963840133734a738220693b840147382f5224b06f3782b0c69e464f8,0x4352d5f6e8638411d6cb5c3698164e15544050694f7bf30585046ea09069464f74040a,0xe069438657240a8e7387d06b138405c5773b4d1183682f739706cb0a06f048306183011506,0x4d4775440a65069638641373f4a5854206981722144d92f864733d10246f614f93507b226e8,0x664768b8407c50d396cb5c3693b4da335320506f2f830707260c6e71b0694167d2240a,0x4d6b987840855d52b5545c3693b4d8083b4120694f754706260f52c0906f4167b27738,0x6c547546e87c5111c726686ce88626077264f6ce73626046f81041329739,0x4d475544fc8e8504974c6a8503b4bb086cb4f4fc1a4db02473464fb224fc,0x7a81d898300a7d74a8678881e183681989e70652618306281d,0x3d8705f81d2a8595a8306c06b0765236439733d10476f23706227d7,0x4381e5f7d77187a7d06b0a89e5c3693b4dd1881e707260e8152781d,0x4d36b4489e3c81e5d8411b81e37841128242981d,0xe06f6687a837d5898300a7541e78e3b4da183684f8251a8250a06f0c87a61830297d5,0x728257c4fc138304006f068302706f00471464f527754,0x53752836e88663d2b5ea6a36d817383206b01840366172906b3078e0b3680575611856,0x537693406f7a7397c5066749568637884f018532167a4355921d06b0086f2140c65843,0x664ae6d6e1866e5484b01e5684b7183206b018592f40c355871d06b0f8560558c623d1,0x1706b244e6754b28f6e50606b0a65f6a3d1884f12d6cb164da6e40c1f5322872627830,0x748035463d897397d06b497f85c6e5816170840c2f7397377d00546055cf295ef]
private def payload74 : Array Nat := #[0x244ea5f6248e5683963d4a739818033206b088650961730780047394681e65546,0x2d06b244e75f4c67c6e51c52e3a81d7865a073be0949d6e40c0253b3f4b827589,0x244e98b4f27140a2b4e85c6375d6272e6cb6f3d11a6c2205321e06f0583060830,0xe069437a47a7388d40a0206f138302c5068883014368366cb3586f1d06b04840614e347426,0x6d876717521e7d53006f2d8702f8300c825623d1,0x8b4f3718991e899884f333825377250282528725,0x435066d517635061d5b12c50d3b5b1085b11650d1a5b1255060551745506,0x666cb6d54663368493f3805848e0778c5b02e3f41940a7055e255060d7383506f11568,0x5e5136450685506595d22c5b03b5b0153f21940a1a514023f2055142740a,0x58518755180a4851e485765ad0651a1651a2706f1a5140251a0d51a3506f11514,0x4d5206d5205506f715141c5203a5202206f3b51407520195201106f1a51400520055203506f27514,0x4d5156d51f8d40a1c40a5c51f785150740a3651f57515005150551f2940a,0x4d51e543af8e4fc138405c6b63b5140740a094941a5b20051e103af624fc,0x4d5396d5364507e485681e4853b5b40640e513f66e5b32406b0081d124233506f626e5,0x66553645065506f897392b3f54c3f73b5b00851c2f7391a5b94306b0486f108657b3d1,0x4d54b645065506f8d3bf39623776235b507186235662335507255060554b3506f113bf,107796,107796,0x6654626069758657940a493f26a3f8788672e3f9095e96e5b0008704650647739,0x66554728562b5461e485400698c5b80651a097382706f6e5b5037ec0d51a3506f65840,0x4d557645068d73939630776468c5b11863056646845b1005170554b11738,0xe069665526d51d825461c7ee684868c5b901498513f9845142550605555626cb,0x4d556755187c6e80a48868494420698c5b7015ea513fa1a5140251e0554427840,0x665507e5418540a2b8401e49e3b5af0740a096b2578660a06f008300551362738,0x250697d8637e541865462b82b4c3fe785150740a313fb1a5ba010690c8630d54140546,0x6653b6d5328d8401c5204c3fd2206f15843313fc1a5140253b0553229840,0xe069667bf6d5438d40a0a6e85c51f3b5bb0740a366cb375bc08069027bf055432940a,0x87870895dc0740a19825477d5,107796,242964,0x4d54a6d5408d8502b8434c3ff3b5ae15843313ff1a5ae0054a0554029850,0x665406d540824dc0a4a14c4003b5ae15400094a1375ae0254005540114dc]
private def payload75 : Array Nat := #[0x398155c8151a514,0x398155c8151a514,0x4d87f645065506f7c89e1d81e4a8823b5b90881e2f8821a5b90486f1181d,0x6c86f3406f797d5493f97781a7f5b9186471687a5786700880465063506f29825,243118,0x7d83e395d23a89615899096b541856,0x2b3fd4c3fd2206f1a514,254936196534,327487149052,0x5e83083830853ad48647685de5006b4b7cf0186f19368306cb003d14686760830,0x746e88771d7c63d4966a1e5de3006b5b75204069146c119368306492036d235e860830,0x536b55463d826cb1c6234a6e58606b4b7212d6265650c8506d357dc3e7d5056b522532,0x6c62783567716370a75b3a6cb4b63d2e726345328206f708300240a3f67945698,0x6686787830713d1138302c3ad8883014368366cb3586f256e51b06b286c522628,0x4359d6106b8381d633d1137391e3ad8181d04069336e51206b5181d70408286cb2781f,0x4359f5463d636cb1357c3a4134b54115585517bf6e73f0e3d10556a7906b226e9,0x4d63d836b1637390b06f497255a5065d7bd040691486734726355870c6373f73c40617,0x1f06f4d7cf645328f7d54963d3c6cb816b51450c6f57830626256370556960623,0x435a18356c1357b3c546400698157d4e5083678e55840007383f7d53506f4559e,0x536a9836048f8401357e5c7394b63d0752e3177d3763f0f5460556637069455a0,0x436947e5e889850136b16a850765e92e6493672547069036cb217f729725,0x668153406f797d5136b52c75469876008252863d,0x8783471840138708063d8c70f3382436896554bb0f6cb286cb45884,0x536b5836b585828136b54c828816b504828056b5276b5,564095112555,0x3306b53856448668d3d11506b497cf3c5de5d6272e6cb3440a35866005130583060830,0x536635463d8d7397406b678185c5de4b4b9083bf095df374240440c2872557069274a2,0x584b63406b5f6e38a6e5384ba2c5685b579184190949c706131d06b256b92152e27587,0x5e40d548357981d2e06b5957f3c6e55b4b4083be3440a555a4255782872029626,0x4d63d8357182739200691c7f95a6135b61b175e936630374840254023546570694581e,0x5369d755217c6e8675ee77546420695b57a2d7254f5eb7061325613287264742e,0xe069438698356f79546020691d8654c40a887b2143682f7396e74c0c6e82678e6251c]
private def payload76 : Array Nat := #[0x535a98356d8f840595825c7393b63d07372094a21106f555a60053b615755b069455a0,0xe06f5383087830715060c069678656a40a787b21436809739708651d06b0384061577454d1,0x5e7e561069835738640a1370d886c0075461206931840555a20b5060906f286cb5706927738,0x535a7460698b6ce8f546595810d07c4c6e87f521185a305069094a0555a51d06b207256136957069454d9,0x66815797d56781e2c7d78875b0181e377261d06b023b96136957069454de,0x535ac835708d739595802c8288875b4e8182f7cb0086f106c157069,0x6c5608b6278e637385206a7262206f69830076cb165915540c006e70540a4767d,0x6c5617a5968240a395200d06f2c8306b726186cb1940c505910055c4163740489,0x5863d7a59782739497a41e6e1695872b0772e7a4096e1356170706f035e0265067b59a,0x7936d2b077015d11940c6e4ab0081e0d7526273a,0x6c55f260697a6ce895460a6130d0693c8636b7262b077187251940c6e4ac0069d1907b236e860519,0x1706f6c562727d663506598671e4bc698632a07733867346076e6910e5680573927862,0x250696c5637a5958a5463863f1e7a78c546085e916604506a90e568107397b59b,0x7e63d89825387268c815158301006f0c88421752,0x6c565838566363d2a8991e4d94b6c2143bc0982450892007500d5ed65899,0x6c5647a5987963d2a3bc1e824784e52b07714899096f86e4a802750055ed7b899,0,0x7d6d57a6d0638286606b1e4da5d6c14e756165936e5a10055d214dc7b59c,0x437d37a599797396606b0a8281e4d44b6c2014e40986f35897037f9124dc42709,0x6c42c6d6e3866e5484c23c6134b66b2b06b1881e2f52e470695587a25756056af275db,0x745687a67a7973913654805686961b2e7250986f47069527a70e5e96181827648,0x58818755e985637136555c7394b63d0752e377250f5463f739607db,0x1f069436987a6798f40a4963d5c6cb8c75b06830366cb470695787a025e93f7cf4748b,0x325f1260697a7367c6134948a1e8404b66c2b06b0777d2c06f566c16e53b027562863d45694,0x43697875f28f6372a5401e7d54b66a06578315fe470693764603374056b5275db,0x436e926069547887940a6752d2c6e8698760873f167bf355850f6cb2863d29728,0x4369c5f413826cb1c5fc5a8408c7582d62610069095d0357dc1f7261906f3f67b22532,0x745687a67f8273920069136571e5465b5ff2e64834780376044307a2063f23546457a7,0x745687a6807c6cb0b06f136563c7386b52b4e50c2f623377213e50c2162329721,0x1f069436f35f602635464963d4a7394b66d2d64809604376300f4170d76f65546,0x1f06f436996452f7c7384963d3c6cb816d71450c6f578376230b50c2872160623,0x665f7460697a67e8e546136d63c6e87652a2e7256f369554d90f5a3090692386329726]
private def payload77 : Array Nat := #[0x585fa460697a67c8f546136584c6e86952306626050693186337726037392863d45695,0x4369f7a5d4636cb13659774fc78856184bb3471e308591f63d2183422859,0x4369e7a681714fc1370d6a63d8188e185ed1b850355840f4d90586f45696,0x43825838950a86f687d54006f5b7d90186f0986f357540e7d5058303506f2787a,0x436ff7a7398d739678035c4dc3b8032d6441682837644007393f739456ff,0x588152606f79738136d61e7545b87a2b06b077fc6f36947069554df0377d1e06f29726,0x85899787da2b06b554da00856,0x7d7257553b650698d71d02069498156840c2d4d919818305de0f86f3f6637b63d,0x5e77d5f3b08663f595ef80546420698c5cf33617347f835840047393f6667b63d,0x585cd4450c8f486384961e50c8c5cb2e5282c06f5166250738206cb4663d27765,0x25069585d0835768f4940206f498352c726785321463d3174a576cb008400d5fd27758,0x5836a5f3b7650698f6b52006a676466a53b8c5cc0306f086bb3152e377382584026740275f0,0x5987a1663d37825047d5,0x247465f3b1650698f4a41d8436a3b88c5ce086ba195d337850036cb3f667115d8,0x1f06f64870858302a40a5a8250006f36870527d5007542176522818,0x585d15f3b1650697c8961d8435a8998c5ce367d237850036cb3f668276c0,0x64725650695a8990f82545856,0x3d78e6f06b8b7ee8a617388562c3ad88756066134f80b3581f256e51b06b6175222647,0x5906b534a23406f726c1637d56748d3a8405d8180873f120691b7365552e0b7562863d276a3,0x745e026069547888e63d4952d2c6e8817640873f1206916864554100f6cb2863d4788e,0x5906b438705f8648f3d1388596840a40069698640652609876376cb0e73f2863d5706911745,0xe072434cd835227f06b7c42f020693865b685467663d00069087ee6f738733730436805574276a8,0x3242c875fe4506c896464852b4a7383006f8c65a08740315f01a50c0e3760d76542613,0x5906b535ea4436c714d9386d65c6e84b52a145f628069316ce55544255a33606905572276ea,0x4d630835f98a5e93865d5c7397663d0752431767354170f5460556e37069276a6,0x4d63f7e77d855216763d1e7398c65c04069186a74f62455546006483f6177b7f8,0x5906b43825726c38f3d113870687d54006f81891186a16f81835754008700d8303506f,564207659072,0x534a1446c1896531c7654c8288c6d5733c2038970d76511748,0x5349f446c46349f3865e1e4dc8c65e186a4316d05541c2541c0d6d0276a4,500433127490,0x5f86480899186a835825]
private def payload78 : Array Nat := #[0x5e8308383079513394cd685de5006b766a1040691875b3640a306cb003d14686645756,0xe06d438565462d8d4200c06b4966e4c5de7f4cf2e532346176e830206cb0d4fc276b7,0x434fc83803827396766f775685b615040690786334726356260f413124134281e,0x74617545fd717a4496703c5063006f6b5e015617345fd557a40f739238432736b,0xe069437bf5463d8d54402069676714c40a5b675184fc3464e706cb0b63d3f5e86253d,0x5e73f26069546458e63d4951b2c6e83b6770873f12069346455263d0f6cb0d4fc277c2,0x434fc75843637390b06f676725a5063b676030691486734726703b23e8403f5e5405f4,0x43501645f8858401c8302c40a420693b867146cb5186f1a368045063f7383b06f27830,0x7d5f454639828401c8304c5062206f8183018739346cb1a3680040a218301a06942867,0x54726636b95c81d5b815184fc1a89e6187a6281e,0xe0696440a866522a7063a7d74b82208830558590481d22870,0x6c899546cb8d870676741e63d81870184fc2f8461a824008403f850,0x438565465363756676731e4dc696df186b73464c5089702828055ea276b7,0x546403a89a3f842,0x536b54c8285b678456b8,289737496245,0xe06986725388563a82584899,0x5e4bd727368d613150772b3c11e87a6b726153bd1940c6e6942048e266e51a06b65683,0x5e4bd7a687825682b3c12c5876b7262b077076c11940c5058c3e4c1266e565683,0x1706b7d5bf754c38f6e50a5785a4b869589143be1658e5540c0b40f2181d7b685,0x6c5c3544138973906073134c42c5883b4b51540c165866e7a84306b005be416e5224be,0x6c5dc7273a7c6cb678304c8766b6cb2b0772e7bf2f6188d06b707ef025c0263d18906b7b684,0x6c5c254413897392b3bf3a7db6b72515546517256e7a83e818126374773c,0x5848e7a68682840150774981e6a7262206f7f87a4e756096945540c005c1126131a06947736,0x1706f6c5c48352f8d7381c50c6a721766230750c5172155623005dc126cb6568e,0x3d81454413796cb6740a41069697dc177261006f1a532005bd2684062734,0x25069248677a8308540a150772b8402c58b6958307368516cb5086f0a06f00830055067b830,0x250697d5c57e5f3865462b3c06a7278851607368517256e870010690c8631240a7b830,0x6c5dc75891896cb497bf3a8407f7a74e83031882526cb07069025c84640a65689,0x585277a68d636e82a73f2c585220696b722064d9517285540c005c11040a1a0697b68c,0x6c5dc7a68f7c6cb2b3bc1e6fa6b6cb2b07714850165845058d005c9124fc6568a,0x544137c89e387261772604871]
private def payload79 : Array Nat := #[0x6c5dc6389e1281d29881,0x86752397263c815187261282527413,0x6c5ca877397c7390a81f2c5927f6ff17644098285059225818414dc22803,0x7d7b8448998d4dc15077388282c591695904e4e45086f005c62173965690,0x2481682739138286a7286b7282581605739,0x7d8227a68d63754678226a7262206f2b077157fc165945540c3e815217383b06f,345090012811,0x5f89a150772c591336c123899,86135,0xe069747db5463f636130a8406a490696a92b06f336c1120691977d845460f63d21739476af,0x6c6b26d7252b5466a63d40069696ad0151c097382706f6e830037e52640a5706927865,0x3263d726b4637391c6e84c525696b32a06a148634f7265062607069006b00d54640626,0x1706f6c6b48b5328d738398406a721766230750c567dc1a6260f63d126cb476b5,0x6c6aa87617898401d506808153006f696ab18726315ef3085b006b1287391163d,0x7d75b6d63d796cb6740a410692c6ae697dc17726568301a5320362726840627cf,0x445d77c8962a6cb5d816568413f899,0x726b1868992b8247f5e2508411263d,0x8d4dc388281e75b6b728336c15086f2581621739,0x7d75b726b5868281c4dc040696f6c1376c10275b23828476b5,491417421484,0x1e75b336c123899,0xe069747fe835db6349d7d06b2a7065c6e54b58a0853b1a81e255680d759224c5,0x747d5547228273f496db3a63d5b54e040690788e3640a554d90440a090690588e2274c,0x4d63d546c98273920069496dd1e5465b6030306a078633472635626036e823529457a7,0xe0694d728835db8574c2a7067507d5c6e84b541145f628069347226e73f3e40a360690d6cf45700,0xe06943754446198573f02069496dc4c40a887dc066133464e6e74c0c6e86187a6253d,0x4d63d547238d5540b06f496d93c7385d5440306a3385d34626705781f8402160545701,0x53830547268f3af0c069496da6a40a887e2066133464c376cb038402662845702,0xe069436f8835db867251d5337507d3a6e88c76f185a5100692f86370626025460d6ce6261d,0x5862646069546c78f546496de4c6e87f546066263464837780037392863d45704,0x66816798565c8993464002896235da,0x536b5547230a8324c8283b8140d83242814]
private def payload80 : Array Nat := #[0x536b5546ca8a8973a4dc7f6df3375634653357560c8280d75b45703,0x435a1718255c8990573a,0x546ca688991a6c1,0x5906b436e4726e48640a496cb5c63d5b6d52b06b2d73436538554c40f538284d97806b45841,0x6c73a8b568826cb5940a210691e6d35b7f00848919375736e00086346830116cb,0x1706f648238f5321c840804955b6d50406936532737e20336c284da45843,0x250696c67d647dc8540a2b840687cf3b60808413516cb736f90a06f0f7904153211726,0xe06924788726e97c4100a6e87752d5b6d408413366cb736f408069286e947585,0x6c6808b568633761d7382106f3b540145f26f50c736eb0b5fe3f64611721,0x3d413726f57c554488404a60a5b6d20306f2d67b4f72652544070693e85d3f626477dc,0xe069837dc7c5a3136e88053d5b6d62d67e36544306060336c284d91164e,0x827260841309825,0x3d865726fa826170a6cb1e6d85b5d918790094fc736fb0f7904658462850,0x1706f648236377d137541e6d65b6d61306f1977d578230336c3c06b284df7806b654df,465601672919,0x7c4191c8992d682256c27806b,0x633775b6d5736fe036c17806b,491627,0x584d93406b7a88e635de397256a644400695d85e2e7394f7fe356e81f8232152e57069,0x244137a74e636e8200697758570069186e80970c356e8070696158557069,0x7d7358b6608940a0a8306a6cb400692e637516615582b025db286cb570697b6f9,0x6c8307a8307c506386473a8403b7271840a120696e8300086f1036857069,0x4373a7a5dc636cb1d87677830698654e40a280691670b5272b0b618417bf407ef,0xe0695461d82546020692c6263b726156e81670e84535025db287257b695,0x6c83046069548676340a396c53c8406b60001506098306e830206cb103686286f,0x25069248657a86f8540a0c069396c63a5463b5fb16870508880a06f008306151c62738,0x437347a7508d840385326a7268f06f076cb56814356e8027dc286263506a,0x244136d8148d6cb0b06968626787dc17840196295272c0706f2672629532,0x24616260697a751895460a604686488869214739093bf5272f206c82663f60546,0x250696d8158a5465c8233b726018401660b70882025db,0x4373b2606f7a74f8550648607808678869101739093bf377300e607468677b691,0x437377a753714fc138706a63d400696986b016cb0987e355dd008702863d570692786b]
private def payload81 : Array Nat := #[0x6a7260889e356e828726,0x4373b793bf07825093bf,0x8a899765e8086cb568167b87a,0x6c8997a826638285c86f886f618739097115272e23899,585880643373,0x548143b7230882816710,0x7d73971825396cc5c899338991670f2672562825,0x4338d758437c5ea2006f0a6bc6a3af6b74703069086bd317e2703b23e8402176040625,0x5e77d83486868662a528688303006f337cf3160d1a50c036cb217657b63d,0x2477c6440a8f4a35980d808408160e337d51006f31742558590054636069217614761c,0x5361e546307c5e92b61b6a546220696b85e04069088332f5463063f207397b63d,0x4338d7a5eb8f5ea200697773f5b6120306a317dc35613036e81253d27766,0x250692477a7a7388f4880206a0a8692c7803b6131463d3174950739026e86153427767,0x250695385d546268f494498352c726785441463d3174a84554008400d62027767,0xe0694463d7c5e01d8645a4fd6b73f1463d2f88e706cb0c6e8217647b531,0x24779835d28f4a0020690a6be2c7253b613075214f86d8107c3763f0f546126243706927762,0x4338d835eb8f6b52006a0a7596a53b6961a0306f3153b356b9258402175d2760f,0x24611546468f4960a5f04c50c6b7400876509613703b7207381e06f60540,0x6c6228349e8f5e9020690a75b7774c3b613040691787a34541703b50240a2175f1a06927763,0x4338d4c81e5281e,0x6440a7c89e2b8763a7d74b82208830558590481d22870,44934764389,0x8f7da0a6bf5a825703ba6588e,358736942773,0x437695f86686532394c9685de5006b7f7482b06b337651b5de5742b0f5324686645756,0x5906b7d8037a5de714da7406b678035c5de4b4da185a834717375ef0441821739457a8,0x7d870448998240c494d92c6e54006b7f6e20873f1989950738254140d4fc45755,0x5906b5381e7553089627496cb8063d8c88e2b06b087f034790703d10f6cb2183065863,487546247232,0x3d63d83803827390a772775685b6442b06b078637206b098633561703739124134281e,0x3d63d8e816805685d824,0x3d63d5f88e896cb1d7905a3d18f06b817f03383009863376cb0f7bf125847c06b4281e]
private def payload82 : Array Nat := #[0x4d482547157c42e2b6493c613220695b7312b06b1881e4f5505742725756055eb2736d,0x7464754714717a40a7733c5063006f3b7321449534716557a40f86f238432736d,0x3d4838381871840487e44c613220698c80a188563471b703d100859218303b06f47834,0x5906b2488e7a5de714d90a7747507e5c6e83b536185a7280693478a505e00f41041864457bd,0x5906b435ab7a5de714d90a776774fc78856335dc3471e356b20c7d53f85022859,0x5906b7a5de714dd138543a7d7817b706815528150f542,0x435aa5471d718281c7782107f6a7395b7321888e31899558280f86f27757,0x537655471d716ff0a7774a4dc8c7b82b06b098665742d2575627756,0x4369d6d87a718820a7754a7383006f3b7331869d4f87a558820f8292736d,0,0xe06c8372663780020692c7258c5db15856348227363d025683f830,0xe0692474a725098940a136e83a57876720064c85406b096e0506e50081d0d4184773a,0x587dc64626866422a532688303006f067493163070637036cb288147b63d,0x7d72544368650698d870020692b87a2c63d7672508830280695188e846133e40a4186311830,0x5836a446c1650692006f3a6b9767260f069317dc6e6131f8402348f2775b,0x7d7268777d6e06f8d87602069487076a4e48c5db4e7096f72173637255462649127759,0x585d0546268f7dc0206f2c72678532156e819814576cb008400d62127758,0x5836a64725650692006a3a6137672603069196441a5460f6e84186d4253d,0x585cf54726865ef0206f386ab6a3b076724156e8317f535739048400571222617,0x5e5466463f65069866c8386a94a5e98c60c4e7072f546377391f546090692685e6561b,0x7d5415f830650698a87a137cf3a5e9886184e705050695176b3540a046cb4663d2775b,0x5386772867637d71c8303a81d0889e1b89e0b81d2186f,0x5836a7e7fc650692006f3a6b9767260306f0981537738037544186d4287a,0x386b5517707382805713,0x498165a825378992775a,0x8664e558990382505888,0x66644878998a73f397a15a63d5d8562b06b0788e1b5de554d92540c238641a06b47815,0x5906b436f8836e57c429388563c63d6b86e087dc2f85d706262554462726,0x5906b726e489623496cb5c6cb3b79636538738410f53845841,0x744c75477e714c7594ca686e53006b5b6e62b06b0874a1b5de554d22554260418,0x5906b436f9836e57c42b1d4c93a6e58a06b4b6f92b06b337a830532255326306b457a8,0x5906b5f8678d587138623c5688186f2b06b3478e7081e023ad27873]
private def payload83 : Array Nat := #[0x325f15478b89615498034a6378188e2b06b2c06f3188e6e53b0f54e2863d65854,0x5906b4369a836e5714da678033c6377864c186a03471a375ef0f4183f73945823,0x5906b4369b836e57c42d4973e4c6378162b0853b3471d376430f53b0d75911493,0x5e48c547897c4280a63c3a6373b74a186a41b5de554d5254181e06f60542,0x436e926069547888e63d4953c2c6e83b79c0873f1206934788355850f6cb2863d457a5,0x4369c836e5635eb1c62e5a8403b795186ea1006934789357dc257a811542,0x248635f863636170c069137ad3a5463b644066133471c37725255543f73945822,0x668675f8638a6170206f137a92c5068184f06613098623586f257a40d6cd22647,0x4e06e437544462c6349e02069137ac4c40a3b797066133471d554d60f8306187a7b537,572607555385,0x745685478d7c4300b06f137aa3c7386b53a186a534780377210f55021605457a7,0x7d6015478282840388704c5062206f8c8881886f703d10f51c2183042867,0x5906b58816547908f3d1496cb4c54662069818612b06b337a7165307382b0f6cb0d83035069,0x6c5f5547818d864137ae3a6cb817392b06b1788409865554d90f51d057f01a069,0x436996453885841496cb3c6cb3b79934719376230f5522781c,0x5906b537516d62a7c42a496cb3a7393b79a186a24f80c554b7048650573c457a2,0x585fa4606982830388574c6e8817b4067800506937726037392863d,0x5906b836e57c4313a752347840f540,0x588152606f634a2497fe1e754818142b06b1b5de554de0f55627823,0x4386f3f06f7589963830137b03b79d3381d0506f16899528670f86f057542786f,165437,0x5906b538285478c714d4137ab0d0804a7393b7a0087f93471f554dc25419058972786f,0x4386f8e816137b13c7393b7980788e0988e378280388e,0x538226d88271882137af4a7383006f3b79e338224f87a558820f829407d5,0x588152606f8e815388541e7548c7b72b06b1b5de554df0f7a827823,345989,0x547844a89a347840f41a,0x4369c4c8283b79f457a6,0x637da3b79b0d6d1,364651,176235,0x6654275542486ea5a6ea7877e2d6e62f4d2526e50b4d23f6e6226e5]
private def payload84 : Array Nat := #[0x3d81d75419385872f06b3c8225d5500878d1b4d3845680478021721426e3,0,0x32859723ad8f7391c4c02f06b5a6ec3b6e5157b2198655540a0451c7a072217386278e,0x244975f52e8f7361c4cc2f06b5a6ee3b6e50749d19663356370b4d02653b7b5df,0x3d81d5f54a858321c4cb6a740885df0306f075e61b54d3736d0b4cb287407b5df,0x3d823754187c739595ef6865f78783015ea098036e6370b4da1906b3f6ed226e5,0x747df757bf8582b676cb3a8307f882157f0120691a40a256cb1056865891,0x58870723ad8f7391c4d12f06b5a6fd3b6e50886f280695540a0451c3f83065867,0x537265f544450692b626687dc22069157b72f554526e82564e3f6f8226e5,0x588227555085634677212106c5a882787802e54c2c06f507382564a105686278d,0x5354875830638821c4d64a5685d891157b305069098005040a0b4ce3f6f07b62c,0x4d7e05f410600691c4d92f06b5a6f43b6e51753e168021a6e80b6e912606370696278a,0xe06f538337a86f8952f67642686097877f0873909889376cb25642266096277f,0xe06f5f5174885e3a8267f718087391a7390e85e2182645718,0x3d86f5f41785833676305a6f38c62d08889096cb37739256303f6f36562d,0x3d8205f6cb63413385855a6e978788087b50953c576e81f5853f6e962788,0x24542757a81c4d75a6f53b6e5087b76f63c708401f7dc267dc62789,0x3d5e15f7567c73d1c4bf2f06b5a8788c866087b83675e5063d0b4dc237cf2975c,0x245e45f86f1c8285a6e1185e7098041a7390b8283f6e1,0x588224e8735081d2565210568,0x58822758828f73a1c81e4e8732c06f357d50b82510568,0x5881d547d54506f71899137d55a81d2206f4b899157b9368950b86f2186f22754,0x3d8235f5561c7a83a8233006f08814097fe307540b4de1906b226e5,0x1706f588828b8708d83013752687ef7878f15891097fd703bf043d11906b3f6fc62791,0x3d8715987a096cb578253e87a,0x588287a7398f7391d4dc687f88c869157b451897507391f5922181f22828,0x3d8277554e8f7391c4da5a6ff787861588e16803704dc256443f6f162792,0x588267541b858996764e5a82878787157bc167ff707390b81f3f6f262793,0x3d829723ad7c7fc1d8415a6fd8c8670886f098051a7380c8413f6fd65867,0x58822758828a8821c7a74e8732c06f50738027fc10568,0x3d8235f7a81c7a83a8233006f157b709802307540b4df1906b226e5,0x3d81d5f8291c8823a8225d8820306f087ba09801377380b8822182242882]
private def payload85 : Array Nat := #[0x647fc63413677265a823087b535754257263f823,0x588828b8708d830137545a6f77878f158915187070738043d11906b267fc62794,0x5f7a33a89a576cb3f6ef,0x5881c3881c506cb0b89a,0,121559578361,0x3d821087bb528283f6f5,0x5a6f4157b61a825,0x8f73a558993f6f6,0x1f06f645408e7d52b5462c3b640069888321450c6f7406e646206462872160611,0x2464a2606985613394964c5e95d7061450a31546470690b86d2863440550,0x4463d8d739397de6a6487864801546280692f7ea5763f0c51d2863f6577d,0x7d7d087632898402a53b776b98606f0653b2f7dc2706a2064b287234538d,0x7d7d18b63b8d840385446a7268f06f015542f7f4356e8027dc286263506a,0x7d7cf64633858400a7dc2c40a5006a146cb2f7f2356e81f532287267c06f,0x1f0697d7d4837ce8f40a2b5463a74c400695d708063b536541470691a70620722127ef11622,0x3e0696d725715462b5466a725400694907d2d63f0987473533048630560465779,0x6a7260889e356e828726,0xe06f7d7d97a86f8d7d50a8825c3bf88830143682f7fa470691a825027522864727867,0x7d7d8838952a7ec687d54006f5d70a0186f0986f357540e7d5468673506f6286b,0x7d7d387893797392a7f91e4dc5d709064e40986f47069028282864e6577b,0x776b9336b94538d,0x7d7d97a86f897380206f0a8825c73888830143682f7fc470691a7fc027542864d27867,294349473842,0x837da3c899188562864c,0x7d8703406f8788e8253b3863868637767441761c4f809376151f8560d4fc457c1,0x7d870260697586b8e63d496cb2c6e86987e2e870120691686b5263d0f6cb0d4fc277c2,0x3d6cb5f8648640a2a7e46840a4006969864015314f80d356e8255432863d57069277bf,0x3d63d6d80b637390b06f3882a5a5068c84f14865517ee505d20b85b3f5e54063e,0x4366564637636b5497e3808408162f0852e1006f354a20f53b5f06f0d759457bd,0x3d63d6d80a636b20b0690a8377740a8c7c6087451963a3549e258300906f1287a29551,0x2488e646378a5eb138545c6e83b54e145ee280694f808505e00f51e41864457bd]
private def payload86 : Array Nat := #[0x7d82a6d80c85521496cb1e739817c9337624f631505e53e8653f617457be,0x5e74964637635ea1d5497507e3a6e8817ca087dc100692f85d35488255443f5e962635,0x53764445458e8350a8381e6cb817394e5fd4f7db848642551d3f5e0370697b85f,0x5e60d5f7f989866498894a6cb817390860d097f9378660386f105401a06f,0x646373a7524f83f,0x634916875236637,0x646373a7d70681535497,0x4386f638300a89e5d89e1886f358300f81d057d72781d,315356268581,0x646374a752087f04f80f354a2,0x64637138543a7548c814068151006f52815,0x4366964853634950a8432c5ed817cc1866936853354950f51f05894277c5,0x7d7d36d8106349f0a83a1e4dc817cb186644f807508972555b055ea277c0,0x2488e5f88e638280a83b5c739817c71886f528160e88e3f88e,0x6d80a5a8990906f457c4,0x5e74a4c8288c7cd457c3,410276484437,0x25069876c18d5db0c069806c1785db175db096c129069025db106c157069,0x667687e49a89840397263c77d8606f08613347dd2906908069466c1625db,0x538117549b8d840385326a7268f06f076cb56814356e8286263506a,0x6c8316d53f856e8596193a73f3b7220740a347dd290696e82f08069207282374c625db,0x538327a3bf796cb2a6238050c3b721087381006f568111a54b036234650c22721,0x538335f5477c6e8676266a7265006a0873956817356e825626287263506a,0x436e8896cb4a61810618,362942916625,0x53834548128e4fc0c069397293c74c785db014fc6f8126e834025db2174c5706922729,0x548157c81d0a5db6a65240069017d73682257882080694681e22726,0x7a3bf7c89e0881d,0x6c8303406f87876637d5397272c7528c7ef2e3bf168826e83008069037fa10368570692272a,0x6c8358788e8d4dc0c0692a7fb4a50b3b725187395681b6e82c2072528644570697b886,0x6c8303406f8788282738397272c7543b7272e7382c06f168826e83008069037fc1036857069657fc,0x6c8318787471754397263c77d8606f147386f8154b06f08069237fc625db]
private def payload87 : Array Nat := #[0x7184040069188965582b57069,362945951523,0x89899397252c8804006906899080696188022725,0x2489f7a8840c0695c86f3b72a18739508950e89f23899,0x6d816858251889920728,0x4d83c5f7d55506f2b6b93c8134b8820881e2f87a3087a048251136b,0x4d83d547548d83d5a8a1348a126840,0x4d83c6d7385506f2b822688414b882158224f84130882047fc1136b,156804335612,0x448993a89a158256e8883f842,0xe0697d8827a8308a541138405c5e97876f1840a120694f84a557460f75b127d562870,0xe0693280c877ce8a51d67490778657f76a17645317db7049200739286cb4584b,0x747693406f7e86682532395320d06f778667f769068434f637557480c7484163765843,0x5e7d53406f648328254f674993a64678740176461b499557400706f25832467d54254f,0x665e86475882552675e84a5525d7581562316743557430084d106cb116cb,0x5e7d53406f8a5555807d674984c5507f76f148633187a5061f070690084c0d54640649,0xe0695385e5461b825461d5e92c6486b7de1763f120693180e8454600739217396285a,0x250697e6cb825431d6e8778607854e1840a568646e8700c8641240a62870,0x667e88b6288a7bf385417786369830176cb120695688e57613027f00540a3706962853,0x4d7ef83627827bf1c6cb778618c546175415686350830007f00d40a3706962852,0x7d830648307c5133940a778667f76e148404f63755741080693e8664140a62859,0x247263406f82544674880d0693c85d767dc1764e4f637557490084e236e840554,0x5e7ed7706f8251e1d5eb3a8407f76d087ed31808376121f856056e862858,0xe0695885f877ce8a51d1c835778657f76c17645317db3061000739286cb62855,0x3406f825172b8914c89f698843189f508840073905739,0x325513406f548768a830676b24c8918c5462d7ef6f63a557451f7e92140a1a06962851,0x666435606f648918a53b674a20d06f4c82e7653b177234f6375574b026410584062854,0x3e0693d867648308a51c3940a7786569739158401b7f81a6140282d0d50647870,0x7d87a8255813899778626b7cf145d55574d106cb62888,0x328496107e386536a84c5d814176510084d1282811889,0x8a559674a16884a7f771318065574800848468284584b,0x6686d7587a8a8824976f77863157fc12069576130084f217383b06f]
private def payload88 : Array Nat := #[0x82556674a20d06f788154f6370084e0d75462854,328631261247,0x7d8847589f2b8995a89f2e86f12069508814173947895,0x877da674a37f8805688e12899,444182386504,0x7e8828687a397a75c8137688214879097d54b06f3e8254263d,194714,0x6c86f6d6cb7c506395f83a7eb767eb185f8197eb557eb0086f46506116cb,0x6c8896d6cb8d739396303a7e77864218630197e7576420086f0554b3506f65833,0xe0697d8935464a825462b8632c7218188218634168747055000738055553506f,0x5364e547f363840396262c7dc7885d187264f5447106f008720d554476e8,0x6c86f728628d546396074c863788671864d197e15785b00873465063506f,0x7d8617e6cb865462b82b3a7f1787bf1740a197f0270690c8630d5417b830,0,0x7d7237e7f682840397243a53b8182e18723197f6558400c7240d53b6582e,0x4364c447f5718401d5ef1e7e2700695d85c1864c197f555840008750d51835078,0x6d6cb858252b81c1581c00871,0x445eb89850396363a7f77886418649195e02706957868048540d55a7907e,0x248324483982850396503a7e36b75918650197e352759037d60554a3506f,0x6c7396382533899318841286f,350272,0x6381d396523c546400690f822,0x7c8503964f3a5e0400697886a,0x6c892728947c4fc3963d1e870400695b89f1863d09870270693589f0087e285ed6582b,0x7d88e794dc3964c3a7fb7886418644197f0270695786c00885418567b82c,0x6c7397289763739397251e86f400696b8282e4dc197f85786900886127396582d,0x6c86f3406f827383964d2c882788671864d168825786700887465063506f297fc,0x4d871717543972618726127fc476e8,0x7d89187870897380a7543a7f1788601740a197fc2706902882418707b830,0x397245584005556,0x43873637382a7fc3c54640069186c8008740588265831,251228469310]
private def payload89 : Array Nat := #[0x71840400691584655840008703506f,0xa8803a7f04006957864,470442989618,251241006883,83872807009,0x6389a2a7fc3a7fc40069358a1278a1,0x7d8828787a8981e778827881e2e36d2c06f50880287d562825,0x2481a878828e82267882778827881e187d52c06f50880287d562825,0x87825895dc0a882177d5098812706f028764182262882,0x7a5dc8e824777a31463d55895257d746899,156723411008,0x7a5dc7c7fc1d88278822087381006f1a8810c88262822,0x247d77782388823077541b87d3787d618237b823,0x7a7503a89a076cb6e895617a3,96868419813906341,0x6c5ec8788d8f5eb0a7650888d565ec355eb21765,0x435ed7a7cc718432c7d2185e335856057d2,0x7a8428f8501e8996988e08888507390088a215e222898,0x7a7c82c7da556d1057da,252044,0x438568389b79856395eb2c85031850355eb055ea,0x878507175b3a88e338365689d507391f85621739,363072829581,0x538385d88b6289c,0x3d8875f36d4506f3986d3a8823b882088771006f1a7382086d2188222882,0x718a1498156a8153006f1487b2f87b3075422752,0x4506f3b8441a89a22844,0x5f7c20888a35825,87560104588629779,0x7d882878828981e0a81a7788288822087d52c06f5087f4181d7b825,0x7a5e18e8257781c1463d3589e257d941884,34966]
private def payload90 : Array Nat := #[34856,0x7a81d898291d8825c88278822087381006f1a87f0c8824188262822,156723345236,0x7a86f89881498995c884087393589e0f89941884,96868419814823968,0x668a1488a11489a4182962829,0x87876778822e3bf578190a06f287d562881,0x7a3bf7c7fc1d882087381006f1a8810c882,0x7d882878828e87467882778827686d2e7382c06f508800a06f287d562887,0x1706f6d81582815067540e752,0x6d8133a89a076cb6e8953f83e,0x7686e178283f86e,0x7a850088771006f357d6,0x6c8788789f82841138572c7d97f8844e8792c06f50738007fc4663d,0x718a1488804a8733006f4f8835589111899,289353848883,221228673020,0x3d87c5f87e63754388703a86f8c89f087fc554fc1f8702186f6589f,0x5f89a2c7d218894376cb057d2,0x858997f8a25575b0085605895,0,0x248858784e8d891814dc1584e198856e8910284f2184f1a06f118a0,0x547541d8753b875088751a87510754,0x4d8876d7385506f2b8744a8824b882158742f88230882048871906f11738,0x6d6cb7c7fc2b841158410089a,294272436052,0x5f89a3a8a1088871006f1a887218a1,0,0x7a7397c7fc1d8843a89f0886f1006f1a8810c8842189f,0x448991006f1a87321891,0x728281d87222872,0x5f89a3a8a1088871006f1a887218a1]
private def payload91 : Array Nat := #[0x2b8454b8451584530845,0x64843858962b8433b896158431a8964684347896,199789598790,0x8788849899158420089a,0x6d889138470684711889,0,255704729747]
private def payloadTable : Array (Array Nat) := #[payload0,payload1,payload2,payload3,payload4,payload5,payload6,payload7,payload8,payload9,payload10,payload11,payload12,payload13,payload14,payload15,payload16,payload17,payload18,payload19,payload20,payload21,payload22,payload23,payload24,payload25,payload26,payload27,payload28,payload29,payload30,payload31,payload32,payload33,payload34,payload35,payload36,payload37,payload38,payload39,payload40,payload41,payload42,payload43,payload44,payload45,payload46,payload47,payload48,payload49,payload50,payload51,payload52,payload53,payload54,payload55,payload56,payload57,payload58,payload59,payload60,payload61,payload62,payload63,payload64,payload65,payload66,payload67,payload68,payload69,payload70,payload71,payload72,payload73,payload74,payload75,payload76,payload77,payload78,payload79,payload80,payload81,payload82,payload83,payload84,payload85,payload86,payload87,payload88,payload89,payload90,payload91]

private def tagMaskB0 : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,0xc0000000000,52776558133248,0xc00000000000,844424930131968,0xc000000000000,0x30000000000000,0xc0000000000000,0x300000000000000,0xc00000000000000]

private def tagMaskTable : Array (Array Nat) := #[tagMaskB0]

def tagMask (i : Nat) : Nat := (tagMaskTable[i/32]!)[i%32]!

def pop4 : Array Nat := #[0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

def pop24 (x : Nat) : Nat :=
  pop4[x%16]!+pop4[(x>>>4)%16]!+pop4[(x>>>8)%16]!+pop4[(x>>>12)%16]!+
  pop4[(x>>>16)%16]!+pop4[(x>>>20)%16]!

def pickRef (i t : Nat) : Option Nat :=
  let layout := refLayout i
  let other := layout % 16777216
  if (layout >>> 24).testBit t then some i
  else if other.testBit t then
    let z := (payloadTable[i/32]!)[i%32]!
    some ((z >>> (20 * pop24 (other % (2^t)))) % 1048576)
  else none

def mask (i : Nat) := rm[nodesClass i]!

def one (i : Nat) := banks (nodesFirst i)

def two (i : Nat) := banks (nodesSecond i)

def wt (i : Nat) := nodesWeight i

def classOf (i : Nat) := Fin.ofNat 48 (nodesClass i)

def sw (i : Nat) (q : Fin 12) (b : Bool) : Nat :=
  (((next (classOf i) q b).map (fun j => weight[j.val]!)).getD 1)

def homogeneous (m : Nat) : Bool :=
  let k := lab[m.log2]!
  m &&& tagMask k == m

def present (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tagMask k != 0 then n+1 else n) 0

def apart (a b : Nat) := a ^^^ (a &&& b)

def baseScore (s a b raw : Nat) : Nat :=
  if homogeneous (s &&& a) && homogeneous (s &&& b) then raw else
  min (present s) (min (1 + present (apart s a))
    (min (1 + present (apart s b)) (2 + present (apart (apart s a) b))))

def fits (rotated a b : Nat) : Bool :=
  homogeneous rotated || rotated &&& a == rotated || rotated &&& b == rotated

def dirMask (q : Fin 12) (b : Bool) : Nat := if b then cols[q.val]! else (2^60-1) ^^^ cols[q.val]!

def sideScore (i : Nat) (q : Fin 12) (b : Bool) : Nat :=
  let s := mask i &&& dirMask q b
  match pickRef i (2*q.val+b.toNat) with
  | none => max 1 (baseScore s (one i) (two i) (sw i q b))
  | some h =>
    let j := h%4096
    let o := h/4096
    if j < 2919 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i)) (one j) (two j) &&
       fits (permute o (s &&& two i)) (one j) (two j)
    then wt j else 0

def nodeOK (i : Nat) : Bool :=
  let s := mask i
  !homogeneous s && s &&& one i != s && s &&& two i != s &&
    (List.range 12).all (fun v => decide (wt i ≤ sideScore i (Fin.ofNat 12 v) false + sideScore i (Fin.ofNat 12 v) true))

def panel (beginAt count : Nat) : Bool :=
  (List.range count).all (fun j => nodeOK (beginAt+j))

theorem joinPanel (lo n m : Nat) (a : panel lo n = true) (b : panel (lo+n) m = true) :
    panel lo (n+m) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have h := List.mem_range.mp hi
  by_cases small : i<n
  · exact List.all_eq_true.mp a i (List.mem_range.mpr small)
  · have ok := List.all_eq_true.mp b (i-n) (List.mem_range.mpr (by omega))
    have eq : lo+n+(i-n) = lo+i := by omega
    simpa only [eq] using ok

private theorem done0_16 : panel 0 16 = true := by decide +kernel

private theorem done16_16 : panel 16 16 = true := by decide +kernel

private theorem done32_16 : panel 32 16 = true := by decide +kernel

private theorem done48_16 : panel 48 16 = true := by decide +kernel

private theorem done64_16 : panel 64 16 = true := by decide +kernel

private theorem done80_16 : panel 80 16 = true := by decide +kernel

private theorem done96_16 : panel 96 16 = true := by decide +kernel

private theorem done112_16 : panel 112 16 = true := by decide +kernel

private theorem done128_16 : panel 128 16 = true := by decide +kernel

private theorem done144_16 : panel 144 16 = true := by decide +kernel

private theorem done160_16 : panel 160 16 = true := by decide +kernel

private theorem done176_16 : panel 176 16 = true := by decide +kernel

private theorem done192_16 : panel 192 16 = true := by decide +kernel

private theorem done208_16 : panel 208 16 = true := by decide +kernel

private theorem done224_16 : panel 224 16 = true := by decide +kernel

private theorem done240_16 : panel 240 16 = true := by decide +kernel

private theorem done256_16 : panel 256 16 = true := by decide +kernel

private theorem done272_16 : panel 272 16 = true := by decide +kernel

private theorem done288_16 : panel 288 16 = true := by decide +kernel

private theorem done304_16 : panel 304 16 = true := by decide +kernel

private theorem done320_16 : panel 320 16 = true := by decide +kernel

private theorem done336_16 : panel 336 16 = true := by decide +kernel

private theorem done352_16 : panel 352 16 = true := by decide +kernel

private theorem done368_16 : panel 368 16 = true := by decide +kernel

private theorem done384_16 : panel 384 16 = true := by decide +kernel

private theorem done400_16 : panel 400 16 = true := by decide +kernel

private theorem done416_16 : panel 416 16 = true := by decide +kernel

private theorem done432_16 : panel 432 16 = true := by decide +kernel

private theorem done448_16 : panel 448 16 = true := by decide +kernel

private theorem done464_16 : panel 464 16 = true := by decide +kernel

private theorem done480_16 : panel 480 16 = true := by decide +kernel

private theorem done496_16 : panel 496 16 = true := by decide +kernel

private theorem done512_16 : panel 512 16 = true := by decide +kernel

private theorem done528_16 : panel 528 16 = true := by decide +kernel

private theorem done544_16 : panel 544 16 = true := by decide +kernel

private theorem done560_16 : panel 560 16 = true := by decide +kernel

private theorem done576_16 : panel 576 16 = true := by decide +kernel

private theorem done592_16 : panel 592 16 = true := by decide +kernel

private theorem done608_16 : panel 608 16 = true := by decide +kernel

private theorem done624_16 : panel 624 16 = true := by decide +kernel

private theorem done640_16 : panel 640 16 = true := by decide +kernel

private theorem done656_16 : panel 656 16 = true := by decide +kernel

private theorem done672_16 : panel 672 16 = true := by decide +kernel

private theorem done688_16 : panel 688 16 = true := by decide +kernel

private theorem done704_16 : panel 704 16 = true := by decide +kernel

private theorem done720_16 : panel 720 16 = true := by decide +kernel

private theorem done736_16 : panel 736 16 = true := by decide +kernel

private theorem done752_16 : panel 752 16 = true := by decide +kernel

private theorem done768_16 : panel 768 16 = true := by decide +kernel

private theorem done784_16 : panel 784 16 = true := by decide +kernel

private theorem done800_16 : panel 800 16 = true := by decide +kernel

private theorem done816_16 : panel 816 16 = true := by decide +kernel

private theorem done832_16 : panel 832 16 = true := by decide +kernel

private theorem done848_16 : panel 848 16 = true := by decide +kernel

private theorem done864_16 : panel 864 16 = true := by decide +kernel

private theorem done880_16 : panel 880 16 = true := by decide +kernel

private theorem done896_16 : panel 896 16 = true := by decide +kernel

private theorem done912_16 : panel 912 16 = true := by decide +kernel

private theorem done928_16 : panel 928 16 = true := by decide +kernel

private theorem done944_16 : panel 944 16 = true := by decide +kernel

private theorem done960_16 : panel 960 16 = true := by decide +kernel

private theorem done976_16 : panel 976 16 = true := by decide +kernel

private theorem done992_16 : panel 992 16 = true := by decide +kernel

private theorem done1008_16 : panel 1008 16 = true := by decide +kernel

private theorem done1024_16 : panel 1024 16 = true := by decide +kernel

private theorem done1040_16 : panel 1040 16 = true := by decide +kernel

private theorem done1056_16 : panel 1056 16 = true := by decide +kernel

private theorem done1072_16 : panel 1072 16 = true := by decide +kernel

private theorem done1088_16 : panel 1088 16 = true := by decide +kernel

private theorem done1104_16 : panel 1104 16 = true := by decide +kernel

private theorem done1120_16 : panel 1120 16 = true := by decide +kernel

private theorem done1136_16 : panel 1136 16 = true := by decide +kernel

private theorem done1152_16 : panel 1152 16 = true := by decide +kernel

private theorem done1168_16 : panel 1168 16 = true := by decide +kernel

private theorem done1184_16 : panel 1184 16 = true := by decide +kernel

private theorem done1200_16 : panel 1200 16 = true := by decide +kernel

private theorem done1216_16 : panel 1216 16 = true := by decide +kernel

private theorem done1232_16 : panel 1232 16 = true := by decide +kernel

private theorem done1248_16 : panel 1248 16 = true := by decide +kernel

private theorem done1264_16 : panel 1264 16 = true := by decide +kernel

private theorem done1280_16 : panel 1280 16 = true := by decide +kernel

private theorem done1296_16 : panel 1296 16 = true := by decide +kernel

private theorem done1312_16 : panel 1312 16 = true := by decide +kernel

private theorem done1328_16 : panel 1328 16 = true := by decide +kernel

private theorem done1344_16 : panel 1344 16 = true := by decide +kernel

private theorem done1360_16 : panel 1360 16 = true := by decide +kernel

private theorem done1376_16 : panel 1376 16 = true := by decide +kernel

private theorem done1392_16 : panel 1392 16 = true := by decide +kernel

private theorem done1408_16 : panel 1408 16 = true := by decide +kernel

private theorem done1424_16 : panel 1424 16 = true := by decide +kernel

private theorem done1440_16 : panel 1440 16 = true := by decide +kernel

private theorem done1456_16 : panel 1456 16 = true := by decide +kernel

private theorem done1472_16 : panel 1472 16 = true := by decide +kernel

private theorem done1488_16 : panel 1488 16 = true := by decide +kernel

private theorem done1504_16 : panel 1504 16 = true := by decide +kernel

private theorem done1520_16 : panel 1520 16 = true := by decide +kernel

private theorem done1536_16 : panel 1536 16 = true := by decide +kernel

private theorem done1552_16 : panel 1552 16 = true := by decide +kernel

private theorem done1568_16 : panel 1568 16 = true := by decide +kernel

private theorem done1584_16 : panel 1584 16 = true := by decide +kernel

private theorem done1600_16 : panel 1600 16 = true := by decide +kernel

private theorem done1616_16 : panel 1616 16 = true := by decide +kernel

private theorem done1632_16 : panel 1632 16 = true := by decide +kernel

private theorem done1648_16 : panel 1648 16 = true := by decide +kernel

private theorem done1664_16 : panel 1664 16 = true := by decide +kernel

private theorem done1680_16 : panel 1680 16 = true := by decide +kernel

private theorem done1696_16 : panel 1696 16 = true := by decide +kernel

private theorem done1712_16 : panel 1712 16 = true := by decide +kernel

private theorem done1728_16 : panel 1728 16 = true := by decide +kernel

private theorem done1744_16 : panel 1744 16 = true := by decide +kernel

private theorem done1760_16 : panel 1760 16 = true := by decide +kernel

private theorem done1776_16 : panel 1776 16 = true := by decide +kernel

private theorem done1792_16 : panel 1792 16 = true := by decide +kernel

private theorem done1808_16 : panel 1808 16 = true := by decide +kernel

private theorem done1824_16 : panel 1824 16 = true := by decide +kernel

private theorem done1840_16 : panel 1840 16 = true := by decide +kernel

private theorem done1856_16 : panel 1856 16 = true := by decide +kernel

private theorem done1872_16 : panel 1872 16 = true := by decide +kernel

private theorem done1888_16 : panel 1888 16 = true := by decide +kernel

private theorem done1904_16 : panel 1904 16 = true := by decide +kernel

private theorem done1920_16 : panel 1920 16 = true := by decide +kernel

private theorem done1936_16 : panel 1936 16 = true := by decide +kernel

private theorem done1952_16 : panel 1952 16 = true := by decide +kernel

private theorem done1968_16 : panel 1968 16 = true := by decide +kernel

private theorem done1984_16 : panel 1984 16 = true := by decide +kernel

private theorem done2000_16 : panel 2000 16 = true := by decide +kernel

private theorem done2016_16 : panel 2016 16 = true := by decide +kernel

private theorem done2032_16 : panel 2032 16 = true := by decide +kernel

private theorem done2048_16 : panel 2048 16 = true := by decide +kernel

private theorem done2064_16 : panel 2064 16 = true := by decide +kernel

private theorem done2080_16 : panel 2080 16 = true := by decide +kernel

private theorem done2096_16 : panel 2096 16 = true := by decide +kernel

private theorem done2112_16 : panel 2112 16 = true := by decide +kernel

private theorem done2128_16 : panel 2128 16 = true := by decide +kernel

private theorem done2144_16 : panel 2144 16 = true := by decide +kernel

private theorem done2160_16 : panel 2160 16 = true := by decide +kernel

private theorem done2176_16 : panel 2176 16 = true := by decide +kernel

private theorem done2192_16 : panel 2192 16 = true := by decide +kernel

private theorem done2208_16 : panel 2208 16 = true := by decide +kernel

private theorem done2224_16 : panel 2224 16 = true := by decide +kernel

private theorem done2240_16 : panel 2240 16 = true := by decide +kernel

private theorem done2256_16 : panel 2256 16 = true := by decide +kernel

private theorem done2272_16 : panel 2272 16 = true := by decide +kernel

private theorem done2288_16 : panel 2288 16 = true := by decide +kernel

private theorem done2304_16 : panel 2304 16 = true := by decide +kernel

private theorem done2320_16 : panel 2320 16 = true := by decide +kernel

private theorem done2336_16 : panel 2336 16 = true := by decide +kernel

private theorem done2352_16 : panel 2352 16 = true := by decide +kernel

private theorem done2368_16 : panel 2368 16 = true := by decide +kernel

private theorem done2384_16 : panel 2384 16 = true := by decide +kernel

private theorem done2400_16 : panel 2400 16 = true := by decide +kernel

private theorem done2416_16 : panel 2416 16 = true := by decide +kernel

private theorem done2432_16 : panel 2432 16 = true := by decide +kernel

private theorem done2448_16 : panel 2448 16 = true := by decide +kernel

private theorem done2464_16 : panel 2464 16 = true := by decide +kernel

private theorem done2480_16 : panel 2480 16 = true := by decide +kernel

private theorem done2496_16 : panel 2496 16 = true := by decide +kernel

private theorem done2512_16 : panel 2512 16 = true := by decide +kernel

private theorem done2528_16 : panel 2528 16 = true := by decide +kernel

private theorem done2544_16 : panel 2544 16 = true := by decide +kernel

private theorem done2560_16 : panel 2560 16 = true := by decide +kernel

private theorem done2576_16 : panel 2576 16 = true := by decide +kernel

private theorem done2592_16 : panel 2592 16 = true := by decide +kernel

private theorem done2608_16 : panel 2608 16 = true := by decide +kernel

private theorem done2624_16 : panel 2624 16 = true := by decide +kernel

private theorem done2640_16 : panel 2640 16 = true := by decide +kernel

private theorem done2656_16 : panel 2656 16 = true := by decide +kernel

private theorem done2672_16 : panel 2672 16 = true := by decide +kernel

private theorem done2688_16 : panel 2688 16 = true := by decide +kernel

private theorem done2704_16 : panel 2704 16 = true := by decide +kernel

private theorem done2720_16 : panel 2720 16 = true := by decide +kernel

private theorem done2736_16 : panel 2736 16 = true := by decide +kernel

private theorem done2752_16 : panel 2752 16 = true := by decide +kernel

private theorem done2768_16 : panel 2768 16 = true := by decide +kernel

private theorem done2784_16 : panel 2784 16 = true := by decide +kernel

private theorem done2800_16 : panel 2800 16 = true := by decide +kernel

private theorem done2816_16 : panel 2816 16 = true := by decide +kernel

private theorem done2832_16 : panel 2832 16 = true := by decide +kernel

private theorem done2848_16 : panel 2848 16 = true := by decide +kernel

private theorem done2864_16 : panel 2864 16 = true := by decide +kernel

private theorem done2880_16 : panel 2880 16 = true := by decide +kernel

private theorem done2896_16 : panel 2896 16 = true := by decide +kernel

private theorem done2912_7 : panel 2912 7 = true := by decide +kernel

theorem certifiedBlock : panel 0 2919 = true := (joinPanel 0 2048 871 (joinPanel 0 1024 1024 (joinPanel 0 512 512 (joinPanel 0 256 256 (joinPanel 0 128 128 (joinPanel 0 64 64 (joinPanel 0 32 32 (joinPanel 0 16 16 done0_16 done16_16) (joinPanel 32 16 16 done32_16 done48_16)) (joinPanel 64 32 32 (joinPanel 64 16 16 done64_16 done80_16) (joinPanel 96 16 16 done96_16 done112_16))) (joinPanel 128 64 64 (joinPanel 128 32 32 (joinPanel 128 16 16 done128_16 done144_16) (joinPanel 160 16 16 done160_16 done176_16)) (joinPanel 192 32 32 (joinPanel 192 16 16 done192_16 done208_16) (joinPanel 224 16 16 done224_16 done240_16)))) (joinPanel 256 128 128 (joinPanel 256 64 64 (joinPanel 256 32 32 (joinPanel 256 16 16 done256_16 done272_16) (joinPanel 288 16 16 done288_16 done304_16)) (joinPanel 320 32 32 (joinPanel 320 16 16 done320_16 done336_16) (joinPanel 352 16 16 done352_16 done368_16))) (joinPanel 384 64 64 (joinPanel 384 32 32 (joinPanel 384 16 16 done384_16 done400_16) (joinPanel 416 16 16 done416_16 done432_16)) (joinPanel 448 32 32 (joinPanel 448 16 16 done448_16 done464_16) (joinPanel 480 16 16 done480_16 done496_16))))) (joinPanel 512 256 256 (joinPanel 512 128 128 (joinPanel 512 64 64 (joinPanel 512 32 32 (joinPanel 512 16 16 done512_16 done528_16) (joinPanel 544 16 16 done544_16 done560_16)) (joinPanel 576 32 32 (joinPanel 576 16 16 done576_16 done592_16) (joinPanel 608 16 16 done608_16 done624_16))) (joinPanel 640 64 64 (joinPanel 640 32 32 (joinPanel 640 16 16 done640_16 done656_16) (joinPanel 672 16 16 done672_16 done688_16)) (joinPanel 704 32 32 (joinPanel 704 16 16 done704_16 done720_16) (joinPanel 736 16 16 done736_16 done752_16)))) (joinPanel 768 128 128 (joinPanel 768 64 64 (joinPanel 768 32 32 (joinPanel 768 16 16 done768_16 done784_16) (joinPanel 800 16 16 done800_16 done816_16)) (joinPanel 832 32 32 (joinPanel 832 16 16 done832_16 done848_16) (joinPanel 864 16 16 done864_16 done880_16))) (joinPanel 896 64 64 (joinPanel 896 32 32 (joinPanel 896 16 16 done896_16 done912_16) (joinPanel 928 16 16 done928_16 done944_16)) (joinPanel 960 32 32 (joinPanel 960 16 16 done960_16 done976_16) (joinPanel 992 16 16 done992_16 done1008_16)))))) (joinPanel 1024 512 512 (joinPanel 1024 256 256 (joinPanel 1024 128 128 (joinPanel 1024 64 64 (joinPanel 1024 32 32 (joinPanel 1024 16 16 done1024_16 done1040_16) (joinPanel 1056 16 16 done1056_16 done1072_16)) (joinPanel 1088 32 32 (joinPanel 1088 16 16 done1088_16 done1104_16) (joinPanel 1120 16 16 done1120_16 done1136_16))) (joinPanel 1152 64 64 (joinPanel 1152 32 32 (joinPanel 1152 16 16 done1152_16 done1168_16) (joinPanel 1184 16 16 done1184_16 done1200_16)) (joinPanel 1216 32 32 (joinPanel 1216 16 16 done1216_16 done1232_16) (joinPanel 1248 16 16 done1248_16 done1264_16)))) (joinPanel 1280 128 128 (joinPanel 1280 64 64 (joinPanel 1280 32 32 (joinPanel 1280 16 16 done1280_16 done1296_16) (joinPanel 1312 16 16 done1312_16 done1328_16)) (joinPanel 1344 32 32 (joinPanel 1344 16 16 done1344_16 done1360_16) (joinPanel 1376 16 16 done1376_16 done1392_16))) (joinPanel 1408 64 64 (joinPanel 1408 32 32 (joinPanel 1408 16 16 done1408_16 done1424_16) (joinPanel 1440 16 16 done1440_16 done1456_16)) (joinPanel 1472 32 32 (joinPanel 1472 16 16 done1472_16 done1488_16) (joinPanel 1504 16 16 done1504_16 done1520_16))))) (joinPanel 1536 256 256 (joinPanel 1536 128 128 (joinPanel 1536 64 64 (joinPanel 1536 32 32 (joinPanel 1536 16 16 done1536_16 done1552_16) (joinPanel 1568 16 16 done1568_16 done1584_16)) (joinPanel 1600 32 32 (joinPanel 1600 16 16 done1600_16 done1616_16) (joinPanel 1632 16 16 done1632_16 done1648_16))) (joinPanel 1664 64 64 (joinPanel 1664 32 32 (joinPanel 1664 16 16 done1664_16 done1680_16) (joinPanel 1696 16 16 done1696_16 done1712_16)) (joinPanel 1728 32 32 (joinPanel 1728 16 16 done1728_16 done1744_16) (joinPanel 1760 16 16 done1760_16 done1776_16)))) (joinPanel 1792 128 128 (joinPanel 1792 64 64 (joinPanel 1792 32 32 (joinPanel 1792 16 16 done1792_16 done1808_16) (joinPanel 1824 16 16 done1824_16 done1840_16)) (joinPanel 1856 32 32 (joinPanel 1856 16 16 done1856_16 done1872_16) (joinPanel 1888 16 16 done1888_16 done1904_16))) (joinPanel 1920 64 64 (joinPanel 1920 32 32 (joinPanel 1920 16 16 done1920_16 done1936_16) (joinPanel 1952 16 16 done1952_16 done1968_16)) (joinPanel 1984 32 32 (joinPanel 1984 16 16 done1984_16 done2000_16) (joinPanel 2016 16 16 done2016_16 done2032_16))))))) (joinPanel 2048 512 359 (joinPanel 2048 256 256 (joinPanel 2048 128 128 (joinPanel 2048 64 64 (joinPanel 2048 32 32 (joinPanel 2048 16 16 done2048_16 done2064_16) (joinPanel 2080 16 16 done2080_16 done2096_16)) (joinPanel 2112 32 32 (joinPanel 2112 16 16 done2112_16 done2128_16) (joinPanel 2144 16 16 done2144_16 done2160_16))) (joinPanel 2176 64 64 (joinPanel 2176 32 32 (joinPanel 2176 16 16 done2176_16 done2192_16) (joinPanel 2208 16 16 done2208_16 done2224_16)) (joinPanel 2240 32 32 (joinPanel 2240 16 16 done2240_16 done2256_16) (joinPanel 2272 16 16 done2272_16 done2288_16)))) (joinPanel 2304 128 128 (joinPanel 2304 64 64 (joinPanel 2304 32 32 (joinPanel 2304 16 16 done2304_16 done2320_16) (joinPanel 2336 16 16 done2336_16 done2352_16)) (joinPanel 2368 32 32 (joinPanel 2368 16 16 done2368_16 done2384_16) (joinPanel 2400 16 16 done2400_16 done2416_16))) (joinPanel 2432 64 64 (joinPanel 2432 32 32 (joinPanel 2432 16 16 done2432_16 done2448_16) (joinPanel 2464 16 16 done2464_16 done2480_16)) (joinPanel 2496 32 32 (joinPanel 2496 16 16 done2496_16 done2512_16) (joinPanel 2528 16 16 done2528_16 done2544_16))))) (joinPanel 2560 256 103 (joinPanel 2560 128 128 (joinPanel 2560 64 64 (joinPanel 2560 32 32 (joinPanel 2560 16 16 done2560_16 done2576_16) (joinPanel 2592 16 16 done2592_16 done2608_16)) (joinPanel 2624 32 32 (joinPanel 2624 16 16 done2624_16 done2640_16) (joinPanel 2656 16 16 done2656_16 done2672_16))) (joinPanel 2688 64 64 (joinPanel 2688 32 32 (joinPanel 2688 16 16 done2688_16 done2704_16) (joinPanel 2720 16 16 done2720_16 done2736_16)) (joinPanel 2752 32 32 (joinPanel 2752 16 16 done2752_16 done2768_16) (joinPanel 2784 16 16 done2784_16 done2800_16)))) (joinPanel 2816 64 39 (joinPanel 2816 32 32 (joinPanel 2816 16 16 done2816_16 done2832_16) (joinPanel 2848 16 16 done2848_16 done2864_16)) (joinPanel 2880 32 7 (joinPanel 2880 16 16 done2880_16 done2896_16) done2912_7)))))

end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open PCX150.SmallChart PCX150.Bands
open PCX150.Sparse (TestTree Triple Valid box leaves)
namespace Local
theorem labSame (r : Sample) : geo.tag r = Scoring.label r := rfl

theorem labelSame : geo.tag = Scoring.label := funext labSame

theorem tagSame : ∀ k : Fin 22, tagMask k.val = Scoring.tags[k.val]! := by decide +kernel

theorem numSame (m : Nat) : present m = Scoring.present m := by
  have go (xs : List Nat) (n : Nat) (sub : ∀ i ∈ xs,i<22) :
    xs.foldl (fun v k => if m &&& tagMask k != 0 then v+1 else v) n =
    xs.foldl (fun v k => if m &&& Scoring.tags[k]! != 0 then v+1 else v) n := by
    induction xs generalizing n with
    | nil => rfl
    | cons k xs ih =>
      simp only [List.foldl_cons]
      rw [show tagMask k = Scoring.tags[k]! from tagSame ⟨k,sub k (by simp)⟩]
      exact ih _ (fun i h => sub i (by simp [h]))
  exact go (List.range 22) 0 (fun _ h => List.mem_range.mp h)

theorem subsetIf {s u : Nat} (h : s &&& u = s) : bits s ⊆ bits u := by
  intro p hp
  have e := congrArg (fun m : Nat => m.testBit p.val) h
  change s.testBit p.val = true at hp
  change u.testBit p.val = true
  simpa [Nat.testBit_and,hp] using e

theorem useAnd (s t : Nat) (r : Sample) :
    r ∈ bits (s &&& t) ↔ r ∈ bits s ∧ r ∈ bits t := by
  change (s &&& t).testBit r.val = true ↔ _
  rw [Nat.testBit_and,Bool.and_eq_true]
  rfl

theorem subsetBack {s a : Nat} (range : s < 2^60) (h : bits s ⊆ bits a) : s &&& a = s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases sm : i<60
  · cases v : s.testBit i
    · simp
    · have w : a.testBit i = true := h (show (⟨i,sm⟩ : Sample) ∈ bits s from v)
      simp [w]
  · have hn : 60 ≤ i := Nat.le_of_not_gt sm
    have small := Nat.testBit_lt_two_pow (lt_of_lt_of_le range (Nat.pow_le_pow_right (by decide : 0 < 2) hn))
    simp [small]

theorem rangeGen (g : G) (m : Nat) : quickGen g.val m < 2^60 := by
  rw [genAsRoll]
  have bs : ∀ (i : G), ∀ p ∈ parts i, p.destination < 2^60 := by decide +kernel
  have eachPart (xs : List Part) (h : ∀ p ∈ xs,p.destination<2^60) : roll xs m < 2^60 := by
    induction xs with
    | nil => decide
    | cons p ps ih =>
      apply Nat.or_lt_two_pow
      · exact lt_of_le_of_lt (Nat.and_le_left (x := p.destination)) (h _ (by simp))
      · exact ih (fun y hy => h _ (by simp [hy]))
  exact eachPart _ (bs g)

theorem rangePerm (o : ID) (s : Nat) (range : s<2^60) : permute o.val s < 2^60 := by
  have go (w d : Nat) (ok : ∀ k<d, (w >>> (3*k))%8≤5) : useWord w d s<2^60 := by
    induction d with
    | zero => exact range
    | succ d ih =>
      simp only [useWord]
      split
      · exact ih (fun k h => ok k (by omega))
      · rename_i h
        let t := ((w >>> (3*d))%8)-1
        have lim := ok d (by omega)
        have small : t<5 := by dsimp [t]; omega
        have z := rangeGen (⟨t,small⟩ : G) (useWord w d s)
        exact z
  exact go _ _ (fun k h => digits o ⟨k,h⟩)

theorem homTag {m : Nat} (range : m<2^60) (h : homogeneous m = true) : plain geo (bits m) := by
  have lo : m.log2 < 60 := by
    by_cases z : m=0
    · simp [z]
    · exact (Nat.log2_lt z).mpr range
  have small : ∀ r : Sample, lab[r.val]! < 22 := by decide +kernel
  let k : Tag := ⟨lab[m.log2]!,small ⟨m.log2,lo⟩⟩
  have sub : bits m ⊆ bits (tagMask k.val) := subsetIf (eq_of_beq h)
  refine ⟨k,?_⟩
  intro p hp
  have be := sub hp
  change (tagMask k.val).testBit p.val = true at be
  rw [tagSame k,Scoring.tagBits] at be
  exact of_decide_eq_true be

theorem admits {m a b : Nat} (range : m<2^60) (h : fits m a b = true) :
    ∃ j, bits m ⊆ box geo.tag (bits a) (bits b) j := by
  unfold fits at h
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  rcases h with (hom | sub) | sub
  · obtain ⟨i,hi⟩ := homTag range hom
    exact ⟨Sum.inl i,fun p hp => hi p hp⟩
  · exact ⟨Sum.inr 0,by simpa [box] using subsetIf sub⟩
  · exact ⟨Sum.inr 1,by simpa [box] using subsetIf sub⟩

def triple (s a b : Nat) : Triple := ⟨bits s,bits a,bits b⟩

theorem embedded {s a b m u v : Nat} (o : ID) (range : s < 2^60)
    (eq : permute o.val s = m)
    (f : fits (permute o.val (s &&& a)) u v = true)
    (g : fits (permute o.val (s &&& b)) u v = true) :
    Nonempty (Sparse.Embed geo (triple m u v) (triple s a b)) := by
  have eqSet : bits m = acted (orient o) (bits s) := by rw [←eq,actionSet]
  obtain ⟨i,hi⟩ := admits (rangePerm o _ (lt_of_le_of_lt Nat.and_le_left range)) f
  obtain ⟨j,hj⟩ := admits (rangePerm o _ (lt_of_le_of_lt Nat.and_le_left range)) g
  refine ⟨⟨orient o,eqSet.subset,?_⟩⟩
  intro k
  cases k with
  | inl l =>
    refine ⟨Sum.inl ((orient o).a l),?_⟩
    intro p _ h
    have z := (orient o).label ((orient o).s.symm p)
    change geo.tag ((orient o).s.symm p) = l at h
    change geo.tag p = (orient o).a l
    simpa [h] using z
  | inr k =>
    fin_cases k
    · refine ⟨i,?_⟩
      intro p hp h
      apply hi
      rw [actionSet]
      apply (useAnd _ _ _).2
      exact ⟨eqSet.subset hp,by simpa [box,triple] using h⟩
    · refine ⟨j,?_⟩
      intro p hp h
      apply hj
      rw [actionSet]
      apply (useAnd _ _ _).2
      exact ⟨eqSet.subset hp,by simpa [box,triple] using h⟩

end Local
end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open PCX150.SmallChart PCX150.Bands
open PCX150.Sparse (TestTree Triple Valid box leaves)
namespace Local
def treeRaw : TestTree → SmallChart.Tree
  | .leaf => .leaf
  | .cut q l r => .node q (treeRaw l) (treeRaw r)

theorem rawLeaves (t : TestTree) : SmallChart.leaves (treeRaw t) = Sparse.leaves t := by
  induction t with
  | leaf => rfl
  | cut q t u ht hu => simp [treeRaw,SmallChart.leaves,Sparse.leaves,ht,hu]

theorem positive (t : TestTree) : 1 ≤ Sparse.leaves t := by
  rw [←rawLeaves]
  exact SmallChart.leafPos _

theorem rawIf (s : Set Sample) (term : Sparse.Box → Set Sample) (t : TestTree)
    (v : Valid geo.val term t s) (plainHere : ∀ i, ∃ j, ∀ p ∈ s, p ∈ term i → geo.tag p=j) :
    SmallChart.rawValid geo (treeRaw t) s := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := v
    obtain ⟨j,hj⟩ := plainHere i
    exact ⟨j,fun p hp => hj p hp (hi hp)⟩
  | cut q l r hl hr =>
    exact ⟨hl _ v.1 (fun i => (plainHere i).imp (fun j hj p hp => hj p hp.1)),
      hr _ v.2 (fun i => (plainHere i).imp (fun j hj p hp => hj p hp.1))⟩

theorem rawAfter (s a b : Nat) (range : s < 2^60) (t : TestTree)
    (v : Sparse.admissible geo (triple s a b) t)
    (ha : homogeneous (s &&& a) = true) (hb : homogeneous (s &&& b) = true) :
    SmallChart.rawValid geo (treeRaw t) (bits s) := by
  apply rawIf (bits s) (box geo.tag (bits a) (bits b)) t v
  intro h
  cases h with
  | inl i => exact ⟨i,fun _ _ z => z⟩
  | inr i =>
    fin_cases i
    · obtain ⟨j,hj⟩ := homTag (lt_of_le_of_lt Nat.and_le_left range) ha
      exact ⟨j,fun r hr z => hj r ((useAnd _ _ _).2 ⟨hr,by simpa [box] using z⟩)⟩
    · obtain ⟨j,hj⟩ := homTag (lt_of_le_of_lt Nat.and_le_left range) hb
      exact ⟨j,fun r hr z => hj r ((useAnd _ _ _).2 ⟨hr,by simpa [box] using z⟩)⟩

theorem scorePaid (s a b raw : Nat) (range : s<2^60) (t : TestTree)
    (v : Sparse.admissible geo (triple s a b) t)
    (paid : SmallChart.rawValid geo (treeRaw t) (bits s) → raw ≤ Sparse.leaves t) :
    max 1 (baseScore s a b raw) ≤ Sparse.leaves t := by
  apply max_le (positive t)
  unfold baseScore
  split
  · rename_i h
    have u := Bool.and_eq_true_iff.mp h
    exact paid (rawAfter s a b range t v u.1 u.2)
  · have vs : Valid geo.val (box Scoring.label (Scoring.bitset a) (Scoring.bitset b)) t (Scoring.bitset s) := by
      have bset (x : Nat) : bits x = Scoring.bitset x := rfl
      simpa only [Sparse.admissible,triple,labelSame,bset] using v
    have h := Scoring.numericalLeafCover geo.val s a b t vs
    have sameApart (x y : Nat) : apart x y = Scoring.apart x y := rfl
    simpa only [numSame,sameApart,Scoring.basic] using h

abbrev NodeID := Fin 2919

theorem rankOK : ∀ i : NodeID, nodes i.val % 64 < 48 := by decide +kernel

theorem maskEq (i : NodeID) : Chart48.node (classOf i.val) = bits (mask i.val) := by
  change bits (rm[(nodes i.val %64)%48]!) = bits (rm[nodes i.val%64]!)
  rw [Nat.mod_eq_of_lt (rankOK i)]

theorem maskRange (i : NodeID) : mask i.val < 2^60 := by
  have h : ∀ k : Key, rm[k.val]! < 2^60 := by decide +kernel
  exact h ⟨_,rankOK i⟩

theorem dirBit : ∀ q b (r : Sample), (dirMask q b).testBit r.val = decide (geo.val r q = b) := by decide +kernel

theorem branchBits (s : Nat) (q : Var) (b : Bool) :
    SmallChart.branch geo (bits s) q b = bits (s &&& dirMask q b) := by
  ext r
  rw [useAnd]
  change (_ ∧ geo.val r q=b) ↔ (_ ∧ (dirMask q b).testBit r.val=true)
  rw [dirBit,decide_eq_true_eq]

theorem rawHalf (i : NodeID) (q : Var) (b : Bool) (t : TestTree)
    (v : SmallChart.rawValid geo (treeRaw t) (bits (mask i.val &&& dirMask q b))) :
    sw i.val q b ≤ Sparse.leaves t := by
  let k := classOf i.val
  have square := chart.proper k q b
  have eq : SmallChart.branch geo (chart.state k) q b = bits (mask i.val &&& dirMask q b) :=
    (congrArg (fun s => SmallChart.branch geo s q b) (maskEq i)).trans (branchBits _ _ _)
  rw [←eq] at v
  change (match Chart48.next k q b with | none => _ | some j => _) at square
  unfold sw
  change ((Chart48.next k q b).map _).getD 1 ≤ _
  cases track : Chart48.next k q b with
  | none => exact positive t
  | some j =>
    rw [track] at square
    obtain ⟨f,hf⟩ := square
    rw [hf] at v
    have w := SmallChart.rawLower chart (treeRaw t) j f v
    change Chart48.chart.wt j ≤ Sparse.leaves t
    simpa only [rawLeaves] using w

def item (i : NodeID) := triple (mask i.val) (one i.val) (two i.val)

theorem noLeaf (i : NodeID) (h : nodeOK i.val = true) :
    Sparse.admissible geo (item i) .leaf → wt i.val ≤ 1 := by
  intro v
  obtain ⟨u,hu⟩ := v
  unfold nodeOK at h
  simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne] at h
  cases u with
  | inl j =>
    exfalso
    apply chart.rich (classOf i.val)
    rw [show chart.state (classOf i.val) = bits (mask i.val) from maskEq i]
    exact ⟨j,fun p hp => hu hp⟩
  | inr j =>
    fin_cases j
    · exact False.elim (h.1.1.2 (subsetBack (maskRange i) (by simpa [box,item,triple] using hu)))
    · exact False.elim (h.1.2 (subsetBack (maskRange i) (by simpa [box,item,triple] using hu)))

theorem pivotPay (i : NodeID) (q : Var) (h : nodeOK i.val = true) :
    wt i.val ≤ sideScore i.val q false + sideScore i.val q true := by
  have all := (Bool.and_eq_true_iff.mp h).2
  have pick := List.all_eq_true.mp all q.val (List.mem_range.mpr q.isLt)
  have eq : Fin.ofNat 12 q.val = q := Fin.ext (Nat.mod_eq_of_lt q.isLt)
  simpa only [eq,decide_eq_true_eq] using pick

theorem childPay (i : NodeID) (q : Var) (b : Bool) :
    let s := Sparse.restricted geo (item i) q b
    (∀ t, Sparse.admissible geo s t → sideScore i.val q b ≤ Sparse.leaves t) ∨
    ∃ j : NodeID, Nonempty (Sparse.Embed geo (item j) s) ∧ sideScore i.val q b ≤ wt j.val := by
  dsimp only
  let s := mask i.val &&& dirMask q b
  have r : s<2^60 := lt_of_le_of_lt Nat.and_le_left (maskRange i)
  have eq : Sparse.restricted geo (item i) q b = triple s (one i.val) (two i.val) := by
    change Sparse.Triple.mk (SmallChart.branch geo (bits (mask i.val)) q b) _ _ = _
    rw [branchBits]; rfl
  rw [eq]
  cases h : pickRef i.val (2*q.val+b.toNat) with
  | none =>
    left
    intro t v
    simpa only [sideScore,h] using scorePaid _ _ _ _ r t v (rawHalf i q b t)
  | some w =>
    let j := w%4096
    let o := w/4096
    by_cases hg : (j < 2919 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i.val)) (one j) (two j) &&
       fits (permute o (s &&& two i.val)) (one j) (two j)) = true
    · have pack := hg
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at pack
      obtain ⟨⟨⟨⟨jt,ot⟩,same⟩,f⟩,g⟩ := pack
      right
      refine ⟨⟨j,jt⟩,embedded ⟨o,ot⟩ r same f g,?_⟩
      simp only [sideScore,h,if_pos hg,le_refl]
    · left
      intro t v
      simp only [sideScore,h,if_neg hg]
      exact Nat.zero_le _

theorem bankSound (checks : ∀ i : NodeID, nodeOK i.val = true) (i : NodeID) (t : TestTree)
    (valid : Sparse.admissible geo (item i) t) : wt i.val ≤ Sparse.leaves t := by
  let rule : Sparse.Rule geo NodeID :=
    {item := item, weight := fun i => wt i.val, base := fun i => noLeaf i (checks i),
     kw := fun i q b => sideScore i.val q b, fork := fun i q => pivotPay i q (checks i), child := childPay}
  exact Sparse.soundRules rule t i valid

end Local
end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart
def full : Nat := 2^60-1

def len : Nat := 7056

def big : Nat := 2^7056-1

def R (a : Nat) := if a=0 then 0 else rm[a-1]!

def weightR (a : Nat) := if a=0 then 0 else weight[a-1]!

private def testMaskCodes : Array Nat := #[0x7836828271763918217793299391398243994729479189128218972128373288,0x767641a25837267728678914411a8284423a2873479597251982931628767137,0x733aa731aaab67951984baaa2872531a6791a11158763488a3161288a2266729,0x14889595aabaabaa28a267494a19767397455677a265845878631958586733a8,0x54a5a742a655772833aaa2a68954a382a56276676599282a428a848458739549,0x8896aa328379a5641a6522aaaa11988679394a3a877699728397a55347872898,0x89194aa447973a6a479887735a2a9837987617784999939879a173a8771a8a71,0x87829829989182899991288788379177783878392977938947794a6a87187187,0x9a7147a72a78a287982a47a89a37839aa917938a8a9293a728a8499aa7377918,0x883a917a793a7a383a8739a7297a2a7928a9478a277a27a7a19772a8728aa919,0x8a7688a6a89688a277a687a2a278a8867a862a97289a8a72a782983a288a8a37,0xa1a87aa2aa55977587958a7592aaa73a1a4a3a7a987319899aa691aa9a1a791a,0x8a934aa8777348aa87583aa988589a5783aa5a5a2a8aaa17a3a8aa92587955aa,0x8aa172aaaa19a2a98489aa7149aa2aa9aa2858782aa85aa57488a2a76a5a6779,0x68999a74a6a49aa2a37a6a6a79734a7a4a8aa9a627aaa71aa3a7a19a7967a18a,0x16aa8478aa399597a82a19873aa79589a93a38aa15aa8a3a999529aa9a3a7a2a,0xa27a81aa7697aa725897aa812a9aaa3895986999a46a3a9a19985a4a588737aa,0x8884a5a4a8a27aa1a81aa4a359776aa3679873aaaa278784a7a2a1a9a29a8487,0x8a949a4788a49a58a5899a759a7398a3979178379399717778767a1aaa968a2a,0x774a677a8a5757a7a4895a87967aa7845a78885aa86985a97a587a93a893984a,0x6a97796aa4788a747a6874a8886a849aa5971a87a78568a918a87a958a599a84,0xa91871a7717a78a69a2928a7a83786a7a88487a4a5986a9888a3776a84a7a767,0x1a7aa9a39aa31aa9a8767a76a17782a8828aa7919a9197a1783aa399939a93a9,0xa6a9aa48aa93aa836aa89a5aaa945a9a5a8aa8a49aa45aa9aa758aa55aa869aa,0xa75a7a5a7a4a68aa6a7a6a8a75aaa47aaa57aa4757aaa94a6aa7a85aa84a86aa,0xaa85a8a5a4a794aa1a9a18aa7aa5a9a5a6a81aa759aa8a6aa68a8a4aaa59aa69,0xa7a4a57aa96a85aa7aa496aaa69aaa74aa68a49a74aa9a6a17aaa58aa5a7a4a9,0x88788887889728aa2aa7a2a89878a9587978a83a99789a2aa5a8a7a3a76a8aa3,0x7989788871aa8899888988798798788978997aa677788778aa29a72a88987999,0x4a9a4aa9877977798789778998798999aa18a91a8a1a97788797877787877979,0x999799879979988999899898988899779788978797a57798a39aa3a9977747aa,0xaa76a8a68979899779987987a28a897777977997778799983a8a789898979887,0x7aa3aa73a8a39a4aaaa13aaaaa3a4aaaaaa2a1aaa2aaaaa62aaaa3aaaa1aaa2a,0x6aa9a48aa4a895aaaa95a7a59aa51a8a1aa8aa49a74aa5a98aa4aa84aa58a9a4,0x9a7788a798a9897aa9787a6aa67aa6a776aaa86aa59a58aa5a7a5aa767aa6a9a,0xa999a989a97789a7a777797a888aa899a879a8788a9887a88a787a7878a988a8,0x79a899a889a98a99977a879a899a878a7a997a79777aa788a779a7898a778a87,0x78a8a887989a9a9798a7999a998aa8979a799a89887a97a7978a97a899a9a998,0x9a88a987a79787a9987a798a7a9777a779a77a8777a9a888a7987a88789a788a,0x8a79877a7a898a97a97987a779a9889aa88988a9a778997a9a78779a9a988a89,0xaa4a6aaaaaa4aaa35aaa778aa997a787a898799a7a98988a9a8799a798a877a8,0xa9a88a8aaa997a7aaa7789aaa87a8aa89aa9aa6aa5aaa6aaa4aaaaa51aaaaa5a,0x8aa7a97aa9a988aaa8a9aa789a7aa79aa98aa7a97aa7a8a7aa8878aa9a9a97aa,0xa8a8a7a87aa89a8a98aa9aa799aa9aa88a9a8a7aaa79aa898aa9a77a87aa7aa9,0xaa7a8aaaaaa9a78a7a9a7a8a77aaaa97aa87a99aa9a7a7a779aaa89aa88aaa98,0xaaaaaa9aaa8aa7aa7aaaaaa7a9aaa8aaaaa89aaa]
def testMask (i : Nat) : Nat := cubeValue ((testMaskCodes[i/16]! >>> (16*(i%16))) % 65536)

private def staticFlagsB0 : Array Nat := #[544777605266688,457456971942092,557533999661056,559252338966528,422229644935168,427436456411136,368202968708352,544165919735808,380435318177792,547561085600256,422212465065984,422212465065984,281492156579840,544786009833488,383321888587776,548729316704768,427436219039744,422229644935168,299084342624256,557566757175312,383594252439842,548762074228736,559557198741536,475040567003272,545362330779648,422212465065984,548729316704256,422229644935168,378236563357696,422212465065984,531169888185344,457448380958924]

private def staticFlagsB1 : Array Nat := #[366002066395426,541965013237792,281492156579840,539974571671568,457439792595136,422212465065984,544777586655248,427436386942976,281492293071872,422229644935168,557529704693760,559247960047616,299067162755072,474989023199744,383317593620480,548725021737472,368821385082112,381603549282304,281492160774340,383321888587776,544784403415040,548729316704768,281492156579840,286698968055808,423311976693760,423311976693760,427435145297920,422229649129472]

private def staticFlagsTable : Array (Array Nat) := #[staticFlagsB0,staticFlagsB1]

def staticFlags (i : Nat) : Nat := (staticFlagsTable[i/32]!)[i%32]!


private def oveField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def oveClassData : Array Nat := #[0x50db6d54e361969646b014e130900c0188c2dcedb84bc5f6bb5aabd4e9f6cb152a8f46a1482a,0x48921c8520c811fc7cac2a4a5a869da6a9924a0781c02804002ccaa2729b2629719a5029ca127094504d,0x2a0a729aa4a8ca2a829fa7c9ea60972569524e910120400a002b0a428ea126896247254932448f23504c,0x50941cdc0781a05d314bd2548d193f02d455133e4f53c4ec002fcbeaf4bcaf0bbaecbaae6b82dab5d033,0x4ed3a4e537cd521c7f1dc5b114410f06e1b0601384a11844004931b4671543819056148500e83957d00f,0x52ef7ba20882006818058100380c02806010020053f4f4ff34ccd314a3264600701404809535494e5000,0x698e17dd5d54d11c50c0eb8db4c2ca2481e69651028610203298,0xc4423f1705864270a8004829218501a2d080441004b5daad368b3d9acb64b1d8ac360afc96e,0x4a8bbaa463cd1334c933ccb30c92ff14a46bf8b7136be29ea728cafac0b3afc49af20982401800a1502a,0x27217af2bc2eab92d0a8a765d0011d2965e2df2d2eca3cb8b8ad6b1ab8a68692dcb329ca525ae89d503a,0xe028014cd31485153d4e7382c8ae2a2a080d4fd172c0800ed3d49d254750740cfeb92ceb0ac0ad502c,0x414ce1d84a12047801414ff344af2a358120400e02c0a8280901343cf930cb527aeeb629e1183e0f5022,0x6a34da4d16833f9dcde6b3195c9e4b2390c7bbdc6df6cb51a2d0608ec015faa5025529944908,0x2bb5cadd6ab358abd5aab54a9d4aa350a6d32974aa3d1a8b44a0cfe7b3c9cce26f369ac97c,0x19b264a6c3a8f313e2f43daab02609006002eea6acac22f6bd2b4b0a9cbcad4af2bec0ae8a9adca5d02a,0x3cb0e79bc5aded7f3b4cdecf5bdd94db6d7bfcfea7c3bbe1de6bfcbaccbf8fbbd3e3f148a4,0x4df374d534ccb31cc1264db364d733cbf24bc4aa1ca004ccb2851384c530cd1322b6a72963b47e5f5038,0x4a6e9aaa380b80b53748d173eca4bf2f8bd2dcaf01c0449ac0ac4b0ab6acaac66958050015454b50d02c,0x5775d5715bd6b58554fcbe6f83d4e6b8c709b66c11c420800c826058120400c005ad695a364563565001,0x8463c09078520f1b0184e0d1a058762c0002c096db65aad364b1d8abf5eae56aaf56aac96c,0x4cb262e7292b4c1caf31cb8abaaa5cca733cd8b3aa1324b335cc2f4cd1312f80982401af2002e4b8d02a,0x50338cace4294974cf314bd2ecb2f12daa3a8c6a8003eb8720ac8ac27ea88a69a96aab0d529ca527d041,0x330b7248509200453548bbebf2fab12c2ad0f2075414ad1d414f7363f3424f336bf4f08c60054b51502c,0x53b4e5334c52efb37a4f816050100300168da1665933ace32eca51fc6e68914190195a55f55bdae1d004,0x7c1438210ac3c18230c0016db65aed567b358ebf5eae56eb357a853e9b48a0cfe75389b496c,0x4d0b22be09800a449932aad30ccf2482401cc9312ccbf2eabca9d34bdafc2a8a9b02b42f9354d6aed02a,0x432821eb1ba347c491172fefe246758151fc6af8a5678c76fba207f00094be6ce2290941874c13035084,0x4d125c447592c0c00152ced3a4d534ccec02c0a49be6e1ac4dd45484ff332bcae00b4ed2f478293f5031,0x56b595635454f5354750d3f4f536e5a7e6b9103a852005a96956f4e4c5009ac4bd7f5854b5053b4cd003,0xbc2b4baad6a928cb029ab7288a8a8ec2af8af298b2ae2ac28b57d5d5555153d4d52d475052749502a,0x30cc1cd331cc4c22febbad4b1aa4a89993206b30cbc1eab24688ab9ae0b6ac8ad182bb2980801e00502d,0x2d8b4abeaeab2ac27c58032a28620900128ca0bb2e0b3abca6296a027a9c1a859cc12fcbd2ecb12bd035,0x4bf2e2dab3a920480d42d093bc7c00801454ff3f4f937cdb35cd2b4ab2a62869ea68962e4b72d4b45040,0x14004ef374d91fc6b14c4f0f4341604348cdf32c4d0786e1905e1584a120461003e0cd7151d27475013,0x54b51d455053b4dd354cd314bbf4fbbdaec39cdfa8c090014f4b72a49d2548b1f2027d1a0130400f5000,0x595d54d13cd2c50c0fb8db4caca2692271a61651238a182032a7,0x2f60028534a9cb44cb2fadeb4b0cb1300b9a8ab32baaacc0f0ad6a5286bd2e89fd5955d5554d5153d02d,0x2c549d1cbc2e6004ab21a8eb1827334b2b8cd3324d530bd332c9eb6ca8092c933acca84d6b82aebe502a,0x4e736cbb2dca70ca7c82001414dd30428f22b6a027b3b2b8390b540cc92a8cc9da6b3e4169bcc519d049,0x1be3b0b40a8016a5a56859f52c4c8e9ca1f0380cda36753d4e4001bd071ab1cc021e57869655835dd003,0x72b93c7e0f037fb9dc6df69b3d96b355a3d16632d94c9e471d8cc5e2b138875b95b8da00490f,0x27eb54c2f34d0a88212f2bc002e1324b8c329734adcababef7ab6b14a0aaaf4bb294a1aeb304cb2fd02d,0xc0be53d4ed27152d32e2aca850740aed472b2004b664306bdad12ccccaaa9f34ccaa3cd52d2ce09502a,0x4df3648ce52925c0f4050014e52b444f5323d6a7a9c5f4ff3e4d5349082f5233f4e2b211346d0f3cd038,0x57d5cd715b54b51d455053b4c52f4b52b4a3eef42789b23e771be4a002005a165d394dd348cd9d64d003,0x5e4c421e80062011f0680425558b03c0714c8a4328b5daad368b3d92c561aed72b155aa496e,0x541493f4b72f8bb298c4936b297b35cd3251c409000a94beb980732027314c6b64c2bc2a12b4cf34502a,0x6230a8ddbec33598bfdf2f369881a81d90c5b8811acd3238f78dbc5945d5e44e9f239f004921,0x53d4dd314ad28ef368899b60e816020014e4e702c027e8f62b05d6a5a36356758d414fd32cf133605003,0x49253231cca2541b001123e2a0a0c41ab954822db6ab4d9ecd64b1d8ab358a94f277399c496c,0x310a590cb7a3f40ad3484b8a4383254b48a4c8a9806a928f3382609000b04a2beadafb4d2bbcc6ae502a,0x3aa9d0014dd1b424e6e9a866854338cd73246eea2d6b22c205d1d3fcbd2c3c6b527f4c4fd212733dd034,0x51d46bbcea052110416458d6151945be0d72b000589455127805011d815f50ef8a881ad6d56d414c5010,0x4923c3e90844600e1fc8c54ba2011a4c1a1e802db6bb3d96c35bacd22833a9c4de6d359a496c,0x2dea6d00accbd2b0272e4d734995324c2af024004a2a3cb0be006b1be0bc312a52c3364c4b14cf35502a,0x12dca1264403307016c8d1a3ee6713d1f47117c4b0ea112547823c6a9320e7dbe491c972188b1bd07d,0x5314bd2b49523483b4e2a94a01d6721ae21028004c6625a166d9564416fb9974e5334a306c12e8b4d007,0x1e90c002da6cf8683324cfc5d2a7077dbdddeeb71b6d96b759a5d26832d90c7e3b1b8cc4c918,0x4d133cc729cb2be2caa83f2fbbc727afcb8298a2aecb39540982401800b929cbeadabdac8c1ad2c1502a,0x4350cc2a85a007f1d096a548f22c83a0c7c00108c2107c1d05c14779fa7e40ccdb128a05efea3a7fd085,0x314bb2e4b7ad0118400f82201001475001383a055574dcef3aab607818cd32ec930cb8ae01682f465017,0x342c7310b9ad8a58340b0280980c0047512a9aa28320600e02d234751943d0941cf93dcdb362fcbc502c,0x36ad22a4a7298a51ba0902002b68d5058008015ad655855d53d494fd31394c121c5d13446f9bdee05015,0x7cfc7b7af9f8f776f675f47271f16f6decec6beb69e8e7e766e564e4118c888041d3,0x49c002b32aac8afc6ea62e6b74ae9abb4b4270ad4a7294b34e5374d5334c52f4b52b4a5274952348503d,0x50910b94c253c09541493bcbf2f8ecaa52db012f97801c96a74bd314d734cc6002c3264ceb4bc732502a,0x402c6adc268011641903400e8ae030c7111c430d41702be6498df1dc30b5a4f1b45e8094907c0514d097,0x5a767d9b6659560d755ad4950d394dcf7399f872804005a559d414ed2d000e4325a36858b51d354bd004,0x480801f0ac523b270ec9a4b28220962b2200008860c0bc8c7e1e5d8f86b1f8f486496bb5496e,0x55b5252d3c4e9382eeb62174d53347caf26abea7026094ad4f16745d00b9ab8af4a6b6cbaa500001d02a,0xee0058f4ed3747214480dc3459f635894f4a042551494ba75d956458151d354a3eaa5d654bbf89a5009,0x1bafb1f06fa0c76a227d3f6bc1c86b3fcfebf2ffc872047f1f4790941f05c13034070126c0e016005096,0x5173449c7202749c9b184a9252e8aba9eeccc73051d27824a1801322dea4006afb0b30ccd362c4b1d02a,0x7928c4709bd84800127c7719c428c223264530f33a2d4a123c2908b02880851a4410ba431fb98615087,0x5a167d9d65d7b4fd3b434f4eb94a060160059b54d414f5374bcf0790da1a549515434d52ad4ae8abd002,0xf5ae92f2be0829730cbec228eb54d0c2cc1334aaac2fca0a9d322ff33aed32cc734cc55655153d02d,0x54f4f5173cba26a5013a3ea96d4d5251e2dd413d20e8080138525442b2093b74b5354cd0324ad2b0d02a,0x4d9354cd2147b1e4721003e0e000d1b0019cb92dc8b2246ccd92d394bf21c751c422bf22874ce9385063,0x49a003b09e29ca2ab7284a32d2d929abeba470bacb32ba6f2aca49ea812b4a92c49f4ed394d5314b503c,0x4f88900754d42eb25756d3542d08c63395754b4133ec0d40ca527482f6afd1d41d0f40a970d82600502a,0x5a56859b5454550d3f4dd354cc8c2b80168d9d53d4ab58fe32dab63549505314b9905b57f5f57759d000,0x4b6ab824faa90002dca94d8b5cd332cc7314d6c3b06ae4aca22ff30abca64d5344c933ccd57d5955502a,0x54f513b15053947490af11947ceaeaa3955d49432d2ae52d49a4ca60214ba854c4ff3e4af284a200502d,0x58760d7f4cd2d4851f465111c0b02902a0058948d1b1929838571555394bd915cd454f5374a5166ed00f,0x48c07800f2cd32fcbcb5abeaa2ecb14c530ccec02d130282c22b0a4b0aaba8732ad5324c75655354502d,0x4f534bfcbe2ecb951535b08afd330dd3546b12bdabcae8bf2fa0947ca6c1528bc2e6ac826004ab2dd02a,0x5293c4d333cbb1c38c68d25394e1364c73039eb39280052d469b54f526e4ab87c80f3f4d130cbe36d03a,0x4f942cff64d8f6358961d855cd6b4c52f4851d444eed38902200162d7f58d3d4ad1f4611c2784760d010,0x2c6ada8c09800a702529aae01cd131cb530cc8b7312c2a9ebea94b22f724cd3332b3364d4a428533d02a,0x7cbadcfe26cfe9cce5f0659e9eced1f06c077b3a9c3e009a4923007a39dc744f8b47cace48e4,0x525465176ada36859d655374c4b2e7a2a0059b4fbfef091e23d514f40e8d9d66986167d974a9e169d004,0x54541d0142d02a7cb725024a9000b6af009cd13230b30cd2b7a95352c4c4cc6b928d33a91314d6a1502a,0x477525454ad17433b4e6001555309591f50d24c555151d0b3dcac8dd3ab32baae2974cd1d28a80b8d02d,0x4430fc3d0eccd32cc7304bf1845f1745906bece30112d46918c5513c4d12be4ee00130c8f14c49075073,0x2ed48c8d29021343e2a74b8ad80007ac0b12eabccc32f4beaccc0b4abea0a92ab2b0b430b314d2b5502d,0x54d4ace8ef3babdd4750519262508154f4c937574ff3e4f4c22e503adc69d2d494b138000c4d0d4d502a,0x5414cd2b4a1b83a89203806005914f536955855f5354c456c118050da163d61535494632c820841d5007,0x1eac001312bf2ccbd31aaf30acaa5ab933cccb14af344d332cc9304bf565535454f5354b42d033dd02d,0x3ae0054b51d3b4b331555234149f4a3068bd5b55ce14d31e8dd1740284b75414c51f43826acac326d02a,0x50b4450166d9563d89615374c52b49d16348020058d4bba8e157b4b5294798c4659962d795bd5148d00c,0x50b3782739024ac800aa2c4aeaf4c2007362d324cccb314f30ae4a5cc8c3cc6a2cd135cd2a74a732d02a,0x4bcba9cc4380145d15424ff32cb3404acfb9634a5233ccdcf42967d51f1ecc719cef3dabeae4e33d5042,0x4c52e4cb31cc35555351d43505373d4eb3a49e38801544ef343a46c9861e06d534ff390c352d3f3cd02f,0x5394dd26add09404fd232bcbaab200296c201ec2aed30a94ab4d13130d34abea34bf304aaa8cccb1d02d,0x4f3368e347d0d3e4f13836837d5b4ed3344d5d48cecae92a0055553d53414e352d40f05014929809d02a,0x34ab5ac8bc300d0b1334d1142d08c5d0140d0d66d9564d8d6258560d394cd2b49d25460be2380a00500c,0x21d23ac62fd0d290c72aaf947d2868adcc22bf28026002cc092eebb4d930c10b94c801acaa24cabcd02a,0x1de6a86a004430d419022a0a211b0ba5c4c0a10c424ffbe24743d003ccf01e504be8f13d80dc22f3d0b3,0x5694cd2d48d1b4625e005936358960d7f5952f443ee639681658f53d3f4951cc71f86c53547c2eced00f,0x2cd2a30e094d8c34cabd000abb12ad4cd312d4a4cc735cd2a94bf343cf33cc9354c357d5b5454b4fd02a,0x4e2bd51f372a287d57555434b22e4ed473ecf33bad480544ab23b452b34852eea517404fd2aac000502d,0x51d6ada568da167593625494a4d528888078100059b4dcf6529321cd9f50d3d4b58b5dd755654b4ed004,0x4e4bcad400522b9afeb72af30cbcaf2a207bf2ab28f2fac4ac4d333abea0aecba4c4c2cc1323f731d02d,0x54d51ceeef308af51b433a553d2537bf5575113d4f134d132c2b9424b86fcc0b9026004d74d4fa69d02a,0x7a03804005a1675996458f5b55b51d2c490f56152949d2115a669584967d9b5c53d4bb2cc12608ad007,0x2531928515a8e9226f14c50a245f164608c26116c211545d18b5b13ceb374bf224791c44a17020005064,0x16c58d5d54d3540cf50054efdd32f40274fce337d493ba885a54d39c932fd2d46024a8006fe800c3502a,0x59b6659764d895053b4b0360054f4e472e1b74418f16355d4bd1e520454cd22fed61564f0e559d50d009,0x5254cd1b24d4a09026002ed2c28ea78072b4cd364d6f74d3352f0c3cc6ac4c530bff344c933ccb57d02a,0x35e1e50d3a0014dd1b36c8493a294a4e0f152b3622d515414b504e92e14ea03525193c495341df51d033,0x32ebf2d2d651544ae5465173db12b5320d44e14451f43d1b6a5a767ccd2d8c60059b665914fd2f1ed005,0x4fb3c4de55d3eb9ad9492c2652bf4e5354249d23ab40980134bd4bb4eab72babbcd93080729caa09502a,0x4930d42c9a8fc31048004a9294610a94e4dc811fc4709a1647c971c160498d316bf8d230927c7918d082,0x40f07c18c341d034a728c9f264950dc350bc2b0a379294912247b1ac450c3dac1afa208160049b24d086,0x3bf4c55954d4093c954950b2b49f53d460000724ac2098247a2eafebcb32cc930cd9332c0a74cf34d02a,0xe028016bdaaf5bab6a5a153d4d515376757d4e3be5b5334bc0b60d7552a8e785414fc0e9ea6d5ad000,0x52d4ad2747d1b460641884545d1340d154450b4250f415016759b63d894f5334c4fb3b39a3780c00500b,0x4e33353b37826028014dcd93d4eb4cd075053f444fef43c4f0d4343cf94f5352f4b73ccecf5bbceed033,0xc87200930585721024aa4ec10e01c8a13900922b299248e451f92a865f6db65aed563acc96c,0x3128a55736aff514f539a4b52d1d37430afade913012854d49d0324af535516090073ecbe9600009d02a,0x45c320020052d4994044d8b535494951abaae87f14e49d835d5915b56b4ed394cbf2a11656151cfbd00c,0x5391c4650ec2d3f4fb4c52e09006004d5314c335cd333cc9344c73655f5755b565535452b3cca521502a,0x4e00701001001354ce03009374d143cff2f4bb4cd30f43bd51d4007d2d4ace337cd935d454fd374d5032,0x4da652c000585e0d76478722290c96412993c400928914323f24b65aed569b358ec3389bc96d,0x51d09a854bb00525454e531444f68854ec1d4d51d0b28ae8a4cf0000073302536cd3392ec09a9eb4d02a,0x5af6b5a964583408821380e005a166d6f309416ada55754d023fedcd4acd86568d98eeac88a1dd69d002,0x525444fb3a4e337d595351951d3b17c3d08c1b3cce5454fe09006004d7344c9354d331cc533cc332d02a,0x4cf30ccb3226e99d5b54d5152d453a4d60e8340400b3ccd8005234183209540f5bc755d4f44d4d51d02c,0x5120ad5352ce4d7ce34f53b454f93a4df53d415354951c8d51130078005ecc534cc32f4d133ccb2fd02d,0x30ab2d694db1cb3d093f50f3e50d41d013fd0540d0b3ed93634872144e070015ad39173d1653e756d00f,0x1a005a766d4e2ed694e0b36787a1cdb15fa5f6ad756a5a55953ee3508f3581575716bd99645a1675001,0x3b139ce34b5015554754d4f3bce550d1b464fe09006004d333cc735cd5344c5324c3334eb39458c6d02a,0x51f44d1b6b59b663dcec01a005af69d9cef3755353b4e1b34b8536255868d8554da9681154a51b025002,0x5494951156d4b3ece938cdf5654d4ed1951c5f0f42306cf3395153f8240180135cd1324d534cc731502a,0x4e1314d3334cb2fcd133cc3304c756d5153d4d5283a0d01002cf1398014cd260c82550512f5bc754d02c,0x18b3d1a44d9193ece355d48768b15151753bf0f6d4d565373ccdf4551151d5b52d253f824018013a502a,0x5996959a13d274651346d25485154751f45d1148d8753bde3501a005ad68da167b7d4ed394a40900d003,0x4972f4b532cbb304bf2e4c32dcc931cc53c5374d41ee14dd02001545454ecfaec02351cd75053953d031,0x4892b4a6ddb8edd4811f46d1fc7b1d4731e46f1acff3c000d8d07314a93f4ef3d4f313d013e4fb3dd056,0x16031e65f9644d1094fd335254147512f8d1b413db53d4b5102151d42fc4e738cd73501e003d33a502d,0x51543cc326c95264912348b2949f24ca1274bd2b49723ccb31d27495234851b2f4ab298e7314c2005046,0x4c72fd575151141ce534cd152ccf30d4951cfb3e55b35d53535465b1195154a005513b4df36d5753d02c,0x54a0900152d474f4c32dd3f4dcb546cf550d354cd414cce93754aebba14fd034]
private def oveClass (i : Nat) : Nat := oveField (oveClassData[i/32]!) 11 (i%32)
private def oveFirstData : Array Nat := #[0x36db6dbb6d24924924924924e3,0x155555556eeeed99999a6599991d,0x15555555555555556eeed5555554000011d,0x3ffc000003c000003eaaaaaaaaaaa918,0x8421086318c6319ef7bdef7c0c6318cf7bdef78158,0x634a5294a5294a5294842318c6318d294a4210956,5026338869458,0x248e48a39249238e48e492492492400c30c30c30c30c30c3180,0x8ce00000008a649e1111155d65e666551d,0x169111111268d25451051121680000d111c,0x21080420000215294a8040884000084000294a52956,0x895294a80004211508421084200021085295084156,0x405511111151112eaaeaaabbaeeaea910,0x2400a28b28b2ca2ca28a2904514114504114104114104114180,0x20499008892222151995d595999dddddd1d,0x2915154a628025560445605148e0889111b,0x4010820028842108a52a1022a042108452d5054155,0x1cf75a1541cc653defabed67d5ef7c1f6adac00014f,0x42084000b16c5ad6e739efa56b6b5ad6000063194f,0x218e38628a29228e48e39249249002c928a2494514514514580,0xd4d64c9156908954908908a2aa9aa251b,0x202254a210842294a542104a94b52a0f82a0631955,0x215856b6419ef7bdefb58c83990681d4a842d60014f,0xa42908c53ed6b5ac00000f53d8a53e15b18c68c54f,0x228a28e38e49249002cb24b2c94514514104114504514d45180,0x116654c9449264495565490e5dddc89d1b,0x2d81b0015db30019e0199b29da08b0dd18,0xea85636b056a5194f7bed6ac40a4ae16b00c6b194e,0x431886329084231ce84296000c6841f0318c942d4e,0x268a28a38a38a28e38e38e38e39249240082082892ca4104580,0x15000111151124684696a95562259eaa91c,0x1555595a6daeed11555555556a84404051b,0x41529508042044200084000842b5294b5294b52956,0x21021507218e73be00420c974210842108402000556,0x210040031ce631951908c7418e68421194154,0x84804059dda1dda1dddddd99d9e1a2e90a,0x2092276189d7639248a486186289d7e38e39249002ca2ca2d80,0x18032b159ab0df0cccdcde972d71d72e918,0x600088a53e030014a84144542042120a7114e22554,0x1d0856c00000a74215b580049dd67c212ad6c03194e,0xa42908842318463073ab29565294a5296b5ad7140,0x218109a01a189218a1991dd1a1e2208891b,0x31c0019a29c0202b1f31da0e2cce0e2b117,0x147545f5adac0028ca7c6363298cb58c6342ca5194d,0x8318c8421084210846b5ce745cfb5800318f50194d,0x227618618e38a28a37e28a28dd75d00a28724a2474104504180,0x16dd5e6e2c89eeee5aacecceceadd5518,0x10a88446530ca8be95319f602a3052a368596a5594d,0x6320c6c635b4ad6ab4b9d5ac2800a0a5314eea214e,0x1c75d81c7228617618a28df7e300a24a1c91c74104124934580,0x1a2d6c28166ddece6e64eeedde6552d6d18,0x211b0946546750294a8be10b594b63210829528a94d,0xc472a3488000322368580c3c2d610950b58e63194d,0x1c7e372086389d8de8a37638e30082072d14514514d14514580,0x2e419ded48ac89eed9de6ede26651295518,0x2c002cd5b59068dac65194a829765dad08d14aaa94d,0x82208425a18c631929d1f30000073e66419cf73d4f,0x228648628a28a492490028a2872874104104104114d14d14580,0x44cd110888ddddd5626665559955dd91c,0x1d9999ddd99b0888009998d55b1a2919,0x2aaaabfffbfccfffc019a7fe666667fcd16,0x10642529842108390852a108400100020010005ad55,0x88d54db776233b80000000089555599117,0x888888800080080808095555555732a90f,0x1a8a276281f86181d89f8a289d75d00b34b28a34b24a2c92980,0x232cb0896ed6e323326e111132d9f19116,0xd07daca698d27d86a5994d95ac033e4054eca5294c,0x318c0a5296d7398cc579c3b18c6579c4a60d64146,0x1a8a281f69a85d69b8a27db8a18a285d8a27e289c71d7401980,0x605294aadaab53210956d692acb5d6d58da15b594c,0x216120c7b5ad600c09958c99586351906958cd7d54c,0x2176182286189d7e289c71d7402491c641241249041679b6d80,0x52a81991a6a4c581aaa8a1aaa48ce2918,0x2c049a56b08e633de35aa161814a7d6ca6aa4a9594c,0x310d295ad73bef7b42d8d5adf5be9ab6b5f4a5d47,0x217e166186165a86185a85a69f82086176176175c71d0091980,0x893bad652a16201b65aad6b296d85a0c6b554b554b,0x205b5ee656b6ce6dc649ad65b8a6358fcf2db42945,0x1f85d86186169a6a06a185f85b6e16db86175d75d0052081580,0xd6b10f0b016c6c62422ed65556dad5aa5aad3b594b,0x20314d6b96b65b8a531d7e710f6b9ecde1af73145,0x1f8617a186181a85a69a69a86185f8616e185d75c71d0072180,0x6378149956a94bea31a6b5632b5ab2ac4aa109554c,0x10b98e5314db677c53db6be9af630ee7b1f18dd45,0x1e8a275b6db8a082289b6dd8616e18618218a276275d0081d80,0x659980a20604199b32305e0a22f31e116,0x2939cd285506598c783ed611ec3042d6b314d5594c,0x1d75d0062c82c64514d14d04126dc72238e4925164a27a13d80,0x21de21e1a2001801a1de1a2188a08a21119,0x6319c26195023156ad88c72acf7d54a659526414b,0x1d75d00914715249355a84f4da7217914da8618213cf5213d80,0xcc0f267332f31571572d6f17323223115,0x20422566842c435ac05d88452a166dab4b35b0b594b,0x1d75d74014520841341345145b3d345345145b7a12d15147980,0x2419240a59666662088a4a62222664ce518,0x86342100294fb588ca914e54210b59aa9bad05354b,0x87295af7d6b519cb34a4ea739f4000e52a5f5ad54c,0x208206607d966066082069a81f75d6dd71c00a2082854104980,0x2160116889167aaad62956ab594ab59cd6aad6b554a,0x1d75d0041c81134114106a080e4da81051042078f3945545180,0x17172f32eef3132933173171b199b2e514,0xf294a41408ab408cc90406332520b1304a5ce3254e,0x1b6dd75d00410825140e49065b3945596db8203934202ca4180,0x8cf0402f3333333317319b1b319af1b114,0xc5aa8a52a2150190519d759d4632258454589ad54b,0x207a185f8207dd71c85b6dd00718420611041148e41a6e08180,0x2deac1ad940aadddaee2e64ce252ee92d16,0x1efad0202a5d5aa6b4aa58c4d4694a9e96adb56354c,0xc832106858042000639a747c84859ccfac5067c14b,0x207a081881882082081d6a081a69a81f75f6db75d0061494580,0xd033ed62808ab58ad532d62dacd931b46a954b594a,0x1d00710710441241045b7e080e55981b80e4905134554135580,0x5a201da2042220dd8a1c55e21ca091d118,0x604bdf049ea44a5e36a52c4cead85610ad58d7554b,0x236b580428c093a0d6b390b3c2b5b14a659a10b594a,0x3f7fdfbffe33fc773efe7f9e73fd012129ca99d6940,0x210000a44280f2ae045280a84009839298420c8414f,0x202102e53b7c6321cb5b6b8c1dce42378c35c35543,0x2d69f9ffffffdffbfec631fc77ffcff7afef5de8140,0x216642c043a12b2a16542c633db0b1ac652a90b1949,0x1f8207da69e6db7e082081f69d6dc0031504197c934d3d44d80,0x100311b0732c8d167330d6d732913223114,0xc934e7394c415965318d4a7b8079cde77362259d4d,0x35ad7fbd019243ba4f8422d54e509c339ceb7a7b540,0x1440013079c8f7801083d9084210839294a61072d4f,0x2d6b10168048952520532165424a52ad584256b3d49,0x339ce739ef7b7bdf7bdef7be8063441b194a79ffd40,0x840921080484211400a9308402a50006329508414d,0x35ef5bdcb7af7efbdcef3ded6758cefd0018c654141,0x1f102da52aa215298f6460b0a150821518a9718c54e,0x110b5a0b8586951dd67c2b632c0b5b0ca85a2354949,0x29ce7398c631ce72d6b6b5ad6b5c014c542a317c140,0x908420424204210852a950808305298c630400214c,0x339c7bdef7afbddef8c63dedefdce81ad3198c8c140,0xea8160e294a54400e0808e7bd508220b42a108414e,0x424210cebde6b652cb152766f8b63ce4675ce3d40,0x19a222000c133332222333199aaaaaab10f,0x2f7dee10014a52c21bdef6f7edefdeebbdbd7563d40,0xf000170218e76b9c109084812108418a531ef7bd4b,0x33abdf39a5294b5ad6d6b5a212108674d6eb40d4541,0x35a421b593eabd6815d2e2e7463ad69ef9319573941,0x3eeeec00ceee2ee3ffeaabbbbbbbddcbd0c,0x318d29467bf7b014bbdd62fddf75aee945af7296d40,0xa514ac631842a105842106318c8420a529ce7394a,0x2d3ad718ce739d00842135ad69ced39dad529ad2940,0x20683dec6001082942840844b18c610a5632108314a,0x1ed6de12bdef39daf5aded77535a01084a4210d6940,0x296b4216b42d6b5ad6135568bec0699f0b1ecd53141,0x294a631894a56b5ad6b60a68c41189ced6c96b5b941,0x2107bdef79080029505ae04212063418c6321083149,0x1ceac20f7d6afad6109ceb5ad40318c6f7bf0d6e540,0x2314a6108c62c8c5ef88c152a95189d354ce7563140,0xb584e75ad295ad694aca55ac318ad40]
private def oveFirst (i : Nat) : Nat := oveField (oveFirstData[i/32]!) 6 (i%32)
private def oveSecondData : Array Nat := #[0x9838ab8ab8ab8ab8ab8ab8ab8ab8ab000000000000983983983983983983983983983983983983983983983983983983c000,0x8ea3a8ea3a8ea3a8e8de378de378de378de378000000000000378de378de378de01806378de378dea8a5,0x37cdf37cdf37cdf37cdf37cdf37cdf37cdf37cdf000000000037cdf37cdf37cdf37e3b8ee3b8ee3ba8a4,0x99e67944000000099e6799e6799e670026799e6799e6799c00298a6298a6298a6298a6298a6298a6a8dd,0xa9aa9aa9aa9aa9ab18b18b18b18b18b18b188dd8dd8dd8dd8dd8dd8dd000b18b18b18b18b188dd8dd8dd8dd8dd8ddb44c000,0xb2eb1ab1a000000000000000000000000000000000000000b2eb2ea9ab18b18b18b18b18b18000000000000b2eb2eb2ec000,0xb2eb2eb2eb2eb2eb2eb2eb2eb2eb2eb2ec000,0x9839838c89238b18af8be8be95b8b29839848f08be9838c88b08af983000000000000000000000000000000000000000c000,0x7bda9928028d2348d2348d2347bc6c0e80008cd80050d5064a2a0750784543400360320c8320c8c8a8ab,0x36c012cdac8564d9364d6b006001f20583e36e379362e8dc7b6b21536cdb009fa3f8fe7e9f26b22ea8a8,0x9c000ca9ca72b5ad6b1a1a868b9446b0780d69cad41b00c35ad456a729c8ec561500836e4d8b8dca8a8,0xa9d0793a15320c80e2b2a1e738995941c350a0a5294350cc360029d502737ce71370dc2b0330cc28a8a7,0xb2e000000000000000000b2e0000000000009359aeb4e935b4eafdb4eb4eb0cb1ab18b188f4b18afd8f3c000,0x8be000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000,0x2d1bb3a8fb2e6247e1f86e4e0050140501432131018003f4c800805804073ec05320190640300401a8bb,0x1e55f24091c088a8ce028044c53133a3e2fc0a3c5ed3c537031ed7959f8a80e01a2a8aa2a3c1e5a8b5,0x9e9339ea7a9eab04cde69ea7a9ea7a9e9e618d04018949ea3f0027a9ea7a9ea7a821a08fc03798bba8b4,0x1646499c0373895a46aa9be519324996659342590701c79cd099e59684e8964bc01400256739ce73a8b3,0x935b4e935b4eb4eb4eb1aa54b1ab0cb1a9489489488cf8cf8cf8cf8cfb26b26b26b64b05b5dc000,0x9538cc954af59539538c99838c995b9838cb8ca9838c89838c88c8000000000000000000000000000000000000000000c000,0x94e5079a50244b9942157418a628a574215855e679a15742158544d85615000050140522805004b9a8ca,0xa02419a809848909aa6a9aa6a9a80a2540801cab00003025d67b2318c631004bf2ae310065964d93a8c4,0x270bf8bc0e0380ba02990259064007641900086197a80a025e9a96114e809aa6a14def0040098a62a8c4,0x935affb0c8cf8cf8cf8cf8cfb26b26b26b26a9aaffb18b18afdafda54af59258cfb5db5db5d935935c000,0xabc9b992098491e9159839838d4983000000000000000000000000000000000000000000000000000000000000000000c000,0x921db878731ce016860a554d1829c51cc737360a5fde876cae8060a108012b84c45c9e0020a828d5a8d5,0x978b281957610b39d2741a1ca780b300614851ca88de09d20e819e000053728eb8967e9f8b361dcaa8d0,0xb59affb18a83a818cf950b26b2eb4bb2e000b2eb1ab0cb1a8d38d293daf5b26a27b44b2eb1a98390ea12b05ae590ea0fc000,0xb4eb1ab1aaf5b1a953948b26b26b64000b188cda54b0caa9b64b64b2eb2eb2ec000,0x8dd9589539588ec9588ec8ee8ee95b95b8ec8ec8ed8ef8ef8ed8f09838f0983000000000000000000000000000000000c000,0x1fa188fa028f8798622b1f8791f0760260200dc0700051e408018100407704c13030770480000000a8dd,0x1e87a1d8762922977808000a400800001bb6ede378de31e477859e3859de02c0b70dc306dc306dc3a8df,0x952541e47978c030082408a836700000a8309024a0c23090229a9e378c7c1f1e31f07a1fde378c15a8da,0x4000882167c200741c9041b06c7301a8b0859f0741a01c031d0751d40500c05018039b686a2e57a8d7,0xb59b59000b59000000b4eafdb1ab4eb4eb4eb0b8d98dd8fbacc8f2b18b4e8f68f58eb8e48e88d98d8948c000,779805048832,0x905948973adf974908adfadf9159049049169839749059de908908adf917907915915904904904000000000000000000c000,0x36a409007f008440208c1c004110e26587f388e2388e204ce26580202444045db000da76c7f04404a904,0x915103a25a8be191d40412645799e68640b210841d52837c02002459162f004df01d2803017914e5a8ff,0x8620a8284611a24892248922c1d1d4750461184e892248b25701c4e66216010040001211a24691a4a902,0xb2e000000b2e000000000000000000000b4eb4eb4eb1aad6c000,0x6b369a202e5368dcd1431b9b5cac2b5993ca3739192020080520d96b17800003772b95ca9915,0xdf93a4e938093a98b231a193a4e5164e3807482c051d1a12318b8fd453323f8fd458fd8b38074a90f,0xb2e000a008cdb1a91091094894f000000ae3a0fb59976a54a5496fae5ae3b2eb2e912914ae5a0fae5b1a913ae3ae3a0fc000,0xb4eb4eb0cb0cb1a96fb1aaa29839830009e9000000000911000ae5c000,0xabcadf99ba33abc9eb9839aa91f9c79839179219aa9ec983adfadfadf000000000000000000000000000000000000000c000,0x729ca254690249024008005d9002348d180008691a5db800061a53d1a6034f46980c0901180715c5a91a,0xb44b5991fb26b26ae5b44b2e000b59b1a9249ef97eae5b059cb91d000ae39c7922b449ceade9c59cd983ae4b44ae491bc000,0x935935b3fb1a953983983983b2eaff9ca9cb96f919b1a953b26b26b44b64b05000000b2eb1a9c1b44c000,0xaa2adfadfa099a69a69319c6934adf9fe92f93192e93a93a983000000000000000000000000000000000000000000000c000,0x1d05c001af2790002e1d29806039735cc0348874170040162b1705c1712e1f80c031bf5ec096e009a927,0x93892b926b26ae3aa8b2e8cd983928000b599ceb59b18939b1ab1a98394fa10b44aa0aa193bab0ab09a7a10a9aa08b44c000,0xb1aa00b1a94fb0c000000000000b59936935937983000b2e000928925925b26b26b2e93792994f9a7a0fb3c000c000,0x9a6a9a983aa2a319b4984abcadf9839bb9aa984adf9809b69b6000000000000000000000000000000000000000000000c000,0x76009af559560fd5882a0a0e60a8292c0fc3f4c92c558c30fc3e5bdaf3bcc33bd5e1886666d9ba944,0x93c000000b4400094193da83b44aa8a9a943942aa8a10a0fb59b599b4b44b4493fb4498394499bb1899b9a7a1093e9a7c000,0xb4eaffb1ab1ab1ab3fb1aaf5953983b1893db26b26b26b26945985940b64b2eb64b1ab0ca54b0cc000,0x958956950956958958958958983983983983000000000000000000000000000000000000000000000000000000000000c000,0x8fa02809bd6f47d1f47a21c8721dbd1dc771dc771e87a1cc00000000007a1e47b1ec7a1e87e1f87ba8dd,0x9ee7b9ee172c262988b02b8ae2b8b02c0b02a2779de77304c19de622d0b39d4be2fa62001f42d4b5a8a6,0x6bdaf6bdaf6bc3b0ec3b0003a0ea208803b0f43a16c5b8360d11c3a0e84b12c4b1244c1243a0ea13a90e,0x5417055d374dd3014030140300c00745d10340e0080200802859fd85a167f61686de786c215d976a947,0x7c5f120a4f93c828fc000006f210841b000002699a6699a6699a6699a6248908b22c8b22c8822083a8db,0xacdacdaccaccc000,0xb4e983983adf9ecab0a9a9ee99bab0adf9739179ec9ec983adfadfadf000000000000000000000000000000000000000c000,0xf681ed404ba04ee974e79fcffcf3fea827aa0004e547fb777bbddeef04cfe08b79ec0dde9970,0x976b3f96e96cb44b21000000b18b3f96db26b44b44ae5b59b21b1a9eb971000ae5b3f975000ae3983972b59979ae4c000,0xb1ab3f983983000000000000000b3f96b96ab26b26b44000000b21c000,0xb4e9b9982af3a9ab4eb4ea33adfb4eb1d9b8983a9aa579b8abda2d97f9b4adfabc9aaa749aa983aa29a6adfadf000000c000,0xb26000a38b599bfb599ba983998b44b44b44986acdb0c99b983983b1ab5497ca10ae39ba980981a9b9839bda07983983c000,0xab0983b26000000000a83a2d97a9b2000b26000b2eb1897baa8b64b1897db26b26b4400000000098597ea37b2eb3fa28c000,0x99cadf9dea089a099f9de98badf9179a1983aa29a6adfadf00000000000000000000000000000000000000096fb1ab1ac000,0xe0c74fc5100706b60d07e5c14590c6f23c10e0e5c00000072c13530016109cb3198da4589983,0x9db000b44000a9a9899d4a12aa6aa8000ab0b1db26b44b5998e988b260009e7b59b3f9de987a27b219e7b109e898f999c000,0xb4eb1a983983983b26000000000000000991a81b0c953000000000000b2eb0ba7098ac000,0x9839a499eaa199d983a07aa0b4e9a099b983b4e9a1ae0b4ea9aa08ab099a99cadf99fadf983adfaa29a6adf000000000c000,0xb26b05000ae19a3996b64a25a95999b26000b44994b5da7b998997983b59b5db44ab0983b3f9a7b44b44a589a5a1aaf4c000,0xb10b0cb0cb1a8cdb3f995000b44000000000b3faf5b26000000000000b1a9a2b0fa05000b26c000,0xa9a9839afaf59ac9abaf5b4eb4eb4ea2fb4eabca33a9aa33b1da57983b1da57a2d9aaadfadfadfadf000000000000000c000,0xa4e983b26000b3fabc000b5d9b1b449ad9adb26b26a38ada9abb059aeb54b44a31a2ab44b04ae3b059a99b0983983c000,0xb1a983b26b26000000b2a9a8a28000b44000000000000af5b1a000b5db64000c000,0xa9a9b78a49bb9b68a4b08a0ab4e9b8b4eb00b00b4eb4e9b4a2da33a9a9b4983a0e9b99b7adfa9daa2aa2a9d000000000c000,0xb26b26b3f000b44a11b1aaf5a04b05b64b3f9b3b26b26b05af59bab44b44a07a308a4b449b5b44a119c09bd9bea768a4c000,0xb3fb1a9538a4b260000009bcb279b2000b64000000000b64b64000b649bfb59a81c000,0xb1a983983ae6b1db52b1d9839fb9fb9c99c9a57a57adf9fd9fda499c69f99f9ad69fe9c79c7adf983adfadf000000000c000,0x90a46001996fd992e2057e5f98b6018b4b97060380cb12aa032b8ba2d9f48b5f47d4e31b06c2da03a917,0xb440000000009cc9caaf5ae5b24b440000000009cbb0b9c394db26b649c4b260009cb9c8abc953ae49ceb2e9ce9c2c000,0xadfadfadf000000000000000000000000000000000000000000935b0bb1a983b26b26b24000000b2e000a1ab0b953b26c000,0x2c15d34000015c01172c8023b1e3047a3a5a2c15cae5b8696cb7173198cac6331958015c9983,0xb45b45000b2e9e9b44000b599e2b26b44b599df9d89d5b26b44ae19e79d69e19e09d39e89e8b5d9839e89e4ae39e5c000,0xadfadfadf0000000000000000000000000009d7983b260009e0b2a9d29db0000009e19d79df9db959b26b260009d4b26c000,0x5429f8fdb3a7d4a8e639001460020b51800aa6a9522a9aa54982ea982cdeaa54751e3a5223a8e8dea8a5,0x9f0b26b26ae4b44000b3fb3f8a5b260009ed9ea000b44adab26b269f59f49f29eaae49efa549839efae4b449f39839ecc000,0xadfadfadfadf000000000000000000000000000000000000b3fb260000000000000000009f1b189ef000000000000a9ac000,0xbcf06b67e006678875cbb4400003ca5a5971e5d779677e5dc8f0e2a9d48ec7a3db5334009983,0xb26a7d000b3fb3fb1a000b64a03a009f7a4eb26b449f6b26ae3b2eb59a70ab09ff983a4cae4b05b1ab2e983ad8a02b44c000,0xb0bad6b0c983983983b26000000af1b44b44000b2ea75b10b0ba5c000000aa6000000b5db0ca15af5956c000,0xaf5a09af5aa1a08a9aaa0aa0a08aa1a0aab0983b4eb4ea09a9aadfa9da0ea9daa2aa2000000000000000000000000000c000,0xa94af5000b26b64000a0ca12b5daa8a9aa11b08a05b26b26b59a11a92a06aa9aa6a88a0bb44b5db5da0faf5a07a0aa9ac000,0xadfadfadf000000000000000000000000000000b0caf5af5b26000a0ca0d000000000000a04a05b26a12a10b44b64000c000,0x51eaee5abb9266e4974ca613895b97152d97cca69231da954a3c9aae802bb5daed4e2f5c9983,0xb59a20a16ac2959b26b5d000ae5b2eb2e000a25a23a15b26b26ae5b64a22983a17b26a24b59adeb5db5da1ea1eaa9b44c000,0xb1db1dab7adfab7000000000000000000000000000000ad6adfb26000b59a21b1da81a44a44b26b64000a13000000000c000,0x5af6bb4adcfad1671752aad5972b94b6e4a8b94cd4ea9e5f2d597d5700397cb8baaafaaf9983,0xafcb44000000000000a34af3000000b64000b26b04b21b08b08af5b26b26b26b05b2eb26b05a35b44b04a29af5c000,0xa44abeabdabda6bac2ac2a9aadfaa2aa2983b52a49a9d000000000000000000000000000000000000000b4eb1aaf5af5c000,0x5fd26e0b6e8b156f4aa0747830fc2bb5dac400001c60086429ecf6cad039600bcb8b97799983,0xa6fb1aa40a3b000000a7db05a46a45a41b04a45a62a3cb22b44b44a7ba43b26ad0b64b5db1ab05b2eb59b2ea3eb44b2ec000,0xb1d983000b26b26000000a4a0000008cda62a3da81000b04b44000000af9aeda3fb22000a97a6fc000,0xad6adeab0af5b48a55b1caf4af5a51ad5a53adfb4ea54983b4eb4eae0ad6a9aadf917b1da57adfadf000000000000000c000,0xb0c000b2ead7af3b26000b26b64a4fa4cb26b44000b59af5a4db26a52a50b5dad8a5ab5da56b5da59a58b1aaafaf5c000,0xa9d000000000000000000000000000000000b1a953af5af5b26b2eaffa4bb1aaf5b26000000000b05000b5d000b64b59c000,0xd5bac0172e0c29d8ea72c6e3971725c9e10871f2dd3097b571d0e2bcc32faee7ac7de31f9983,0xa7e000000a94a70af1aa6aa9a92b26b05a7aa97a7fb44a7bb64b5da7ca76a69b44a9ca5fa77af8af5af5b59b44b2ea5ec000,0xa81af5af5af5000b26b26000000b44000000000a5ca5bb44000b59000a75a63a61af5b26b46a7db64000af9a6aa62a88c000,0xa8db59a89b5da91a8ca90a9fa9ea8ca9fadfa9ea8aa8faa1a9aaa0aa2aa2a96a9d000000000000000000000b1aafda3dc000,0x894576fb79bcdfe72adbca67528004e26934ebefe3111dbcd6572deaf54001400498011c996f,0xb0b96f000000000a92b14a5fa5db26b5d000000a60ac2b63000a94b64aa8a9ba92000b44c000,0xb5db5dab8b1ab26af5af5af5aafab5aacaadaf5b1ab1cb1fb1fab4b1cab7ab0ab1ab6aaeb1db4eab3b1db4eadfab7000c000,0xb49a44b5db21af5000000b2eb19b3faabb22b21ab3b24b21af0b26b26b44ab9ab2983b26aaab26b25b24ab5b53a90b26c000,0xac3abfabbac0b4eb4eabeb1db1da9aabcabcac2ac2a9ab39adfb52b1b000000000000000b0caf5000000000000000000c000,0xa96beaf9e0a7a5393e5f935de86eaeade9e9662685c00002b788e1ea226293e6396e5b0022789c00a8a6,0xb22b2e000935afcafcaedabdb26b60b44000abaa85000000b21b59af3a9c000ad1abaabfac1acfaceacbac8b26b44ad0c000,0xae0ae0ae0917adfadf000000000000000000000000000000000000000b04000000000000b19ac7ac7a82b1aafdb26000c000,0x8c6379ee7ba66289be998de338ce7b9ec000026f8b400002278aa328ca349c69da76718b22b8d235a8ab,0x8ab8ab8ab000000adab11000000000000000000000ae3b2eb11b08000b21adbae5ae5000ad3b08b21ae1adbad4ad4ae4c000,0xb2eb2eb2eb2eb2eb2eadfadfadfae7ae7ae7ae8ae8ae8ae8ae8ae8adf000000000000000000000000000000b1b8ab8abc000,0xb26b3b951951951b26000000000000b44000b26b44aeaae6ae6ae6b26b44b44000000ae9ae9b44b44ae6ae6ae6c000,0xb1aafab08b5daf3af7b59af0b01b48b18af4af1afbb0badfaf6a9ab1db00b1db49b4eb1b917000000000000000000000c000,0x5e03ac348e7ce006eece024287014a4ddf2b2bd2b33028577281050a7aeb,0xaffaf5af5b21000af8a89000b5eb5d000b62af2b0ea9cb1aa64b26b05000b04b22b64000b02b16aeda8d000000b3fc000,0xb3cb2ab2ab2ab2ab2eb2eb44b44adfadfadfb5ab3ab3ab39b39b4eb4eb4eb4eadf000000000000000000000000000000c000,0xb1bb1bb1bb1bb07b3b95d95d000000000000b51b51b44b44b06b06b26000952b44b44b2eb2eb2eb2eb26000000b3cc000,0xb21b21b62b08b09b0bb0bb18b59b0fb0fb5db58b1cb1fb1fb1ab09b1db1db1ab1badf000000000000000000000000000c000,0xed650019fc4c2f45a2d0e87ad75eee2b47a3d065b0f87ce800019b006af379dc6803118a9983,0xb4ea08983983000000000b5eb0c000000000000b16b15b11b62b0e95ab26000b14b39b1bb1bb26c000,0xcbfbd7af5eb3c7cd9e860c18307af5fb28000035eb9dab56ad5366807adf,0xb56b56b52b52000000000000000000000000000b1bb1bb1bb1b00000095e00000095e961b5db29b28b26000b5d000b26c000,0xb33960000000b2eb31b65000b34b34b44b53b53000000b26b26b26a9ab26a93b1ab1aad9b5db50b50b5db4eb4eb4eb4ec000,0xb13b12b44b44b13b13b4db4db4db4db59b59b59b59b52b52b52b52000000000000000accb1a000000b32b30000b3fb33c000,0x935935000000000ae3b54000ae3000accacc000b54afd000b38b26b26b38000b35b36b35b37b37b54000000b54b26b26c000,0xb3fb59b59b44b44000000b26b26b59b59b3cb5db5db3cadfadfadfb3ab5ab3ab4eb4eb4eb4eb39b39adf000000000935c000,0xb42b42adf000000000000000adfadf000000000b27b27b59000b3bac5b5995db44b44ac6b3db3d000000a72b51b51b3fc000,0xb5db5db26b26b59b59b59b59b46b46b45b45b46b4eb4eb4eb4eb59b59b5db5d8cd8cd8cdb43b43b43b42b42b42b42c000,0xb59b57b4ab4ab48b48b49b49b49b49adf000000000000000963963963963000000962000000962962b5db5db3eb3e000c000,0xacb000acab1bb1bb59b59000000acba97b5db5d000b47b47b26b60b4cb59b59b5db5db60b26b26b44b44917917917b59c000,0xb26000000b18b5cb51b4eb5db59b4fb4fb5ab59b50b4db4eb54b44000000917917000000000000000000000000b3eb3ec000,0xb55b5db5db5fb5fb5db5db5fb5db5db56b56b56b44000000000b2b000000b62000b26000000b40965000b62b26000000c000,0xb59b5db5db49b49b49b57b57b57b58b58b58b58b58b58adf000000000b41000000000000000b26b26b55000000000b26c000,0x967967a9da9da9da9da9d000000000000b5db5db49b5db5db49b60b60b60adfb26b26b49b59b59b59b59adfadfb49b59c000,0xb26b26b62b5cb5cb5bb5bb59b59b61b5ab5ab5cb5cb63b63b59b59b64b64000000000000000000000000a9d000000967c000,0xb67b67b65b5eb5e000b5fb5fb26b26000000000b2e000000000aa5aa5000000968000b63b63b62000000c000,0xb66b66000b5eb5e000c000]
private def oveSecond (i : Nat) : Nat := oveField (oveSecondData[i/32]!) 12 (i%32)
private def oveWeightData : Array Nat := #[0x85100d1104020c001229000000006b4c04001a09020c1e3b52310f5b47033a28800,0x86204c4080125e2cb21083aa6a461b948c50a451271a40cb56cf3c72700,0x7938701b4322623418780563062a2f12873226257b2300423c5617001d091c04801,0x11291001121b0512570736220a1b04373519001d5d320a5f538937151b5c124b800,0x5040230237001292f2e1d3604410b2000030f005e0f89105f1828083c360718800,0x3214900000000000000000000000103d4b9b67abdd32000000024083700,0x510774b85e2a0018600,0x163c5f84002c586309000001005f365800007500000000000000000000000000800,0x3250872c05087143163d00490500062c00258c215f00092c801c5c0000000000800,0x3000065784085e1c3c002c158f2c370a312101550c550f0c00138b4305058601800,0x180000570704610308031c45892c03053e632c13122c18012100002c010a0d16800,0x2a001b005c57024a100a64000c130d4727052c000000210d6d81714358130551800,0x50000000000000a00000000473c0d426b1b31108b40356a05697a00800,0,0x12444b6720857c1ff162c58b089e011db7c8f1c8801203cace51e380700,0x472751834a00430947472c72365e7900208b605747680c4f0100001e05283631800,0x4730b102c51060607014c1555264709476728060005200260650f8273476279800,0x47405c00522a781b464a4a8328173952722c230a5f7a490a3a7147008d150673800,0x364291e5e5b18515d052d8a2f6f2c2c2c2c2c0200040d8335800,0x366fdfd34689fc3588d000a6a81a00000000000000000000000000700,0x4a7914000a2c0431278f2b1243017c6579041e7c0005020d0e0e0e0d0e7e36800,0x1012190b0500054c1528204d020000390d004d0c6006120c7e2b79830d0d2762800,0x53917062c06271b7e42624d11820d550d28010004055c090702180900000614800,0x304200e0e0e0e0e0f1528312312207804234814880e084e6f2922800,0x6b060d1e8a0a1e6b002800000000000000000000000000000000000000000000800,0xa7f6210106e6b0917884300101043008d8a135c005c4d000d8a508e00131e18800,0x1e8e491e63060f03700d1e18007b6e030988361e7b8a000d5b6b531718858d16800,0x3a03623c18000812048813005c390b5800007f03005c091938632c54536e0a2c800,0x283510e092910020f0a001b14267a5b67181d2103800,0x6241149005001253b054ec005d80600000000000000000600,0xcc408812584012c24b160b0d605000008000b0986584c9960000000700,0xc05edf8627e85599001300c42ae30d8b063744ad10a009ac2600005700,0x803010618131305053e43052c122c130413000000642e583d8b5f0909433605800,0x9acfa4c2934eb000600402e40014013071d38558001800b84190700,0x410405c000298812c6f08be00000c84c0ef000028500142d8700,14943744,0x80bc4816cf82828e3638d14240748c014408e340408c000000000000700,0x73846e09462f477439472f2c04360673747600722347002f40433e2c1e393e0d800,0x837990ca7850d5e17a065003e79f99430080497288dca02880f8a57700,0x18732c2a2f020f0004050a60058a671d76061027461b31643e0d40466f73382b800,0x80000b00000000000001c878d28700,0x3d5f9803d6c4f612272434f93b016de79bc0034481bc2868012a0282700,0x1e1c781b0d7c317c65351951081e09060d0a607904518f57494f4848065e09800,0x40009105c0d002a45000065461b7c49827974020b1000002c0d062400056000800,0x11e87535f361867090900570000000d0076800,0x300a8d5a2e83185a00000112008a810018160100000000000000000000000000800,0x8c455c2c8d5c0c8d00058d5a5c158d0000878c8d000c00098a0f6f00000d4305800,0x38d8c060a0c21007c0a8d058443210000000d8d004700511f1f890a03438d800,0x42040c547a00000008211f8d8d8d51740d150d610a000003288d23800,0xaaecd3628a8072009390004001008e00000000000000000000000000700,0x2a72024f7268000172001055760072144702004f4747475f2a02008b76020400800,0x200000c1a55042e070200838729040070811c13361a4e4e00152b145c673637800,0x2f21819d800000051000014700800000401403320015d54bc480700,0xf1689406a5c182d160f2068000d005c8d000000000000000000000000000000800,0x185c00880f0e0068686a0086898d00002d5c0c700000018b89616a4f0186430a800,0xd0000000723401500004f61053c7c8d780c00215c00010a0f0f700001800,0x788826284b154461740005180215134300001840212f3764686b800,0x9a0828005b7f00a63f92800000000000000000000000000000000000700,0xb0c2120834280cdb40239a0b300cd340070e1c382da1468d0a146e6700,0x664d877e12000d7e0d05664d056d05020d0200000400004d7e0205280c0200800,0x53200f7472056f0222664d071980000505006d006d020d05020d7e026d6d0002800,0xd00007081300548000200005b576d000d674e001b01084e096f050400002841800,0x51cb34c2a0259b10b42800b3b792f15d184196da84243410500166e6700,345788446464,0x89000f05538415818d550a8d4d27810018160100000000000000000000000000800,0x478d0a8d0a008c450e835368818b898c8d005013011f5a5c2000050043530086800,0x8d8a8d00230d0000187c8d450108433c430a8100008b0c0000012c8d030043800,0x5230000000000003c00007951a00045700,0x868d00880c89686a0a6a052d0104868d016a008d43208601685c4001160d0000800,0x200893c8d7c2d0f0107230c002064010000130f0061458d000086002d610000800,0x4500280000000768008d004300040000402f5b0000130d00000000006a218686800,0x5c000785cbb6008681728b4b849e0000000000000000000000171837700,0x3a2d8e7d281b0900000900002e3f2d00080028852863006e287d7885006c636c800,0x2005c00000000782d5a00138c000912000002007d8d2d7d001e0902097d002e800,0x47022828280c0000000000004b1f4300000000196d8e00800,0xc000378c3e00000b4006dc19bea80010c00ab8368002c00000700,0x653000d000081168a0028000c0012000000007c042118008a002f235a001681800,0x225d4883030c0000180000003c810f000000004300456f0000800,0x270c002100006f000c5757552c55150c5857308c00570005081c3d0000000000800,0x60000032005e02380ae8c6557b5d3807e06ad51020e08015c60c700,0x7618190800170000009c00000011090140300700,0x53700370000278384373c811c1f2c372c3c0d00375f00000a50748a20000000800,0x334550000d83451c83813c203723061c810023395f2c002f00515f0037003700800,0x3c5f130000000037163700450000001c330081377c50800,0x5100000e83186f2c001f1f00200c0a1f0000001f0051001f0005004318000000800,0x4a18498d18841f813664230f070018543400008c0000008c1881101f00001f8b800,0x30000001f0058186f5c0000001f2800315183008c00001f1f22181f0a0000800,0x1e090000000000000000000000000000042781000f0c83000008008b454006800,0xd80bfa8500142d00a16ad042047d05f766c1000108040366cfa01443700,0x454400190209001200311b8d026c022808096c7d006c6c6c0014857d020900800,0xcd84800000000000000004a030001fc164000367d0000c80fa03602700,0x6c356441196c362e006c000972003f79478e394736382e054147004300001e28800,0x47067f020800638f0002002c0000361e0f28002c726965473f79007d022c856c800,0x141619800000000000000000000018c400000000008e256000000002700,0x81181800008140008c2000000051510586431f0020810000518b000000208300800,0x8100000e7c540012000000200623008c43164a0084002c204381815100180007800,0x461822000000450000050d57000800648c1700008a000018268b6f0c800,0x623e31236200233e287948493e8e1e6200236223000000000000000000800,0x6200073f00003e4d89180aef810fc6f98bec4c5180244228000f8062700,0x864c00000000000000000012c0000801f0000000007c032007c8ed80700,0x130002030200020013130013027b1316090000121300121300187b8813001209800,0x1d00001d03874000880413000000007a091309006300161312000c1b13001204800,0x8c6f8b058d000000000000000000007b72020004006012213a0f870000000000800,0xc4a69006f0000000c0c0027218b270c278d000c5a550c270c30000c0c002100800,0x270c00000000007c000065008c2181212727150600210a0c270c5c270027800,0x1f00001f001f00030a8a50001800500000000000000000000000000010282727800,0x81004300001f1f38187227001f0000001f005050001f69008a008c005081800,0x1f3400000000008c001f1f81001f1f275103000006005c185481232708002f41800,0x3100000f0000001f000003000050008c47000081580045005000800,0x1c818b451c00514545008100080000300c2c1c812705148c001c3d0000000000800,0x40000a8132230021650000515c004a6f000c00003e1c002f006e0000818d45800,0xa000000000000000000008c162c50c22280ed140000003780a001fde700,0x800006f18500000008a8a81006f0050001f0050000a000081508100008a0050800,0x8a00818a8a8a0681008a0021003c18000000418a0000816f6f272f2300800,0x726f6f6f000f0000001b00000000000d007c0000000081120d000d008100008a800,0xf49bf2600000004c988260000026000130000000000000000a7b05700,0x80011bd2600800b04c980ae4c980e2400165000013d2a6be4ae4eb93700,0x5857000000003d3e8c0c3e00007341080013151300130081800,0x4230d160c2727270d0d000d2713090a09000a0d000d0000098d0d0a8a430000800,0x7d230c0962000021095a0d0a16000a13370f090d000d5c28000a160900810512800,0x1f508a0045270d1f00001f032e0a182700000000007427000000000000800,0x233c5c7f0d8181818c11001307478c001f000018000008278c27818c00001f00800,0x27030004818c580012070300001900002727810b00001f1f1f00001f00061800800,0x887b1b1300000000000000000000000000008100000000271f0042548c0000800,0x7b7b7a091213090413887b16870000160000007b7b887b097a007b097b004313800,0x7b7a000000000000007b03090900877b88000088097a0088130013800,0x4cfe361acd12244804500ba280b75201200000000000000000068000700,0x14256695f0300000005200202d709beb2a05b8000a40420028300700,0x6a00006e00006c00003636000000250000027d006c448e6c0f00000000000000800,0x475f2d19186c2644007d08360000004143002884197d5e7d0000000400000000800,0x7800006c00282500812d00000063896c24310000006c0000006c0009000026800,0x27126d058305121028010101070f53270f5371270f0100000000000000000000800,0x15db87033478fa600000009c78524a400f0010e78992b52c2a0000f700,0x4000002491e80000800924001000400100000218000000000000000700,0x8002802438402000200128e0876283100020200022828002819020002280055800,0x367350a0000006ef000000000000020268000003793d0f700,0x886df942e89a8640022ba60d540bf6c0091224980004d5840010009700,0x133f000000000000000000002f35191a00008b0000642840000002003a000c800,0x400001001b807e0003f00000000ca000cc0891127efc000b44df80700,0xf2111dc2128c2e3e013e9be24f805c60000000007c44000137e0063f700,0x4040000005b18002200053500001900180f001300001f831f133800007d060c800,0x40820b9b8000000d7bd057d84008102098800b098500140080000004700,0x8004800000000102000000ceb3900030dc009e3ec0a000007c14041700,0x181082196fca1744d90464027af606a05fb6fd0a1420d500063e4aa700,0xbe2498008009ab08004800000000436dd7900009000131440754c180700,0xb60301a136d08000879c074027ee5084240756d0ba0430200366cdf9700,0x180005fc4000414e4c008d2000132770000366c00000000000001a99700,0x3f006222085c516e817a0800000000007b00002700000000100e0047060000800,0x5d42008d8f7c010a005d0a01372900240000005d0000000000280c1200000006800,0x253e29013742000000000002298e013724010200242803580a37290024244d01800,0x50c42257d3c4cd0000cba3e3b50c09b3300000000000000000400033700,0x5b5d375585003651280c00000019000000200f000012000451000000800,0x393c006e8d00800]
private def oveWeight (i : Nat) : Nat := oveField (oveWeightData[i/32]!) 8 (i%32)
def ove (i : Nat) : Nat := (oveClass i <<< 0) ||| (oveFirst i <<< 11) ||| (oveSecond i <<< 17) ||| (oveWeight i <<< 29)


private def extsField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def extsClassData : Array Nat := #[0x242f533c1492c5408b51a8314bc4a65127825d63d1385d7e9742acd3a792badcd65b08004927,0x50e7000d9ecb61afd76b757aad4e8f45a0cee6b2f93c96331184c15fef57568aeda0c94fc926,0x535150be292a51ca44d047c74e41bf9e9c9406b89817970020161594b60b0703c231,0x28d247759200d49a4b244e31288c3a130481c05fefc7dbe9eaf4793c5c833168a848070049c7,0x706feeee6d6c68e86764e1605cdbdb5907f574f2f1004f37aa4cc63ab9b8b841c1eb,0x5e411e741d170ab4d801c4808fc4a0e188e3ddecc65723cf4341122d283291486411c8dc9b7,0x14080d0100414090403c1c003d9e8b803beddaeb74b9dc6dd61b0572b358a7d3a9b4aa3495c,0x3424f2082b6e1706793664b1f7eb523d1380bc2331777b75acd567b2e251184bd5d2cd004962,0x5d1a8ca5f34524a263a58089400800054fa34fa497ea74ea7337be4b6592b845e647228bc923,0x7be77d73c6fb6985f6d54cf2450c0fb8caeaa279848e20403299,0x3ca12f84a249ae8882bb1d0bc48a392c93482f942993fa8930771399400871529c45118849c8,0x3ab32b224300f877f3efef6eed6cec69685f5e5d5cda570885810077767574f5c1e9,0x42e130481bfdf8fb7d3d5e8f26f371a10c6c359010a51a49ba9486bce0ce9038005a2a5149c7,0x776a46415eaf2640b4c6a4f972f075ebe9624e00ab88af8a8a07840079f978f7c1e6,0x240401e0da0cfe3f0a850000f1a0c852248e466311689c4a110780badd4e8723786f1a87c9bd,0x6f6d22ee68660050aeec6261e0eb5fdcda2f2cc8b128a3ebdf5edb58bb30a33c41f8,0x44630fb7c10988b5592690a3f1b09c341f0100249228f46225107fbe1e2ef763add2e891c9b5,0x50cdcb4ac746c4bfbcbc3bbb393836b4544ed2c5d147d03d198a9292070054ce422f,0x44b7c62bc82a078038b834a23d2e2da341bfb729bb3936a6b02d2c287775f57441eb,0x4ac9c948c7c7464543c0bdba38b7b6353433b331b130a81327122781a600250cc23a,0x59f3eee7f36ceb495cc03cb0f0e25e5dca333aa784860075f574f473f372f27141ee,0x45625077f9093485230fc6c411386c3e100100249239147a391b8842608f3783add5218bc9b5,0x50c589b413d4ce5041bd4f409f878700524bcb3fbf5147c744ad8b20198ad44ec22f,0x47a1d047cbe1907c0948a2f158641dfeb63c09c32021f8c83e0092486411f79bc1d8ea73c9b5,0x3b3a523f403b9a9039370bbc1c8cb88d07959356d04aa5058055cf49c3ae1b06c22b,0x76ed7675ea69f271d7c7c150beb67b706f67e3dec4003f88857ffdfc7bfb79f2c1da,0x78250a04c14058d4662f158843a14e670b81bae959ba15e7f863c5cea6419f8e11886c9bf,0x221c697451d0e4c63aad144aa4e41204f862ac550368541e0b017fbd9eaf176ba5d0db0049c1,0x44e2302763a2130881bd5dce3240cc581f00492431f8ec6de6ec75399cae45948228a54dc9b5,0x47413b6735fffa795248c2392e51b3adad29878077f16bef6d6b7aeeec6a8279c1d8,0x2953b0f813fdfaf715a78e23116074120a12878011086c320f056fb71acd23f37912d33ec9c9,0x3a3654cf51c5413c9eb852c8d142c1a90fbb9b3a982f13833708005248473eabc22c,0x3f9faf677b982f1982c1204f2753a47a3045a502088220d83200914823f1d8e44a1cf17849b7,0x3c1f8f97c3a633158937db89d7fb8d48e250a8206ea559da15018b425fd1885c0a000086c9c0,0x4f0068e7665ed3afefef6cec54d453d2afa6cfa6202eae635dda33e3dd68e4e1c1fa,0x4ccc4bcb3ab8b5b531afaf341604000f8ecd47c548ba391f86bebe12c03db6b3423d,0x3adeaef76a8000c759a4a15077e3c436b83d9c213037f3d9cae086c15fef273b787c1a8dc9be,0x1ea110780bcdd1228e4662ef076ba9d0e0712e15aa83d43e010880b4964980021d11187bc9b7,0x77f774e461313b7a60cd2579f36cb56a69e530cb41bf8075f471e8f27166e64241e1,0x25c4703803d9d6e07dbe9f2f46fc0a02ff7ab8dacf2773a9cad86a8d8440f0701401158749c4,0x1007775f573f2f1dedd5b5a56acc4af28a0f670cec1cdbe3227f06be64b403941eb,0x271ba7f59a5cdf148441df4ef86bd5e8ed652898cb24287200fd7c3a9c6d80d0401e001749c0,0x3fbdbbbb34b353524e4b483ab936b4b452d15049cecdb987b251ccbf070003b74233,0x7271f0ebdbd3b26a3c259dc0aa4b1fc1bd2d6d6ae8e7e05f5dbb6564e4578062c1f1,0x10c53a31a8c3b7b7338b019b998f80803bb9322ea91486c2c1403d38adabc9c84246,0x405d6d06431162ff7ebc9f6e17bb79ecad451a9365b33b0cd257001fcf2f46cb39deed6bc9d8,0x3f55c3fdfc796c4cc8fb7aef6ece93aef7f776ed0073f1f0efee75f574f46863c1d0,0x4a473c3b42c13f3d3cb5b4d4d352d2514ebcb7c03ac1362624110db402000c90c230,0x4c0101803f126887d1a95a9945bcdcad866b29dced6ab8dc4e1703257ef277ba5b8f478c9d8,0x74eef9ed66d4b5ab2cabf86ae57675bdbaf8ecec6a68d37270ee6763de34800941dc,0x3bb63ebe3dbb342eb9b93735b4b24bcac9c72faf2dacac004b3ac610409b8448c242,0x413e3d3ab65450cf3c392ba85251cb451e869a0897000605029bcdcc49c0ca494231,0x3b714113180801c919b0b4841bc38a8a0970129a91c1bc544c4413a36b4bfbf4236,0x4c000d511e976cd7a5c786fd35ae58a942162c37e7c78d07ffefbf3aba5a,0x34b13f3ebd3bbab830d1d150d04ece44b69b024dc544241f87a3a1b41d003f3bc236,0x414d4d347c53c1d9d3b9700ba990229a61c112a2481802aa69387c9c948c845c22d,0x73e2b883531000cefef6eee64eded6c6be4605fbdbd39a7766a69e66562de7c41e1,0x60433fb3a5f9f978726ecedf5ac778f0f7716f653fb0c26fe44fcd48852e002cc1e6,0x188100087c2e150782359148866a1cc685323edf2d5683ddeae26d360c29e352e16e914249ca,0x392465605bc8c83fb330ae51c9c240b1acd0cd3ebe3ca7ce4dc4b983004ac7a6c1e6,0x2dcec7438196230e53284e26a894420f05813a9c2fb7d395b6341800202de6eb0566a24fc9c7,0x151300803e117a6b55534bc7c5c56f65e2d2d24d3db83675dad7cec846b1ee56c1d2,0x27d12853a3412e8a361a1aed4473fdc8a5411f9771187c321506602d4d2c14089042060049c8,0x5550d055d3d13890904dc241b94a46bf3a4d3bbb2616950043bc34a41f1b8ab6422e,0x5200911d079901cb483c3ac13fb6b5a9a69d83b997139290bcb51f9c12100200422d,0x53ba9493b613014c3d3bc240b7ba1a02ab18119e84bda09d110319805754d453c22b,0x2247a3a1b0b83000864662f1689405e2ec82b9190ba571b91adc43214383a070c6331489c9c0,0x55d4417b796fd94744f14b4a946dcbbc8657c21c9b8f8e89b9b819070684805641be,0x49bc3a5144c13db92f2ea1a12e261c86a8250c00504fc639d756d65551cec23d422b,0x37b633d1d1504ac9c03b51d150d04eb71411328382b18080168407060d04cdc54236,0x4636181039b716804f4e4d4ac9c8c8453c384238]
private def extsClass (i : Nat) : Nat := extsField (extsClassData[i/32]!) 11 (i%32)
private def extsFirstData : Array Nat := #[0x2b4a12767493a122954da593726482512890942612c937928924f27425522f24c25944009001,0x9d09d0008d93653ce3653ce3ce3ce36536517716018a1a91611641641a916016118a14812512514805505504e04b04bc004,0xdef40d011b16061b5cd635ad7358d6b5cd63581806c0800cbb040100441100c1b0600825c0100005a092,0x4104104109c04c04c0450450450458783b637b37b14a15515311715815514a11715810e156124003000003000002002c057,0x55d1155d114d9364d95744536445573d0f43d0f400311c4711c440025c461189725c461184b12c40a058,0x75ed3190d804305e0530590060fb04b31811713d0013181171170a005205c04800800808b05000087e3ba4ac4ac3bac051,0x100101000100101000100101000100102f02f05a0009423634f73cc63840516816316e1a916e1651a916a166146123c006,0x8ad3dd7c8086818186d3dd7c80ddd3807cd3dd7c8086868181dcdc8d7d7d8d008016,0x94160a2582d9489c4e27800b6000000144924928a549f4c2613f294f329949e95261309f9001,0xaa685aa686aa686a17deaa4520ec3e2103b0f88414852210840ec3b1483e0f823000000002308c23a129,0x11831911805a0580d90533191181180a90580530510530470a905105805305805805100005100005100005100088d4b7c050,0x8c05108c0510510008f83bd3bd15a15a11c11c15c11c11c15c1090d90d91090d90d900a00a00a0043bd3bd3bd3bd319c050,0xbc8ecc8911a5aa4488d2d52244488d0cf19e33ef20cf1e41258784f09e3c824b0f21cc3c8700000000000047b05a,0x3ba15e0520540d804a05905405e0a205931811713d4ac15e11813d0a000708b00808b0000080010010009325ed5ed3bcc051,0x6300300a00a0590590010010010010030080000000089345ef3bc5ef4ae31a11c1251210fd0fd0fe0da0fd00931a13fc04f,0x61ec40283ba21c438000cf07ec488810f22128c8710e2aa1302609907e1241eb102aa4508710f1041342d858b05a,0x11831911811800709805d05d05205200900700900000100900293338238251922a22a1b51b50d90dc0d90d90fd0d9319c050,0xb3a91d238d2196348698cb11022c4408b1102b0560886d8335b60cd6624399890e0000240780f000025640c7b0a1,0x940430940430940430000000480480480480480480480480740740740740410410410410410410410419285e35e35e3c05b,0x6db1a46411122244464111190444888c8222444570ae15c2b8570ae15c2b8288000a2000288000a200028800b09e,0xd55ea1141185ea1141200980f804f05705531529413a13a0980550880880060060008893b74c13b74b34b34c13b74b3c054,0x2982341231190070520550000090080000090020010020090029333193195ee5ee5ee2df2df2df0fc1090de0de5ee13ec050,0xb4c3580309100ab44683731b845d688d003200022012b4c341280d31ecce88b8d41b81540681501204abe0d8b098,0x3b929411f23011a09705e0053b915611811412011805305200600600600300600000092f5ea5ea3160d50d80d50f90f9c054,0x24895dd8d65b8b60300a248b5028c204c133081304c12066d2344d114c4504ed2344d144c5c03000a097,0x11912c13f2e02991192e019e0b405b0520a404304651a11d12311f0da0da08d00006300a0059345ef3833c55ef51a22bc04f,0x80000010010000080019323185ed5ed31931827a1080f10dd0db0fb0520fc0520521171170d804304808b059381119c051,0x228d71245814c532845127c5313046479178c8a11445101d16b7a964f2354652257521b791e35c00a052,0x2982e01240d90d92e02df1242980d90d90000020090020019333bb5ee31931b0fd0dd0dd0df0fc0fc04e31915f06105fc050,0xf853160d20f71244556270531285814c910f04a14c58008024451544515b6630c491155911002d8a057,0x520524ac13d15e11f1180070610640080010000010000010070078535ed31c3813810de0db0de0fc0410d80540db044c051,0x12a245b99176e645d2b0b50242796a2505a23d8680570322440089100215c0004b16802c024651a245c7b05bb098,0x1b511d11d0d90d900a58d1b511d1b511d0d90d900a00a05105100a05100000500400a9333196994ad4f72ee2030dd0fcc050,0x2db2941202db13a92f3c03b910510504d226105056105056056226226053088226230315114114315114156114000589c054,0xcf00022a28e11610f0cf08284b30f5e45e40f20d40f20d40530500f208205005705713428e1340571341341342d511ac05a,0xca3512d34af54c9584a8b412c2785a8c10240700d009024b447b0d05a23d86805b0003514b80952e37128091b098,0x11915e23323306300a09b05b05422b11b11912c0080a40440541b62d319e2e00fd0da19e2d31b62e00fd0da000008934c04f,0x4828f22b1942d60f3a9c5e53bb3100e90f41000f40d30d008304e04d05727210f1112210a208305900005705331010fc059,0x774d997cad21a816c2e58319e2a426b0f2684382e2945c8b902d0a90ae140002e45aab914a28e230b5515089b05a,0x4c00711723616115e0d81172df15e1610d82972df1232de0fb0fb1232971242de0fb0fb008000001000008001aa4318c051,0x7aa35ec3b931733c3b90fb0fb0db0dd0fb04909c08a05805b31713c0a10510a105305d05b11613c1190a104c046c052,0x943682209b08616e571602325808cb5f2bc4b0960a20a42783086901a4909392424e3686d00000800401803b04f,0x2962911ba0d70b30b38ea33954625a1bc0960b40960970b45a55467d72975a533909200009063311611600a008020090c099,0x62379988a971ac3d4222d70a422c2e85910826c258ab08c1489b2e626c4849b2902ae2108891b4583d000296b058,0x244d70da0dc09731c11b0e90e900f01306106000e0000392bc0e00e40ba09702301429d25629e0e30e2097097a635acc092,0xa9c1db0d60e90d709437968d2216e11fa5861133790aa08304009104803a0f404a05100003903a1111560d210f1fa10fc059,0x1a0ac1612cb4ed33f844111e5b82a48ac6302866b822b57aa4002dd465196799eb6edbbfeff3f4fda04f,0x2472880a508f2470d02972882a808f0a58c832b3074c24c232b2ab0890d40820c30840440440350000b200300300f035c0a7,0xa9c3103b204a04231005b09a04404510f15928f0f40d01352e513510f28f2961590d00f42961351352e52e52f6c059,0x402b7af311923c2c4260690b6228ae95d1b25748b04c0a32d4af15d2bc4744f921248484920fa1f41a004800b052,0x2a529624f1eb2912a529609d2912a52961eb24f09d80d37259f5a50900960b30b40b40005a50db3720431bc0630166a1c099,0x1882f11d87c0f9ff95e31354c2042b056626af0708e10080101b0070000bc1780005e0bd48a824769f51da7db0ad,0x128981284a2604a1280200802008d03624f2405a168000005a16800000d093cd03624f2409093cd0a099,0x9900100003a0074530fb0bb0fb0fc0da2340b427b19f0fc0b70bc0c60990c11822760c208209807da2b2b82b82b878dc0b4,0x8608624c0d128c0d0245086086a523685713684a479e11008c00000762924510c04c04e00004a0490a900001728d1b0c0a3,0x802b56d595a562641e078981284a2604a12851144080205a1680000051144080225693cdaa58dba099,0x6006300706006300700913c2ec13c2442ec2a82fd2a83012fd0fb0fb0510510510516e71251e41e41250e40e4a8dc052,0xdf09109104f04f9313b93b91611610aa0fa0fa09b7ef15e4b515d15d2f809109106815e2dd0a10a109c000062000062c052,0x62000000a8e58c78578558c0e10660660e10660660640641241210fb0d82fa1241210fb0d80560500500b20b208b08bc051,0x12848b7cd83f0a22884a148521209c27061150611509c27054184541849c27062188000009c27062a051,0x9b05c05d05d05c6e46e404f04f04f04fac44a74a71592da1120f72da1121590f70000030032da0f70d309d09d04d04dc056,0x408000011a40a4a4de288a216459120484a4de378a2288481644816716280a01886118462c58a0a051,0x8b08b0920920e008b08b0920920e30e305e11711705e05e0690a28e44ac4ac4ac4ac0a20a00620a0062000001008001c051,0x78c78c7a8a462d52d509a0220220da25624f0b32560da24f0b32560b309005a0040020002560900b305a000004002098c099,0xed200000000000000002754ea25c4ba754ea25c4b84e09c09c1387d04e008010270fa1f40100200409c13802b0b5,0x72908600e00e08600e00e27d09f09f27d27d09f08900000004100700702f02f08403603602f02f036036820771771771c0ad,0x6000000700000000700015dac64ab67a5ec1162962962fd0d70a10a10510470910e20680680090070070068c5784784c052,0x1445114601804fb14451144fd1bc6f010fd1bc6f01060180070000001c0018060000000000701c60a052,0xc30820826850c30c308208203a03a00000003a03a00000003a03a0000000bb19f19f0999e668668668668619f19f099c0b4,0x98098098a7978c78c2332330fe0fea2a68468468468407e00600607e00600607e0060060000000000000000006840c2c0b5,0x15a87f0000c55a87f062003f47e8fd1fa05ea9d53aa754e89bb0b2]
private def extsFirst (i : Nat) : Nat := extsField (extsFirstData[i/32]!) 12 (i%32)
private def extsSecondData : Array Nat := #[0x68b008d1c740c378630472c383f0009507d433884718a213c7a7c57895582800,0x27040b00142b44123b426c19166d74735e84556e32857a3883533f7155717c8a800,0x817e7d60011c1e790726363300760607454c1b1b7f463676618c794e3b62203f803,0x464d07216377808d0f402a127c4b03101a25210e2602240a1b640d4f0f4d0063802,0x1e4b3c778a220325146b3443671d002c0979204202081f50307127482a7b5f09801,0x4c4e210d201156122e3516073d18573b5d73825d553b880c7b200801515534806,0x758a628f58195f63073d7c6927000f104a7b24511f4c1b041d5f6c668d130e2c800,0x38117169012c7b7e25008453127f16316f2f587c18470f6e834a63637a824a3580b,0x6c71855564008a8f6e8243248d4484718273016470578b45051f3f000935507d800,0x2a71117e4b44525503156c70725381830500546d4c3108848c378271521e3e59801,0xa29397c8b4705037909346828046011312769652d6c237c62791f3926360033800,0x2b1f316226362f147d1c8920651028020c570d401e3e000f3f410284837f4a21800,0x5c7d054c7165548e6002150d40005d472d6529484f6860210a03090e423f1127800,0x254e8385610c171f1e3e54131e73441a1c797b5b0b70891e0e0e008808171982801,0x5f777756243d6d227e115660516a450049644b43198b248a387805063f2c1a40800,0x395c15106d7e1c364e4d2b02157c112252728751516d31366b3a8700014f0944800,0x200b1e6386232d201f2e2c687b1e5c000047738825838b79634828081d302d18800,0x4b4a7a2d825e1b3f31762381042507006c3e1f4d604e6d3d151476810a43122a802,0x8751284c413101097c6089457b656379012d4f09828f11428d8a29220039543b800,0x3091f9e1af1323c296f4686fa3e73a004ac113a9481ca8f94e6b78e9701,0x5532b832769230d77001f1e1802793e0b883b0b361f000606191b63453a3942801,0x4c89605b861f2e2c2c1e717b635c18000000141a4b294d7c8a0c380513274940800,0x4b4d4a0026122a32303d091c081c1343391e7a857b604e821b84883215146e84802,0x76235541350979735586888e04496e8e6339183f265c13003954613383062709800,0x1471900442c49814e344c62060d168a2e28870705828108131c0d8a21708252800,0x6948737b8462898b26705646463473001c3e05010d11674083277d7626570d8e801,0xb1f8480257575001449286f0b0d0524277a388435011e2c1e257b120c55700f800,0x6d28118d5403101d503c6e7057230c388471711f6d201039112932855c00090b800,0x4a204b060b503c1d5c70423a55558d000c2a461e5833588c3f7c36204417512c800,0x53515a0f291a0f4c6f71578021472303430016236a0137293241043a1e35502c800,0x10f18056d20392c202e0f0f892537015c3c006744588f1805273f65355c1b63800,0x9af2f0c616fffdd6550b6e6718eff770400a243212aede3bd4b25cc9706,0x5f6c7d674e396c60024500010a3f264c81793105412e18001a130d690e573378800,0x482b0c1d5a28543a6916708f50062c8249238d6e0812281c0d8a070510827300800,0x42201f4a204b066800076b6a622c5e474f735a632e47725e2a8769625b1f233c800,0x1282277e02843277121a6e82704f0b5650193f697821366e7f000b163b1c5b6f801,0x13677d142b591f36051c7c0a5d8e4666596a28764962862c658c4823163d3100800,0x5b8f186e8d47005d3d8d554601476c562602395b7459361d512738131e312f41800,0x24097b006229857a2c35001083018d3a79141262024922861707217c3185637b800,0x605c8907685d28648a1b6e622057230c787c290385007a360f8980257575024a800,0x40402648631d428832045780210c546c1b29193f3f00371f1e2d1e0f107e6d6f801,0x560a223e46540c6c884e36013948344b0d2b8b4f28818b6d806141112d1d2200801,0x3477a001b3600701b0e73188343166f017a81203d8f0f120249402225032e06800,0x3f4119452e8a62526c1725874b0b06106988001b0b341d323d1b0105070e5272805,0x1f73003e01013948345649111d7a64348b1c803f4125692b491f5d4a050a4466801,0x6c701521131d6d80497e1218268c020b0f3c00206c225220443e0c1f0c675434803,0x3f2a471f1c0b387182205787353771627050847a63111a306f56060115081300800,0x78a380e3a03858d133f34572b72104a040047098375093d585c8122750b6d41800,0x3f212512247d47481003343a1d3a2b032a727a7b2466130604004a8170778414802,0x560b356a591a72170f313f210e6c888440015e5a08347b818b6d804f894f3400801,0x15858f1884088d474d792d63140e0030643d06432e6f5d12014b861773638081800,0x1a63440e1f004a09006278027a1083340a097b12397915220886861707327c73800,0xb250310331907254e6045700b86720f270141502e00365d634207797a645e78801,0xe5170066e7c3e1a25561f120d232d7703418d162b020c00081d3f24081a1d34800,0x81296c1a0963192a00001857398c3a646e612e11394332218a79231a44087935800,0xc243557000d013c1c0c5c3a283557381a84342242075e647c74187e323f1704804,0x7c8f42608d2945015e8f431b8d2b02156e00010a7c608945003a6c7d190e1f01800,0x2607a395a2716377a6400674e845477453c23087a642c56841e0d275f118822801,0x4d251a097a28478913785c0041621f3e7c31474b8e6452282c0040210c02603f800,0xac90992759b6f759c34bae84a612f93f3016b640022a219cfad682670c,0x72071d3648037532814d741d50803b12202e4f233d27006c6e6800233b1d6c0a805,0x3d2537253f0574186f5671827057481f006242613a121e1b708f341739544761800,0x1c3d36180d35581d074317248542337c314b0051091a6d3c0e57536924020245804,0x675b888bef629f7e341b0264015259282a845808be543c042c3ed4cb700,0xc4f8fa038e45b1364a637a5ad48e4b01093c1e2e3f06030fb82eade2700,0x6a0a785c0241627383726f568547390b26603f867503617b5f7904002141785c800,0x6c5e0e700045723f5e54487f272f5150273f21003d391a344f340e05561a2780801,0xda2c1d7886e042de67a66e8ca5162ccc76d1776e83eae804281bc029704,0x186045045b35253e570701370b62024247032900054c591a0008507a8d4a5d05800,0x2a0d95043da13bb090042c65b8c0034e883c54b042e1448e027c6b5704,0x2123830e1600784f46437d0c02133a550635803]
private def extsSecond (i : Nat) : Nat := extsField (extsSecondData[i/32]!) 8 (i%32)
def exts (i : Nat) : Nat := (extsClass i <<< 0) ||| (extsFirst i <<< 11) ||| (extsSecond i <<< 23)

private def startsOverB0 : Array Nat := #[0,237,447,622,790,939,1158,1312,1453,1583,1711,1844,2061,2178,2288,2403,2501,2595,2691,2813,2909,3004,3113,3197,3291,3377,3493,3583,3690,3777,3853,3962]

private def startsOverB1 : Array Nat := #[4045,4103,4202,4265,4352,4412,4462,4516,4573,4629,4686,4722,4752,4812,4849,4872,4887,4888]

private def startsOverTable : Array (Array Nat) := #[startsOverB0,startsOverB1]

def startsOver (i : Nat) : Nat := (startsOverTable[i/32]!)[i%32]!

private def startsExtraB0 : Array Nat := #[0,0,61,118,165,209,322,378,420,465,527,580,649,687,745,807,857,912,974,1033,1083,1112,1153,1210,1250,1310,1370,1410,1472,1525,1566,1618]

private def startsExtraB1 : Array Nat := #[1659,1702,1751,1793,1851,1885,1947,2007,2048,2084,2115,2137,2188,2230,2237,2258,2258,2258]

private def startsExtraTable : Array (Array Nat) := #[startsExtraB0,startsExtraB1]

def startsExtra (i : Nat) : Nat := (startsExtraTable[i/32]!)[i%32]!

private def rowFactor : Array Nat := #[0xefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xefad74cf2e78df6c31beea689e6b6caea9258e275c6da8607de6194503ce34c5d65544d22472c62880c1140102,0xe78efadb7d74c70cf2b6cbeeaaba689649e68608e279f75c6586da5535d25942ca2481c64503ce34c105083001,0xe78d74c70efadb7cb3b6ca68964beeaab9a786075c6588e279f69b2ca2481c65535d25943cd44c40e080101143,0xd74efacb3e78c31df6a68bee9a7b6c925aea75c8e269b8606197de3cd44c40e2472c62885d65544d2043005084,0xd74e78c31efacb3db7a68b6c925bee9a7aab75c8606198e269b79f2472c62883cd44c40e5535d25940020440c5,0xebbdf6e78cf2d74c70bafaeab6c9e6a689648a37de8606da75c65859751549341138f30d1440c20402ca2481c6,0xebbcf2d74df6e78c31baf9e6a68aeab6c9258a36da75c7de86061941138f30d5975154930c11401022472c6288,0xdf6ebbe39cf2c70d74aeabafb2d9e6964a687de8a38216da65875c5125935d51440c204041138f30d28b209187,0xdf6cf2c70ebbe39d35aea9e6964bafb2da297de6da6588a382171d1440c20405125935d538c40d44f2062872c9,0xcf2ebbd35df6c31e789e6bafa29aea925b6c6da8a371d7de61986038c40d44f0c11401025975154931c918b20a,0xcf2df6c31ebbd35e399e6aea925bafa29b2d6da7de6198a371d8210c114010238c40d44f5125935d51881ca24b,0xe39db7efac70d74cf2b2daabbee964a689e682179f8e265875c6da4d549751628b2091871050830014503ce34c,0xe39c70d74db7efacb3b2d964a68aabbee9a782165875c79f8e269b28b2091874d54975160801011433cd44c40e,0xdb7e39ebbc70cf2d74aabb2dbaf9649e6a6879f8218a36586da75c4944d655710508300128b20918741138f30d,0xdb7c70cf2e39ebbd35aab9649e6b2dbafa2979f6586da8218a371d1050830014944d65572062872c938c40d44f,0xc70e39d35db7cb3efa964b2da29aab9a7bee65882171d79f69b8e22062872c90801011434d549751634f311390,0xc70db7cb3e39d35ebb964aab9a7b2da29baf65879f69b82171d8a30801011432062872c94944d655730e3503d1,0xd35cb3efac31e78df6a299a7bee925b6caea71d69b8e26198607de34f3113901c918b20a0430050845d65544d2,0xd35c31e78cb3efadb7a29925b6c9a7beeaab71d61986069b8e279f1c918b20a34f3113900020440c55535d2594,0xcb3d35ebbc31df6e789a7a29baf925aeab6c69b71d8a36197de86030e3503d10430050841c918b20a597515493,0xcb3c31df6d35ebbe399a7925aeaa29bafb2d69b6197de71d8a382104300508430e3503d11881ca24b5125935d5,0xc31d35e39cb3db7efa925a29b2d9a7aabbee61971d82169b79f8e21881ca24b0020440c534f3113904d5497516,0xc31cb3db7d35e39ebb9259a7aaba29b2dbaf61969b79f71d8218a30020440c51881ca24b30e3503d14944d6557]
private def holeFactor : Array Nat := #[0xefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xbeeb6caeaa689e6964efae78df6d74cf2c708a382179f71d69b6195545d64933ce45030d2482ca1870c2144001,0xebbe39db7d35cb3c318e28607de75c6da658beeb6caeaa689e69645974d255441134c3ce28b1c62481050400c2,0x8e28607de75c6da658ebbe39db7d35cb3c31bafb2daaba299a79254d259751534c41138f1c628b209040105083,0xbafb2daaba299a79258a382179f71d69b619efae78df6d74cf2c705154935d638f30d4502091872ca083001144,0x8a382179f71d69b619bafb2daaba299a7925ebbe39db7d35cb3c3149351559730d38f41118720928b001083105]
private def inverseFactors : Array Nat := #[0,48,16,8,2,1,64,56,50,49,96,24,18,17,32,10,9,3,4,112,72,66,65,80,58,57,51,52,104,98,97,40,26,25,19,20,144,34,33,11,12,5,120,114,113,88,74,73,67,68,160,82,81,59,60,53,128,106,105,99,100,152,42,41,27,28,21,146,145,35,36,13,136,122,121,115,116,168,90,89,75,76,69,162,161,83,84,61,176,130,129,107,108,101,154,153,43,44,29,147,148,37,184,138,137,123,124,117,170,169,91,92,77,163,164,85,178,177,131,132,109,155,156,45,149,186,185,139,140,125,171,172,93,165,179,180,133,157,187,188,141,173,181,189]

def embedDirect (s a b j o : Nat) : Bool :=
  j<2919 && o<144 && permute o s == mask j &&
    fits (permute o (s &&& a)) (one j) (two j) && fits (permute o (s &&& b)) (one j) (two j)

def getUp (a z : Nat) : Nat :=
  let m := testMask (z%2048)
  let t := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  let allowed := if j=0 then max 1 (baseScore full (R a) m 43) else
    if embedDirect full (R a) m (j-1) o then wt (j-1) else 0
  if t≤allowed then t else 0

def getB (a z : Nat) : Nat :=
  let m := testMask (z%2048)
  let j := ((z>>>11)%4096)-1
  let o := z>>>23
  if embedDirect m (R a) 0 j o then wt j else 0

namespace Local
open PCX150.Sparse (TestTree Valid box leaves)
theorem allTestSmall : ∀ k : Fin 2048, testMask k.val < 2^60 := by decide +kernel

theorem dataSmall (z : Nat) : testMask (z%2048) < 2^60 := allTestSmall ⟨_,Nat.mod_lt _ (by decide)⟩

theorem checkedEmbed {s a b j o : Nat} (range : s<2^60) (ok : embedDirect s a b j o = true) :
    ∃ id : NodeID, id.val=j ∧ Nonempty (Sparse.Embed geo (item id) (triple s a b)) := by
  unfold embedDirect at ok
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨jt,ot⟩,same⟩,f⟩,g⟩ := ok
  exact ⟨⟨j,jt⟩,rfl,embedded ⟨o,ot⟩ range same f g⟩

theorem boardPaid (checks : ∀ i : NodeID, nodeOK i.val=true) (s a b j o : Nat) (range : s<2^60)
    (ok : embedDirect s a b j o=true) (t : TestTree) (valid : Sparse.admissible geo (triple s a b) t) :
    wt j ≤ leaves t := by
  obtain ⟨id,eq,⟨f⟩⟩ := checkedEmbed range ok
  have ready := bankSound checks id _ (Sparse.embedTree f valid)
  simpa only [Sparse.sameLeaves,eq] using ready

theorem rootRaw (t : TestTree) (v : SmallChart.rawValid geo (treeRaw t) (bits full)) : 43≤leaves t := by
  have same : Chart48.node 47 = bits full := by
    change bits rm[47]! = bits full
    have num : rm[47]! = full := by decide +kernel
    rw [num]
  have good : SmallChart.rawValid geo (treeRaw t) (SmallChart.acted (SmallChart.Aut.unit geo) (chart.state chart.root)) := by
    change SmallChart.rawValid geo (treeRaw t) (Chart48.node 47)
    rwa [same]
  have cost := SmallChart.rawLower chart (treeRaw t) chart.root (SmallChart.Aut.unit _) good
  rwa [Chart48.rootWeight,rawLeaves] at cost

theorem upperPaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple full (R a) (testMask (z%2048))) t) : getUp a z ≤ leaves t := by
  let m := testMask (z%2048)
  let k := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  have fullSize : full<2^60 := by decide +kernel
  unfold getUp
  dsimp only
  by_cases jz : j=0
  · rw [if_pos jz]
    have p := scorePaid full (R a) m 43 fullSize t valid (rootRaw t)
    split <;> omega
  · rw [if_neg jz]
    by_cases ev : embedDirect full (R a) m (j-1) o=true
    · rw [if_pos ev]
      have p := boardPaid checks full (R a) m (j-1) o fullSize ev t valid
      split <;> omega
    · rw [if_neg ev]
      split <;> omega

theorem middlePaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple (testMask (z%2048)) (R a) 0) t) :
    getB a z ≤ leaves t := by
  let m := testMask (z%2048)
  let j := ((z>>>11)%4096)-1
  let o := z>>>23
  unfold getB
  dsimp only
  by_cases ev : embedDirect m (R a) 0 j o=true
  · rw [if_pos ev]
    exact boardPaid checks _ _ _ _ _ (dataSmall z) ev t valid
  · rw [if_neg ev]
    exact Nat.zero_le _

end Local
end PCX150.Scalar

namespace PCX150.PrivateGame
open PEqualNP.ProofComplexity
open PCX150.SmallChart (Sample Var Tag Key Domain Aut acted branch plain)
open PCX150.Chart48 (geo)
open PCX150.Sparse (TestTree Triple Valid box half)
def wire (v : V) : Var := Fin.ofNat 12 (port v)

theorem coord : ∀ p v, geo.val p (wire v) = assignment p v := by decide +kernel

def falsifiers (C : Cl) : Set Sample := {p | ¬ ClauseSat (assignment p) C}

theorem emptyMask : falsifiers ∅ = Set.univ := by
  ext p
  simp [falsifiers,ClauseSat]

theorem insertMask (C : Cl) (l : Literal V) :
    falsifiers (insert l C) = branch geo (falsifiers C) (wire l.1) (!l.2) := by
  ext p
  change (¬ ClauseSat (assignment p) (insert l C)) ↔ (¬ ClauseSat (assignment p) C) ∧ geo.val p (wire l.1) = (!l.2)
  rw [coord]
  have test : assignment p l.1 = (!l.2) ↔ assignment p l.1 ≠ l.2 := by
    cases assignment p l.1 <;> cases l.2 <;> decide
  rw [test]
  unfold ClauseSat
  simp only [Finset.mem_insert]
  aesop

theorem clauseNamed (C : Cl) : Chart48.named (falsifiers C) := by
  induction C using Finset.induction_on with
  | empty => rw [emptyMask]; exact Chart48.allNamed []
  | insert l C fresh ih => rw [insertMask]; exact Chart48.namedBranch ih _ _

theorem labelBook : ∀ n ∈ labelMasks.toList, ∃ k : Tag, ∀ r : Sample,
    n.testBit r.val = true → geo.tag r = k := by decide +kernel

theorem rawOwner {C : Cl} (ax : C ∈ PHP 4 3) : plain geo (falsifiers C) := by
  obtain ⟨k,tk⟩ := labelBook _ (axListed ax)
  exact ⟨k,fun p hp => tk p ((privateBit C p).2 hp)⟩

theorem treeRaw {A : Cl} {i : Nat} (pa : ResTree (PHP 4 3) A i) :
    ∃ t : TestTree, Sparse.leaves t = i+1 ∧
      Valid geo.val (box geo.tag ∅ ∅) t (falsifiers A) := by
  apply Sparse.transferTree (F := PHP 4 3) wire geo.val assignment coord
  · intro C ch
    obtain ⟨k,hk⟩ := rawOwner ch
    exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pa
  · exact fun _ hp => hp

theorem treeOne {A B : Cl} {j : Nat} (pb : ResTree (insert A (PHP 4 3)) B j) :
    ∃ t : TestTree, Sparse.leaves t=j+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) ∅) t (falsifiers B) := by
  apply Sparse.transferTree (F := insert A (PHP 4 3)) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | ax
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨k,hk⟩ := rawOwner ax
      exact ⟨Sum.inl k,fun p hp => hk p hp⟩
  · exact pb
  · exact fun _ hp => hp

theorem treeTwo {A B : Cl} {k : Nat} (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) :
    ∃ t : TestTree, Sparse.leaves t=k+1 ∧
      Valid geo.val (box geo.tag (falsifiers A) (falsifiers B)) t Set.univ := by
  apply Sparse.transferTree (F := insert B (insert A (PHP 4 3))) wire geo.val assignment coord
  · intro C ch
    rcases ch with rfl | rfl | ax
    · exact ⟨Sum.inr 1,fun p hp => by simpa [box,falsifiers] using hp⟩
    · exact ⟨Sum.inr 0,fun p hp => by simpa [box,falsifiers] using hp⟩
    · obtain ⟨i,hi⟩ := rawOwner ax
      exact ⟨Sum.inl i,fun p hp => hi p hp⟩
  · exact pc
  · intro p _ hp; simpa [ClauseSat] using hp

abbrev Choice := Fin 49

def candidate (a : Choice) : Set Sample := if a.val=0 then ∅ else Chart48.bits (Chart48.rm[a.val-1]!)

def price (a : Choice) := if a.val=0 then 0 else Chart48.weight[a.val-1]!

def code (k : Key) : Choice := ⟨k.val+1,by have := k.isLt; omega⟩

theorem priced (k : Key) : price (code k) = Chart48.chart.wt k := by simp [price,code,Chart48.chart]

theorem coded (k : Key) : candidate (code k) = Chart48.node k := by simp [candidate,code,Chart48.node]

theorem candidateZero : candidate 0 = ∅ := by rfl

def Match (real cur : Set Sample) := cur ⊆ real ∧ (real ⊆ cur ∨ plain geo real)

theorem matchSame (r : Set Sample) : Match r r := ⟨(fun _ h => h),Or.inl (fun _ h => h)⟩

theorem match0 {r : Set Sample} (h : plain geo r) : Match r ∅ := ⟨Set.empty_subset _,Or.inr h⟩

theorem actEmpty (f : Aut geo) : acted f (∅ : Set Sample) = ∅ := rfl

theorem actUniv (f : Aut geo) : acted f (Set.univ : Set Sample) = Set.univ := rfl

theorem twiceInv (o : Chart48.ID) (s : Set Sample) :
    acted (Chart48.orient (Chart48.inverse o)) (acted (Chart48.orient o) s) = s := by
  have inj (f : Aut geo) : Function.Injective (acted f) := by
    intro u v h
    ext r
    have e := Set.ext_iff.mp h (f.s r)
    simpa [SmallChart.acted] using e
  apply inj (Chart48.orient o)
  exact Chart48.invertAct o _

theorem namesPair {a b : Set Sample} (ha : Chart48.named a) (hb : Chart48.named b) :
    ∃ (f : Chart48.ID) (x y : Choice) (o : Chart48.ID),
      Match (acted (Chart48.orient f) a) (candidate x) ∧
      Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
  have oneB (f : Chart48.ID) : ∃ y o, Match (acted (Chart48.orient f) b) (acted (Chart48.orient o) (candidate y)) := by
    rcases hb with hp | ⟨j,q,rfl⟩
    · exact ⟨0,0,by rw [candidateZero,actEmpty]; exact match0 (SmallChart.actedPlain _ hp)⟩
    · obtain ⟨n,eq⟩ := Chart48.composeAct f q (Chart48.node j)
      exact ⟨code j,n,by rw [coded,eq]; exact matchSame _⟩
  rcases ha with pure | ⟨j,q,rfl⟩
  · obtain ⟨y,o,hm⟩ := oneB 0
    exact ⟨0,0,y,o,by rw [candidateZero]; exact match0 (SmallChart.actedPlain _ pure),hm⟩
  · obtain ⟨y,o,hm⟩ := oneB (Chart48.inverse q)
    exact ⟨Chart48.inverse q,code j,y,o,by rw [twiceInv,coded]; exact matchSame _,hm⟩

theorem canMove (f : Aut geo) (s x y a b : Set Sample) (t : TestTree)
    (h : Valid geo.val (box geo.tag x y) t s)
    (ax : Match (acted f x) a) (byy : Match (acted f y) b) :
    Valid geo.val (box geo.tag a b) (Sparse.renamed f t) (acted f s) := by
  apply Sparse.moveTree f h
  intro i
  cases i with
  | inl i =>
    refine ⟨Sum.inl (f.a i),?_⟩
    intro p _ h
    change geo.tag p = i at h
    exact (f.label p).trans (congrArg f.a h)
  | inr i =>
    fin_cases i
    · rcases ax.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 0,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f x by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ x := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)
    · rcases byy.2 with sub | ⟨j,pure⟩
      · refine ⟨Sum.inr 1,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        have z := sub (show f.s p ∈ acted f y by simpa [SmallChart.acted] using h0)
        simpa [box] using z
      · refine ⟨Sum.inl j,?_⟩
        intro p hp hx
        have h0 : p ∈ y := by simpa [box] using hx
        exact pure _ (by simpa [SmallChart.acted] using h0)

theorem shrink {bit : Sample → Var → Bool} {term : Sparse.Box → Set Sample}
    {s d : Set Sample} {t : TestTree} (h : Valid bit term t s) (inc : d ⊆ s) : Valid bit term t d :=
  Sparse.smaller h inc (fun i => ⟨i,fun _ _ hp => hp⟩)

def converted : TestTree → SmallChart.Tree
  | .leaf => .leaf
  | .cut q l r => .node q (converted l) (converted r)

theorem ccost (t : TestTree) : SmallChart.leaves (converted t) = Sparse.leaves t := by
  induction t with
  | leaf => rfl
  | cut q l r hl hr => simp [converted,SmallChart.leaves,Sparse.leaves,hl,hr]

theorem noExtra {s : Set Sample} {t : TestTree} (h : Valid geo.val (box geo.tag ∅ ∅) t s) :
    SmallChart.rawValid geo (converted t) s := by
  induction t generalizing s with
  | leaf =>
    obtain ⟨i,hi⟩ := h
    cases i with
    | inl i => exact ⟨i,fun _ hp => hi hp⟩
    | inr i =>
      refine ⟨0,?_⟩
      intro p hp
      have z := hi hp
      fin_cases i <;> simp [box] at z
  | cut q l r hl hr => exact ⟨hl h.1,hr h.2⟩

theorem charge (a : Choice) (t : TestTree) (h : Valid geo.val (box geo.tag ∅ ∅) t (candidate a)) :
    price a ≤ Sparse.leaves t := by
  by_cases z : a.val=0
  · simp [price,z]
  · let k : Key := ⟨a.val-1,by have := a.isLt; omega⟩
    have eq : code k = a := by apply Fin.ext; dsimp [code,k]; omega
    rw [←eq,coded] at h
    rw [←eq,priced,←ccost]
    exact SmallChart.rawLower Chart48.chart (converted t) k (SmallChart.Aut.unit _) (noExtra h)

def scoreClaim := ∀ (a b : Choice) (o : Chart48.ID) (t u : TestTree),
    Valid geo.val (box geo.tag (candidate a) ∅) t (acted (Chart48.orient o) (candidate b)) →
    Valid geo.val (box geo.tag (candidate a) (acted (Chart48.orient o) (candidate b))) u Set.univ →
    41 ≤ price a + Sparse.leaves t + Sparse.leaves u

theorem allThree (test : scoreClaim) {A B : Cl} {i j k : Nat}
    (pa : ResTree (PHP 4 3) A i) (pb : ResTree (insert A (PHP 4 3)) B j)
    (pc : ResTree (insert B (insert A (PHP 4 3))) ∅ k) : 38 ≤ i+j+k := by
  obtain ⟨f,a,b,o,ma,mb⟩ := namesPair (clauseNamed A) (clauseNamed B)
  let ren := Chart48.orient f
  have emp : Match (acted ren ∅) ∅ := by rw [actEmpty]; exact matchSame _
  obtain ⟨x,hx,vx⟩ := treeRaw pa
  obtain ⟨y,hy,vy⟩ := treeOne pb
  obtain ⟨z,hz,vz⟩ := treeTwo pc
  have first := charge a (Sparse.renamed ren x) (shrink (canMove ren _ _ _ _ _ _ vx emp emp) ma.1)
  have snd := shrink (canMove ren _ _ _ _ _ _ vy ma emp) mb.1
  have third := canMove ren _ _ _ _ _ _ vz ma mb
  rw [actUniv] at third
  have total := test a b o _ _ snd third
  simp only [Sparse.sameLeaves,hx,hy,hz] at first total
  omega

end PCX150.PrivateGame

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def preID (a r : Nat) : Nat :=
  if a < 144 && r < 60 then
    let f := inverseFactors[a]!
    let middle := (holeFactor[f%8]! >>> (6*r)) % 64
    (rowFactor[f/8]! >>> (6*middle)) % 64
  else 0

def col (r : Nat) : Nat := (List.range 144).foldl
  (fun z o => z ||| (staticFlags (preID o r) <<< (49*o))) 0

def everyCol : Array Nat := Array.ofFn (fun r : Fin 60 => col r.val)

def meets (m : Nat) : Nat := (List.range 60).foldl
  (fun acc r => if m.testBit r then acc ||| everyCol[r]! else acc) 0

def sameMask (m : Nat) : Nat := (List.range 60).foldl
  (fun acc r => acc &&& (if m.testBit r then everyCol[r]! else big ^^^ everyCol[r]!)) big

structure CountVec where
  w0 : Nat := 0
  w1 : Nat := 0
  w2 : Nat := 0
  w3 : Nat := 0
  w4 : Nat := 0

def inc (v : CountVec) (x : Nat) : CountVec :=
  let c1 := v.w0 &&& x
  let c2 := v.w1 &&& c1
  let c3 := v.w2 &&& c2
  let c4 := v.w3 &&& c3
  ⟨v.w0 ^^^ x, v.w1 ^^^ c1,v.w2 ^^^ c2,v.w3 ^^^ c3,v.w4 ^^^ c4⟩

def thresh (v : CountVec) (k : Nat) : Nat :=
  let advance (i a z : Nat) := if k.testBit i then a &&& z else a ||| z
  if k ≥ 32 then 0 else advance 4 v.w4 (advance 3 v.w3 (advance 2 v.w2 (advance 1 v.w1 (advance 0 v.w0 big))))

def tally (m : Nat) := (List.range 22).foldl
  (fun acc l => inc acc (meets (m &&& tagMask l))) ({} : CountVec)

def weightGE (k : Nat) : Nat :=
  let first := (List.range 49).foldl (fun n i => if k ≤ weightR i then n ||| 2^i else n) 0
  first * (big / (2^49-1))

def packedExtras (a : Nat) : Nat :=
  (List.range (startsExtra (a+1)-startsExtra a)).foldl (fun h i =>
    let z := exts (startsExtra a+i)
    h ||| (sameMask (testMask (z%2048)) <<< (7056*getB a z))) 0

def closeWord : Nat → Nat → Nat
  | 0,t => t
  | n+1,t =>
    let w := closeWord n t
    w ||| (w >>> (7056*2^n))

def extraWord (a k : Nat) := (closeWord 6 (packedExtras a) >>> (7056*k)) % 2^7056

def rowQual (a : Nat) : Array Nat :=
  let r := tally full
  let f := tally (full ^^^ R a)
  let hom := big ^^^ thresh (tally (R a)) 2
  Array.ofFn (fun k : Fin 43 => if k.val≤1 then big else
    (thresh r k.val &&& thresh f (k.val-1)) ||| (hom &&& weightGE k.val) ||| extraWord a k.val)

def covered (a : Nat) : Bool :=
  let qs := rowQual a
  let seen := (List.range (startsOver (a+1)-startsOver a)).foldl (fun acc i =>
    let z := ove (startsOver a+i)
    let m := testMask (z%2048)
    let t := getUp a z
    acc ||| ((big ^^^ meets (full ^^^ m)) &&& qs[41 - weightR a - t]!)) 0
  seen == big

end PCX150.Scalar

namespace PCX150.Scalar
def atCount (v : CountVec) (i : Nat) : Nat :=
  (v.w0.testBit i).toNat+2*(v.w1.testBit i).toNat+4*(v.w2.testBit i).toNat+
    8*(v.w3.testBit i).toNat+16*(v.w4.testBit i).toNat

theorem countZero (i : Nat) : atCount {} i = 0 := by simp [atCount]

theorem countInc (v : CountVec) (x i : Nat) :
    atCount (inc v x) i = (atCount v i + (x.testBit i).toNat)%32 := by
  simp only [atCount,inc,Nat.testBit_and,Nat.testBit_xor]
  cases v.w0.testBit i <;> cases v.w1.testBit i <;> cases v.w2.testBit i <;>
    cases v.w3.testBit i <;> cases v.w4.testBit i <;> cases x.testBit i <;> decide

def compareBits (k : Nat) (a b c d e : Bool) : Bool :=
  let step (n : Nat) (u v : Bool) := if k.testBit n then u && v else u || v
  step 4 e (step 3 d (step 2 c (step 1 b (step 0 a true))))

theorem boolCmp : ∀ (k : Fin 32) (a b c d e : Bool),
    compareBits k.val a b c d e = true ↔ k.val ≤ a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat := by decide +kernel

theorem finiteCount (v : CountVec) (i : Nat) : atCount v i < 32 := by
  unfold atCount
  cases v.w0.testBit i <;> cases v.w1.testBit i <;> cases v.w2.testBit i <;>
    cases v.w3.testBit i <;> cases v.w4.testBit i <;> decide

theorem cmpGood (v : CountVec) (i k : Nat) (small : i < 7056) :
    (thresh v k).testBit i = true ↔ k ≤ atCount v i := by
  have base : big.testBit i = true := by
    rw [big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact small
  by_cases outside : k≥32
  · simp [thresh,outside,show ¬ k ≤ atCount v i by have h := finiteCount v i; omega]
  · let f := fun (n a z : Nat) => if k.testBit n then a &&& z else a ||| z
    have step (n a z : Nat) : (f n a z).testBit i =
        (if k.testBit n then a.testBit i && z.testBit i else a.testBit i || z.testBit i) := by
      dsimp [f]
      split <;> simp [Nat.testBit_and,Nat.testBit_or]
    change ((if k≥32 then 0 else f 4 v.w4 (f 3 v.w3 (f 2 v.w2 (f 1 v.w1 (f 0 v.w0 big))))).testBit i = true) ↔ _
    rw [if_neg outside]
    simp only [step,base]
    exact boolCmp ⟨k,by omega⟩ _ _ _ _ _

theorem foldBits (xs : List Nat) (f : Nat → Nat) (i acc : Nat) :
    (xs.foldl (fun a e => a ||| f e) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j ∈ xs, (f j).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons]
    aesop

theorem foldCounts (xs : List Nat) (piece : Nat → Nat) (i : Nat) (v : CountVec)
    (small : atCount v i + xs.length < 32) :
    atCount (xs.foldl (fun x q => inc x (piece q)) v) i =
      atCount v i + (xs.filter (fun q => (piece q).testBit i)).length := by
  induction xs generalizing v with
  | nil => simp
  | cons a xs ih =>
    have low : atCount v i + ((piece a).testBit i).toNat < 32 := by
      cases h : (piece a).testBit i <;> simp_all <;> omega
    have add := countInc v (piece a) i
    rw [Nat.mod_eq_of_lt low] at add
    rw [List.foldl_cons,ih]
    · rw [add]
      cases h : (piece a).testBit i <;> simp [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · rw [add]
      cases h : (piece a).testBit i <;> simp_all <;> omega

end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev OptionID := Fin 49

def place (b : OptionID) (o : Chart48.ID) : Nat := 49*o.val+b.val

theorem placeRange (b : OptionID) (o : Chart48.ID) : place b o < 7056 := by
  have := b.isLt; have := o.isLt; unfold place; omega

theorem unpackEnd (a b : OptionID) (o : Chart48.ID) (good : covered a.val = true) :
    ∃ z, ((big ^^^ meets (full ^^^ testMask (z%2048))).testBit (place b o) = true) ∧
      ((rowQual a.val)[41-weightR a.val-getUp a.val z]!).testBit (place b o) = true := by
  let n := startsOver (a.val+1)-startsOver a.val
  let itemAt :=  fun i : Nat => ove (startsOver a.val+i)
  let hit := fun i : Nat => (big ^^^ meets (full ^^^ testMask (itemAt i%2048))) &&&
    (rowQual a.val)[41-weightR a.val-getUp a.val (itemAt i)]!
  have eq : (List.range n).foldl (fun acc i => acc ||| hit i) 0 = big := eq_of_beq good
  have yes : ((List.range n).foldl (fun acc i => acc ||| hit i) 0).testBit (place b o) = true := by
    rw [eq,big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact placeRange _ _
  rcases (foldBits _ _ _ _).1 yes with bad | ⟨i,_,val⟩
  · simp at bad
  · refine ⟨itemAt i,?_⟩
    exact Bool.and_eq_true_iff.mp (by simpa [hit,Nat.testBit_and] using val)

open PCX150.PrivateGame (candidate price)
open PCX150.SmallChart (Sample acted)
open PCX150.Sparse (TestTree Valid box leaves)
def dataB (b : OptionID) (o : Chart48.ID) := acted (Chart48.orient o) (candidate b)

def upperData (z : Nat) := Chart48.bits (testMask (z%2048))

theorem widenSecond (A B H : Set Sample) (sub : B ⊆ H) {t : TestTree}
    (valid : Valid Chart48.geo.val (box Chart48.geo.tag A B) t Set.univ) :
    Valid Chart48.geo.val (box Chart48.geo.tag A H) t Set.univ := by
  apply Sparse.smaller valid (fun _ h => h)
  intro i
  refine ⟨i,?_⟩
  intro p _ h
  cases i with
  | inl k => exact h
  | inr k =>
    fin_cases k
    · simpa [box] using h
    · apply sub
      simpa [box] using h

theorem reachTarget
    (allCases : ∀ a : OptionID, covered a.val = true)
    (compare : ∀ (b : OptionID) (o : Chart48.ID) z,
      (big ^^^ meets (full ^^^ testMask (z%2048))).testBit (place b o) = true → dataB b o ⊆ upperData z)
    (firstTree : ∀ (a b : OptionID) (o : Chart48.ID) k, k<43 →
      ((rowQual a.val)[k]!).testBit (place b o) = true → ∀ t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) ∅) t (dataB b o) → k ≤ leaves t)
    (lastTree : ∀ (a : OptionID) z t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) (upperData z)) t Set.univ →
      getUp a.val z ≤ leaves t) : PrivateGame.scoreClaim := by
  intro a b o t u h g
  obtain ⟨z,sub,ok⟩ := unpackEnd a b o (allCases a)
  have hh := compare b o z sub
  have hu := lastTree a z u (widenSecond _ _ _ hh g)
  have ht := firstTree a b o _ (by omega) ok t h
  change 41 ≤ weightR a.val + leaves t + leaves u
  omega

end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open PCX150.SmallChart (Sample)
abbrev Bank := Fin 49

def lane (b : Bank) (o : Chart48.ID) := 49*o.val+b.val

def active (b : Bank) (o : Chart48.ID) (r : Sample) : Bool :=
  (R b.val).testBit ((Chart48.orient o).s.symm r).val

theorem posLane (b : Bank) (o : Chart48.ID) : lane b o < 7056 := by
  unfold lane; have := b.isLt; have := o.isLt; omega

theorem liveWide (b : Bank) (o : Chart48.ID) : big.testBit (lane b o) = true := by
  rw [big,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact posLane b o

theorem flagData : ∀ (r : Sample) (b : Bank),
    (staticFlags r.val).testBit b.val = (R b.val).testBit r.val := by decide +kernel

theorem flagSmall : ∀ r : Sample, staticFlags r.val < 2^49 := by decide +kernel

theorem indexData : ∀ (o : Chart48.ID) (r : Sample),
    preID o.val r.val = (Chart48.backward Chart48.words[o.val]! 9 r).val := by decide +kernel

theorem stripe (m : Nat) (i : Nat) (b : Bank) (o : Chart48.ID) (tiny : m<2^49) :
    (m <<< (49*i)).testBit (lane b o) = true ↔ i=o.val ∧ m.testBit b.val = true := by
  rw [Nat.testBit_shiftLeft]
  have lim := b.isLt
  unfold lane
  by_cases eq : i=o.val
  · subst i; simp
  · by_cases below : i<o.val
    · have bound : 49 ≤ 49*o.val+b.val-49*i := by omega
      have no := Nat.testBit_lt_two_pow (lt_of_lt_of_le tiny (Nat.pow_le_pow_right (by decide : 0 < 2) bound))
      simp [eq,show 49*i ≤ 49*o.val+b.val by omega,no]
    · simp [eq,show ¬49*i ≤ 49*o.val+b.val by omega]

theorem columnExact (b : Bank) (o : Chart48.ID) (r : Sample) :
    (col r.val).testBit (lane b o) = active b o r := by
  apply Bool.eq_iff_iff.mpr
  unfold col
  rw [foldBits]
  simp only [Nat.zero_testBit,Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨i,mem,h⟩
    let s : Chart48.ID := ⟨i,List.mem_range.mp mem⟩
    have val : preID i r.val = (Chart48.backward Chart48.words[s.val]! 9 r).val := indexData s r
    have sm : staticFlags (preID i r.val)<2^49 := by rw [val]; exact flagSmall _
    obtain ⟨eq,hit⟩ := (stripe _ i b o sm).1 h
    subst i
    have v := indexData o r
    rw [v,flagData] at hit
    simpa [active,Chart48.orient,Chart48.backApply] using hit
  · intro h
    refine ⟨o.val,List.mem_range.mpr o.isLt,?_⟩
    have v := indexData o r
    have sm : staticFlags (preID o.val r.val)<2^49 := by rw [v]; exact flagSmall _
    apply (stripe _ _ b o sm).2
    refine ⟨rfl,?_⟩
    rw [v,flagData]
    simpa [active,Chart48.orient,Chart48.backApply] using h

theorem colLookup (r : Sample) : everyCol[r.val]! = col r.val := by
  rw [getElem!_pos everyCol r.val (by simpa [everyCol] using r.isLt)]
  simp [everyCol]

theorem meeting (m : Nat) (b : Bank) (o : Chart48.ID) :
    (meets m).testBit (lane b o) = true ↔ ∃ r : Sample, m.testBit r.val = true ∧ active b o r = true := by
  have replace (ls : List Nat) (acc : Nat) :
      ls.foldl (fun z i => if m.testBit i then z ||| everyCol[i]! else z) acc =
      ls.foldl (fun z i => z ||| (if m.testBit i then everyCol[i]! else 0)) acc := by
    induction ls generalizing acc with
    | nil => rfl
    | cons a l ih => cases h : m.testBit a <;> simp [h,ih]
  unfold meets
  rw [replace,foldBits]
  constructor
  · rintro (no | ⟨i,mem,hit⟩)
    · simp at no
    · let r : Sample := ⟨i,List.mem_range.mp mem⟩
      cases hv : m.testBit i
      · simp [hv] at hit
      · refine ⟨r,hv,?_⟩
        rw [if_pos hv] at hit
        change (everyCol[r.val]!).testBit (lane b o) = true at hit
        rwa [colLookup,columnExact] at hit
  · rintro ⟨r,hm,h⟩
    right; refine ⟨r.val,List.mem_range.mpr r.isLt,?_⟩
    rw [if_pos hm,colLookup,columnExact]
    exact h

theorem upperMask (m : Nat) (b : Bank) (o : Chart48.ID)
    (h : (big ^^^ meets (full ^^^ m)).testBit (lane b o) = true) :
    ∀ r : Sample, active b o r = true → m.testBit r.val = true := by
  intro r hr
  by_contra bad
  have on : full.testBit r.val = true := by rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact r.isLt
  have conflict : (meets (full ^^^ m)).testBit (lane b o) = true := by
    apply (meeting _ _ _).2
    refine ⟨r,?_,hr⟩
    cases hb : m.testBit r.val <;> simp_all [Nat.testBit_xor]
  simp [Nat.testBit_xor,liveWide,conflict] at h

end PCX150.Scalar

namespace PCX150.RootBits
def closeWord : Nat → Nat → Nat
  | 0,t => t
  | n+1,t =>
    let w := closeWord n t
    w ||| (w >>> (7056*2^n))

theorem foldBits (xs : List Nat) (f : Nat → Nat) (i acc : Nat) :
    (xs.foldl (fun a e => a ||| f e) acc).testBit i = true ↔
      acc.testBit i = true ∨ ∃ j ∈ xs, (f j).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true]
    simp only [List.mem_cons]
    aesop

theorem closure (n t i : Nat) :
    (closeWord n t).testBit i = true ↔ ∃ j<2^n, t.testBit (7056*j+i) = true := by
  induction n generalizing i with
  | zero => simp [closeWord]
  | succ n ih =>
    rw [closeWord,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftRight,ih,ih,Nat.pow_succ]
    constructor
    · rintro (⟨j,lt,hit⟩ | ⟨j,lt,hit⟩)
      · exact ⟨j,by omega,hit⟩
      · exact ⟨j+2^n,by omega,by simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hit⟩
    · rintro ⟨j,lt,hit⟩
      by_cases small : j<2^n
      · exact Or.inl ⟨j,small,hit⟩
      · right
        have sub : (j-2^n)+2^n=j := by omega
        refine ⟨j-2^n,by omega,?_⟩
        have same : 7056*(j-2^n)+(7056*2^n+i)=7056*j+i := by rw [←Nat.add_assoc,←Nat.mul_add,sub]
        simpa only [same,Nat.add_comm i] using hit

theorem wideStripe (m pos k i : Nat) (small : i<7056) (limit : m<2^7056) :
    (m <<< (7056*pos)).testBit (7056*k+i) = true → k=pos ∧ m.testBit i=true := by
  intro h
  rw [Nat.testBit_shiftLeft] at h
  by_cases eq : k=pos
  · subst k; exact ⟨rfl,by simpa using h⟩
  · by_cases less : k<pos
    · simp [show ¬7056*pos≤7056*k+i by omega] at h
    · have t : 7056 ≤ 7056*k+i-7056*pos := by omega
      have off := Nat.testBit_lt_two_pow (lt_of_lt_of_le limit (Nat.pow_le_pow_right (by decide : 0<2) t))
      simp [show 7056*pos≤7056*k+i by omega,off] at h

theorem extractWord {items : List Nat} (mask cost : Nat → Nat) (k i : Nat)
    (bound : ∀ z ∈ items, mask z < 2^7056) (small : i < 7056)
    (seen : (((closeWord 6 (items.foldl (fun t z => t ||| (mask z <<< (7056*cost z))) 0)) >>> (7056*k)) % 2^7056).testBit i = true) :
    ∃ z ∈ items, k≤cost z ∧ (mask z).testBit i=true := by
  rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight] at seen
  simp only [decide_eq_true_eq.mpr small,Bool.true_and] at seen
  obtain ⟨j,_,cell⟩ := (closure 6 _ _).1 seen
  rcases (foldBits _ (fun z => mask z <<< (7056*cost z)) _ _).1 cell with bad | ⟨z,hz,bit⟩
  · simp at bad
  · have e : 7056*j+(7056*k+i) = 7056*(j+k)+i := by omega
    rw [e] at bit
    have result := wideStripe (mask z) (cost z) (j+k) i small (bound z hz) bit
    exact ⟨z,hz,by omega,result.2⟩

end PCX150.RootBits

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
def domainMask (b : Bank) (o : ID) := permute o.val (R b.val)

theorem domainBit (b : Bank) (o : ID) (r : Sample) :
    (domainMask b o).testBit r.val = active b o r := actionBit _ _ _

theorem smallTag : ∀ l : Fin 22, tagMask l.val < 2^60 := by decide +kernel

theorem nonemptyWord (m : Nat) (small : m<2^60) :
    m ≠ 0 ↔ ∃ p : Sample, m.testBit p.val = true := by
  constructor
  · intro h
    by_contra no
    apply h
    apply Nat.eq_of_testBit_eq
    intro n
    by_cases ok : n<60
    · have dead : m.testBit n ≠ true := fun yes => no ⟨⟨n,ok⟩,yes⟩
      cases hm : m.testBit n <;> simp_all
    · have smallN := Nat.testBit_lt_two_pow (lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt ok)))
      simp [smallN]
  · rintro ⟨p,h⟩ e
    simp [e] at h

theorem tallyCell (m : Nat) (b : Bank) (o : ID) (l : Fin 22) :
    (meets (m &&& tagMask l.val)).testBit (lane b o) =
      ((m &&& domainMask b o) &&& tagMask l.val != 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [meeting]
  simp only [bne_iff_ne]
  rw [nonemptyWord _ (lt_of_le_of_lt Nat.and_le_right (smallTag l))]
  constructor
  · rintro ⟨r,hm,hb⟩
    have hh := Bool.and_eq_true_iff.mp (by simpa only [Nat.testBit_and] using hm)
    exact ⟨r,by simp [Nat.testBit_and,domainBit,hh.1,hh.2,hb]⟩
  · rintro ⟨r,hm⟩
    simp only [Nat.testBit_and,Bool.and_eq_true,domainBit] at hm
    exact ⟨r,by simp [Nat.testBit_and,hm.1.1,hm.2],hm.1.2⟩

theorem counted (m : Nat) (b : Bank) (o : ID) :
    atCount (tally m) (lane b o) = present (m &&& domainMask b o) := by
  let f := fun l : Nat => meets (m &&& tagMask l)
  let g := fun l : Nat => (m &&& domainMask b o) &&& tagMask l != 0
  have rows (ls : List Nat) (ok : ∀ l ∈ ls, l<22) (a : Nat) :
      ls.foldl (fun n k => if g k then n+1 else n) a =
        a + (ls.filter (fun k => (f k).testBit (lane b o))).length := by
    induction ls generalizing a with
    | nil => simp
    | cons k ks ih =>
      have eq : (f k).testBit (lane b o) = g k := tallyCell m b o ⟨k,ok k (by simp)⟩
      have sub := fun k hk => ok k (List.mem_cons_of_mem _ hk)
      cases h : g k <;> simp [List.foldl_cons,eq,h,ih sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  unfold tally present
  rw [foldCounts (List.range 22) f _ {} (by simp [countZero])]
  have v := rows (List.range 22) (fun _ h => List.mem_range.mp h) 0
  simpa [countZero,g,f] using v.symm

def priceStripe (k : Nat) := (List.range 49).foldl (fun n i => if k≤weightR i then n ||| 2^i else n) 0

def replicated (k : Nat) : Nat := (List.range 144).foldl (fun n o => n ||| (priceStripe k <<< (49*o))) 0

theorem priceEq : ∀ k : Fin 43, weightGE k.val = replicated k.val := by decide +kernel

theorem priceLow : ∀ k : Fin 43, priceStripe k.val < 2^49 := by decide +kernel

theorem priceEntry : ∀ (k : Fin 43) (b : Bank), (priceStripe k.val).testBit b.val = decide (k.val ≤ weightR b.val) := by decide +kernel

theorem projectedPrice (k : Fin 43) (b : Bank) (o : ID)
    (bit : (weightGE k.val).testBit (lane b o) = true) : k.val ≤ weightR b.val := by
  rw [priceEq,replicated,foldBits] at bit
  rcases bit with nope | ⟨i,mem,hit⟩
  · simp at nope
  · have ok := ((stripe _ i b o (priceLow k)).1 hit).2
    rwa [priceEntry,decide_eq_true_eq] at ok

theorem meetFixed {m : Nat} (b : Bank) (o : ID)
    (yes : (sameMask m).testBit (lane b o) = true) :
    ∀ p : Sample, m.testBit p.val = active b o p := by
  let band := fun i : Nat => if m.testBit i then everyCol[i]! else big ^^^ everyCol[i]!
  have all (ls : List Nat) (start : Nat) (h : (ls.foldl (fun t i => t &&& band i) start).testBit (lane b o) = true) :
      start.testBit (lane b o) = true ∧ ∀ i∈ls, (band i).testBit (lane b o) = true := by
    induction ls generalizing start with
    | nil => simpa using h
    | cons v vs ih =>
      obtain ⟨common,rest⟩ := ih _ h
      rw [Nat.testBit_and,Bool.and_eq_true] at common
      exact ⟨common.1,fun i hi => (List.mem_cons.mp hi).elim (fun e => e ▸ common.2) (rest i)⟩
  intro p
  have h := (all _ _ yes).2 p.val (List.mem_range.mpr p.isLt)
  dsimp [band] at h
  cases e : m.testBit p.val <;> simp [e,colLookup,columnExact,Nat.testBit_xor,liveWide] at h ⊢ <;> simp_all

end PCX150.Scalar

namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart PCX150.Bands
open PCX150.SmallChart (Sample)
namespace Local
open PCX150.Sparse (TestTree box Valid leaves)
theorem presentCard (m : Nat) : (Sparse.liveTags Scoring.label (bits m)).card ≤ present m := by
  classical
  let test := fun k : Nat => m &&& tagMask k != 0
  let ls := (List.range 22).filter test
  have fold (xs : List Nat) (n : Nat) :
      xs.foldl (fun k j => if test j then k+1 else k) n = n+(xs.filter test).length := by
    induction xs generalizing n with
    | nil => simp
    | cons a xs ih => cases h : test a <;> simp [h,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have sz : present m=ls.length := by simpa [present,ls,test] using fold (List.range 22) 0
  let labels := Sparse.liveTags Scoring.label (bits m)
  have sub : labels.image Fin.val ⊆ ls.toFinset := by
    intro n hn
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨p,hp,hit⟩ := Sparse.ofLive hl
    have points : (m &&& tagMask l.val).testBit p.val = true := by
      change m.testBit p.val=true at hp
      rw [Nat.testBit_and,tagSame,Scoring.tagBits,hp,hit]
      simp
    have ne : m &&& tagMask l.val ≠ 0 := by intro h; simp [h] at points
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr l.isLt,by simpa [test] using ne⟩)
  have bound := Finset.card_le_card sub
  have nd : ls.Nodup := List.nodup_range.filter _
  rw [Finset.card_image_of_injective _ Fin.val_injective,List.toFinset_card_of_nodup nd] at bound
  simpa [sz,labels] using bound

theorem singleTag (m : Nat) (one : present m≤1) : plain geo (bits m) := by
  classical
  let t := Sparse.liveTags Scoring.label (bits m)
  have bound : t.card≤1 := (presentCard m).trans one
  have here (p : Sample) (hp : p∈bits m) : geo.tag p ∈ t := by
    change Scoring.label p ∈ Sparse.liveTags Scoring.label (bits m)
    unfold Sparse.liveTags
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hp,rfl⟩
  by_cases any : ∃p,p∈bits m
  · obtain ⟨p,hp⟩ := any
    exact ⟨geo.tag p,fun q hq => Finset.card_le_one.mp bound _ (here _ hq) _ (here _ hp)⟩
  · exact ⟨0,fun p hp => False.elim (any ⟨p,hp⟩)⟩

theorem repSmall : ∀ b : Bank, R b.val<2^60 := by decide +kernel

theorem wordRange (b : Bank) (o : ID) : domainMask b o <2^60 := rangePerm o _ (repSmall b)

theorem outsideBits (m a : Nat) (size : m<2^60) :
    (full ^^^ a) &&& m = apart m a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,Nat.testBit_xor,apart]
  by_cases l : i<60
  · have wide : full.testBit i = true := by rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact l
    rw [wide]; cases m.testBit i <;> cases a.testBit i <;> decide
  · have off := Nat.testBit_lt_two_pow (lt_of_lt_of_le size (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt l)))
    simp [off]

theorem countPaid (a b : Bank) (o : ID) (k : Fin 43) (t : TestTree)
    (v : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (first : (thresh (tally full) k.val).testBit (lane b o) = true)
    (second : (thresh (tally (full ^^^ R a.val)) (k.val-1)).testBit (lane b o) = true) :
    k.val ≤ leaves t := by
  let m := domainMask b o
  have x := (cmpGood _ _ _ (posLane b o)).1 first
  have y := (cmpGood _ _ _ (posLane b o)).1 second
  rw [counted,full,Nat.and_comm,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (wordRange b o)] at x
  rw [counted,outsideBits _ _ (wordRange b o)] at y
  have vs : Valid geo.val (box Scoring.label (Scoring.bitset (R a.val)) (Scoring.bitset 0)) t (Scoring.bitset m) := by
    have sets (s : Nat) : bits s=Scoring.bitset s := rfl
    simpa only [Sparse.admissible,triple,sets,labelSame] using v
  have z := Scoring.numericalLeafCover geo.val m (R a.val) 0 t vs
  have e (s : Nat) : Scoring.apart s 0 = s := by simp [Scoring.apart]
  change k.val≤present m at x
  change k.val-1≤present (apart m (R a.val)) at y
  rw [numSame] at x y
  have same : apart m (R a.val) = Scoring.apart m (R a.val) := rfl
  rw [same] at y
  simp only [Scoring.basic,e] at z
  omega

theorem bankRaw (b : Bank) (o : ID) (t : TestTree) (good : SmallChart.rawValid geo (treeRaw t) (bits (domainMask b o))) :
    weightR b.val≤leaves t := by
  by_cases z : b.val=0
  · simp [weightR,z]
  · let k : Key := ⟨b.val-1,by have := b.isLt; omega⟩
    have name : R b.val=rm[k.val]! := by simp [R,z,k]
    have eq : bits (domainMask b o) = acted (orient o) (Chart48.node k) := by
      rw [domainMask,actionSet,name]
      rfl
    rw [eq] at good
    have pay := SmallChart.rawLower chart (treeRaw t) k (orient o) good
    change weight[k.val]! ≤ SmallChart.leaves (treeRaw t) at pay
    simpa [weightR,z,k,rawLeaves] using pay

theorem monoPaid (a b : Bank) (o : ID) (k : Fin 43) (t : TestTree)
    (v : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (few : (big ^^^ thresh (tally (R a.val)) 2).testBit (lane b o) = true)
    (priced : (weightGE k.val).testBit (lane b o) = true) : k.val ≤ leaves t := by
  apply (projectedPrice k b o priced).trans
  apply bankRaw
  have few' : ¬ 2 ≤ atCount (tally (R a.val)) (lane b o) := by
    intro z
    have bad := (cmpGood _ _ _ (posLane b o)).2 z
    simp [Nat.testBit_xor,liveWide,bad] at few
  rw [counted] at few'
  have mono := singleTag (R a.val &&& domainMask b o) (by omega)
  apply rawIf (bits (domainMask b o)) (box geo.tag (bits (R a.val)) (bits 0)) t v
  intro j
  cases j with
  | inl j => exact ⟨j,fun _ _ h => h⟩
  | inr j =>
    fin_cases j
    · obtain ⟨owner,ok⟩ := mono
      refine ⟨owner,fun r hr h => ok r ((useAnd _ _ _).2 ⟨?_,hr⟩)⟩
      simpa [box] using h
    · refine ⟨0,?_⟩
      intro p _ hp
      have falseBit : (0 : Nat).testBit p.val = true := by simpa [box,bits] using hp
      simp at falseBit

end Local
end PCX150.Scalar

namespace PCX150.Scalar.Local
open PCX150.Chart48 PCX150.SmallChart
open PCX150.Sparse (TestTree Valid box leaves)
theorem chosenSet (a : Bank) : bits (R a.val) = PrivateGame.candidate a := by
  by_cases z : a.val=0
  · ext r; simp [bits,R,PrivateGame.candidate,z]
  · simp [R,PrivateGame.candidate,z]

theorem activeSet (b : Bank) (o : ID) : bits (domainMask b o) = dataB b o := by
  rw [domainMask,actionSet,chosenSet]
  rfl

theorem fullSet : bits full = Set.univ := by
  ext r
  exact iff_of_true (by change full.testBit r.val=true; rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact r.isLt) trivial

theorem sameLow (m : Nat) : sameMask m < 2^7056 := by
  let f := fun i : Nat => if m.testBit i then everyCol[i]! else big ^^^ everyCol[i]!
  have sub (xs : List Nat) (n : Nat) : xs.foldl (fun t i => t &&& f i) n ≤ n := by
    induction xs generalizing n with
    | nil => exact le_rfl
    | cons a l ih => exact (ih _).trans Nat.and_le_left
  exact lt_of_le_of_lt (sub _ big) (by unfold big; have := Nat.two_pow_pos 7056; omega)

theorem learntMiddle (p : ∀ i : NodeID, nodeOK i.val=true) (a b : Bank) (o : ID) (k : Nat) (t : TestTree)
    (good : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (data : (extraWord a.val k).testBit (lane b o)=true) : k≤leaves t := by
  let n := startsExtra (a.val+1)-startsExtra a.val
  let z := fun i => exts (startsExtra a.val+i)
  let maskOf := fun i => sameMask (testMask (z i%2048))
  let cost := fun i => getB a.val (z i)
  have foldEq (d w : Nat) : closeWord d w = RootBits.closeWord d w := by
    induction d with
    | zero => rfl
    | succ d ih => simp [closeWord,RootBits.closeWord,ih]
  have data' : (((RootBits.closeWord 6 ((List.range n).foldl
        (fun acc i => acc ||| (maskOf i <<< (7056*cost i))) 0)) >>> (7056*k))%2^7056).testBit (lane b o)=true := by
    simpa only [extraWord,packedExtras,foldEq] using data
  obtain ⟨i,mem,paid,eq⟩ := RootBits.extractWord maskOf cost k (lane b o)
    (fun i _ => sameLow _) (posLane b o) data'
  have cells := meetFixed b o eq
  have same : bits (testMask (z i % 2048)) = bits (domainMask b o) := by
    ext r
    change (_=true) ↔ (_=true)
    rw [cells,domainBit]
  have useful : Sparse.admissible geo (triple (testMask (z i %2048)) (R a.val) 0) t := by
    change Valid _ _ _ (bits (testMask (z i%2048)))
    rw [same]
    exact good
  exact paid.trans (middlePaid p _ _ t useful)

theorem decodedRow (p : ∀ i : NodeID, nodeOK i.val=true) (a b : Bank) (o : ID) (k : Fin 43)
    (hit : ((rowQual a.val)[k.val]!).testBit (lane b o)=true) (t : TestTree)
    (good : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t) : k.val≤leaves t := by
  by_cases few : k.val≤1
  · exact few.trans (positive t)
  · have array : (rowQual a.val)[k.val]! =
        (thresh (tally full) k.val &&& thresh (tally (full ^^^ R a.val)) (k.val-1)) |||
        ((big ^^^ thresh (tally (R a.val)) 2) &&& weightGE k.val) ||| extraWord a.val k.val := by
      rw [getElem!_pos _ _ (by simpa [rowQual] using k.isLt)]
      simp [rowQual,few]
    rw [array] at hit
    simp only [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at hit
    rcases hit with (⟨x,y⟩ | ⟨x,y⟩) | u
    · exact countPaid a b o k t good x y
    · exact monoPaid a b o k t good x y
    · exact learntMiddle p a b o k.val t good u

theorem resolve38 (p : ∀ i : NodeID, nodeOK i.val=true) (all : ∀a : Bank, covered a.val=true) : TreeLower := by
  intro A B ia ib ic x y z
  apply PrivateGame.allThree ?_ x y z
  apply reachTarget all
  · intro b o z bitsOK r hr
    have real : active b o r = true := by
      rw [←activeSet] at hr
      exact (domainBit b o r).symm.trans hr
    exact upperMask _ b o bitsOK r real
  · intro a b o k range hit t good
    apply decodedRow p a b o ⟨k,range⟩ hit t
    change Valid _ (box geo.tag (bits (R a.val)) (bits 0)) _ (bits (domainMask b o))
    have empty : bits 0 = ∅ := by ext r; simp [bits]
    rwa [chosenSet,empty,activeSet]
  · intro a z t good
    apply upperPaid p a.val z t
    change Valid _ (box geo.tag (bits (R a.val)) _) _ (bits full)
    rw [chosenSet,fullSet]
    exact good

end PCX150.Scalar.Local

namespace PCX150.Scalar
open PCX150.Chart48
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem orbit0 : covered 0 = true := by decide +kernel

private theorem orbit1 : covered 1 = true := by decide +kernel

private theorem orbit2 : covered 2 = true := by decide +kernel

private theorem orbit3 : covered 3 = true := by decide +kernel

private theorem orbit4 : covered 4 = true := by decide +kernel

private theorem orbit5 : covered 5 = true := by decide +kernel

private theorem orbit6 : covered 6 = true := by decide +kernel

private theorem orbit7 : covered 7 = true := by decide +kernel

private theorem orbit8 : covered 8 = true := by decide +kernel

private theorem orbit9 : covered 9 = true := by decide +kernel

private theorem orbit10 : covered 10 = true := by decide +kernel

private theorem orbit11 : covered 11 = true := by decide +kernel

private theorem orbit12 : covered 12 = true := by decide +kernel

private theorem orbit13 : covered 13 = true := by decide +kernel

private theorem orbit14 : covered 14 = true := by decide +kernel

private theorem orbit15 : covered 15 = true := by decide +kernel

private theorem orbit16 : covered 16 = true := by decide +kernel

private theorem orbit17 : covered 17 = true := by decide +kernel

private theorem orbit18 : covered 18 = true := by decide +kernel

private theorem orbit19 : covered 19 = true := by decide +kernel

private theorem orbit20 : covered 20 = true := by decide +kernel

private theorem orbit21 : covered 21 = true := by decide +kernel

private theorem orbit22 : covered 22 = true := by decide +kernel

private theorem orbit23 : covered 23 = true := by decide +kernel

private theorem orbit24 : covered 24 = true := by decide +kernel

private theorem orbit25 : covered 25 = true := by decide +kernel

private theorem orbit26 : covered 26 = true := by decide +kernel

private theorem orbit27 : covered 27 = true := by decide +kernel

private theorem orbit28 : covered 28 = true := by decide +kernel

private theorem orbit29 : covered 29 = true := by decide +kernel

private theorem orbit30 : covered 30 = true := by decide +kernel

private theorem orbit31 : covered 31 = true := by decide +kernel

private theorem orbit32 : covered 32 = true := by decide +kernel

private theorem orbit33 : covered 33 = true := by decide +kernel

private theorem orbit34 : covered 34 = true := by decide +kernel

private theorem orbit35 : covered 35 = true := by decide +kernel

private theorem orbit36 : covered 36 = true := by decide +kernel

private theorem orbit37 : covered 37 = true := by decide +kernel

private theorem orbit38 : covered 38 = true := by decide +kernel

private theorem orbit39 : covered 39 = true := by decide +kernel

private theorem orbit40 : covered 40 = true := by decide +kernel

private theorem orbit41 : covered 41 = true := by decide +kernel

private theorem orbit42 : covered 42 = true := by decide +kernel

private theorem orbit43 : covered 43 = true := by decide +kernel

private theorem orbit44 : covered 44 = true := by decide +kernel

private theorem orbit45 : covered 45 = true := by decide +kernel

private theorem orbit46 : covered 46 = true := by decide +kernel

private theorem orbit47 : covered 47 = true := by decide +kernel

private theorem orbit48 : covered 48 = true := by decide +kernel

theorem allRootCases : ∀ a : Fin 49, covered a.val = true := by
  intro a
  have range := a.isLt
  by_cases l24 : a.val < 24
  ·
    by_cases l12 : a.val < 12
    ·
      by_cases l6 : a.val < 6
      ·
        by_cases l3 : a.val < 3
        ·
          by_cases l1 : a.val < 1
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=0 by omega)) orbit0
          ·
            by_cases l2 : a.val < 2
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=1 by omega)) orbit1
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=2 by omega)) orbit2
        ·
          by_cases l4 : a.val < 4
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=3 by omega)) orbit3
          ·
            by_cases l5 : a.val < 5
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=4 by omega)) orbit4
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=5 by omega)) orbit5
      ·
        by_cases l9 : a.val < 9
        ·
          by_cases l7 : a.val < 7
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=6 by omega)) orbit6
          ·
            by_cases l8 : a.val < 8
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=7 by omega)) orbit7
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=8 by omega)) orbit8
        ·
          by_cases l10 : a.val < 10
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=9 by omega)) orbit9
          ·
            by_cases l11 : a.val < 11
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=10 by omega)) orbit10
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=11 by omega)) orbit11
    ·
      by_cases l18 : a.val < 18
      ·
        by_cases l15 : a.val < 15
        ·
          by_cases l13 : a.val < 13
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=12 by omega)) orbit12
          ·
            by_cases l14 : a.val < 14
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=13 by omega)) orbit13
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=14 by omega)) orbit14
        ·
          by_cases l16 : a.val < 16
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=15 by omega)) orbit15
          ·
            by_cases l17 : a.val < 17
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=16 by omega)) orbit16
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=17 by omega)) orbit17
      ·
        by_cases l21 : a.val < 21
        ·
          by_cases l19 : a.val < 19
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=18 by omega)) orbit18
          ·
            by_cases l20 : a.val < 20
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=19 by omega)) orbit19
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=20 by omega)) orbit20
        ·
          by_cases l22 : a.val < 22
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=21 by omega)) orbit21
          ·
            by_cases l23 : a.val < 23
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=22 by omega)) orbit22
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=23 by omega)) orbit23
  ·
    by_cases l36 : a.val < 36
    ·
      by_cases l30 : a.val < 30
      ·
        by_cases l27 : a.val < 27
        ·
          by_cases l25 : a.val < 25
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=24 by omega)) orbit24
          ·
            by_cases l26 : a.val < 26
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=25 by omega)) orbit25
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=26 by omega)) orbit26
        ·
          by_cases l28 : a.val < 28
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=27 by omega)) orbit27
          ·
            by_cases l29 : a.val < 29
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=28 by omega)) orbit28
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=29 by omega)) orbit29
      ·
        by_cases l33 : a.val < 33
        ·
          by_cases l31 : a.val < 31
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=30 by omega)) orbit30
          ·
            by_cases l32 : a.val < 32
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=31 by omega)) orbit31
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=32 by omega)) orbit32
        ·
          by_cases l34 : a.val < 34
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=33 by omega)) orbit33
          ·
            by_cases l35 : a.val < 35
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=34 by omega)) orbit34
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=35 by omega)) orbit35
    ·
      by_cases l42 : a.val < 42
      ·
        by_cases l39 : a.val < 39
        ·
          by_cases l37 : a.val < 37
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=36 by omega)) orbit36
          ·
            by_cases l38 : a.val < 38
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=37 by omega)) orbit37
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=38 by omega)) orbit38
        ·
          by_cases l40 : a.val < 40
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=39 by omega)) orbit39
          ·
            by_cases l41 : a.val < 41
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=40 by omega)) orbit40
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=41 by omega)) orbit41
      ·
        by_cases l45 : a.val < 45
        ·
          by_cases l43 : a.val < 43
          ·
            exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=42 by omega)) orbit42
          ·
            by_cases l44 : a.val < 44
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=43 by omega)) orbit43
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=44 by omega)) orbit44
        ·
          by_cases l47 : a.val < 47
          ·
            by_cases l46 : a.val < 46
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=45 by omega)) orbit45
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=46 by omega)) orbit46
          ·
            by_cases l48 : a.val < 48
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=47 by omega)) orbit47
            ·
              exact Eq.mpr (congrArg (fun n => covered n = true) (show a.val=48 by omega)) orbit48

end PCX150.Scalar

namespace PCX150.Scalar
theorem bankReady (i : Local.NodeID) : nodeOK i.val = true := by
  have ok := List.all_eq_true.mp certifiedBlock i.val (List.mem_range.mpr i.isLt)
  simpa using ok
end PCX150.Scalar

theorem PEqualNP.Outside.L_pcx_150 :
    ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 51) :=
  PCX150.finishFromBounds PCX150.OrbitCert.hard
    (PCX150.Scalar.Local.resolve38 PCX150.Scalar.bankReady PCX150.Scalar.allRootCases)

import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_150_aux
namespace PCX150.FastPresent
def mark (m : Nat) : Nat := if m = 0 then 0 else 1
def three (m : Nat) : Nat :=
  mark (m &&& 3) + mark (m &&& 12) + mark (m &&& 48)
def lookup (x : Nat) := (0xfefefea9fefefea9fefefea9a9a9a954 >>> (2*(x % 64))) % 4
theorem sixBits : ∀ r : Fin 64, lookup r.val = three r.val := by decide +kernel
theorem truncated (n x m : Nat) (hm : m < 2^n) :
    ((x % 2^n) &&& m) = x &&& m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases sm : i < n
  · simp [Nat.testBit_and,Nat.testBit_mod_two_pow,sm]
  · have h := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
         (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt sm)))
    simp [Nat.testBit_and,Nat.testBit_mod_two_pow,h]
theorem shifted (s x m : Nat) : (((x >>> s) &&& m) <<< s) = x &&& (m <<< s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : s ≤ i
  · have back : s + (i-s) = i := by omega
    simp [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,h,back,
      Nat.add_comm (i-s) s]
  · simp [Nat.testBit_and,Nat.testBit_shiftLeft,h]
theorem markShift (x s m : Nat) :
    mark ((x >>> s) &&& m) = mark (x &&& (m <<< s)) := by
  rw [←shifted]
  simp [mark,Nat.shiftLeft_eq]
theorem lookup_correct (x s : Nat) :
    lookup (x >>> s) = mark (x &&& (3 <<< s)) +
      mark (x &&& (12 <<< s)) + mark (x &&& (48 <<< s)) := by
  let r : Fin 64 := ⟨(x >>> s) % 64, Nat.mod_lt _ (by decide)⟩
  have h := sixBits r
  change lookup ((x >>> s) % 64) = three ((x >>> s)%64) at h
  have idem (a : Nat) : lookup (a % 64) = lookup a := by simp [lookup]
  rw [idem] at h
  rw [h,three]
  have bound (m : Nat) (small : m<64) : (((x>>>s)%64) &&& m) = (x>>>s) &&& m :=
    truncated 6 (x >>> s) m small
  rw [bound 3 (by decide),bound 12 (by decide),bound 48 (by decide),
      markShift,markShift,markShift]
def fast (x : Nat) : Nat :=
  mark (x &&& 63) + mark (x &&& 4032) + mark (x &&& 258048) + mark (x &&& 16515072) + lookup (x >>> 24) + lookup (x >>> 30) + lookup (x >>> 36) + lookup (x >>> 42) + lookup (x >>> 48) + lookup (x >>> 54)
def tags : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,13194139533312,52776558133248,211106232532992,844424930131968,3377699720527872,13510798882111488,54043195528445952,216172782113783808,864691128455135232]
def slow (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tags[k]! != 0 then n+1 else n) 0
theorem inc (m n : Nat) : (if m != 0 then n+1 else n) = n + mark m := by
  by_cases h : m=0 <;> simp [h,mark]
theorem exactFast (x : Nat) : fast x = slow x := by
  unfold fast slow
  rw [show List.range 22 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] by decide]
  simp only [lookup_correct,List.foldl_cons,List.foldl_nil,inc,Nat.zero_add,Nat.add_assoc]
  rfl
end PCX150.FastPresent
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
  let j := w % 128
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
  let j := w % 128
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
def index (code : Nat) : Key := Fin.ofNat 48 (code % 64)
def turn (code : Nat) : ID := Fin.ofNat 144 (code/64)
def mono (code : Nat) : Tag := Fin.ofNat 22 (code/64)
def node (k : Key) := bits rm[k.val]!
def next (k : Key) (q : Var) (b : Bool) : Option Key :=
  let d := slot k q b
  if d % 64=63 then none else some (index d)
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
    by_cases hom : d % 64=63
    · simp only [next,show slot k q b % 64 = 63 from hom,ite_true]
      refine ⟨mono d,?_⟩
      intro r h
      have both : (rm[k.val]!.testBit r.val && (geo.val r q == b)) = true := by
        have hl : rm[k.val]!.testBit r.val = true := h.1
        simp [hl,h.2]
      have e := facts r
      change (if d % 64=63 then _ else _) at e
      rw [if_pos hom] at e
      exact e both
    · simp only [next,show ¬slot k q b % 64 = 63 from hom,ite_false]
      refine ⟨orient (turn d),?_⟩
      ext r
      have e := facts r
      change (if d % 64=63 then _ else _) at e
      rw [if_neg hom] at e
      change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
      rw [backApply,←e]
      simp [node,bits]
  subadd := allCost
theorem rootWeight : chart.wt chart.root = 43 := by decide +kernel
end PCX150.Chart48
namespace PCX150.Chart48
open PCX150.SmallChart
def alongCode : Array Nat := #[21542142465,38789383680,56036622346,68971138567,73015430152,303041801,94842913043,107776907011,111687505156,4749596165,129337398018,142270930716,146064540701,9179301150,163831546660,167554327832,13556327961,17870299674,176180175643,189702736390,202635619626,206262110251,26594969900,224196888370,227751244559,30971343888,35285970961,236377747730,250065074187,253574589196,43960118285,271624047421,275063258681,48336027450,52651102523,283690209852,293185860110,296591691587,61308080196,65616823605,305212311094,77599294007,319053580308,322446105877,82884304406,340612551757,343934324297,87259762506,91575294539,352561732428,362174817303,365463214163,100232272212,104540558631,374083376680,116406047273,388044954712,391313709344,121804577313,126120315682,399941323811,409601333279,412839387230,134773875039,139085373531,421462761820,150900713821,425811923749,156302791718,160614590307,434435598436,172455716183,448408332902,451679053614,182169921583,186485652272,460306660401,469966677549,473204731500,195139219309,199450717801,481828106090,211266058091,486177260339,216668128308,220979934577,494800942706,232821060423,504464031032,507752429940,242521487989,246830298688,516373116737,258695785282,520718873662,264044311871,268356108409,529342546298,280250973048,289851142469,533724820038,301813417852,543268818248,546674657661,311391046270,315701821264,555297308753,327684283730,559643065678,332915834447,337227632770,568266740099,349239936129,358722200405,572648547414,370801923973,577010228825,380230328154,384542137222,585633913991,396669847650,406031926880,590010943329,418229084809,431166686565,594424392807,440426392936,444738201994,603048077963,457035189360,466229496430,607426612079,478594429069,491531369587,500607646070,611857431159,513090025614,526024216187,539278869119,616303133568,551895466383,564830506884,582078138760,599325052300]
def invName : Array Nat := #[0,1,2,3,4,5,10,7,8,9,6,14,12,13,11,15,16,18,17,19,36,29,30,28,24,25,27,26,23,21,22,31,37,38,35,34,20,32,33,40,39,41,50,43,44,61,67,68,60,59,42,57,58,54,53,55,56,51,52,49,48,45,62,63,70,69,66,46,47,65,64,71,88,83,84,76,75,77,94,95,100,99,93,73,74,92,91,87,72,89,90,86,85,82,78,79,97,96,101,81,80,98,102,116,117,114,113,107,108,109,122,121,124,106,105,120,103,104,119,118,115,111,110,123,112,125,126,135,134,133,131,130,137,129,128,127,136,132,139,138,142,141,140,143]
def follow (o : ID) (g : G) : ID := Fin.ofNat 144 ((alongCode[o.val]! >>> (8*g.val)) % 256)
def inverse (o : ID) : ID := Fin.ofNat 144 invName[o.val]!
set_option maxRecDepth 10000 in
theorem followBoard : ∀ (o : ID) (g : G) (r : Sample),
    backward words[(follow o g).val]! 9 r = backward words[o.val]! 9 (rs g r) := by decide +kernel
set_option maxRecDepth 10000 in
theorem invertBoard : ∀ (o : ID) (r : Sample),
    backward words[(inverse o).val]! 9 (backward words[o.val]! 9 r) = r := by decide +kernel
set_option maxRecDepth 10000 in
theorem zeroBoard : ∀ (r : Sample), backward words[0]! 9 r = r := by decide +kernel
set_option maxRecDepth 10000 in
theorem followAct (o : ID) (g : G) (s : Set Sample) :
    acted (gen g) (acted (orient o) s) = acted (orient (follow o g)) s := by
  ext r
  change ((assemble words[o.val]! 9).s.symm (rs g r) ∈ s) ↔
    ((assemble words[(follow o g).val]! 9).s.symm r ∈ s)
  rw [backApply,backApply,followBoard]
set_option maxRecDepth 10000 in
theorem zeroAct (s : Set Sample) : acted (orient 0) s = s := by
  ext r
  change ((assemble words[0]! 9).s.symm r ∈ s) ↔ r ∈ s
  rw [backApply,zeroBoard]
set_option maxRecDepth 10000 in
theorem invertAct (o : ID) (s : Set Sample) : acted (orient o) (acted (orient (inverse o)) s) = s := by
  ext r
  change ((assemble words[(inverse o).val]! 9).s.symm ((assemble words[o.val]! 9).s.symm r) ∈ s) ↔ r ∈ s
  rw [backApply,backApply,invertBoard]
set_option maxRecDepth 10000 in
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
set_option maxRecDepth 10000 in
theorem nextName (k : Key) (q : Var) (b : Bool) :
    plain geo (branch geo (node k) q b) ∨ ∃ (j : Key) (o : ID), branch geo (node k) q b = acted (orient o) (node j) := by
  let d := slot k q b
  have facts := allSteps k q b
  by_cases hom : d % 64=63
  · left
    have h := chart.proper k q b
    change (match next k q b with | none => _ | some j => _) at h
    rw [show next k q b = none by simp [next,show slot k q b % 64 = 63 from hom]] at h
    exact h
  · right
    refine ⟨index d,turn d,?_⟩
    ext r
    have e := facts r
    change (if d % 64=63 then _ else _) at e
    rw [if_neg hom] at e
    change (_ ∧ geo.val r q = b) ↔ (rm[(index d).val]!.testBit ((assemble words[(turn d).val]! 9).s.symm r).val = true)
    rw [backApply,←e]
    simp [node,bits]
def named (s : Set Sample) := plain geo s ∨ ∃ (k : Key) (o : ID), s = acted (orient o) (node k)
set_option maxRecDepth 10000 in
theorem namedBranch {s : Set Sample} (h : named s) (q : Var) (b : Bool) : named (branch geo s q b) := by
  rcases h with ⟨a,mono⟩ | ⟨k,o,rfl⟩
  · exact Or.inl ⟨a,fun r hr => mono r hr.1⟩
  · rw [branchAct]
    rcases nextName k ((orient o).v.symm q) b with mono | ⟨j,p,eq⟩
    · exact Or.inl (actedPlain _ mono)
    · obtain ⟨u,hu⟩ := composeAct o p (node j)
      exact Or.inr ⟨j,u,by rw [eq,hu]⟩
set_option maxRecDepth 10000 in
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
open PCX150.SmallChart (Sample Var Tag Key)
namespace PCX150.Scalar
open PCX150.Chart48
private def cubePart0 : Array Nat := #[0,0xcf510510145140,0xa20a200cfa28a00,0x5100cfa204924bf,0xa20a200cfa28a3f,0xcf51051014517f,0x5100cfa20492480,0xaeff305dfb6db7f,0x5df5dff305d75ff,0xf30aefaefebaebf,0xfffffffffffffff,63]
private def cubePart1 : Array Nat := #[0,0x488488333514028,0x33384484428a005,0x844333488861012,0x33384484428afc5,0x488488333514fe8,0x844333488861fd2,0x7bbcccb7779efed,0xb77b77cccaebfd7,0xccc7bb7bbd75ffa,0xfffffffffffffff,4032]
private def cubePart2 : Array Nat := #[0,0x281c3c142300861,90657122719368468,0xc3c281281c0028a,90657122719626516,0xc3c281281c3f28a,0x281c3c14233f861,0x3c3d7ed7e3ffd75,0xd7e3c3ebdcff79e,0xebdebd3c3f3faeb,0xfffffffffffffff,258048]
private def cubePart3 : Array Nat := #[0,5912485282197699,0x2afc001500c30c,5912485265682627,0xfc002a02a030c30,0x2afc0015fcc30c,0xfc002a02aff0c30,0xfd503ffeaff3cf3,0xfeafea03fffcf3c,0x3ffd5fd5fcf3cf,0xfffffffffffffff,16515072]
private def cubeValue (w : Nat) : Nat :=
  cubePart0[w % 16]! &&& cubePart1[(w >>> 4) % 16]! &&&
  cubePart2[(w >>> 8) % 16]! &&& cubePart3[(w >>> 12) % 16]!
private def banksCodesPart0 : Array Nat := #[0x4113312331254235423433353334231523142313222522242223112211110000,0x5226122641625122441635262241511125224115443233563141633253323426,0x3127423723192318312831292229222722281334333746323631343133466226,0x9111282256223546245148324732522325153145115131718332733237264118,0x5611336323548226722692264613112491226115362322453926382622712424,0x222a3984333a1339198219181726651681112922493239315362531383163535,0x52282518733423592942239482463175314711713958717378335318312a9725,0x9741583722473a2622a1952924275722811528674a3233a61376934992235229,0x4734353776375911822347499151a22653826729419471241127a12294263148,0x3986298211471175531a133a93569622529128243a312a1158763946a3163935,0x3648291773399339235a59422a42157623a43187942337293a23935313933a46,0x44694753242a2729811871183943782698269651861513a692299228522a2972]
private def banksCodesPart1 : Array Nat := #[0x2447419949184719912947643399285517239726287162a62872317731782277,0x6834931938376618591597111629a622255729187171917153592377793253a2,0x6856a22357248722972252486913551852857916392854292829429918466a32,0xa916958298239428372a736967959373935813a33a863a76114a118711a51984,0x3a4319767a269a2699512a7153795867a61533a9922a36787962a155a73115a6,0x1a2317282a449a11974556773a29227a8458a2297863272a9627195839733949,0x95497184931aa37676189915591759721929674988344a198174767372832747,0x11a88954295788568a229a22581869924a9246a46599a319617984845873a129,0x117797519723982828751729469939489393937815893aa67175765871989955,0x8915a37393698962581a2a1a8864257759575a72698267a21973997619a6a2a6,0x479397245729957318769843398315a339793a733a49aa16aa26967599715399,0x4aa25775a82329a45a7158585a551a2854789448a2673a2a9429962995584889]
private def banksCodesPart2 : Array Nat := #[0x44998744295a555a4759476975768a3488398179939472a35747891372894794,0x914a287455a425a9584928892a8495a22aa2174876a2192a83a4738986749359,0xa2732a589a46164a2847a93479391837544a167859749a155a4499449a429972,0x951aaa32a1a2a5926a927782796476842477882928577483a48677432a2a61a9,0x69185918a3a2a3848a5613996773885399279278527a924a7a1379196a199818,0x1a763a833a79a91513a9a962377a5a8269a299a69a23172a738a46a9394a71a5,0x9a7229a998a2a3598a39247a81a9a39453a98a13a7232a89a772a6298a719a24,0x99751a2a927a981a72a9a8197a92a786a2799a8638a9a189a9391a2987a69a17,0x6aa29858977197282878547a5a58577866a949993978a9531aa668a3a9557178,0x9837997398839a4339893aa3197984795a575a47a3a38992167a1778994715a9,0x9929585a964a886988598849957874897a43788696784aa387735a2a1a7395a3,0x8a64a9648a446a59a6747959a2a3794979699a554aa4799494787784aa235a75]
private def banksCodesPart3 : Array Nat := #[0x95a49a4498845889995793796a69697964a94a6aa5a67993a593a3a48818944a,0x7783174aa743867918897589584aaa34783878392977557a59a4955a99829974,0xa569889384a3a684a6a287821a4998298894a1a4a44967a46889aa429891a483,0x28a849a9a7373a7871a8791859796aa69918a58474a3a473a4a66a9367a3aa24,0x9a7147a72a78992aa92947a89a279a379a7698a63a8983a9a9928a9293a79a28,0x28a979a2a379a389489a48a94a794a89478a79a6277aa179728a71a9a919a771,0xa88288a277a673a97a82a278a8867a86a9728a7282a9917aa8297a38297a7a29,0xa47987958a757958a73a99581a4aa993987319899aa67678177a91aa9a1a8a29,0x88589a5789945a5a2a8aaa17a3a8aa64aa928599a89498a45879a1a87aa29775,0x1978aa5378837869aa4387a34aa8777348aa1aa318a9577799a39a833aa98498,0xaa447967aa19a2a984892aa99748967758785aa5a9a1a859a92a6a5a677986a9,0x6789a38a7a5979734a7a947a4a8a874977491a79a5a3a9a627aaa9699747a3a7]
private def banksCodesPart4 : Array Nat := #[0x9949a4a58a3a99957a2a68999a745aa459a9a6a45a8999849aa28a6974a9a774,0x76977984aa72aa868974aa812a9aa7836999985a5a4a588737aa8478aa399579,0xa81aa4a3a689a7a66aa3679887848873a7a289597599a1a984877a9477a46aa4,0x9a75197aa9739a7398a39399479989189729787628778aa68884a5a4a8a27aa1,0x67a8a7738a7319a9984a8a949a47a994995a994a88a45a799a589a48a589a775,0xa7475a87967a76a9a7847a845a78885aa869a84985a9a7587a93a893859a77a3,0x58a999a49a848a4979a3597a875a6a897a697a49677a577a57a7a959a949a489,0x75a9a5796a97796a8a74a974a67984a97a6874a8957a6a7968a977a5a9958a59,0x69aa1a7aa9a39aa31aa98a1889a29a29a8377a37a88487a469a96a9888a3776a,0x86aaa6a9aa48aa93aa836aa89a5aaa945a9a5a8aa8a49aa45aa9aa758aa55aa8,0xaa69a75a7a5a7a4a68aa6a7a6a8a75aaa47aaa57aa4757aaa94a6aa7a85aa84a,0x17aaa58aa5a7a4a9a8a594aa1a9a18aa7aa5a9a5a6a859aa8a6aa68a8a4aaa59]
private def banksCodesPart5 : Array Nat := #[0x7978a83a99789a2aa5a8a7a3a76a8aa3a7a4a57a85aa7aa4aa74a49a74aa9a6a,0x78897899a873aa29a72a8898799988788887889758a72aa7a2a895a99878a958,0x778998798999a91a8aa297787979798978888a84889988798798a5997a7378a3,0xaa2aa8a6799867a9786a9979988999899788a3a997774a9a4aa9877977798789,0xa5a98aa4aa84aa58a9a47aa3aa73a8a39a4a4aaaaaa2a1aaaaa62aaaa3aaaa1a,0x9a7788a798a9a9787a6aa6a7a86a58aa5a7a5aa76aa9aa951a8a1aa8aa49a74a,0x7a997a79777aa779a789a999a989a977888aa899a879a8788a987a7878a988a8,0xa88988a9a778997a9a789a9887a977a9999a998a9a79978a99a989a98a99977a,0xaaa35aaa778aa997a89899a798a877a88a79877a7a898a97a97987a779a9889a,0xaa997a7aaa7789aaa87a8aa89aa9aa6aa6aaa4aaaaa51aaaaa5aaa4a6aaaaaa4,0x8aa9a77a87aa7aa98aa7a97aa9a988aaa8a9aa789a7aa7a97aa7a8a7a9a88a8a,0xaaa89aaaaa7aaaa9a99aa89aaa98a8a8a7a87aa89aa799aa9aa88a9a8a7aaa79]
private def banksCodesPart6 : Array Nat := #[0xaaaaaa9aa7aaa9aa]
private def banksCodes (i : Nat) : Nat :=
  if i<73 then (if i<36 then (if i<12 then banksCodesPart0 else (if i<24 then banksCodesPart1 else banksCodesPart2)) else (if i<60 then (if i<48 then banksCodesPart3 else banksCodesPart4) else (if i<72 then banksCodesPart5 else banksCodesPart6)))[i % 12]! else default
def banks (i : Nat) : Nat := cubeValue (((banksCodes (i/16)) >>> (16*(i % 16))) % 65536)
private def nodesField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def nodesClassDataPart0 : Array Nat := #[0x2492491249249249249249200df,2199023255651,0x3fffffaaaa9554000a4,0x2a555555540000000a7,41,41,4397509640297,4398012956778,4398038122603,44,4398045986924,45]
private def nodesClassDataPart1 : Array Nat := #[45,45,45,45,45,45,45,45,45,45,45,45]
private def nodesClassDataPart2 : Array Nat := #[45,4393751543917,46,46,46,46,46,46,46,46,46,46]
private def nodesClassDataPart3 : Array Nat := #[46,46,46,46,46,46,46,46,46,46,46,46]
private def nodesClassDataPart4 : Array Nat := #[46,46,46,46,46,46,46,46,46,46,46,46]
private def nodesClassDataPart5 : Array Nat := #[46,46,46,4398038122606,47,47,47,47,47,47,47,47]
private def nodesClassDataPart6 : Array Nat := #[47,47,47,47,47,47,47,47,47,47]
private def nodesClassData (i : Nat) : Nat :=
  if i<82 then (if i<36 then (if i<12 then nodesClassDataPart0 else (if i<24 then nodesClassDataPart1 else nodesClassDataPart2)) else (if i<60 then (if i<48 then nodesClassDataPart3 else nodesClassDataPart4) else (if i<72 then nodesClassDataPart5 else nodesClassDataPart6)))[i % 12]! else default
private def nodesClass (i : Nat) : Nat := nodesField ((nodesClassData (i/32))) 6 (i % 32)
private def nodesFirstDataPart0 : Array Nat := #[0x28201810101010146c6c6c6babaa81d1c9c929291918a8505048484800014024000,0x106418300c0300c0300c0300c0300c02f8be2f8be23870148501384e0280a0280a0280a0280a02d000,0x9c0a05028140a05028140a02892ed12511a8000000000d80000000000013000000000004800,0x8da368da36598fa3386c1b06c148080100000501060c0300c0300c0300c02f8be2f85213d000,0,0x4f6cd9b366cd9b366cd9b366cb16182c4c78e1a203000000000000003800,0xc420080400c0201000000000000039d5fafd4a9143a044a25126e359aacd5daed3868324800,0x16c68341a0d068341a0d068341208c460d06802c54260b055ca150a6130982b0cc623118c804,0x620200801004000000000000000000000000000000000013fc168421084210842105514e4d8c42fd000,0x42a150a85429e4d164b0576b73399cca6532078000000000000000000000000000000000483d,0x40200000000000000000000000000000000000000000000000eb576bb5daed76bb51a3c800,0x4b2aebae8a230c30c30c30c30c28a10410400000000000003002]
private def nodesFirstDataPart1 : Array Nat := #[0x46318c5ce735ad6b18c5ad6b5ad6b5ad6a50c000282a,0x638595d75d73cd34d23efbc30c30c3000000000000000000303b,0x596596596575d75d75d75d75d550208208208208208208203071,0x5ad394a31739ad6b1084210739ce000000000000289d,0x4a52949ef7bdef7bdef7bdca490000000000000028b3,0x407ee1bb76ccd9b25ebd791222850a0408102040810000000000000038c5,0x6eeeeeeeeeeeeeeeeeaaaaaaaa2200002105,0x444444444444444444444444410000002112,0x6386186186186165965965931c30c30a28a2882081800000311a,0x7ffffffa80000000114b,0x41041041041041041041040fa869a6124104000000000000314e,0x48c8c8c8c8484840c0c0b8b8b5b5b5b5b5b5b5b3333199068686858400000000416e]
private def nodesFirstDataPart2 : Array Nat := #[0x595944444440bebe8e8e8e8e8e8c0c0a0a07878787870606058584848300000041ff,0x601806018000000000000006899e6799e6798adf57d5f57d5f573d875d5735bd6759d6759d6759d000,0x7fffeeeeeeeeeeeeeeeeeeeeeeee80002003,0x7fffffef7bdef7a5294a5294a5294a50000000002812,0x665dddd91111111110888888888000002031,0x430c30c30c30c30c30befbcf3ce000000000000000000000303d,0x7ffffeeee66666666666666665d80000205e,0x555554a0000000001072,0x5b6db6db6db6db6d96596575d75d75d555555555400000003074,0x555000000000000010a1,0x7fffffff08a3,0x5294a52939ce108418c4a524200000000000000028a4]
private def nodesFirstDataPart3 : Array Nat := #[0x71c71c71c71c1c71c71c70e38e38e38e082082082082080030b8,240,0x59000000000000000000000018f0,0x7775ddccaaaa9999999988888800000020f5,0x6eeeee6665554cccc9999999999999982103,0x69a69a699e79e79e79e6aaaaaaaaaaaaaaaaaaaaa00000003111,0x4924912492492492492492401945,329,329,0x444000000000000000000000000000002149,0x6eeddda22221999911111111088888002151,0x4cc444444443bbbbbaaaaaaaa8000000215e]
private def nodesFirstDataPart4 : Array Nat := #[0x4c9999999911108888888888880000002167,0x6ddbb76e8cf9f3e7cf9f366cd9b366cb972e5cb8b162c58b162c40003970,0x4b2ca082082080000000000000000000000000000000000031dd,0x5b6db6db64924924489249001a02,0x4ccccccccccccb3333333332aa800000220f,0x4ccaaaaaaaaaaaaa22219991111110002218,0x5dbb76eddbb76eddbb76eddbb7448912244850a142850000000000003a21,0x6318c630739ce739ce42108421084210000000002a7e,0x451430c30c30c30c1041041041040fbefbefbefbefbe00003296,0x7fffffffffffffff000000001ab8,0x7fffffffd2492490000000001abf,0x4e739ce734a5294a5294a5294a400000000000002ac8]
private def nodesFirstDataPart5 : Array Nat := #[0x62c583060c183060c182e5cb972e5cb972e5bb6081020408000000003adb,0x4e9d3a74e0e1c20408102040810204081020408102000000000000003b3d,0x7ff800000b8b,0x2504a0941282504a0940080100200400801002004008000000020ec0f81f03e01bde7bcf71ee38d71ae35c6d800,0x6baebaebaebaebaebae9a69a69a69a0208208208208000003025,0x4081020408102003060c183060c18000000000000000000000000000385a,0x5555555555540000109c,0x4a952a54a952a54a952a54a952a54a952a54a952a54a94000000000038a6,0x49244924924924492492400018f0,0x4c993264b972e5cb972e5cb972e5cb972e5cb972e58000000000000038f4,0x48db6db6db6d9249249249001940,0x46464646464646464646464646461212121212000000000000000000000000004144]
private def nodesFirstDataPart6 : Array Nat := #[0x596575d75d75d75d75d75d75d75d6000000000000000000031d3,0x555552aaaa80000011ff,0x7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af5ebd7af400000000003a01,0x6db6db6db6db6db6db6db6db6db6db6db6db000000000000327b,0x7fd555555000000012b1,0x5b6db6db6da00000000000001ab4,0x4141414141414141414141414141414141414141414141413e3e3e3e3e00000042b9,0x50a142850a142850a142850a142850a142850a142850a14284b000003b3b,0x7cf9f3e7ce9d3a74e9d3a748b162c58b12244850a14183060c1830403b8b,0x125ebd7af5eb264c993264c9932647cf800000000000003c1c]
private def nodesFirstData (i : Nat) : Nat :=
  if i<82 then (if i<36 then (if i<12 then nodesFirstDataPart0 else (if i<24 then nodesFirstDataPart1 else nodesFirstDataPart2)) else (if i<60 then (if i<48 then nodesFirstDataPart3 else nodesFirstDataPart4) else (if i<72 then nodesFirstDataPart5 else nodesFirstDataPart6)))[i % 12]! else default
private def nodesFirst (i : Nat) : Nat := nodesField ((nodesFirstData (i/32))) 11 (i % 32)
private def nodesSecondDataPart0 : Array Nat := #[0x2010080b85424080068db4d844a29108844220a08b108a43e1e0f8783e1e02a203c3b004805,0x13044f13bd4b523e889564d91c390d2470e2338b03d8b02c0b02c0403a0e42707e1d8741b02407d008,0x9cf67925108823d0c858181faf446231132444682b0398e22b91a8d00111601646a3419c801,0x1802801872e2a4a5c8d2348d25c3f08c8d0861013e3353f45514f0a4c8a944418f2450dc2f8be2fd001,0x5d2a345a24d23d1d8e3e5ecf478b5d8ea73d9c8d2602b130823b1c0dc622913888140600480e,0x164e73308e1b8590b61c05e17044108380ca242e0cc0050c0333003224895534248920b9ed3332cc5036,0xf24f924379706d06b0abdeb4aac73800e659edf59ea1b7cdf29ea1238a79976799967d58b913edf5010,0x2b9a49a2e958a2482107032077d8e80e6120073e736fefbdf7c9b03edb8a47d9795606004836,0x26081178bca61ebf77b8e410c404fca5c709b22d88a12801a668f564ecf9ac09fa0678a348d234685017,0x33ec6a849ba2487a1e9ba4a8921fd626ebe1209224b43ba4e7b50d3b40cb2928921e7c9c25100a00504e,0x5c107e6f79d6116338b7a9ea0a72859e0769d860176518be2c8601000122ddf4043304ba8b5ad984d007,0x1e627522958dd2aa568721a84a10771d07290c3087a841cb94c9c568cd7a5cd713b6d919864140005065]
private def nodesSecondDataPart1 : Array Nat := #[0x1b64988e0a8208b9c432e089b22436c38ac0e1853a0899ee4d8f62384e04806002fa532fe6d11a30d038,0x9e9707699a4c5a91a0036c7d9aa70599414acc31e66a9343359d4bd233f3b0d0b36bba9e8e2306fd078,0x16c4c11a3384608d4523b187e9dc649521e062005d825d454ec58d92f4a6a1656958548e0348d00a50a2,0xb4011660f000158171b00e569160d4acf0a7e7b9bc4c44eab95c2dc74b72bc9ea007f9a06616655d0c0,0x14e2609209001694670c1925996056148350cc1f02ea38a6432cf91ceb17b9c9494c521103c8ec2ad0c7,0xb4929385c8ec4d1283a1393a47e2c4463bbee4b8e66b99451106298a40050d37c46feb6aaba4c8c50d7,0x27e991d266992621805a94a478b21c862160300200400402a10c22a8420700807002003f41200600514a,0x370cf9da57130440fe3e0de360bc2187e1e8781d87019056148500f8380100030d7f06bcce5b70c4512f,0x4105becf8b587299c15003203f6d42002f848b284a3483a00a0e70002000840e8000ebe2f7390d6514e,0x276729ae5d9383b8bc2e8b22b0601584000b5000558f730cc027c811b66819662186488ec2a08412514e,0x2e8911ec7596c4f9364a914350a61f010030081c000f5000c3b0f011be003e2f53b0c3afcbaa808d5173,0x2a14a4f1d501c6b72a14863792b46a1afe458c42c00bcda1fc29b4435fd0d36f56c35d89c9fc]
private def nodesSecondDataPart2 : Array Nat := #[0x44d38ca6321e18d944d7a5aca4f20d8c5d87b6594832e8028b2d8cb64530f01c66d32d484a30,0x2e86a80400536aaa9c951be5265de9ee7ad69f94e6191e437d5dd6fe856fe43a4e85926477dd994f501b,0x104388300071d8fe197c5e9785bf58d03404b31e328a2a3a8b9d86e196591344887c0c717905b55b50a4,0x322b39fa5f8d1bb4f139cbd10219e774dc5ecb8f4f12e494962186d99e07801b03c8d23309622087d063,0xdc006595cd5c8c9afc06b18ce1941cd28c160518fda8df577d0734aee8f0ae1d65593517404e5095072,0x54b4bc9f20b78b69da651884d9200020a21e558903c76eb3ac65594e2d8960f82d3509aae5893c355086,0x6ff2e8d82184350a7c7eebba06596ed953ece128c04f43b28620e5795a0200172243ddeaba26316e5084,0x50737cdb24c74861a4651685101840001b86476756b4bcf73146f0a3c4bb2e69aa3e661624f8f03bd0be,0x1e27799e651925311e3f8941a617249da0464943cc32cc9d1cdd33bc7b1939a470018c6177057b5bd0a4,0x452deb4cd031a00523354b9123ecf739ae3b7ad434ccc31ec6300b2abea2a3286a086d8ba2d09e1e5160,0x4c7304b92ac6d10c3cfe3eaef3aad2a528ba2a899f87d1ce5a1183e0d6338c6300a8168300a80179d0d1,0x4db33c9ce4b4462e252c9247f19005800a320b86454d7c18a9e55745bf6a5a550d3d394df33cbf245126]
private def nodesSecondDataPart3 : Array Nat := #[0x6a1303a0e0360d022005374d50f19c602c4991ac4eef8900d00159cbf2bc390c3e4f80b01c5b3575115,0x5c2d96aac5127f2d7c3a1cedd6d33d86a4512711c8b3a1a09045218f47236158781608004955,0x15e9098556154d273dccf304b11f44f1043109bfefbbecf9bccee3a6e8394e437adbb56d2b26c95135,0x4e7049293d41800c54a82ec4088414cff1b45508c0e2388c004fef82265888d71dbb1d3c43f8e023d149,0x3c2dbafa2300129472d2aad47c96ee5ef1bba2e0083835fb2949cf7bbae9b50cb2cc9308c1d8273f514a,0x472f9b622e07d8848913c24f8b9c5d0634c4df2f4b913c2505b582d05c0d8340c00187d931f3ac22512f,0x721b068198420b821504f525c30fdbc6ef352d1b1ec42eca7a027e1a26392e348480a8200052915d149,0x5b59d453524ccaca463fba39b6b433b0abab241f9e9c191817961307038201804184,0x4ece4dc9c3c03c352eaca3a29a1999181794131210900e0c8888068504020180423f,0x2210600d3db6c356a74ca310481bf5dae76c2f97ab2562a548a24d23912844019cca6424ca98,0x18e3b00102310b5c04e898e4d8f0b28981103702406e42da902127c08608b94ce3368c9f0e32ecadd228,0x1b424398cf306b62b2a71e86f000e6b308ca1a6d9b2b62cea421a5c1521381302b70cdb2eaba749ad22c]
private def nodesSecondDataPart4 : Array Nat := #[0x34189026a33556632c159acd040001fefc6b34d9abb59ab0f2631f8f604bb50235007d31cac8,0x8c0981e00336a6a82972489196ec4ae2ad2aa51944af2ac9b25477bd8c32bca7a9aa0a6c5fc0ae5d23e,0x45de44a8c271025628e5f1b65af46e30f2783b1d0bc522892a8b4398cac5528924701b004aac,0x3c6e4b44c430eb82d6b227c568f6e5392d12ca9c9ba3a89a26000cf9950b412faaca70172ea38ecfd228,0x53293489fc7e38dd6cb5172a64c14b398db8522813f582b12a94e2c3d577ca0c85d689004a4c,0x2fd60827fbb9d0e3622e14a7d2691060008bb91a65250278db5f9f4c970873d962e3188a4ab0,0x3a5c2db61acd64a752a5d285a2993c6400863a9569e19682970d782ff378e863e1e2f0684aa3,0x3c574af4a1e46909843c5dad848180019ec75aacd097ab99cadd4313f53a0ce59e39097bcaa7,0x8401729cc99bed66aa3c7d666eb65aabb44a088c3ec05caad1a6fb75a87c1f05b0d497ecabf,0x31952a04e269208c3f1ece26831160602913890341807802d749a14c1ec9c481d4e8671fcac6,0x5f692f4743598ac4562391686a6c7222e865a3500160061eff4198caa4afc7db419acc65cac8,0x2c1327a30980b821ba59ac95896c15aac35eae5627c38972c734983f980b95c2c4bc43004adb]
private def nodesSecondDataPart5 : Array Nat := #[0x1109553635a01f9b980c027d70cf2ba42389088027a3fd4abfa81855d535aa27c344,0x22a09e9b1ab9b2f76e6bd12c209f1e9e1b1a9a11108a888036acac23a2a09e0ec357,0x5a4c413b38b6302da8a81b80615a595352c13ebdbb35af2dacaaa9a928229188c38d,0x55b55d535253ceb85560d675754b0dbb6e4830003883c0a3a1ed3aae5b8c677806d39dea39f63378d0f0,0x6233ecc72cca6ac1ee4c92e450f600731a267952d430840660717c265394647896223df89a0e6194d07e,0x62b5752d00394e3b720069b545374d5252db8acbee1b7eddb3eafa66759a65d93e498e5514fd3b4e50f9,0x5fb7dde377dd77558559d414ed234851541cf93dcf128474ff2fc0100184d5352d4749d254244edb5115,0x60f79dc36fdb56bd555454f525414cd2f4ad2948c7ef6ba43d06c0f03207810006db554fce939cdf50f9,0x2b0981a64b8f0f934eb9abcaaaa0a72849596c4b06c00408f3b8ad8b00a82687d11d0bc06fe39ee4d257,0x5324f1e8cfdfadb9c8deee748a3d0e77298c4461703682fd20150072f89c0daecb2d399aca82,0x2744dc8b21c811642d00ba6bfaeeb02bc7d1542cc6d1842d07bc8bcaf0baaccb12bc86000f7bc0d4522f,0x69b437cb9d59fee970b81b4d967ad400cc6531988c3db68f2388bedc66ee26fb55a4cc634acb]
private def nodesSecondDataPart6 : Array Nat := #[0x2d15b8ac35e2c9459cbb5bcd966b017ebb5ca045400cee57238bb9be5a8c8613057690314ae2,0x425f2f87b33192b94d89c01a6cc56296fa58a803e1005f237fbdac4620aff7ebedecf3784aaa,0x7439ba5cee729b49a45167931974ae51269045a20ea70b71ac9c4a09001f9f67aba983a5ca7d,0x592893d9b4ce591b873a9c4dc6d355a0c86230572b6140502005006af4fa1cc62f0981bccad7,0x14ca451004d259168a425aed462208d4652c86c333a994c257238fc6631158a44e250f86cb3c,0x48e390b853e17ab248994a8522784c01309549a03007ab4da4bf5ead920773a9bcc65d28cb45,0x411f2f476b8d986c35188b0572b1409248211046630128783a120041de4f1782b22d0f854b5f,0x77f16fef6ae965e3e36261dad9d54e3c342ba412110d0a08060302003ff7f772438c,0x3ebbb8b815cf4443b9b822a09544c3c1393847c5004a4989c43eb9b8209a165143de,0x494cf0b0bf32c50b6d2ea985a406ad1e71a61653444]
private def nodesSecondData (i : Nat) : Nat :=
  if i<82 then (if i<36 then (if i<12 then nodesSecondDataPart0 else (if i<24 then nodesSecondDataPart1 else nodesSecondDataPart2)) else (if i<60 then (if i<48 then nodesSecondDataPart3 else nodesSecondDataPart4) else (if i<72 then nodesSecondDataPart5 else nodesSecondDataPart6)))[i % 12]! else default
private def nodesSecond (i : Nat) : Nat := nodesField ((nodesSecondData (i/32))) 11 (i % 32)
private def nodesWeightDataPart0 : Array Nat := #[0x2db6db4229a6dc6dc9249254cc7,0x2080d119559dd9ddd9dddde1e21e2226504,0x35db6dfec0b56696296592dd8c7,0x32ec91195de25da21e080d1959dddd9dd05,0x945064b2914a371b9238e494cc,0x224e4975b6d52d59e6d069b90c9,0x19e65e21999625014d890d0d5cd84d1cd07,0x1c764b25ae49218842e56e398ca,0x22aee8d59e666af2f6f080cd195dd99dd06,0xda924db416e996d26d4965b8cb,0x225e2aaeea6f72eef33b33740495590d109,0x118d9d191111111565100dd44891155650d]
private def nodesWeightDataPart1 : Array Nat := #[0x23b6b9092cb823ba7db671558cf,0x2cb6cb4bad32b5f814e48e3d4cd,0x11d55550d1d5959dc14cd194ddd561d9d0c,0x2dd636ee95a96d0644eb92d94cc,0x1b4d80db6dc6e28c98e1b9b4ccd,0x1cd95925d10dca11d1114d91501589d8d0b,0xd151955d159d5a5dd4811151d90d11910c,0xa47472c72571e51db230e254cd,0x202dcdfa36eb36d8bf6fd6294cb,0xddd9d999e261611c0d184d90ccd151910b,0xb6db4db99a9a820a92451594cc,0x152214d95d1140851dc8804d0509014110b]
private def nodesWeightDataPart2 : Array Nat := #[0x1551e1859110d89910c9604091d9c91610a,0x2529ce3294a742908401cc119c8508cc338cc109d49,0x273301ddddd9a2222a6ab2eeb27309de10f,0x22eaed221dec0515a21eef2ef5a222aa910,0x15cccd9808c8cddde0884d15e2488d11113,0x1515195d61e1e208e200088888d1119a113,0x232ade2099dda1e1e22ea72f1e4915e50f,0x1dd9df322aaaa809d9d5e2626266aae690f,0x2cfb7d754a605370445ea5268d3,0x15a12491155595599995a19a1e1de1e110,0x45044929429995e72572360d5,0x19d999c9e5e32264a25e40865e2155da10e]
private def nodesWeightDataPart3 : Array Nat := #[0x1d9d9d5a0000898d0c9da44088ccda08113,0x112092d36536934d36e491388d6,0x1c58084911951d91915d9da219dd61dd910,0x1518d2515eaa159112a610de6000cdde910,0x22a3b9da2919cd9e2c06a19de666b33190d,0x1aa2acce199de5dd5dd521a6ee64199f10e,0x1dd519dcc8d14450458cdd9e1999d9c0912,0x2f92492092cb2db2dd6edb6d0d3,0x1965225b09496491b71b71c70d4,0x14cc004495549199d11d1511a2919d96110,0x196015891d995de4c91199ddcd99dd5950e,0x19d1950d155d150d591111255411115550f]
private def nodesWeightDataPart4 : Array Nat := #[0x228094934e24a244b4db29228d2,0x1d6191555555599118995d8a595159c090e,0x159d9e1e10191999555a21a5a5e62e5ad0d,0x161e2a99a265de199a2665e0012999a190c,0x1599599955de1520d6665558194d111590e,0x11914d5110d999594cd95cd0d8dccc2090f,0x125151a2115d6995d62205955801a11550d,0x119a99ddd9aa9d900558d51e188cd21e90c,0x2a4999d96251e21e6a29005d99b2309990b,0x155921914da5cd911115901094e8ddd0d0f,0x816161d96158615165a4d16250d959990c,0x1cc5ddd4080c8ccc8a16584c98d10d9d10f]
private def nodesWeightDataPart5 : Array Nat := #[0x1521911111104c61de4e054105161d5550d,0x1d9ab225202eaaeaa221e21aded62d9e10a,0x159d9e559a1e9191c1d9960a0e5e5e59d0a,0x33ac6b3bde73ad6f7ce737ef106039803220e63a14a,0x15d99e2261e20119999a04155519c15551e,0x273777739f373b7b8404151d599e7b73516,0x4c0449d5599d9d555dd9de4195999ddd1c,0x8ddcd2e26a662e9172ebbb776c2eeaad18,0x1a96b5a74b9ee639ad735ad09d274b1ad8040438955,0x1aef05a66ef32eeeeef2eeeee18221ae916,0x2b04005e1b332f330019a2f32f6ef21e916,0x1087b5d4a5274a5293a5295b012973a4da4ab59d14d]
private def nodesWeightDataPart6 : Array Nat := #[0x253518ec6325174a31a4e53900e9335b294a539494e,0x33333337371e1b7375b708023733733b114,0x1e9adf2eab32db332b2ef2f3330805eb114,0x22b831ac6c9f18ba318c2328ca5564400198e65b14e,0x3bf74c29ab31b772f3040055a5995aaa913,0x19eadbe2777730486269deda2333736d13,0x15d9a3ab1eeb3b7733333730c212855113,0x440dd9925ab2b19de1f25b332f3e8cd912,0x25aa6c0e564b2d549ecc70cf129ab73010f,0x280ca434663b0a45b1886296e81d487a94b]
private def nodesWeightData (i : Nat) : Nat :=
  if i<82 then (if i<36 then (if i<12 then nodesWeightDataPart0 else (if i<24 then nodesWeightDataPart1 else nodesWeightDataPart2)) else (if i<60 then (if i<48 then nodesWeightDataPart3 else nodesWeightDataPart4) else (if i<72 then nodesWeightDataPart5 else nodesWeightDataPart6)))[i % 12]! else default
private def nodesWeight (i : Nat) : Nat := nodesField ((nodesWeightData (i/32))) 6 (i % 32)
def nodes (i : Nat) : Nat := (nodesClass i <<< 0) ||| (nodesFirst i <<< 6) ||| (nodesSecond i <<< 17) ||| (nodesWeight i <<< 28)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def layoutsPart0 : Array Nat := #[0x644104000000,17619096698880,17619096715264,70408472690704,70408472690688,70408472625152,70441775398912,17665217265664,90211352704,90211090560,90211090432,39732707344]
private def layoutsPart1 : Array Nat := #[39732707328,39732641792,39728513024,70374112888832,70374112954368,70374112954384,70374112886784,73032269824,73031221248,73036464128,73032533120,73036727424]
private def layoutsPart2 : Array Nat := #[73031222272,73035415552,73031222400,73031483520,73032270848,70373055922176,70373055926272,70373055938560,74766792785920,74766792802308,74766792802564,74766792802560]
private def layoutsPart3 : Array Nat := #[74766792802304,70369012613120,70369012633664,70369012629760,70369012613184,70369012613376,70369012633600,70369012615488,70369012701504,70369012617280,70369012633856,70369012629824]
private def layoutsPart4 : Array Nat := #[70369012629568,70369012617536,70369012613440,70369012615232,70373041524756,70373041588309,70373039144960,70373041592384,70373039214661,70373039214596,70373039149056,70373039144977]
private def layoutsPart5 : Array Nat := #[70373039165444,70373039230997,70373041590272,70373039161348,70373039144961,70373039165440,70373039233109,70373039210496,70373039147072,70373039161344,70373041242112,70373041524757]
private def layoutsPart6 : Array Nat := #[70373039145024,70373039214656,70373039144964,70373039495252,70373039229008,70373039226880,70373039161408,70373039165456,70373039230976,70373041592400,70373041590341,70373039230993]
private def layoutsPart7 : Array Nat := #[70373039144981,70373039149072,70373039210500,70373039210512,70373039214592,70373041590288,70373041508352,70373041524740,70373041504256,70373039161345,70373039144976,70373041520644]
private def layoutsPart8 : Array Nat := #[70373041569797,70373039147076,70373039161360,70373039407120,70373039230977,70373041520641,70373039149057,70373041590276,70373039147008,70373041520661,70373041586176,70373041588308]
private def layoutsPart9 : Array Nat := #[70373039163472,70373041586180,70373041520640,70373039161365,70373041504261,70373039210497,70373039147088,70373039233088,70373039167568,70373039161361,70373039423492,70373039212624]
private def layoutsPart10 : Array Nat := #[70373039216720,70373039149060,70373041520660,269829199,269766735,269505862,269571392,269766991,269571398,273958217,273962311,269833543]
private def layoutsPart11 : Array Nat := #[273958214,268452161,269484096,269500673,272630016,273961295,273958212,268435776,274027855,269763849,273962304,273962313]
private def layoutsPart12 : Array Nat := #[274027846,273957193,273940804,268718089,268713984,273956937,269746246,268718080,268764480,268435456,269502729,268703808]
private def layoutsPart13 : Array Nat := #[274028870,269500681,269833551,269833537,274026575,268455936,269833545,269833542,269832518,269504774,268452105,268439808]
private def layoutsPart14 : Array Nat := #[269500672,282416199,274026822,268702022,268702790,268456006,268439616,269549568,268435526,273962308,269502721,269500737]
private def layoutsPart15 : Array Nat := #[269751364,268701764,268436480,273765702,268718153,269812800,268714054,268702025,268437760,268699712,273962055,269766982]
private def layoutsPart16 : Array Nat := #[268718337,268701702,268697664,274026569,268697670,268439622,273958208,274026566,268452096,268701760,274093385,269832521]
private def layoutsPart17 : Array Nat := #[269484288,273695040,269746176,273694784,268435520,269500480,268435712,273961286,269571407,269502720,268523846,269504838]
private def layoutsPart18 : Array Nat := #[269899081,269833549,269898052,268849156,269899078,268702017,269828416,269764864,269570310,269762816,272896068,274093382]
private def layoutsPart19 : Array Nat := #[268703812,269488128,269833536,268784975,269500417,268439552,269500416,269815814,269828102,273698822,278151168,268435462]
private def layoutsPart20 : Array Nat := #[269746432,268702016,272716096,273940800,269504521,269766985,274026825,269746438,268767561,268701696,269828096,269751360]
private def layoutsPart21 : Array Nat := #[272629760,269746240,269815878,269750336,269766726,273961225,268697865,269505871,269815808,269815817,268713993,269746441]
private def layoutsPart22 : Array Nat := #[278155273,269762569,269750278,269747273,269750598,269750272,268697856,268697600,268697668,273942857,268783680,272912448]
private def layoutsPart23 : Array Nat := #[268783616,268718336,268451840,273961216,268701700,268439558,274022720,268439556,268505088,269811712,268714048,273958153]
private def layoutsPart24 : Array Nat := #[268435465,268698944,268698948,268715332,269829449,269833540,268784964,274089289,269766980,274027849,268719433,269747264]
private def layoutsPart25 : Array Nat := #[268436804,269746505,269747529,268502336,268714313,269816905,268714057,269484352,274027840,268435464,269484032,268714246]
private def layoutsPart26 : Array Nat := #[268718406,269763593,269832512,273944832,268701766,273961289,273960960,269766976,268783942,269833541,269768006,269766918]
private def layoutsPart27 : Array Nat := #[268703040,278156614,269832527,269828352,269763905,268783872,269763840,269833472,268783686,268522822,272912710,268698880]
private def layoutsPart28 : Array Nat := #[269766912,269762822,272908614,268457286,269566208,268767296,268718345,269762886,269751625,269766662,268456262,269811782]
private def layoutsPart29 : Array Nat := #[269762825,268521536,273944902,269832516,273956928,274010438,268715337,268439814,268501312,272782662,269766921,269767945]
private def layoutsPart30 : Array Nat := #[269833216,269504512,274006281,272961860,273945670,268698688,269570374,268697604,269747200,269766656,269768000,272912704]
private def layoutsPart31 : Array Nat := #[268521472,268500992,278220806,272651264,273940550,278138880,268701952,274006086,273957120,274026816,268767552,269750592]
private def layoutsPart32 : Array Nat := #[269817152,268505408,277173312,269816832,273962048,273940489,273957184,272650240,274022729,268452160,273695049,272908617]
private def layoutsPart33 : Array Nat := #[272715840,272651520,274024448,273956864,273940480,273698816,272892160,272908608,272978240,274024713,273956873,272646473]
private def layoutsPart34 : Array Nat := #[268456192,268718144,268783936,269828169,268439872,273700096,268517440,273694976,272695296,273944576,269830400,273957129]
private def layoutsPart35 : Array Nat := #[272695360,272646464,273678336,268763200,269762560,268452864,268521792,269484041,269484297,273940745,269746496,269811968]
private def layoutsPart36 : Array Nat := #[268832832,273764617,272646208,272629824,272959744,268765504,273941760,269812032,269817156,273944582,269767680,268451904]
private def layoutsPart37 : Array Nat := #[268697606,272781577,268582912,272633856,273697097,274028873,268451849,268452102,269816896,272974144,269504582,268702726]
private def layoutsPart38 : Array Nat := #[269812736,278201664,269485056,268846080,268698624,268715008,268451913,269488393,272630080,268697862,269813056,268701769]
private def layoutsPart39 : Array Nat := #[268784966,269815872,269762630,268453193,268764160,268501056,269504768,268702982,268439878,268440576,269488454,268456960]
private def layoutsPart40 : Array Nat := #[268454208,272646400,272695616,277151744,268763136,269549824,269816900,278222150,278135808,277876736,268850176,278024192]
private def layoutsPart41 : Array Nat := #[268702720,276890624,278200640,278135040,273940736,268714240,277152832,272634880,277939456,278201344,5576021,5264721]
private def layoutsPart42 : Array Nat := #[5330389,5625173,5469655,5756373,5600759,6157813,7673725,14112117,5723509,5592917,8213845,5339095]
private def layoutsPart43 : Array Nat := #[6125525,5600597,7722837,14112629,6117335,6125399,5338583,6247765,5592405,6249845,5625181,6124887]
private def layoutsPart44 : Array Nat := #[6124885,6116823,6100305,7722327,6125013,5600725,5601109,5592407,6116949,5633375,5723477,5600533]
private def layoutsPart45 : Array Nat := #[7853533,5330933,5756277,5731703,5594485,6157821,6125053,6157591,5594453,1168660,1085508,1167685]
private def layoutsPart46 : Array Nat := #[16388,349265,4457733,5596541,4097,98340,1052672,82017,5731669,14112085,5625693,6248277]
private def layoutsPart47 : Array Nat := #[5592533,5594455,6116701,6149469,6116821,5723605,7689557,5600599,5592535,13983061,5338455,13981013]
private def layoutsPart48 : Array Nat := #[1331473,5592413,5592437,5592925,5725557,5625685,4577117,14114133,6125012,1398085,5328213,5723217]
private def layoutsPart49 : Array Nat := #[5263685,13981045,1385621,7689589,1332308,5330391,6125015,6116725,6116695,64,5596501,4096]
private def layoutsPart50 : Array Nat := #[81984,4277508,90176,4160,17408,7692101,5592469,6639636,1398101,5591061,1048580,5723479]
private def layoutsPart51 : Array Nat := #[7673695,7722871,4543607,5592342,265557,7724381,1381908,0,5657941,5594581,5592149,13981141]
private def layoutsPart52 : Array Nat := #[7692117,7689565,7690069,6643161,268368,6249813,65872,6116693,9783637,6115669,16078677,14638421]
private def layoutsPart53 : Array Nat := #[13981533,13989206,5591125,4259840,1066048,5602645,5725525,9786449,5592404,1064964,4214785,4194368]
private def layoutsPart54 : Array Nat := #[8732736,5731671,5609045,1377296,4542484,5598550,65,1197060,131072,14111829,5594461,14014301]
private def layoutsPart55 : Array Nat := #[14014293,4473108,5328901,5526869,4472836,1065024,9787733,13981029,5608789,9786709,263424,9787743]
private def layoutsPart56 : Array Nat := #[4198400,328722,266322,2,5662054,5596503,14111093,5596502,5657957,9721168,4457728,267521]
private def layoutsPart57 : Array Nat := #[5526852,1053952,4539653,5658965,5723607,5724501,5592409,5725527,1397841,65540,344129,262208]
private def layoutsPart58 : Array Nat := #[9786448,5625169,5600593,9852244,13981525,5921109,6117205,5588244,65860,81985,262228,13981009]
private def layoutsPart59 : Array Nat := #[5602641,13990995,5593941,5592913,278528,5600341,13991254,5594454,5591377,6641236,6642001,7673685]
private def layoutsPart60 : Array Nat := #[4,14013781,4543824,1048576,1065232,266244,8388608,2048,5363029,5592661,5625429,5858645]
private def layoutsPart61 : Array Nat := #[5887319,9524309,5330261,5326164,4195412,5572180,5334361,13981021,4260176,5332309,1393748,1065028]
private def layoutsPart62 : Array Nat := #[4259920,4195396,17472,262212,9794901,6641045,5596565,13989333,17476,17409,1065988,5592669]
private def layoutsPart63 : Array Nat := #[5723485,5592406,1065216,278784,4527189,1066304,1136192,5592148,1064969,1048592,5596581,5596486]
private def layoutsPart64 : Array Nat := #[5592565,1048832,1311744,7690103,271426,353317,5395540,1311760,5854545,5521668,5242880,1066052]
private def layoutsPart65 : Array Nat := #[7722325,6772085,5592919,6673749,6640981,2445652,7689559,4543557,6378517,348501,5588566,364821]
private def layoutsPart66 : Array Nat := #[16640,5326405,1118468,65600,1398161,13981014,5600598,4457732,352272,356352,4543957,6640983]
private def layoutsPart67 : Array Nat := #[4523013,65604,4547605,271442,1048577,352321,5592645,1377685,1328212,1381969,4216133,1092]
private def layoutsPart68 : Array Nat := #[5522500,4194304,5587268,4198401,5854805,353601,528449,1049664,1024,1398357,4195328,4260869]
private def layoutsPart69 : Array Nat := #[1066085,1377872,5592677,9700368,1050176,5592660,352577,1088,266324,5510487,1119300,5854553]
private def layoutsPart70 : Array Nat := #[1066564,1394260,1049156,1114113,1381445,1115152,1115137,5120]
private def layouts (i : Nat) : Nat :=
  if i<848 then (if i<420 then (if i<204 then (if i<96 then (if i<48 then (if i<24 then (if i<12 then layoutsPart0 else layoutsPart1) else (if i<36 then layoutsPart2 else layoutsPart3)) else (if i<72 then (if i<60 then layoutsPart4 else layoutsPart5) else (if i<84 then layoutsPart6 else layoutsPart7))) else (if i<144 then (if i<120 then (if i<108 then layoutsPart8 else layoutsPart9) else (if i<132 then layoutsPart10 else layoutsPart11)) else (if i<168 then (if i<156 then layoutsPart12 else layoutsPart13) else (if i<180 then layoutsPart14 else (if i<192 then layoutsPart15 else layoutsPart16))))) else (if i<312 then (if i<252 then (if i<228 then (if i<216 then layoutsPart17 else layoutsPart18) else (if i<240 then layoutsPart19 else layoutsPart20)) else (if i<276 then (if i<264 then layoutsPart21 else layoutsPart22) else (if i<288 then layoutsPart23 else (if i<300 then layoutsPart24 else layoutsPart25)))) else (if i<360 then (if i<336 then (if i<324 then layoutsPart26 else layoutsPart27) else (if i<348 then layoutsPart28 else layoutsPart29)) else (if i<384 then (if i<372 then layoutsPart30 else layoutsPart31) else (if i<396 then layoutsPart32 else (if i<408 then layoutsPart33 else layoutsPart34)))))) else (if i<636 then (if i<528 then (if i<468 then (if i<444 then (if i<432 then layoutsPart35 else layoutsPart36) else (if i<456 then layoutsPart37 else layoutsPart38)) else (if i<492 then (if i<480 then layoutsPart39 else layoutsPart40) else (if i<504 then layoutsPart41 else (if i<516 then layoutsPart42 else layoutsPart43)))) else (if i<576 then (if i<552 then (if i<540 then layoutsPart44 else layoutsPart45) else (if i<564 then layoutsPart46 else layoutsPart47)) else (if i<600 then (if i<588 then layoutsPart48 else layoutsPart49) else (if i<612 then layoutsPart50 else (if i<624 then layoutsPart51 else layoutsPart52))))) else (if i<744 then (if i<684 then (if i<660 then (if i<648 then layoutsPart53 else layoutsPart54) else (if i<672 then layoutsPart55 else layoutsPart56)) else (if i<708 then (if i<696 then layoutsPart57 else layoutsPart58) else (if i<720 then layoutsPart59 else (if i<732 then layoutsPart60 else layoutsPart61)))) else (if i<792 then (if i<768 then (if i<756 then layoutsPart62 else layoutsPart63) else (if i<780 then layoutsPart64 else layoutsPart65)) else (if i<816 then (if i<804 then layoutsPart66 else layoutsPart67) else (if i<828 then layoutsPart68 else (if i<840 then layoutsPart69 else layoutsPart70)))))))[i % 12]! else default
private def layoutIndexPart0 : Array Nat := #[0x40200802008010080200802008020040100000,0x100300c0300c0300c0300401004010080100402,0x1003010030100400c0300c0300c0300c0300c03,0x180501405010040100401004010030100300c03,0x24090200801c0701c0701c07018060180601806,0x2c0b02c0b02c0b02c0b02c0c02c0a0280a02809,0x3c0f0380d0340c0300c0300c02c0b02c0c02c0c,0x541404c120401004410040100441003c1003c0f,0x54140501704c1404c1304c14050140581404c15,0x501306814064140641305018050140501405014,0x50140641404c1406c1b06814064130601405014,0x501405014050130501307014050140501406c14]
private def layoutIndexPart1 : Array Nat := #[0x501a05014050140501405014050140501406014,0x741d0741d0741e0741d0741d0741d0741405013,0x801d0741d0741d0741d07c1f0741d0741d0741d,0x802208023080200882008022088220802008021,0x982509420080240802008020088200802008020,0x94250b42c0a0250ac2a0a827094250a42809c25,0x94250942509425094250942509c280942509425,0x94320c4250942909425094250a4300942f0b825,0xe4360e0370d8350d025094250cc250a42709428,0x104400fc360f8360d8360d8360d83d0f03b0e836,0x11c360d846114360d8360d8440e8440d8430e842,0xd836128431244810c360d8360d8360d83610036]
private def layoutIndexPart2 : Array Nat := #[0x15445150530e8521443e1404f1384d0e84c0d84b,0x100360d8360d8450d841158360d8360d84312836,0x16c5a164580d8361004a10036114400d83615c36,0xd8361043617443104360d83a168361003a0d85c,0x118360d862178610d8401805f1783615c5e17855,0xd8650d8361143a190360d86310c3f1144d1344d,0xd8360d8360d8360e8361703a0d83610c360d83f,0xd841198360d8360d8560d8400d8400d8360d836,0x134360d8360d83619c4a0e8360e839114360d85e,0xd8360d8360d8680d83610c360e8360fc4513441,0xd836100360d85e0d8361a4360e8360d8490e840,0x140360d8430d8361a8360d8360d8540d8570d840]
private def layoutIndexPart3 : Array Nat := #[0x16c3f0d8360d86212836138360d836198361683a,0xd8360e85e0fc430e86c10045100661783a1ac57,0x1286f0d8360d85e1b8360d8430d86d1983a0d86d,0xd8360d8361a4360d8361c0360d85e0d84a1284a,0x10036128450d8360fc5e10c3f1784a1884a0d83a,0xd8360d84c0e83a0d8360fc460d8561c4560d836,0xd84a0d8720d8360d8360d8360d84a0e83613436,0xd85518857154551885e154431cc43178620d855,0x178360d8360d8401c44015462178550d86218874,0xd8360d8360d8360d8360e8360e8400d8360d866,0x194450d8430d836100360d83a100360d8750d836,0x188361b07319c360fc360d840158560d8360d876]
private def layoutIndexPart4 : Array Nat := #[0x114360d8361e0360d8360e83a13c3a0d87718873,0x15c361e4760f8670d83617c4a0d85e17c360d862,0xe8360d8661983a0d83617c4a1e8360fc360d83f,0x21083208812007f1f87d1f07b0d85617c560d866,0x25093248912408f2388d2308b228892208721885,0x284a027c9e2649d2709b2688d264862609725895,0x2b07d2ac902a8aa2407f2a4a829ca6294a428ca2,0x2e0b72888f1fcb62d4b42ccb22c4992c0af2b8ad,0x28ca826499308c1300bf1fcbe2f4bc258bb2e8b9,0x330cb328c9320c731899314a322cc4304c31fc7c,0x350d3264d23449d340a8308a32a0cf338cd244a3,0x388e1380df378dd370db200da364d82a8d7358d5]
private def layoutIndexPart5 : Array Nat := #[0x3acea3a4bf31ce839c9e398a7394a7264ae390e3,0x3bcf228cf128cf0218e53bca82a8ee3a4ed258ec,0x264fd3f0a6310fb3e89d3e4f83dcf631cf53d0f3,0x41d063e5054110322502288f5405003fc993bcfe,0x33896438f9308ea338ce4350c42d0a41d0942106,0x450ce240e63988044c974489744510250a33250f,0x4591c3a91b2511a46518410f945d16451153a50d,0x481094191f340a2458c9305163a4c9479163a91d,0x490d04a9292612848927499254852448d224849d,0x2d5334c8d04c50e425304bd2e4252d4b1243412b,0x4e1374d8ce4d5204813433881274d2330c222d09,0x4e4c926499348d2264992850f410cb264ea21899]
private def layoutIndexPart6 : Array Nat := #[0x4f0c430d3b280c92650d3c0943392b4e93a338ea,0x201435094120cce5008c2c0d23408b2193f4f93d,0x5314b529385254752147519452413451141288c8,0x550a854d3c548c85454a544905414f538a33194d,0x2b93c4e15a564d23855829d57558e922555320a8,0x3089943899264992b95d2b8a84f0d25715b2b8c8,0x324bf58560324fc2515f578992650f43cc243890,0x59564438ea338802653658cbf2a9623250e264d2,0x5b1352656b5a8fc3a969409065a16740166598ae,0x5bd0a3c0905b8c2264ce25099330b0458992656d,0x5d969265753e4995d1735c91c5c49943cce5c0e3,0x3497c2517b3997a2657943d0f5e094474a15dc99]
private def layoutIndexPart7 : Array Nat := #[0x3a5254651c2fcc939942399556017f5f97d3bc99,0x618f55c585611292451e5a583609803a499604e9,0x4698a245896258823d3e611583d91a4fd3d24587,0x64cf66490d6459063d876390f6118d44d8c62d84,0x650912399861d3e63d976599561589285946218a,0x67cce61d0f6799d3f50d3d99c43d9b61d9a664f6,0x684d062936640fd6815c3348f43577284d043d72,0x43d0f43d3b480996992061da569099571a368993,0x264f92650f3c099250f9264c86a1a7265362510f,0x264994649922dac26499349ab264995a5696a9a9,0x4acd25c0993f0b028d36264994d9163a8d026499,0x2511843cf96b4f0348942650f4390f321363f0ce]
private def layoutIndexPart8 : Array Nat := #[0x325af43d362650f43d04411182650f6b90e4d96f,0x6c53c6c0d0330993a499264944390e439a832094,0x3e4d04ac99324992658a6cd0f25099264d06c8ef,0x6dd0f6d90e4d8942649934099264946d5b433899,0x3c0ce43d184610f5c10e3390e6e4966e0c43c0a3,0x265bd6f09943c94438966ec996e96f250c8250c2,0x265b36fce96fdbb5909926499324ce43c9922dbe,0x7091661dbb705c06ad0f3a9a861099459bf43d16,0x2bdc428cc9264993089970c992b899264b6459ab,0x660cc395c7304e93a499264e529dc62649971519,0x728993c5182d50f724ce7250f7210f338994f099,0x338c12657a2510e4749926499734c43250f731cb]
private def layoutIndexPart9 : Array Nat := #[0x264e53a5a8739362c1083149926502325365c099,0x43c95264994d89974189265a9340993d90f265cf,0x264d222c9943c99264a634935264d04809d3408f,0x26499265d32649931d0e438ce749c84750f74499,0x43d0f758992649943c94340ce754c4750993a519,0x478c5265d8265d734936340b0264c2438ce43c94,0x394a1314c1768fc6dce9764ac2a8d0325d92b8d0,0x304e577dde210e9464e5265dd211dc349db264ae,0x264a8340c84f0992c0e95dcd0264ea320cc4d8e5,0x790993a5646eda778cd0265e2265e126589781ab,0x339e643880720d2794c8788f93309d43888320d2,0x79c99264c9324f9340b52510f474b55bda72510e]
private def layoutIndexPart10 : Array Nat := #[0x721eb2d9ca265bc26499264ea265ea7a57a349e8,0x34099474c4348992649926516264b6265ed7b1d8,0x3090f43d1629c99264d2265d6265bb324994cc99,0x3110e3393c28ce53949978c997c1f0220f07bdee,0x265c96f13c6f0ce2650f265c96f17a6f1c869c94,0x458997c90f43dc843c992650f7c4c94f0942651d,0x7d9f77d8997d4997d0e926499721f3478992b8e9,0x81e068160480e02806007fdfe7f5fc7edfa7e5f8,0x85a148561484e128461083e0e8360c82e0a82608,0x8821f8021e875f98721b7e60e86a198621184617,0x8be2e8b62c8ae2a8a62889e268962488e2283a21,0x85238836378da358d20c8ce0f8523280e168c630]
private def layoutIndexPart11 : Array Nat := #[0x916009124390a0c906408fe3c8fa3d8f23b8ea39,0x93a4d9324b92a498320c90e4383dff90e4891e46,0x9565494e0c832529460c8ee0c941ff9061a8824f,0x962588320c95e5593656936428163f8320a8ea55,0x98e3198a619825f97a178fa3f9765c96e5a96657,0x9a668881f98166799a65991ff8f2318166386a4f,0x90e3a8d2709be6e8d26d86a6c9ae248326a8fe3d,0x9da758c6019d2738323e8320c9ca718fe3f86a00,0xa027f8327e9f62485e7c8427b9ca7a9c6799e277,0xa263fa2287a1a8583284a0e3b8ee829ca0589281,0x8fe2082a90a3e8ea368c8328b8ee42935ffa2a3f,0xa6698a5e96a563aa521aa0a31a4e82a4a917e605]
private def layoutIndexPart12 : Array Nat := #[0x806a5a92a3a8aa1a829fa7a9d8829ca6e4da69f9,0x90e82abaad96eacaaeaa8ee3aaa63aaa2a7a9a3a,0xa06b78f605a1eb6ad6b4aceb2ac6b0a763f8c6af,0x8da1aaf66c82ebd8ce56af2bbaeab9ae23fa5205,0xb1e72aca3f8fec6b16c4b0e35b0ac1b02bdafebe,0xb4ad1b42cfb3acd8feccb2ecab261ab223186a1a,0xb6edab66247e60e9aed8b5ed6b5686b52d3b3aba,0x832e4b8ee2b86e0b7df9b7a0c832dd8fedc806da,0xbb6ecbaeeaba6b5ba2e7906e6b96e2b860c8320c,0x86a3b9ca3abca2e8e6f197a3e9bef0bbea7a9eee,0xbf2fb8320cbeaf9be280bdef6bd6179160cbd2f3,0x8bb04bfb0398f0298f01a62a780700bfefebf686]
private def layoutIndexPart13 : Array Nat := #[0xa76bcc360c93f0c8febcc2f0ac2309c2307c1b05,0xc6317c5b15c53138ff0cc4b118ff10c3e4285f0e,0xc7ef5a2f1e8326b97af597b1d85e0cc731bc6b19,0xc6e5cca25ac9e28c9b2597b24c8e05c8a15c8720,0xcd734cce2eccb31b9f30cbf0bcbb2dcb32bcab29,0xc2f3fcfb3dcf33bcbee6ceb39ce32ccab25cdf36,0x9af4898a8bd1f46d166bd130b9bb43a1f42d0740,0xd3e6bd3b4dd0f4cd234bd2b49]
private def layoutIndex (i : Nat) : Nat :=
  if i<164 then (if i<84 then (if i<36 then (if i<12 then layoutIndexPart0 else (if i<24 then layoutIndexPart1 else layoutIndexPart2)) else (if i<60 then (if i<48 then layoutIndexPart3 else layoutIndexPart4) else (if i<72 then layoutIndexPart5 else layoutIndexPart6))) else (if i<120 then (if i<96 then layoutIndexPart7 else (if i<108 then layoutIndexPart8 else layoutIndexPart9)) else (if i<144 then (if i<132 then layoutIndexPart10 else layoutIndexPart11) else (if i<156 then layoutIndexPart12 else layoutIndexPart13))))[i % 12]! else default
def refLayout (i : Nat) : Nat := (layouts (((layoutIndex (i/16)) >>> (10*(i % 16))) % 1024))
private def payload0 : Array Nat := #[0,0,0,0,45056,45056,45056,45056,45056,491520,0,401409,45057,503809,491520,0,491521,0,0,229377,0,0,0,0,485340139524,485339090948,485335945221,485335945222,485335945220,485340811268,188988067844,180234]
private def payload1 : Array Nat := #[322124713986,322124664834,322129907726,188984922126,188987019278,360789233677,322127810574,322124664835,322134151187,188993310724,462863,180239,188995407885,344081,485345382412,180242,485351297036,188998553613,188998553613,344084,188981727235,307217,180244,344085,180245,307222,462871,180247,0,0,0,0]
private def payload2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,137439117316,137440165901,61442,61443,61442,0,0,0,0,26603059331101,32518175,35248830451744,36348341952544,37396306759721,38697683820585,39646868447273,85597044687032361,42945411862567,44044928589872,45144444411932]
private def payload3 : Array Nat := #[44101675,48442982441006,49344559,52841034465326,52841035513902,57389394219047,17227067445,56635443,57684024,59830329,60878907,60,61,12350,16425,176176,24,41,455351468076,46,455350435872,0x6a04e040272804f,455352533034,562726699051,562727747639,0x6a04f000342804f,605678469179,455354613818,0,70,0,69206088]
private def payload4 : Array Nat := #[270649188422,229446,0,0x49410010504d0f00d,0,0,0,98375,127048,274503,0,274507,0x3f03f0004b410000504c0f004,0,0,71430217,0,0,0,0,0,0,78,0,70,368704,0,65,0,21556789250,127048,0]
private def payload5 : Array Nat := #[0,0,0,79,274507,67,0,82898947,137439117316,137439117316,0,188486,0,69,0,0,0,137440165901,0,0,0,0,0,103157858383,72,0,72,0,0,0,0,0]
private def payload6 : Array Nat := #[0,78,0,0,0,0,0,0,0,0,0,0,0,0,21556789250,0,127048,0,0,0,0,0,0,0,0,0,368704,0,0,0,0,0]
private def payload7 : Array Nat := #[0,0,0,0,0,0,450626,32837,0,0,0,0,0,0,0,426069,0x2605d340764f076,426073,524380,286815,0x46061460723f0726f073,0x3f057260746107568074,0x3f058260746107580074,155734,258137,0x46057260756107468075,286810,258139,0x460572607461074,286814,0x4605d260756107468075,286819]
private def payload8 : Array Nat := #[258148,155744,155746,286823,352358,0x4f065260753f0754f079,213096,213097,454762,213099,369479737468,155756,155757,0,0,0x6208d4109928096,0,421046546565,467073,544900,0,0,421098975396,421123068110,421077979299,0x5003470a7280a7,0,467116,0x79000620a1870ab6d004850a972083,580029415550,0,0]
private def payload9 : Array Nat := #[0,0,0,0,164021,421074858122,0,0,0,0,0,0,0,0,0,0,0,0x8e0c5410c7470ce,0x8e0c88509628096,0,610066923715,290970,0,0,0,0,291003,0,0,0x410d0470ce2808f,571433189526,0]
private def payload10 : Array Nat := #[164027,0,421074858144,544918,0,21477400782,0,0,0,0x610293f06e6e0885a0d34707f45085,0x3f0296106e810867f086000290406e47083450836e0ed,0,0x3f0296106e8108b7f082870d31302713075,0x8d096150d4000745508f000e6,0,0x8d0925a0e545093,0,86230,305104158933,0x7f09c130d74507e,0x8d08f6e08f130e68508f5508f000e6,0,0,0,0,0,0,0x5a0275a075810c76e0a75a0ed,0,472603971790,577766,472621019355]
private def payload11 : Array Nat := #[0x8d0ae6e07f850dc0001800070850b8550aa8d0dc,544989,577667,0,25165936,544989,25165936,0,0,0,0,520372,258089,0,0,0x61029610716e0af850de850964507e000ed,0,221,0,0,0,0,0,0,0,528513,116,0x8d081550db00074,577665,348332,0,0]
private def payload12 : Array Nat := #[0x3f0748d08e6e096130df040301306f470b04507f,0,0x8d0b46e08f040301306f470b0,553175,605748125842,472612077684,0x7f084150dd47089,0x810ce6e085150dd,0x6102e610738d0ce6e08d150dd,0x3f0307706f8d0b96e094150dd000302b06f47083,0x61018610708d0b76e07e150dd13075550b68d0e6,86237,0x8d08f6e09b5a0e2470963f0e6,0x470bb550b3000e1,450720,365307392137,0,282759,577668,0,0,0,0,554218901642,545599803611,0,520324,0,0,0,0,577761]
private def payload13 : Array Nat := #[0,554201018574,0,0,32985,450693,0,32985,282805,32985,0,0,554208145637,0x6102e610738d0ce6e0b8130e68508f,0x6102e61073130d9,0x6102e610736e0b15a0dd55083,416660459635,0,348380,228,0,0x3f020610745a0e3,86243,0,0,472607969492,577686,472615223526,0,545614483675,0,0]
private def payload14 : Array Nat := #[90426593433,290999,290999,605740880055,0,290999,0x77018770706e08c550a8,0x7701877070810c75507e6e0d5,32989,0,35369177600160,290999,472648020151,0,0,397360,554215927965,554215858331,554215858322,450720,472662757526,528541,386668982471,0,0,0x8d0c26e0ad870e9000e7,544987,450759,0,0,0x5a0306106f7f0833f0dd,0]
private def payload15 : Array Nat := #[472662691990,0,0,577691,0,0,544987,416645640308,0,544987,0,0,0,0,0,0,0,0,0,0,229,0,450781,0,605756346552,0,0,0,0,365321183469,545614307557,0]
private def payload16 : Array Nat := #[290977,0,0,520338,0x810d05a0dd45083,348381,0,553180,282798,0x3f02b3f077810d07f0c6130d845083,0,0,0,0,0,605743931538,472608252133,605744001178,450747,472662691987,0,368869,0,577682,0,0,16425,0,0,0,0,0]
private def payload17 : Array Nat := #[499941,78045,0x81096550d600074,0,0,78045,0,0x77037770786e0c7470a0550c4000eb,0,0,544913,0,0,258267,0,0,450781,0,554267078784,0,0x470c94508a000d5,0,0,0,0,0x610203f074810857f0ce,0,0,528536,0,0,0x810a26e0c9850d9]
private def payload18 : Array Nat := #[368859,0x3f0307706f130d9,0,580046029034,0,0,0,472655069300,0,282772,472655360199,0,0,0,472662692046,0x3f0296106e6e0bc130e6450ac,554267332751,0x610205a0748109d6e08f04020000748508f4509d,78054,544911,90436567271,230,520362,230,0x6e0b204020000748508f,78054,528590,472596631758,291022,78054,0,0]
private def payload19 : Array Nat := #[0x5a0275a0758d0ba6e0a75508f,0,78054,90436567271,0x5a0275a0758d0bd6e0a75508f,0,577684,0,0,0x5a03a5a07b6e0a0,290954,0,0,0,0x7f07e4708a450ca000d7,282811,282811,282811,282811,0,290976,0,0,0x7703a7707b450cb8d0d9,0,0,0,0x5a02a770767f08347098550ca8d0d9,0,0,0,0]
private def payload20 : Array Nat := #[86246,0,282811,472614465674,282775,544913,472662691968,577688,544919,545611075790,0,0,520337,282777,0,450797,0,0,554259730558,554219602157,605756346552,0,397353,545611075790,0,0,368859,368859,0x8d0d17f0bd0003b0007a8509e,0,0,0]
private def payload21 : Array Nat := #[0,605755465933,0,368857,282783,0,0,0,0,0,0,0,35201673883791,0,282783,0,571459784857,0,472586154117,290974,528590,0x8d0ce7f0c7150dd0002004074,528590,90426339481,290971,472586408135,90426339481,90426339481,554267078791,472586408074,90426593433,0]
private def payload22 : Array Nat := #[0x6e0a4550e5000290406e4708c,545654329502,472586154183,0,90426339489,290989,472586154144,365313937567,450797,554211246317,258264,0,0,0,0,290977,90429227232,0,0,0,450797,348397,0,348397,0,0,0,0,0,0,0,0]
private def payload23 : Array Nat := #[0,0,0x7f088470d0000d8,0,0,214,78036,0,0,216,0,0,577698,0,520335,0x3f020770747f07f8d0d7,0x5a0756e0a345093,0,0,0,554198978759,554198913184,499949,0,0,545611075790,0,0x5a0275a0758d0d26e0a7870ee4508f,0x810ce6e0c7550d80402000074,0x6e09104020000744708f,0,472591397063]
private def payload24 : Array Nat := #[0x810a76e0bf550d81302713075,472591397024,0x810ce0402000074470ce,0,86237,0x7f0cc550d847089,348381,86232,0,0,0,0x8d09d850e8000200407485096,0,0,0,450721,472614719687,0,0,0x3f020610746e09d450ce,291006,0,282791,0x3f020610746e0ce450ce,0,0,0x3f02a61076810a46e0cf150ec4508c,0x5a0275a075810c76e0a75a0ed,0x5a0756e0a34508f,386795851937,0,554267078862]
private def payload25 : Array Nat := #[545618415822,0,0,472662692046,0,0x3f0273f0757f08f850d0450a7,282797,0x5a0275a0756e0a745096,0,0,553179,90420838616,365303988440,0,0,544998,580046061798,0,554218836128,0x5a0275a0756e0a7450ce,554269167774,0,0x92b53b2b5491311416f141314916f090576a0f91a057700f9,0x92516718a192b57d1586c1531b057490fb78059140f9,0x4815514158632b52d1315f14e79251830f935057,0x91562510f4414e632b53e10f5f14e792b5,0x2d24f6724f662fc7d18a4d18a6c2fc640596c0fb89059660fb,0x2d17a48131141587d15b2d1312a1586c15b4e0fe3505d,0xc10f091593b2fc142fd0b1315f1af6c160090598f0fa,0xc10f0916f4e1894414d2e1491410f5f18a5b2b2800fb3b0592d0f9,0x91543b14d0e13d442fd3518d2d1315f17c6c1634e0fe3505d2d0f9,0xc10f092bb3b18e191c60b11c5f1af5b2fc6a0f91a057]
private def payload26 : Array Nat := #[0x441795f17b6c1682d0f9,310054982263,0x2d317441795f17c2d0f9,464153604477,0x6613d481493b14f142fc631602a169492415f059830fb790594d0f8,0x21311e2f73b247141a10b1314d2bb5b2fc2e0f9,249654784503,0x41241e2b23b18d0f120442b26318d0b1113a16a5b16f5f059490fe3b05d8d0fb,0x481491a298442b21f10f2a2e25f0598d0fb,0x21314816e1a2224431c3514d2e1324d2bb49180,0x21314816d1a15e142502e18c141323a254792495f0598d0fb,0x41252d1a14e16f6710f661fd3530b1f1322a2bb5b16f2e0f937057,0x21312d1a81a263192b03a189791975f0598d0fb,0x21312d1a44e1c73a2e25b16f510f9,0x3b2f744160352ef5f0592a0ef,253753377461,0x6613d2d2c61a15c441605b176440552a0ef,0x1e29b1a30b5b16f510f91a057,0x3b2f7441602e31f,0x4e18d6710f1f1403a2095b174,39499182451,0,0x1e1821a320142c12d1322a16b5f0598d0fb,0x2d1a8141a82a0293a16a5f0598d0fb,0x4e31c2e31c2a02949182,0x41251e29b4e2090f1254429b2e2092a0293a16c5b16f490fe3b05d,0x1e2b2442b22a16c5f0598d0fb,0,0x481d26718a0e131192b07d30b0b10d4d1de6c1705f059830ef780598d0fb,0x4814d6717c25131142b0351fd0b10d5f2476c1712d0f9,0x6c1312d31b671af491311431b2e1de791821e05d490fb780592a0fe,438888289035]
private def payload27 : Array Nat := #[0x2d1c26717c251324416f7d2a10b10d3a30b6c1781b0572a0f9,0x482fd4e1c20e132142b06314a0b10d5f2bb6c177490fb5b05b,0x92bb671ae03132662fc6314a2a18c6c2fc6a0f878059,0x92c4193256314a3a1de6a0f878059,0x4416f3a25109057810f9,425548108469,0x2d1c6442322a317,0x4e018001320918a4e1600310f1919d632b52e12279251830f9350572a0f9,0x2d16f4e16f44277632692a18a5b31b3c0592e0f28905c480fb,0x6c124091871a18d03111192503514e2e1213a18c6c2727d0fe8905d,0x41320918c3b18d2a1311919c7d1993a1546c16f830fe6305d,0x10f091bc1a22249132192b27d1862a18c79251830f935057,0x10f092bb3b30b03132192b23514e2e1252a18c791916a0f578057,0x1a222632544d2244926f830f935057,0x481bb191a83514e3e1205f15c79193490f65b058,0x1a16f632b52d1316c327830f935057,0x191ab7d19879192830f935057,537301324178,39349969202,0x6c327830f935057,0,0xc10f0915e3b1856630b3514d2e1324d2b05b1882e0f9,0x92fd441d72a02e4d24f2d0f9,0x931f441845f1ac491f22d0f9,0x93203b14d632fc1f131493132e0f9,0x3b2fc3516f493272e0f9,131380,0x2d2fc3b160441602e2fc2a2416c2415f0596a0fb5b0592a0f3,0x213d092343b18c44160351542e1312a23f792473c06081101,0x4818c672b56710f191ee352593e11c2a2bb6c1bf7a05b8d0fb,0x6c11f092896710f662f72e2ef1f11c5f1de792fc830f935057,0x3b1de441603531c792255f0592a0f3]
private def payload28 : Array Nat := #[0x92703b31b6710f0b11649181,0x1a2fc4429b491802e0f937057,0x672bb632c43a1895b1f81905c8c0f2,0x2d2e51a30b49180510f91a057,180439196244,0x4e31c2a03049182,0x4131092fc672b5192477d17e3e13e492fc7d0f36305f140f9,0x482fc6718a192bb7d2415f160492fc44059830f3780598f0fb,0x482fc672bb441836317f2a2b56c1537d0f23705c,0x4e32f4418c632b13a2fc140f9,0x3b2b0632bb490fb78059,254236988156,0,0,0x481d4142892a317,0x92506718848131192fc2e2773e13e5f18c49269830f463061,0x2d31b3b2b01431b2e1de791821e05d83100630642a0fe,0x2d2724e1fd44153352545f18d5b1bf0905d8310063064140fe,0x4d10f092694e2f70f11c192fc7d2bb7931c09057700f9,0x3b2b0632bb8310063064,0x3b31b492fc8310063064,249654784795,0x1e333671880e11c1431d352ca3e1453a15c49227830f463061,0x352545b1b18310063064,0,0x10e481971a2bb4414e2011c2a30b792b0,0x10e2d1961a30b0311c44270632725b16f510f91a057,108095840944,0x4e3202e19149191,0x21451e29c1a15c140204414e2e3022011c3a305792c45c06666104,0x2d16f4e2fc251311414c3531b5f269792773c059480fb,309591253323]
private def payload29 : Array Nat := #[0x91546718c251324418c2e2692d1313a2fc492776f10463066,0xc1312d1de1a249661885f1975b1591e064140fd,0xc1312d31c6614d3a2fc5b2e2,129636921740,0xc1311e207662475b277,0x2d3204416f3a2fc,0x93176718c4813d1915c2e2c61f11c2a29b492e26f10463066,112391066299,0x2d31c1431c3a258,373332,0x2d209142093a14b1e05d2a0fe,0x1e15c4415c5b159,237973,0,0x213d4818c6716f142b56314d2a2d46c2ef490f937057,0x2d2500e13d141af7d31b2d1314d1de6c31b5f0596f0f03505d8d0fb,0x483231431c6c0294d182,0x491256629b2e2826c0294d21a7914c4910535065,0x482fc662f77d31b5f160792fc830f935057,0x10f091bb1a30b0311c6619f7d1c04d2b56c16f510f657058,0x92604e18a66018191ae2e2693e10f3a2695b26736059140fb,0x924f3b2510311e661626318a3e10f4d1615b1c164064800f9840fd,0x92521a18c66018661646318a5f1fd5b1c24e0f9,0x2d2500e11c191af2e26e3e10f3a2bb5b1ca6c0fc57057,0x6715266018191b06318a4e0f9,0x2d2506716f66018191af6318a3e10f4d1655b1c4800f937057,0x1a1de351c84d1604927e140f9,0x92503b1c72510f142f95f2fd5b1c7,0x48256672071431c4d0184d160,0x93230e13d1915c351ca5f2f7830fc35057,0x1e2504e2c0191a13a31f,0x1114e320351c25b1c24e0f9]
private def payload30 : Array Nat := #[0x4d12f2d1b26715b66018661666318a0b11d4d1655b1cc2e1051a05d,0x4e31c351cb4d0185b1c34e0f9,228108644805,0,228116975975,129199460696,537688142399,0x2d14d4e22248112141517d1b82d10f3a30b5b1fd,0x2d1884e1d20e13e661f7631592d10f5f2bb5b249640648b0fb630594d100,0x67250671316631b7d1de3e13d4d31b491af1905d8b0fb630592d0fe,0x1e2b514151140f9,0x41321e2bb672c60311c442492e209791605110137060,0x2d18c672fc442242e2092a2b5791608b0fb63059,217684,129206665553,0x2d222672500e1327d2d68b0fb63059,0x1e31c4e18c0e1311429b7d0f863059,0x482c01a2b2792b28b0fb63059,0x41240915c661b1631596a0fa3b05a,217684,0x4e0202d2fc1a31344269,0x4d13d1e15c672c60311c6629b2e2093a317791605110137060,0x2d317662893a250,597264052313,39017702069,129212322137,0x1e15b3b3273a294,0x92b06730b0e132142b03514e2d1123a1594922a490fb78059,0x6718a632bb5f1596c294,0x92516718a481314418c7d23f2d1125f18c4926e6c10163060,0x10f03140441f7351be5f15b5b26f,313796296793]
private def payload31 : Array Nat := #[0x1101e31b3b31b4d1ca6c1ca,0x481971414c353273c059480fb,0x482fc672fc4426c6327a2a18a5b31c1b05f140f3,0x1102d1754e1724913244270632726c1c2670fb5d059,0x1102d1734e1760f11c44272632702a18a6c1c55c055840ef,0x1e2ef4e16f4d1c86c0fa5d059,0x3b2092a10f7d32f2a18a5b31c3c059140f3,335808779035,0x2d294192c04d1c23c059480fb,0x931c1a31c0f1161931b,0x2d2bc1a180632c23e10f7927e,0x672fc7926e670fb5d059,0x442725f2723c059480fb,272,0x1e31b3b2096c1ca,0,0x93201a182671326327e7927e670fb5d059,442645205081,0,0x482254e1506330b4914d,0x482493b18d442247d26f4914d490fe3b05d,0x13e2d1f71a159192bb7d1a82a1881b06414100,0x9151672b5191b42e1b63a31c492fc1b06484100,0x4830b6718c25132191892e2c64e10f2a1ae792bb1906414100,0x4e1572a1881b06414100,0x6c145482474e16f142d42e1b52a2bb4914d1b0642e0f93705784100,0x1e31b662f72e2ef1f11c2a2b5792fc1b063830f935057140ff,0x93271a15b25140351f7,0x91513b31c25131632e51b06484100,335846716171,0x4e2bb191891906414100,0x482fc6730b3a31b19063840ff]
private def payload32 : Array Nat := #[0x4e224192591b06414100,0x4e020092fb4e30b1923f353321906414100,0x91b74e2c7192591b06414100,0x1e3323b15c2a1881b06270102,0x482e5672092e1512e0fe1a05d,0x1e14f4e2222d10f792d35f0598d0fb,0x1e18c3b1ea631de5f2fc6c2777d1065b068,0x1e15e3b1ec3518b,39493886498,129423745517,39070221052,112408892083,112084898587,443114975566,0x482331a30b4914f510f91a057,194007638812,320288,0x4e3172e21349213,0x2d30b1a1606710f19225632bb3e1325f159492b9510fb35059,112029942453,0x4e31b49151490f9,0x1351e2ec3b15c2a0305f1595b1cf0906770103,0x4e30b441597d1f7,0x4e14d0e13e661ce7d1505b30b,0x1a158441597d229,0x1324e158441597d22a79186,0x91e00e11c142b7632fc1f1313a1f07918e6c0f957057,0x2d18c4e2b52511c142cf7d1f71f1312a2c6791bb,0x4830b6718c48132192542e2c61f1312a2c1791bc,0x6c1302d1a16716f0e132142b77d1501f1313a1ef5b30b490f937057,310038999495,0x3b15967128441597d22e]
private def payload33 : Array Nat := #[0x2d18c672fc7d22d,512336,0x3b254192547d22e3a2b0,0x3b1de03127441597d22b,278873,0x132091e83b15e192547d22c3a2b0,254204694864,0x2d18c672fd251312e29a,0x6731b7d1502e0f9,0x7d150490f937057,0x413b092b26718f0310f192312a18779320,112034333017,537223422201,193761198799,159249551912,278873,0x2d18c1a32025131,39161447096,102996,0x4e2bb44159792c4,0x3b2fd2e25b49320,406121,102996,0x672097d1502e0fe1a05d,0x6731c2e25b5b302,102959,0x1e151672b56710f191ee2e2cf3e11c2a2b75b1f77a05e660fd,299345,0x21381e2b94e18f141880b10f5f1f33c064700fd,0x3b2f7141883c064700fd,0x1e2b94e2c0442c23c064700fd,257803354365]
private def payload34 : Array Nat := #[0x481cf192b03a2bb3c064700fd,0x1a159201154d1de491f9,0x3b18c1f1154d1fa792474e0f9,0x3b18c192700b1133a1fb792474e0f9,0x2d2503b1500e131441643e1325f2777921e5f0598d0fb,0x3b1583e1154d1de7921d,0x1e14f1a1540e13d142692e2b04e1312a1ff792224e0f9,0x1a2510e13119243352491f13e2a200792476f0f9,0x21321e2161a2542e020192b0141132a2047921b5f0598d0fb,0x1a1550b1152a201792474e0f9,0x931b3b14d6618c6314d2a205792224e0f9,0x4e18c0e1313e1324d1de492c6,0x1332d2504e18c0e13144164631bc2d1322a18b791db5f0598d0fb,0x3b159441603531c201313a2bb792255f0598d0fb,496199,0x48184672470e131141b02d13e2a1b9792275f0598d0fb,0x1e14f3b2ef2d10f79220,496199,0x481d2672b50e131141a82d13e2a18b7924a5f0598d0fb,0x201282a206792476f0f9,0x481d26730b5f277792275f0598d0fb,0x1e2b24e2c0442b25f0598d0fb,0x1e20f672c02e1282a1bd792235f0598d0fb,0xe1313e1402a2027921c,0x67224141a83a2597929c5f0598d0fb,0x2d2fc4e30b142fc5f0598d0fb,443114901982,0x1e14f3b31c4813d2e2c43e11c7921f7a05b8d0fb,496199,0x4e2bb44160792255f0598d0fb,0x1e20f2a1fe79223,0x1a31f631d2792a14e0f9]
private def payload35 : Array Nat := #[0x2d2504e222142c15f0598d0fb,180886147622,112396256027,129410179587,238169,0x1e21a141af2a2045f0598d0fb,0x21382d2c14e2c7141ad141322a2087924d5f0598d0fb,129411375650,0x1341e2ee672fd4813d192432e20a1f1322a20a79224,408115794171,408115794171,389209,129201763069,295676,0x6718a1432f2a2bb490fb78059,0x6717d1420b7d24f4d2247920e490fb78059,0,39016960345,129206686092,0,0x91511a154671311420d352222a2695b30b640674d103,0x91511a2ef4810f632e5,320249,86626226972,0,0,172382,172382,0,0,0x671c62e31779232,0x2d2471a333142273e11c6406884106]
private def payload36 : Array Nat := #[129593787078,193846370682,0x2d2fc3b14d67132142bb3516f4d1f649297,0x2d1554e2b50e145142b52e2fc5f1f5491e1,0x2d1551a31c3e131491e9,193631335196,335740682574,0x1e1fc672c05f1f4,0x1e3251a2092e1d3,0,0x4e3172e1d4491e0,0x6c1314827b3b2b5491316626e3518c6c2501e05d6a0f91a0572a0fe,0x1232d194671947d18d4d18d,0x411c09300672b049131191d3632bb5b1d409056140f7,0x3b2a15b1d26a0f91a057,0x6724f632fd493276a0f91a057,0x4132483253b32f192fd7d2243a1547931c09057700f9,0xc1402d1f1671ee4427235209,0x4818c4e2b5142fc2e2fc4d20c6c1eb,39376425453,249749082604,299606,237918,0x5b222490fe3b05d,0x661222d2601a18c491246627b2e27b2e1225f18c6c2601e05d4e0fe3505d2a0fe,0x6718d49123441bf2e2693a2695b2676710489066,193902993739,0x1e2514e1882513e4418c352342d1313a2476c23f831027c062140f9,0x91541a1540e13d142702e2701f13d2a270492704e0fe2d0fe,0x92501a18d192503518d2e1213a19c492682e1055b065,0x1e2504e2471930b2e2694d2986f1067c068,0x2d2500e11c192b02e26e2d1313a2bb492744e0fe3505d]
private def payload37 : Array Nat := #[108175532796,0x482504e18c481311930b2e2733e1325f18c4926a1b057140f9,0x9154672b548131442a12e2803e13d2a2b049269801048d0f9,0x6716f3518d2d1314d1e14927d,0x1112d24e1a15e4912619187351dd2e1263a1875b1dd,0x1111e2591a30b491251919b2e2722e1243a2b25b18d4e0fe5705d,0x4e0201e2514e2b54418c2e2692d1313a1a0492768010789069,0x482586718a481311424f2e27b2a1af4926e3c0596c10163060480fb,0x9154672fc48131192223a30b,0x91544e2fd6631c3e13d4d31c492802d0f9,0x9154672fc48131192223a30b,0x3b1de491274418c2e26d2a31c,0x3b2fd441f73518d3a2c2492724e0fe3505d,0x91543b1516631c2d1313a222,0x1e2501a24f491284418c2e2792e1242a31c,0x4e2ef4912a191a23518d6c2124e0fe3505d,0x4912b191a83518d3e1203a1a44927d800fe3505d,0x111482561a263192b52e1293a18749275,0x1e2543b2fc4912c191a63518d3e1203a1a749270800fe5b05d,0x1114e2f9192c62e2723a2c6492724e0fe3505d,0x3b1512d1313a2c0,0x925a3b254191872e26b5f18c,0x1111e2591a30b491251919f2e2722e12d3a1a55b18d4e0fe5705d,0x1e2514e30b1930b2a320801086306a,0x91544e2fd442fd3e1323a1a1,0x925c672071431c3a2506f1097c06b,292473185051,0x1111a2c01919e3a2c65b2676710489066,0x1a2227d2604926f4e0fe3505d,0x191a83518d3e1203a1a94927d800fe5b05d,0x931f192b53a2b5,0x9250491241431c5f18c]
private def payload38 : Array Nat := #[0x482561431c3a250,108175683980,0x6731c4912e3518d49271,0x122482641a15c4418c2e2813a2fc49277090574e1088906a810f9,217485,0x672bb1930b7d32a5f18c1b057140f9,0x1e2621a30b141ef3a2c15b18d4e0fe5705d,198218850921,0x91541a31c2e27a3e1322a3255b32f360574d0f9,0x91541a320142f92a2f9,389516,0x1e2504e15f191a12e27f6f10a6306b,0x191aa2e2703a1aa492704e0fe3505d,0x4e320192c62e2723a2c6492724e0fe3505d,0x4e2ef7d2604927c4e0fe3505d,537427100178,292630536784,198224155248,0x1e2603b20948131492696f1087906a,0x48264672f74418c2a15b0905d140fe,238278,0x1a2b57d3336c31b4e0fe3505d,0x9250143173a1a1,537730138720,0x49125191a92e2825b18d,198224155249,0,0,0,112031298014,0,335424176535]
private def payload39 : Array Nat := #[0x6c135092984e16f6710f661fd352a11f13e2a2bb6c1522e0f937057,112031297881,112027156818,320288,107207,0,0,0x13e482d33b30b632fc3a31c5b1d06a0f91a057,0x1e2091a2fc4910f4432c2e3133a31c4914d2e0f9,112032235865,318,0x4e3177d289491d4,0x1121e2a41a2bb44254492fd,0x1124821f3b30b03132632fd3a31c6c1c26a0f91a057,0x91514e16f4428e3530b3a31c4914d2e0f937057,0x673206325c7930b,315868,0,254237004358,0x4e3172e2866c1c6,0x6717c192b52d1123a30b6c2371b057840f5,0x6c131482cf1a2690311c6619f7d2b04d2b56c1534e0fa5705a,0x482fc6718a1423d7d23b4d18c6c153490fb78059,0x7d1585f15c490fb5b05b,37337,0,0x1e2890e11c142bb632fc1f1313a1f0492ef6c0f957057,129695461897,129528914564,112031298295,0x4913d4d2224925c,0x211c7d0296621a63158201395f15c792ec7d1075b069]
private def payload40 : Array Nat := #[425802044039,0x482fc4e18c142412e2e22a1881b064810fd,0x482fc4e18c142406324b2a1881b064810fd,0x1e31c4e16f1424263248792516f0f937057,0x2d1ba1a1c7141b96324a1f1312a1b01b064810fd,0x481cb1a31b03116662932e2271f131,0x1a15c661de1e05e810fd,0x672bb2a1881b064810fd,0x2d211142106324c,39440192089,318,0x1381e235672c72a1323a24f1b064810fd,0x13e4e31c491327d3133a327792514e0f9,0,110692,0x7d13e2d2d31a30b351d20b1326c31c510f91a057,0x3b15f0b1404923a,0,0,82509,0x792bc490fe3b05d,193887183462,0,335420691227,194074960651,0,335842415195,0x2d2fc0e11c142b5632fc4d2f75b2466c0f957057,0x661372d2fd4e16f2510f661fd352381f1322a2be792b56f0f937057,0x1e23e672072a252,0x1e30f3b30b63251670f91a057,335846629625]
private def payload41 : Array Nat := #[0x7d1391e2ef6716f14029142bb351534e10f4d28f5b2a1490f937057,0x2d2fd1a31c2d13d,193907290658,320034,0,0x1e3253b3254432563325,13190226325,0x1e2693b2771414b7d2fc2011c5f31b5b27b,0x21326718d142fc2e2fc3a27a5b26c,0x3123141972e196,0,254055473916,12579,0,0x1e2741920963325,0x48027093336718d2513a1929b6329c6710489066,0,0xc11c1414b353172011c,86528709408,0x9320672b56710f,254199218654,0xc127482cc1a30b6c152510f91a057,107107,422667,0x2d020092fb4e2fc7d234,0,0x3b20a7d2363a243,0x481554e2b52511c142be2e2c22d1315f269492cf,0x1132d2db1a30b0311c79251510f657058,112034136408,0x113482901a15e192be3a186,237977]
private def payload42 : Array Nat := #[0,562902028375,0x6c132091df1a2bb0f1321915e7d2c12a30b4918c,0x672590310f7d22f4d18c492bc,0x1e31c6714d2e3203a1c7792fc,0x2d18c4e2502511c2e2c14e1322a2c6791bb,0x3b251671132e297792bc,0x4830b4e30b48132442b87d2444e1322a2c15b263,0x482fc1a14d193067d2991f13d2a2bb79251830f935057,0x93201a14d6710f1932c7d31c4e1322a2c4792fc,0x1a2fc2e320792fc,0x4830b4e15319330353113a15b4918a670fb5d059,60421558940,0x35222490f937057,0x4831f1a14d0e1311932f7d31c1f13d2a2c46c31b4e0f9,189006,217634,0xf1317d29b4d18c5b31c,0,217692,0x2d18c3b15d2511c2e29a1f13e2a2c6492c4,0x4e0204e30b25114442782e29c4e132792c7,0x482501a320481327d29d1f13c,0x91e3442b82e29e,0x1a18f192d07918f,0x41311e2a1672d1191552a16f6c1a009057810f9,0x41321e30b672b30f1324430b7d2b30b1423a1d44919c5c057810f5,0x7d1131e2a03b1bb142b52e1922011c6c1a8,0x21281e30b4e2cd09057810f9,0x2d2274e2cf191c72e179,0x482fb1a32c6614d6331c3a2fc6c24709057810f9,0x410f1e3051a2bb1914e4d2bc4918c]
private def payload43 : Array Nat := #[0x7d10f142227d2b5,0x4d10f1e245672d5192fc2a16f7931c09057810f9,0x4d10f483134e2c844153632042a16f7931c09057810f9,0x2d2e2672e21418c7d2b54d2b54918c,0x6c1122d2914e1fd0f1321424f4d1c25b31c,0x4d10f1e30b3b2430f132661517d2ba2a16f6c22209057810f9,0x4831a672f77d2b62011c3a2fc6c30b09057810f9,0x21311e2a24e214192987d2b50b1456c2c6,0x21311e2a24e1e1662fd7d2b5,0x661121e26967293142fc2e17c2011c4d2b06c1a35c05a480fa,0x4d1321e30b672d80f132442224d2505b32009057810f9,0x662b54d2fc4918c,0x191de5f31c4918c,0x41121e30b6721f142984d1c25b31c09057810f9,0x41311e30b192fc2a16f6c22209057810f9,0x13e1e2a41a2bb0f132192bb2a30b5b31c,0x7d1321e2a54e2cf441517d2502011c6c2c1,0x4d10f672d7192fc2a16f7931c09057810f9,0x11c0f132442bb7d2c64918c,0xc10f672d6442987d2b55b2b2,0x2131442ef7d2b52e13d4d2c4,0x7d1321e2a54e214192987d2500b1456c2c1,107195,0x1141e2ae1a2bb0f132662f72a020,0x66131142fd7d2b5,0x1151e2a61a2bb44159,0x6c1151e2a73b1bb,0x21311e2aa662fd7d2b5,0x1e269672db3519a,0x41311a3072a16f,0x6c1311e2a9672300f132192b57d2be2a16f492fd1b058840f6,0x131672e2191594d2fd4918c]
private def payload44 : Array Nat := #[0x413148313191552a16f4922209057810f9,0x4d13e1e30b672d30f132142f93a1d05b31c09057810f9,0x6c1321a2bb0f1321915e7d2c12a30b4918c,438888288949,0x192512a16f6c2fc,0x41151e30b672d95c058810f6,0x4d1141e30b672d20f13219222490203a1d009057810f9,0x4d1151e18e4e32a1918c09057810f9,0x4d10f192fc2a16f5b32009057810f9,0x21151e2a71a2bb1915a,0x21321e2a54e1e1662fd7d250,9342636935074485,0x662fc7d2bb4d2b5,0x211c091ee4e2cf142fc7d2b52011c4d2c46c2c6,0x41321e2a1672d8192fd4d2506c1a009057810f9,0x410f672da0313b6618f352b23a3206c187,0x411c1e2a93b1ef0f1321930b7d2c42a16f792f91b058840f6,0x672dd662fc7d2b56c2fc,0x672dc0313b662b57d2fc4d2fc6c187,9342658473874101,0x926c3b3340f132442c0492225c059810f8,107097,0x6331b5f31b7931b,0x21162d2916721f0f132192c07d2c54d1c25b31c1e05b480fb,0x1e2ab4e2142e1e3,0x1e29c1a2596c1a8,0x211c1e29f1931c7d2b52e13d4d2c4,0xf1324415f49222,242107,0xc10f662bc7d2b5,39512761039,0x6c131483161415b2a16f]
private def payload45 : Array Nat := #[0x1e2ad672e0441507d2fc2e13d5f15b5b27b,107195,299404,438444634908,0x7d132142bc7d2500b145,0x1e2ab4e2142e217,0x210f1e2ac1a3061914d7d2bc2013d3a2fc6c18f09057810f9,0x4d1311e305661582a17a4918c,0x1e30b3b334143203a1d009057810f9,8882549042,0x1e3241a2596c1a8,0x41401e2a86729f,123659,0x413248313192fd4d2504922209057810f9,299681,0x21401e2a0672db63271,0x4d131672e24415a3a15d4918c,0x1e2ae1a27a0f132192c72a0202a30b,0x661151e2a1672df6615d3a1d109057810f9,0x1e2a1672e1143173a1d509057810f9,0,0x6c1320313b6c250,0x11c4415c3a3174918c,0x7d132193207d250,38746460409,295821980,0,38746460409,0x41341e2af672e37d2c53a1d9,242183,319839,107107]
private def payload46 : Array Nat := #[107207,112034333017,37664,0,0x6718e2510f792c6,0x1e2851a1901428c,86584304304,0,254204588373,335740682585,0,0x48216672c02a215,422436,0,112529388176,0,86487728422,0x2a1141915e6328a4d1d76c30b,0x1e1b1191d96328b,0x92cd193207d2fc,0,0,0x2d1561905d2d0fe,172832,0,0,0x91554d2091905d2d0fe,249937826338,0,0x2e2986a0f91a057,0,0]
private def payload47 : Array Nat := #[0,0,443049,309851341511,103011,295499,0,0,184903,0x93134e14d6713e142e62e2ef1f11c3a32c6c2fb830f935057,0x493202e0f937057,512318,0,0x2d2471a3333e11c,238179,0x2d2fc1a31c3e131792e7,194074882844,8468,295396,108095840954,320253,253766193495,242015,0,335375602243,172518,0x2d312672c72a259,0x7d141482ce3b15c4d157190684d106,443216704088,320034,0x3b155632fc4e0f9,254199218521]
private def payload48 : Array Nat := #[335846629625,295397,442956640855,0x926f3b2095f2e9492a5,242375,0,0x6731c632584e0f9,0x482fc1a31c2511c632d2,0x482fc3b31c25131632e5,320288,422667,0,184802,107207,0x92b93b190031115f2c2,0x3b2b5632b449317,112034333017,108103180976,0x1e3144e2c744255,112465408334,442956489298,443127407186,112034333006,0,0,188817,0,39394341575,496220,0x6731c14020632516c320,0x6724f7d17d492966c0fb89059,0x4d1322d2b149136142947d2c74d1ad64059660fb]
private def payload49 : Array Nat := #[464120221785,338736174109333,443147,0,0,112402207068,107195,464177828431,0x11148317192b52a2397919009057810f9,0,0,0x3b2c77d2a9492ec,0,0x1e25b3b3202d132492eb,496220,112411730675,0,129545380631,0x413f672c70f11b2a0293a24f,0x672c40f11c2a0293a24f4921a,442877710947,0,0,443147,0,0,442748736196,295434,443114975991,0x7d1481e2564e2fd2d13d2a1e6,320034,0x2d1cb3b31b0e1313a31d49227]
private def payload50 : Array Nat := #[0x1e2f06718a0e1311432f7d31a201162a2216c2926f0f178059,0x1e2ed672073a1b2,0x1a2fc6c1c76f0f937057,0x1e3133b16f0e1317d3274e1145f2f6491d64e0f9,0x1e2f11a30b6c1c74e0f91a057,0x41281e2f23b30b632fc670f91a057,253768364791,129693229392,442749854182,0x931c4e2b54e10f,422667,0x3b2fd632584e0f9,0x1a222632584e0f9,242375,129476174624,0x1e2f3672c75f257,335842611795,112034333150,108116812484,335753069145,335846629625,0x1e3251a20919209633014e10f,0,107981804264,0x1e2ea1a30b792fc510f91a057,253768364377,335740506456,422436,0,0x3b2bc6c0f957057,0xc11c140206630b7d3025f3323a06a70108,0]
private def payload51 : Array Nat := #[85933179492,408882168330,0,106847,39452779296,0x1a2b52e317792b6,0,0,0,0xf1322a2bc5b31c,108000625351,8910156123,405851,8910156123,51831485212,0,103016,107207,537192182368,279324,0,0x41162d2271a31d1931b7d1cb2011c791f2,0x48314672f71915c,39512523531,107097,0x1e30b5c05d480fe,0x4d132483131431c490203a2517932709057810f9,0x411c483161a3072a145142093530f490203a251793171e05d810fe,292423123637,0x7d132193203525b,82466,90951640596091129]
private def payload52 : Array Nat := #[0x2d320360574d0f9,103108,82196,0,0,228378129094,0,0x1925c3a25c5110b3706c,0,112411840955,0,0,0x1a2fc2e2fa792fc,0x1e3176714d0e11c1932c7d3274e1432a2e66c2094e0fe3505d,0x1e3271a251671322e3204e13e6c31c,309861843250,0x2e2f92e0fe1a05d,0x6c13e1a2c70f132443302a30b492fd,0,0,0x483066630e3530b5b2b56f0f537057,425567056218,129210966715,0,0,188962,512779,0x671e72e15d490f937057,0x3b2fc7d2093e125800fe5b05d,129474159303,39383855806,0x6630d7d2c75f25d]
private def payload53 : Array Nat := #[0,0x3b302352b55b2b5490f937057,0,39493673760,320288,0x1e3204e2b5031174e10f,242375,0x2d0271e3273b15b6710f1f1194d2c96c2f4,39493886330,0x2d0271e3273b2096710f1f1194d2ca6c2f5,320192,0x3b2fd7d2606c3274e0f9,0x1a2227d2604e0f9,0x3b2c4632c45f15e79312,0,193907052850,0x4e2c7140201926014132,112503021839,320196,0x1a2506331f492ee,0x1a30b792fd510f91a057,0x4e2bb1418f1f124,0,0,0,0x482fd1a3176713d,335503815252,335749923215,0x3b2c4632c45f254,0,0x6715b631552e0fe1a05d,309810274653]
private def payload54 : Array Nat := #[0,0x482221a3174e13d,184924,0x3b2b5632fc49317,0x3b15c5f2f73606a2a108,0,0,0x2e3275b17a490fe3b05d,0x2d0292d2c04e21a14309632e54406b2d109,0x5b17a490fe3b05d,185105,0x14308493030906c1410b,0x93134e2fc1932d,406215,193848554068,0,0x93056332c5f18f1b0662a104,0,107015,0x411c092fe1a2de0f13e141c96331d4d2fc793131b05a140fa,0,442951,86374478102,0,0x1927e4d25879327,0x41324d2587931c,0,185003,0,0,0xc1321e3113b335141c36c2247a0594d0fb,422495]
private def payload55 : Array Nat := #[0xc11c4831a4e32f6618a633331f1164d3016c2251e0602a101,442951,0x1e2c0141c62a2967a0594d0fb,524079649019,442957,0,499801,238002,0x192fd2a2641b0572a0f9,0,0,107199,0,249937826338,172824,0,0,0x1a3355f1b35110c3706d,320192,0x93183b31c4813d,0x2d31f4e2b5031173e10f,0x1e3334e18d0e1311f1402a2a3492ff,39290250016,443127407193,253768364375,0x6c146093194e2090f1421932b6330a6c31b491053b05d,0,0,0x1a2507d318492ee1e06d2a10c,0,0,0]
private def payload56 : Array Nat := #[0x7d3182e0fe1a05d,512792,0,0x4e160671321932f2e3251f13d2a20749325830f935057,0x4e264492ef510f91a057,0x93201a1540e13e2e320492ee,39452779287,299606,112124314119,242099,0,0,0,0x483281a30b192d16c15b4e0fe5705d,107292,422667,442956333796,319839,193669997344,443127407193,335842558560,0,0x792fd510f91a057,299808,37454,389827,0x142241f1304d329792cb5c06b6610a,0,0x1a24e0e13b1f13b,0,0x2e31c5b30b490f937057,0x1a2c41915e491bb]
private def payload57 : Array Nat := #[299716,426043216580,64708973237,0x1a2507d320792fd,299408,0x13d483044e15b2a131443067d3255f15d7914d490fe3b05d,0x673332e31c2e147492642e0fe1a05d,64709047067,512800,0x483051a2c60f10f3a3275b209,315,0x928044321352244d30e,0x3b2fc6330b490f65b058,0x352fc5b30b490f937057,108209255196,194006889207,198402487051,0,0x3b2fc632fc201213a32b490f55b057,315881,0x6318c4d32a5b30b490f937057,0x211c1e2f73b2fc443200b1315f15c6c325490f937057,198295204145,0,194006700378,0x63222490f937057,512397,0x211c0932f3b300443230b13d5f15c492092e0fe1a05d,0x2d3072e2095f32e5b30b490fe5d05d,90824256870461745,194006995703,0x3b2587d31c490f937057]
private def payload58 : Array Nat := #[194006700380,184921,39397487300,292899123810,129573864129,0,373404,0x6613d1931c7d2fd0b132,406052,0x49327490f937057,0,0x3b3022e31749333490f937057,108175610191,443072,0x1e31f1431c3a250,0,0x931f1905d2d0fe,0x662196c0294d21a6c2c0,0x192c73a2c16c30c,0,300274793292486,0,0x13b491325f3207925b,0,496423,0x2d0273b26067132,0x1a2c20f111792b9,292426322587,0x311c3a3175b150,217636,0,254248284468]
private def payload59 : Array Nat := #[238179,108175683980,17500000949,443011998407,0x92fc663334d2091905d2d0fe,309870252828,254145868484,0x6c13d0f13e4d2fd79320,438925840733,0x483100f1313a209,389642,0x2d31f4e2b5031171f131,0x4831f0e13d662f77d2091f11c5f2f86c31b4e0fe3505d,253766267639,0x2d31e1a1540e13d7d31c1f13d6c31c4e0f9,194111447840,443127558743,112034333431,0x4e2090f1426c31b,254137393401,0x4e15d7d3276c3334e0f9,0x4831f3b31c4813d,242186,112414769967,0x4e3177d3336c3334e0f9,299808,335808750332,0x3b2507d31c49320,0x3b250632fd49320,0,0,0x2d020093331a16f67144193157d2091f11c3a32c6c3274e0fe3505d]
private def payload60 : Array Nat := #[0x2d0202d30b1a3333e11c,238179,0x3b2c4632c43a263,0x2d020092992e1d8,0x3b2c7140201430b2e2fd20132,0,193912193825,0,0,0,0x4e1564e0fe3505d,0,194000511281,254272,0x2d0201e32566027192093531b,0x93174e2b5031171f11c,0x4e250031174e132,0x3b2b2632b220111,0x2d027031171f119,0,45364,0,82631,0,0,0,0,172580,0x4e264792fd490fe3b05d,0x2d2224e17a0e132,0,442768]
private def payload61 : Array Nat := #[0,0x4815f4d331491e9,0,0x4e31c7d32379250,86266843844,0,0x4832a4e2096632f5b18c490fe3b05d,0,315789,0,0,425947616047,82320,422667,242276,112414134982,0x4e020482fc3b3172511c5f2835b32d,0x4e020482583b3275f27e,0x92bd3b1905f26a,17515651680,0x4140483016732a4d18d,0x4134093256730b5f224,0,0x4e020672ac25132,0,39019827546,194019283549,0x93171a1540e13d1932f2e3251f13d3a32f493254e0fe3505d,0x1a2b57d3336c2094e0fe3505d,39484236576,443127407202,0x4e31c6c2644e0fe3505d]
private def payload62 : Array Nat := #[112034156892,0x4e2090f1426c209,0x9317672fc0e11c0b117,0x1a17a4e0fe3505d,0x3b18f633053a32c,0x3b2bc4e0fe3505d,0x2d0271e3333b15b0e11c1f1195f30f79310,0,319838,0,39484449314,0x1a31f4e0fe3505d,0x4e15d7d3276c3334e0fe3505d,0x4e3204e0fe3505d,0x2d0271e3333b2090e11c1f1193a32d5b332,0,0x93173b31c4813d,0,112414769967,0x4e3177d3336c3334e0fe3505d,0x1a2502e3176c31c,0x1a263192c53a2c5,106874,0,0,242277,0x93206725a0e13e1f13b,422494,107295,0x2d0273b264671321f11949324,0,279349]
private def payload63 : Array Nat := #[189207,198398219040,0,0x1a2c7443307920a,308091723841842,0x93331a333031180b117,0,0,217886,0x2d027093250e1321f1193a334,0,0x2d0271e3333b333031171f119,0,0x583864433a8f386675a6765a60657e195a61a33604336285a64257e,0x325a66d5a66a5a66b5a6073362f336373360f5a6115a6,0x3d5a6645a0863b3496288168e015a6365a0303b30248b0d4822733b,0x4d4b67e4a60a41a3a3b33b35f0141a365a6470571a4992548b3f72542386,0x5e33e443368548b593cc2f0592c4993b361084c8193367348b0f3b32134642360,0x43643873780c057675904a336400573b364143362f7354705735643025483f3f95705742365,0x5e377443368968e7d0591c34e2f0595c6403b35c083b56f504470571a76c254e8213804235d,0x4368e7a68d71367675972c386700593b389143360970347057376280705902640213445705942363,0x5836e5f3b3450578978e1c3472f0594a68d3005d3b38a0636e093b3270583778e07059036282135742386,0x5e33f3f0577578e7c4c81c3583b3661837e050571678e574c8070590f68d0905d214594235e,0xe057667b2754c88d3b30205d1377f2c48b8877f14336366283568e070590478e613d042362,0x3d3bf8733e8968d020571c3555a4c83b36014336093711a68e1805b0f78e2145b42361,0x534b67e3868e48b3848b803864b4b6013f71206416499573f70e5900d52942590,0x4d387260597237f8805986640393861e4e8766402d68d1b3677368e2068e3f62829336,0x4d38e723852b4c81e41a40057764884e390120640968d2705d503940373b6148d570576578e,0x536e07237c45060856431c3b34a5e9420575b538013f9120646f4c829057574010468e0546529336,0x5e7b05f4a47c6432a3b32c383420578138c0662d09628843b5023b91069445341,0x7d5e94605764538633b32a4c8230571e5555b3f94e38f12061166435039620465213361167a,0x250574d38d72381853b31405c2b78e2c38281388143b512064516285750b0a05d0077f414a51167b]
private def payload64 : Array Nat := #[0x4d4f77237d7605b8f78e1c6282c384813864e391120641968d1105d503930036e0d3b33705722491,0x4d4f5443d27305a8278e1c68d5a4a52205d8138a4e3971206419628843b5003b30d4f71a05729491,0x747a3443d60a68d3c3c94005d8138b4e392314c847057503952548d2173b57057627b2,0x4d46f724668805971777580592b7772c4668146f4e3982f468503983e6ab415bc406ab,0x43336647256348b0a4992c4925b39908529363b35739a03336467254548b,0x43336546a1450576368e660661c6434c3a05b39d030572d555164c87351c070570f5b10d4c87b3b3,0x4d3717a3368d68e0a4c841057775af7639a1859a5678e573993e7251905d415a81168d,0x664bd7e36c450578d78e2b48b4c3aa2205d5b39c157913668e57482024bd0d36c350572978e,0x536d36457e450588578e394c86841d420573b6cd153a75168e574820036a4661622643,0x4d4bd7e3b37b0588f78e1c6284c3a95b482074a51968d1105d5739b004bd0d3b35b0584278e,0x535bb7a336450577c7e81d76c3b77f0876d19727737b40c77f1176c,0x7d77f3405d727c6637251d7251605d2c7c67f77f2e3a6166a95761300373213363505742774,0x6c44c544f560059794990a3b32c3b340057694990848b4f4b64b05d525a61f4b61248b7b482,0x7d505443c78e4e81c3362c36d400578c3770154b564526b059843d83e5d141725654b2,0x243865446f600598d628594911e3c78605b784f70754b3144485059843d92058261725294b6,0x58590543de8d5a60a46f4a336400577f4d61833b0505d1b554554b020542105a0653c5,0x7d42a543dc7c5a0385b2776ab5d336085a6163f3843da027251033b1a05d60554,0x663d5543dd8c060896433867a1e6285d336143b3195e92905750538003ae464c837057653c6,0x663cb836e08c0608a78e5961e1e4d65d3360768d163f41105d5278420590284c81a0577b603,0x6c46a5433760059857743867b5c7c68876d337251005d3776402556106a962616,0x3d49c72367853671c3442f059683e3500597f3e30149c5648b7348b0b34419059263e335059453e3,0x533675f4986348b140590a5283a34a7f3e201499094a1573b304386124a129499,0x3d49c723678548b593cc2f0593a3467f3e30149c5648b7348b3e3cc1905921346453e3,0x3d4a15f499633b31c44c2f0593a5288c39e014985648b3748b3e4a11238660499,0x3d3b75f3b771499593c9773c92205d7f3680149d0949d0b37e2137e453e0,0x3d3b546057754b68d337140591c3482f0593a34c7f368014b05648b2705d1a3bb2533d190592134d653e1,0x3d3ba753bb893362a33c2f0594c3bb7f3e5014a1164a7573860f5a612386653ea,0x3d3bc5f3be1c3455a4e87f3e9063af540590976c2705d50640070590076c0d3b5653e7,0x53367753c17c62814059385042f0593a3526b3b4064bb1b446844e807059046d31244c42640,0x533675f7bb89628140591c353773cc7f3e8014a41b7bb5548b070590b353613cc453e8,0x533675f76e89628140591c6403a37b8f0597f3e61868c1b76e55367070590b6402137b7c059453e6,0x533675f4d56368e1c6434c4a15b6e003057147b2164c8843b32405f1f5552145d453e2]
private def payload65 : Array Nat := #[0x584bd5f4a5450578978e1c3472f0593a3593005d8c3ec064bd094a52705d3778e070590b35a190592135745368,0x3d3c2723678968e1c350160553a3548c3e40149c094cd1a68d0b3500905521354653e4,0x583b95f4c6450576378e1c34b3a351220577f3ef013b11649d2706552643070590b356190592146545368,0x3d3bd5f3b7450578d78e593c92f0593a68d2205d7f3eb014d6163b0204c82137e37057453ee,0x5336775774717741c6a7805b07f7b40305d017541b7bb737250b6a921466406e0,0x8b7a31c34a2f0591e7e27f3f11578c164da207e44171f,0x757bc2f0597f54b3078e217bc,0x5f4c2593d72f0593a35b7f3e3094c2507e4233ac453ed,456760809358,0x825a61c3492c7737f3f21578c3579d0b7e4277b2,0x437a37968e014d7097bb127da277b3,0x3d6f95f6f9716a91c3593a3593005d013b1093b1306a9070590b46b190592146b45368,546514949101,0x1c3572f0590705921357,503519430579,0x1c3582c774377e407059653f0,0x5e5058b4476357e0c064386404a3c8420595b3f8015041b725843b503336123767b377,0x1705d5e504834b08d33b0c064675a02c43c5b3f5013fb345a68441703336415b2406ab,0x7d58d644e9865a0137255a4b62205d5d5d1014001206419628843b5003b30d4f729491,0x6c68e6460f383b32c5e94005776538013fa120631b4c827057573ff0068d6148b3505d7b379,0x746b0833b582628593b321057685e176642013f6120643478e573fe0e67b1905d4677f114a5,0x5e4036d49b45062856431c3b36868d420575b538013f96f4c829057574010e67a0546529336,0x5e3fc643f77b0648d78e2b48b1e4042205d5b3fd0160e3668e843b50f67b2355a37057227b4,0x5e4026440245064637770c0641d7771e4025b40201402120641b777574020c37a1237a4537a,0x7d3b58377f6348b0a4993a5915d42501473363b33039f03336057bb424a5,0x7443b644eb8e3670a68e5c5a65b60e2d5820964069059735ef0e55a617b465450,0x746a783417715a62a5a06a416764131305d155545133b844bd033360d46f35057425b2,0x5e50b833b54506482628593b32c510764e207591095a0734e10e67b1905d4677f114a5,0x7d3b57243e450647968e396408b0591e47576412014763436773414026e0640593f67b1155a,0x7d3b572440450646368e740671c6431e47476415030570662b164c8734e0070570f5b13f6d34057e,0x5e5067243a7605e8f78e1c6281e6125d5a6174b61968d1105d575bf004f74159022491,0x7443d7243d45064716a91c7254a77f3005d767c61477f197254b05d737c6207742877429336]
private def payload66 : Array Nat := #[0x43487643b38968e7d0592b63d5c6403b448083b5365a847057557a6254e80554c22443,0x437a63405d7a68e7c48b38582685a08146c014a1567a8844c80068e263b3277b2,0x436165f4a17c6436757e774c8420578c7b50868e316a11a336033b33f68d37057657b2,0x43485835428f78e135c55c68e4b5a60636a316d08205d375a80f4c81255a370572753f,0x1f05d4351f834378648b495a61e68e8160e040574e7b43455a844bd0b78e3f54245484,0x4348a83438387251e68d4005d8146d186e05648d8478e0c4c80541a3505745488,0x537b0544c3896432b7da1e6284b5a6184832f69469057847b10b3b33f54d3705745489,0x1f05753540834298f3b3495a65c6288c6b00636f364b63067b0c78e0543345483,0x8341c7c7e25a7e4816126f78f03628457a3,0x2455f5f499855421d3b35c3de815902e4a6363376e4b6204b01e05d103bb2948b,0x4d4e26d3b37c5101c4b65a77f88386074b63477f73386034231041e27499,0x323c07e7258e556133775c46f883862d4f7563c7305051c0590c5f51044f7b54b,0x66632446287c4820a68d1e4b63b4652d3b36d0592f72c70597004055f0594647a27640,0x4d33983628894947d059384915c4f73b44c4d05b17491364f73558d0705d00407124b37b725,0x4d3395f68e7c4937d0591c5b15c3db3b45b083bf2f6161a44607057004091056d4557e,0x6640f7a78e8e582494a61605d4a4eb3b6f9154bd120572f53f5255a0040b103bb4768e,0x4d4117c4953973b410573a6a93b76c1873b28057196a91a76c0476c1905d4647c1168d,0x1705d4d4104448b7c4972005c387b47773d3b44b0f05c177b45673d1a44b254e8464801168e,0x535a6834c8450576378e1333f4a68d220573b78e1468d2f4a74b05d3777a0c5fc4647e,0x434b15f6436378f1d6285c337815b7154c6050574f70f3050304645090574647d403b3,0xe057437b2723b38e68d7d0591378e5c4f63b45d183362f68e706280a05d0477f6177f1148b,0x4d40e543b365057637b1136944a5034205781677144652f7b173386024066147f3506822643,0x6640d8b78e7c492396285c3373b466334b60505d2f77f7067b0c6421b057415e1223b3,0x4d6168778e855452b4d65c3373b4640836e120574f6a9705900f4b00905d415df2768d,0x6c4c9546437c4961c67b6862b885900767b4f62b7359004652103bb2968e,0x4d40c544828e79d496a16a79d3b44a086284f4821a4670240a4648122482,0x7a76c8977f0a7274a7b48876d18336197e8705bb6177f6276c,0x3d7bc5f76c2a7a65a77f6c059075bb363df73386046c42365e22727,0x4376d5f727717c67d0590a7e85c3373b4691876d7067b0e7642776c,0x4d339447e83c76d5d78f1b76d3778f127732976c,0xe05d667c6837258977f0a6a91e6e03b466183364f7741a7740a05d0c7c66177f29725,0x727747c4821377f4005d0677f2705d004084647b276a9]
private def payload67 : Array Nat := #[0x536be3405d7a68e7c48b6742a685a088477184b6166f53550c1d059007bb213b565791,0x664416d63d86640484421e4e84b66e32059017a62f3b5355041d0590f7a30550862386,0x74752545a68968e7d059497475c64081582083b52f68e736d0004c80553f2955a,0x244728b478713b32b4715c5a05d5912e6286f3861a61f204b61e05d0577f6077f,0xe057436f57a68d8d3b30205d1377f2c48b8877f1433636628357bb1d0590478e6146e473cc,0x8b479717e41e7e488479337743767a027742867a,0x4348b6d49c6348b1d5292c4923b52908529164921a5292548b0549c4548b,0x666286d4c863336493a1805028e0648c5282e3a2193b3704df2548b0d68d3505d114e8,0x5e4986448b8548b595422c5283b528153a0193b31a499023a005499273b3,0x5849d7549d0a41a1e41a765250649f1649f2705d1a4990249f0d49f3505d11499,0x4d4a56d4a55505d714991c4a53a4a52205d3b499074a5194a51105d1a499004a5054a53505d27499,0x4d49a6d4a48d3b31c3b35c4a47849a073b3364a45749a0049a054a4293b3,0x4d4a3543698e4821378e5c6133b499073b3094291a52a004a31036962482,0x664d56448b5505d8968e2b3a34c3a43b528084a12f68e1a52f43059047bb107b27b386,0x4d4cd6448b5505d8d3783958d7758d5b48c1858d5658d3548c2548b054cd3505d11378,107673,107673,0x664c826057757b2793b3493a06a3a5787b42e3a6095556e528007bc4648b4768e,0x664d6727a32b4c81e41a400578c52e0649f0968d2705d6e52b0373b0d49f3505d6578e,0x4d4d96448b8d68e3959a775af8c5291859a565af845290049c054cd1168d,0xe057664d46d4a2824c81c73d6841b8c52f0142d513a6844992548b054d762628,0x4d4d87549d7c6430a41d68429420578c52d01556513a71a499024a3054c62778e,0x664d27e4c3853b32b78e1e4333b527073b30960f577b30a05d0077f054986268d,0x250577d7b07e4c3864c82b77a4c3ab7849a073b3313a81a530010570c7b00d4c3404c8,0x664bd6d4b68d78e1c4a54c3aa2205d15791313a91a499024bd054b62978e,0xe0576670f6d4c58d3b30a6435c4a43b531073b33662837532080570270f054c5293b3,107673,242841,0x4d4cc6d4c28d79d2b7914c3ac3b52615791313ac1a526004cc054c22979d,0x664c26d4c2824680a4364c3ad3b526153ad0943637526024c2054c211468,0x397645c7641a499,0x397645c7641a499]
private def payload68 : Array Nat := #[242982,0x7d78c395423a7e2157e409612417a3,0x2b3aa4c3aa2205d1a499,254791492908,327400117161,0x43517610598376c633861368e1e3678176c0405733640120595176c703b2286282776e,0x1f05d4d71f644b68f725495a63c62881612144916f4f730590255a0054e96058d,0x4351a834eb134fa3c4c840057814fb4e48d366e05578e0068d3f7253505d45518,0x536078356f8f78e134fc5c68e4b5a6074b2316d0375a80f4c8054e73705745519,0x435f27e5548979d1360e6a79d765552e5b23667a4705703628217462967a,0x667643405d79725136122c6a9697c200774285a6,0x877837178e137bc805a68c66633773367e25544a0f62828628457d0,0x536128361285777136124c77781612047770561227612,563959846122,0x33059537a3447b38d386150594971f3c54b5d5912e628343b3357b3004980577f6077f,0x535cb545a68d68e74059677675c54b4b448083780954c373ca043b52867a5705727437,0x58445340595f63f8a640384492c4e85b4f8183c1094317057e1d05925616214b227504,0x5e3b6547847976c2e059594fd3c6405b44408377343b35551d254f72867529590,0x4d5a6834f08268e200571c7485a57e5b586175553659a37419024c2234c8570574576d,0x535fb754a67c64367559774c8420575b4f92d67a4f5577057e2557e2867b473d4,0xe057437b5834ee794c8020571d7b24c3b388703143362f68e6e6a10c643266e0624a1,0x53521834ec8f78e595005c68e3b5a60733e094371105d5551f004bd614f45b05745519,0xe05d5377f8777f7148b0c057677b26a3b378703143360968e707b21d0590378e614f64545d,0x5e73561057834f2863b3136658861d074c8120573178e5551b0b48b0905d28628570572768d,0x53520460578b62b8f4c8594ff0d0694c6437f4a61851c05057094355551e1d0592067a613375705745465,0x66764797256776d2c727886b00176d3767b1d0590237361337570574546a,0x53524834ef8d68e594fe2c777886b04e7672f71b007bb1061e57057,0x6c4e18b5918e5a0384a56a67b2205d6977f076281650b553b500642053b3475e1,0x6c4e27a510823b3394a50d05d2c77f6b67b18628193b55050b004dd415a04041e,0x585a67a5118268e496f51e63d695042b0642e6f50963d355820705d0354d2648b7b514,0x7933b2b06401541193b56e43f0076d0d6a76268f,0x6c4e0260577a62b894c80a57e0d0573c7b06b67b2b0641867a193b56e440005fb19068236436049e]
private def payload69 : Array Nat := #[0x1705d6c4e3727266348b597b41e44b697b02a064337b4345726e5ef0e4e80568e277af,0x250576c4e47a50f8a4c8385a81e6f88c4c8085551656f506070e4e81068e7b515,0x7e5a6897743867b8c7641577f1005d0c7d0216a7,0x6c4e6837a3635a62a7e41e4654b61f1437509773507de006a50d558657e4,0x6c4e57a512795a62a3751e773784702b064147e4096526e43c026a5055587b7e4,0,0x7d6327a62d63777660591e4665d61e4e6ab1650d6e51a004de214687b516,0x437237a5137968e660590a7771e4604b61f0146f097bb357e3037481246842661,0x6c3d26d63f866404844e3c57e4b5d22b0591876d2f4b247057557c6256ab0560c27548,0x744e87a5de7968e135bd804e8695862e67a097bb47057526f80e55561767275b1,0x5876775555855a0135be5c68e4b5a6074b23767a0f4c83f68e6072b,0x1f057435f67a5dd8f3b3495a65c6288c6b00677f3662847057577c6025553f71f47420,0x3255c260577a68b7c57e4941f1e78e4b5d32b059076d02c05d5661e6e4bd026ab285a6455f2,0x435f58755d8f5a02a4c21e7254b5d1064f73156947057375af033400561227548,0x4364426057546da793b3674b12c643697c2086941670f355030f628285a62967d,0x435fa5f3bb826281c5675a78e8c6ad2d59010057095403572c1f67b1905d3f5df224b6,0x744e87a5e38268e20057135c01e4c85b56a2e5b1346d33756f43067205a8234c8456f8,0x744e87a5e47c6280b05d135bf3c68d6b4af4e4912f58d376763e4912158d29676,0x1f0574364d5f56d634c8495a64a68e4b5d42d5b10956f3759a0f3bf0d6c4654c8,0x1f05d435f7644b37c68d495a63c62881634144916f4f73758d0b491286766058d,0x66562460577a5e28e4c8136333c643764ae2e67a6f337554650f51c09057237b02967b,0x58565460577a5e08f4c8135c14c643694a80659005057317b03767b0368e285a6455f3,0x435fd7a54463628135c277482787a31844a34673307a61f5a621783227a6,0x435fc7a5e571482136656a5a6817da185581b79d355020f465057bb455f4,0x43774837e10a7bb687254005d5b729017bb097bb356a90e7250577f3505d277c6,0x436577a68e8d68e677525c4683b7522d5ad16777375ad0068e3f68e45657,0x587642605d7968d136331e6a95b7c62b0590774b6f337470575546b036d01e05d2967b,0x857e47872a2b05955466007a3,0x5853d444918f41b3842b1e4918c53b2e4ac2c05d515ca5068d20628465a6276ba,0x2505758540834f58f4290205d497842c67b784b6145a63169f576280078e0d568276ad,0x583385f371650578f61220058675af6a4bd8c53c0305d08618314b23768d2578e266952755b,0x597c6165a63777404725]
private def payload70 : Array Nat := #[0x2469b5f36b650578f4391d7916a3728c53e08617195433779d036283f5ce11546,0x1f05d647bc8577f2a3b35a7740005d367bc52725006a9216ba22767,0x585415f36b650577c7e21d7915a7e48c53e367223779d036283f5cf2761d,0x3d6e06f0598b73d8a582387a32c367886ab0657e4f75a3576e256401b059616a7225b0,0x59059534373405d7261e63725674223a78e5d76708694120571b68b554b20b6ab285a627601,0x7454d26057546da8e5a6494b12c643816b90869412057167b1553b90f628285a6477da,0xe06043459834a77f0597c3d502057385c4684c8765a6000570873d6f68d7333f04336054f327606,0x323d2875694505a895af484af4a68d3005d8c5c3086953155b1a4910e3420d6ba4257e,0x59059535564433a71465386335c6434b4ae14561280573162b554c62551c36057054f127645,0x4d59a835648a555385c65c68e765a6074a9316bc353bf0f4c8054ed3705727604,0x4d5a87e6d0854a6675a61e68e8c5c504057186054f58e554c8005b13f5827b747,0x5905943774726208f386137bc687254005d817dd185ff6f767356a9007bc0d77f3505d,0x534364461e895bc1c6ba4c7778c6327337a037e30d6ba1169d,0x534344462163434385c71e4688c5c7186023162d553c4253c40d62d27602,500246480784,0x5f7b1807e41860635774,0x5e77f8377f79498394596854b50059765ff04057186b0363b33062800386467b3456ab,0x43482837528268e675d5774e85b58004057077b03467b355900f3bb123bb4276d,0x7458254568716f5495d63c48b3005d6b54d1558234568556f50f68e2379127339,0x5e69426057545ae8e5a6494a02c6433b5db0869412057345ae525a60f6280d48227712,0x43482757916368e0b05d675d75a48b3b5da03057147b43467b7036c3e78e3f5514055f,0x43486645638578e1c77f2c3b3420573b7b414628517bb1a3360448b3f68d3b05d2777f,0x7d55f545a28278e1c77f4c48b2205d8177f1868e346281a336003b32177f1a057427b4,0xe057643b3865bb2a65e3a7274b7710877f557a60476c227bc,0x6c7e4546288d7bc675d91e5a6817bc184822f7931a7730078e3f79d,0x437a3545bc636ab675d81e4686963b18614345b5507e3027770555627614,0x545a93a7e53f790,0x536124c7775b5dc45615,289558189586,0xe0578667a387a33a774847e4,0x170597d5347544f8f6400a4f75a447695051437716509553b50b3b82176c7b5e7,0x584237a5e88278e150644976d6a67b2205d7f7c64e6ab095f2553b5005351257e1a0574768b]
private def payload71 : Array Nat := #[0x1705d6c536834b38d68d1c4916a6767658d07491516765558d0054912628655ee,0x3d763543bb79628673b3410576972c1767b1005d1a4b6005332678e62689,0x25057247b47a77f853b3150642b78e2c507695010733651628507bb0a05d0077f0548b7b77f,0x250577d5377e55e864c82b3796a67c8849b073365167a6e7bc010570c7b0123b37b77f,0x6c549757dd896284970f3a78e7f6f84e77f317ce526280705702539463b3655ea,0x584ab7a5ed636432a6942c503220576b677064655167d553b500535103b31a0577b5ec,0x543bb7c7e83867b1767b047bd,0x6c53a8768e7c68e0a76e2c50c7f657175ad097775050c257674146822752,0x247658268e137776a67d6b67d257650568e,0x7d7717a5ed636a9677716a67b2205d2b0641574b1650e553b53e7642168d3b05d,344950552043,0x5f7e5150642c50b3361e237e4,86116,0x6c60f6d67a2b4c86a5a6400576960a014a10968d2705d6e77f03735263b357057277b2,0x325a6726116368e1c6434c4aa696102a058147b04f67b50590070570060d0d4c840590,0x1705d6c6118b4b68d68d3978e6a6767658d074915672c1a5900f5a61262847612,0x6c608875828978e1d48b807643005d696091867b3155a307a80060e2868e115a6,0x7d6b06d5a679628673b3410572c60b6972c1767b5677f1a4b6035912678e6271f,0xe0577474d83548634327d0592a65e5c6404b506084bd1a76d254e80d6ae22451,0x747255467782694496373a5a65b4d004057077da363b355465043b309057057da226a1,0x4d5a6546268268e20057496391e4c85b56e03058077b03467b3559003643234ad456f8,0xe0574d67d83548856a12a65e7506a5c6434b4c31456128057346776e6943e3b3360570d62c45658,0xe057436a9445848569402057496384c3b38872c0657e345b76e6a10c643617c6624bf,0x4d5a6546788d4d60b05d496353c68d5d4c603058337aa34590704f71f78e2157045659,0x5377f5467b8f3690c057496366a3b3887320657e345b5376280378e265924565a,0xe05743652835488667a1d4b77506a3a6438c6c41851e100572f7b070590024c80d62b62588,0x5859046057546248f4c84963a4c6437f4c806590345b1376d30368e285a64565c,0x66765797a35c7e4345a9027e223547,0x53612546780a7814c7773b7630d78142763,0x53612546278a7e33a4687f63b336ab345bc356ab0c7770d6b04565b,0x4351a717745c7e40568f,0x54627687e41a61e]
private def payload72 : Array Nat := #[0x6c68f8b4e882628593b3210571e6305b73f0841e193417363c007b04677f11628,0x1705d647728f4b61c78e8042a5b63204057364b6737320333a2846645791,0x250576c5e16472c853b32b78e6871f3b573083bb51628736530a05d0f6e2414b61167b,0xe057246da726447c3b90a643774b15b631083bb366287364e080572864447503,0x6c5e48b4e8633421d68d2105d3b4c21455d6f491736460b5693f5af11676,0x3d3bb7264f7c4d64878e4a5755b62f0305d2d5df4f67b524c6070573e7aa3f5904772c,0xe0578372c7c51c13643804bf5b6332d5e2364c6305710333a28465115b7,0x8267b083bb09774,0x1705d64772636d0136a91e6335b6331305d196d0577720333a3c0592846b780596546b,465438094900,0x7c3c11c7e42d5e62561f78059,0x633435b632736560361e78059,491609,0x243bb7a6a363643200577750370057186430966435643070576150357057,0x7d68a8b5c8893b30a77f6a628400572e5a0515c95577a0254828628570577b653,0x4368f7a549636281d7c27777f697b24e3b32805716663526800b5834170f4073e,0x6c77f46057547b4633b3396223c78e6b56b0148b0977f6e77f2062810336627bb,0x25057247b27a7bb853b30c057396233a4c83b566167bc507d40a05d0077f614a16268d,0x436897a6a58d78e384b66a67b8f05d0762856763356430272c2859035058,0x243bb6d7638d6280b057685907872c1778e19593526810705d2667b294b6,0x24581260577a6a6894c80a56f685b1885f01468e093785268420625265a8604c8,0x250576d7648a4c85c7723b67b0178e16576707ce02548,0x436902605d7a6a48548b48572807b4885ef0168e09378376850e572467b47b5ef,0x4368c7a6a871482137bc6a5a640057697b701628097ca3554a007bc285a657057277b7,0x43690793780777409378,0x8a7e47655408628567657b7c6,0x6c7e47a775637775c7bb886501868e0966852683237e4,585710773890,0x547633b6780877716667,0x7d68e71774396295c7e4337e4166662667a62774,0x4334f757917c5562005d0a6196a3696b69c030570861a317327036c3e78e216b54058f,0x246cf643b38f4385975c8078e81579337251005d31697557a6004c836057216b647587]
private def payload73 : Array Nat := #[0x4334f7a5578f55620057776945b57d030583172c3557e03643124bf276bb,0x25057246cd7a68d8f41d020580a7b52c6d33b57e145a63169e5068e02643614b8276bc,0x25057537aa545908f429497842c67b784c6145a63169f844d60078e0d58a276bc,0xe057445a67c54d1d7b15a4836b694145a62f7da706280c643216b97b4b5,0x246cc835428f435020570a61b2c67a3b57e074a64f7b981069375a80f4c81258e37057276b7,0x4334f835578f612200580a6ae6a4bd695850305d314bd356162578e216b22757a,0x2457c545af8f42b0a55b4c4916b695086ba0957e703712068d1e05d604c2,0x6c58c834338f555020570a6b0776a13b57e04057177c6344c37036f023b3216b41a057276b8,0x643b37c7e82b7c23a7274b7710877f557a60476c227bc,44755457722,0x8f72a0a61c5a77470374657da,358549247506,0x7d7bc447e4823b5494652c640400597f63e08694197e45068d253bc0d482456aa,0x590595376d754b48959149628805a68c7da2b0590873f346e2703860f6282177f657b0,487359600526,0x4d4185466c7c3d42b5b23c57e220575b6862b0591876d4f4d2573cd256ab055572733b,0x745b05466b716f50a6c73c48b3005d3b6871442a3466d556f50f7bb237912733b,0x59059247da7a54b714650a6c87506b5c6433b4b91852028057346dc5054d0f3b9417b14570d,0x59059435237a54b714650a6ca77482787a333549346733560f0c7253f79d227a6,0x590597a54b71469137a13a7278170806764527640f4c4,0x4352254672717771c6cb2106c6a68e5b687187da317e4557770f7bb276ac,0x435fb6d7c6717ce0a6c94a68d3005d3b688185fb4f7c6557ce0f7782733b,0xe05a8367b636d3020572c67a8c548157a334771735a6024e83f77f,0xe0572469f7248e893b3136433a4f77667506454540590963c506400076c0d3c04768f,0x5872c64590865ab2a4b66877f3005d0669e3159a705a003628287637b5a6,0x7d67a44336650578d7bc020572b7c62c5a67667a0877f28057517da8457e3e3b3417b01177f,0x583384461e650572005d3a6167667b0f0573172c6e57e1f78e23424276b0,0x7d67b876d06e05d8d7c2020574865f6a46f8c5484e6616f676735a0254c826426276ae,0x58540545908f72c0205d2c67b784b61564319763576280078e0d58b276ad,0x583386467a65057200583a57e7667b03057195ad1a4c80f643417b9424bf,0x5853f5467b8655a0205d386096a36a7667915643317443568e0478e0566922582,0x5e4c8645a86505786625386074a5558c5774e65f2f4c83768e1f4c809057267ab65586]
private def payload74 : Array Nat := #[0x7d4c35f77f650578a7c61371f3a555885834e65d05057516c0353b304628465a6276b0,0x537b4727b4637271c77f3a76c087e81b7e80b76c217bb,0x583387e74b650572005d3a6167667b0305d097643768d036a9417b9427c6,0x38612516c5737770566a,0x497655a774377e4276af,0x865b7557e403774057d4,0x665ad877e48a694396f25a5a65d7a32b059077da1b54b55465253b5237b11a05947764,0x5905943652836407c3cf387a33c5a66b7ba0872c2f7aa70590254c66267b,0x74453546d1714535945668640300595b6412b0590869f1b54b5545e254c4603c0,0x5905943653836407c3d11d4553a6408a0594b6532b059336f9304b6254b663059456f9,0x3255c546dd89580497524a5a0817da2b0592c05d317da6e4bd0f4d0285a6657a1,0x59059435f88364071466677523c5a0785b5185fe346703755a0f3c03f68e45772,0x59059435f9836407c3d3496934c5a081595084bd34672375ac0f4bd0d6ae11428,0x5e421546db7c3ce0a5a53a5a03b69f186021b54b55461253c01e05d604c4,0x4364426057546da8e5a6494be2c6433b6ed0869412057346da355030f628285a6456f6,0x435fa83640635571c5985a78e3b6e71864510057346db3572c256f9114c4,0x247b05f7b0635820c057136fe3a4c83b5ad0657e346713767a254d63f68e45771,0x667b45f7b08a5820205d136fa2c48b8179c0657e097af357bb256f50d62a225b0,0x4e05c436a9445966343302057136fd4c3b33b6e80657e34672554620f77f617c67b4ba,572478580366,0x744e8546df7c3d60b05d136fb3c68d6b4bc18603346d3376760f4d221570456f8,0x7d56c546d58278e387bc4c48b2205d8c7d4187bb703860f4a12177f427b4,0x5905958765546e28f386496284c4c862057817ae2b059336f8164b47377a0f6280d77f35057,0x6c560546d48d7b1136ff3a6288168e2b059177d0097b2554650f4a20573f1a057,0x435f7644bb8578f496283c6283b6ea3466f3758d0f4d42776b,0x59059536a66d5947c3d0496283a68e3b6eb186004f75b55446047b205691456f3,0x58565460578277f387a44c64381705066d3050573767b0368e285a6,0x587642605d634374974d1e6a9817632b0591b54b5546a0f4d827772,0x437bb3f05d757e46377f137013b6ee3376c0505d167e4527b40f7bb056a9277bb,165286,0x5905953777546de71460136fc0d06d4a68e3b6f1087483467455468253c1057e3277bb,0x437bb8e765137023c68e3b6e9077da097da37777037da]
private def payload75 : Array Nat := #[0x537716d7ce717ce137004a68d3005d3b6ef337714f7c6557ce0f77840725,0x587642605d8e764387a11e6a98c7082b0591b54b5546b0f6f927772,345815,0x546d64a7e5346d60f3c2,0x435fa4c7773b6f0456f7,0x6372a3b6ec0d62e,364633,176217,0x3d76c753c1385042f0593c7715d4d2086df1b45f844e8046d3216764263f,0,0x327a6723678f68e1c44d2f0595a6473b64015703197b2553b3044a17a0602168d626e0,0x2442c5f4b28f68b1c4582f0595a6483b64007432195cb355a00b45c264bd7b54c,0x3d76c5f4cc857811c4576a6958854c0305d075521b4cf3733b0b457286957b54c,0x7472f7570f8577a676283a77f7f7ce1573f120571a3b325628104e8657dd,0x587bc723678f68e1c45d2f0595a6553b640087bb28057553b3044a13f77f657b4,0x5367b5f4c6450572b5906872c22057157082f4d652643255b73f65222640,0x58771754d28559e676762105a5a7ce786d32e4ce2c05d5068d255b3104e8626df,0x534ca7577f637ce1c4624a4e85d7dd15704050570974f503b30b45a3f64a7b596,0x4d7305f3b9600571c4652f0595a64e3b640174c0167511a6430b6441257137057626dc,0xe05d537827a7bb894b3675ab68574786d20868e097d537628255ab26574626d2,0xe05d5f49c487ab3a7757f66e0868e1a68e0e7ab217754566e,0x3d7bb5f3bf857826759a5a64d8c597087d5096283768e2559a3f64d65597,0x3d76f5f628633bb385035a644786da08706094be576431f5033f644626da,0x244c4756f91c4635a64f3b640087086f5a57078e1f72c2672c626db,0x3d54e5f6ab7c6921c44c2f0595a7c48c7b308709366b3505a60b4682371f296b1,0x245505f7bb1c7775a63d18553097531a68e0b7773f63d,0x587714e7bf5076c255bb104e8,0x58771757ce8f68f1c76d4e7bf2c05d357250b774104e8,0x3d7725f4d81c6f93a7723005d087630974d306a90b46a1905922640,0x1705d587ce8b7bc8d77f136a76873e786e1157dd0974c7037804386190593f654626e3,0x3d7bd597c609628577743e7c6,0x587777a68e8f68e1d468687478c7b515705517e35068e1f50c2176e22777]
private def payload76 : Array Nat := #[0x3d776754d08f68e1c4665a657786d8157da1675270468255ad3f64b626e4,0x58775753c3857e4675b75a777786d91570c1674e7068e0b76e3f64c626e5,0x3d778723677c74b1d78f5a6558c7b4087bb097541a68d0c78f3f655657b4,0x58771757ce8a7ce1c6f84e7bf2c05d5068d0274b104e8,0x3d7725f6f91c6f93a7723005d1570809751306a90b46b1905922640,0x3d76c5f7781c7ce3a7715d7ce0305d0870a097503768d0b7ce21771427ce,0x6474b633bb6767b5a77208706356a92567b3f772,0x587ce8b7bc8d77f136a95a651786e1157dd517bc7068d04386190592674b626e6,0x5f6f43a7e5576283f649,0x5876b3876b506280b7e5,121437943379,0x3d7700870b527773f64f,0x5a64e157071a774,0x8f68f557e43f650,0x1f05d644c28e7252b4c82c3704005788781144916f6956e5af205af286766057c,0x245b3260578557e3942b4c5555d65e1448f314c8470570b7b92859e404d2,0x7d7208759c8978e2a4bd776168605d064bd2f72c27058205b4286784534f,0x7d7218b5a48d78e384c66a67b8f05d014d62f743356430272c2859035058,0x7d71f6459d8578e0a72c2c3b350058146282f741356431f4b62867b7c05d,0x1f0577d7248371e8f3b32b4c83a6a1400575d6600636f364c3470571a65e206771273e1158c,0x6a67b087e8356432867b,0xe05d7d7297a7bb8d7250a7ce5c3788877f143362f749470571a774026a7285b0277b4,0x7d728837e12a73b687254005d5d662017bb097bb356a90e725467b43505d627b7,0x7d723877df7968e2a7481e4685d6610646f097bb4705702777285b7656ce,0x77616336164534f,0x7d7297a7bb8968d0205d0a7ce5c68d8877f143362f74b470571a74b026a9285b6277b4,294160729985,0x8372a3c7e4187a3285b5,0x7d7bc3405d877da824bd385a1685a076699175874f758375801f7a30d48245711,0x7d7bc26057757b78e5a6496282c643697ca2e7bc12057167b7525a60f6280d48227712,0x3d6285f7b1863b32a734683b340057697b1014b54f75c35643254c5285a6570572770f,0x3d5a66d75a6368e0b05d387795a48b8c79c147b25173d505420b7a83f551405a7]
private def payload77 : Array Nat := #[0x435cd645a063612497338078e81599084b21005d354370f4bd5f05d0d6ae4570d,0x3d5a66d7596360f0b0570a785773b38c7160869a195a3354332577f0905d127c6294d3,0x7d7796d75b854a6496281e68e81719336b74f59b505513e7b23f5824570e,0x5e69e645a0635561d4cb7506b3a6438171a0872c100572f7aa3541d254c63f5556259f,0x536b9444c78e7840a7861e6288168e4e5684f72b847b1254a23f54d370577b7ac,0x5e5785f748897b3497d54a6288168e0857809748377b3037bb104c21a05d,0x645a03a6a74f78d,0x63426686a7365a0,0x645a03a727067643542c,0x437bb6377f0a7e85d7e8187bb3577f0f76c057272776c,0x645a04a6a70873f4f75e35437,0x645a0137a13a6a98c763067641005d52764,0x435d0647a06342a0a7912c5588171c185d0367a03542a0f4a4057e027715,0x7d7236d75f634340a7881e4688171b185cc4f756507e3254dc0555627710,0x247da5f7da637770a7895c68e81717187bb527650e7da3f7da,0x6d7595a7e40905d45714,0x5e69f4c7778c71d45713,410088789207,0x666bd7e42f8978e3967b3c6d08605d0857e3472d29057080574661e62548,0x53760754308d78e384b66a67b8f05d0762856763356432859035058,0x6c7806d4c185643595843a6943b677073b33472d290576e77e080572067d236a162548,0x537817a378796282a58d804913b6760868d1005d567601a4cd0358d4649122676,0x537825f4c97c643675906a67b500580868e5676635643255902867b35058,0x43643896284a58310583,362757318496,0x53783547618e4820c0573967e3c6a178548014826f7616e78302548216a1570572267e,0x7a3787c7e80876c,0x6c784877da8d4680c0572a74a4a4903b67a1868e5676a6e77b2067a285ad570577b7d2,0x6c77f3405d877ce8268d3967c2c6a93b67c2e68d2c05d167ce6e77f080570374b10336570576574b,0x6c780877c0716a93967b3c6d08605d1468d6f7644b05d080572374b62548,0x7178e40057187e25577a57057,362760353400]
private def payload78 : Array Nat := #[0x897e43967a2c7cc40057067e408057617cc2267a,0x247e97a7d00c0575c7bb3b67f1868e507e10e7e9237e4,0x6d76585774187e42067d,0x4d78a5f7255505d2b6163c7624b7ce0876d2f7c6307c60477411339,0x4d78b546a98d78b5a7eb347eb2678e,0x4d78a6d68d5505d2b7716878f4b7ce157714f78f307ce0474b11339,156618737483,0x447e43a7e5157746e7d43f790,0xe0577d7ce7a77f8a4c31378e5c555786c4183b3120574f7975569b0f6b012725627bc,0xe0573275b8771e8a4a267425777b27f6bf175ae3172b704270068e2862845798,0x746be3405d7e7b3824b6394b60d05d777b37f6be067914f5a05569d0c69d415a065791,0x5e7253405d64781824d16742e3a5af78695175af1b42e556950705d2578146725424d1,0x66554646ad824d4675544a4d45d6ad1558d16698556980079a1062811628,0x5e7253405d8a4d75806a6742d4c4d27f6c4147b0317c65058907057007990d4c8405b2,0xe057537ab54586824c81d5552c5b16b72e175a8120573175d844c80068e2168e627a7,0x250577e628824c51d643777ad784d0183b3567b16e7bc0c7b1123b3627bc,0x667388b5928a70f384c3777b06977f1762812057567da5757e0273f053b337057627a0,0x4d73e835918270f1c628777ae8c4c8174c3567b05077f0073f0d3b3370576279f,0x7d77f6477f7c498393b3777b37f6c31478e4f5a055696080573e7b3413b3627a6,0x2467b3405d824c66741d0d0573c7aa7672c175b74f5a05569e0079b23643404d6,0x5e73c7705d824a31d5573a78e7f6c20873c317573757d1f7a305643627a5,0xe057587ac8771e8a4a21c784777b27f6c1175ae3172b3057b0068e28628627a2,0x3405d8249c2b7dd4c7e9697d0317e9507d00068e0568e,0x324d33405d547c28a77f6760f4c7dd8c4c82d73e6f5a35569a1f739213b31a0576279e,0x665ac5605d647dd8a4bd674370d05d4c77d764bd176784f5a0556a0025aa0578e627a1,0x3e0573d7b46477f8a4a1393b3777b26968e1578e1b7471a57f0277c0d48b477bc,0x7d7c6824da137e4777af6b71f14545556a210628627d4,0x327966106b385bc6a7995d763175ba0079a12777117d5,0x8a4db67436687977f6c6317555569d007954677745798,0x667b9757c68a7ce496c4777b01574b120575757e0079c2168d3b05d,0x824d8674370d05d787644f5a00079b0d6a9627a1,328444614541]
private def payload79 : Array Nat := #[0x7d7d0757e92b7e45a7e92e7bb12057507cd4168e477e1,0x8772a674387f7cc567da127e4,444011468445,0x7e7ce867c6396f85c762767ce147c5097254b05d3e774425a6,0x6c7bb6d6287c48b395633a73a7673a185631973a5573a007bb4648b11628,0x6c7d56d6288d68e3959a3a737785ab1859a19737575ab007bb054cd3505d65782,0xe0577d7df545b3824c82b7b02c676817ce1859e167c0704d20068d054d73505d,0x535b7547426378e395902c72c787aa1867b4f4c67105d007be0d4d647643,0x6c7bb727af8d4c8395724c7b0787b4185b619731577a8007bf4648b3505d,0x7d7ae7e628864c82b77a3a7407870f173b31973f270570c7b00d4c37b77f,0,0x7d6787e7458278e396793a4bd8177d18678197455578e0c6790d4bd6577d,0x435b5447447178e1d55a1e732700575d7a9185b5197445578e007c10d49d35065,0x6d628857742b76b1576b007bd,0x24781447878279d395b93a7336b6ae185b919733526ae03726054cc3505d,0x6c68e63774337e4317d0127bb,0x6376c395bb3c4c8400570f771,0x7c79d395b83a54d40057787b6,0x6c7de727e07c482395a61e7bc400575b7e9185a6097bc27057357e9007ca285586577a,0x7d7da79468395b53a74a787b1185ad1973f27057577b8007d1417a37b77b,0x6c68e727e36368e3967a1e7bb400576b7772e46819747577b5007d21268e6577c,0x6c7bb3405d8268d395b62c7ce787b4185b6167ce577b4007d34648b3505d2974b,0x4d7bd716a93967b1867b1274b47643,0x7d7dd877bc8968d0a6a93a740787ad173b31974b27057027ce417bc7b77f,0x396795578e054d8,0x437bf6368d2a74b3c4c84005718625007c0057ce65780,251043919756,0x7178e40057157935578e007bc3505d,0xa7cc3a73f40057577b1,470254245761,251055408760,83684063150]
private def payload80 : Array Nat := #[0x637e52a74b3a74b40057357eb277eb,0x24769877ce8e771677ce777ce7876d187252c05d507cc2872562774,0x87774895490a7ce17725097cd2705d027c241771627ce,0x7a5498e773776f4145a6557e125727467e4,0x7a5497c74b1d7ce787710868d1005d1a7cd0c7ce62771,0x247277777288772076a91b7c9377c9617727b772,0x7a6a53a7e5076286e7e1616f4,96673806067046134,0x435587a71c717912c7221854f357a305722,0x7a7182c72a5562e0572a,251864,0x437a3837e6797a3395572c79d3179d3555705556,362884085721,0x537865d7d7627e7,0x3d7d35f33b4505d397b93a7ce3b7ce087c31005d1a68d207b9217ce227ce,0x717eb497646a7643005d147c72f7c7306a9226a7,0x4505d3b7921a7e522792,0x5f712087d635774,87374286937937514,0x7d7ce877ce8976d0a769777ce88771087252c05d507cb4176c7b774,0x7a54e8e7747776b145a6357e825729417d0,34786,0x7a76c897781d7ce5c7ce787710868d1005d1a7cb0c7ce417ce62771,156538795689,0x7a7bb897cd497e45c7d00868e357e80f7e4417d0,96673806067963759,0x667eb487eb147e54177862778,0x877c2777ce2e378577680a05d28725627cd,0x7a3787c74b1d7ce0868d1005d1a7cd0c7ce,0x7d7ce877ce8e7c0677ce777ce767b92e68d2c05d507cc0a05d28725627d3,0x1705d6d76482764066a90e6a7,0x6d7623a7e5076286e7e13f78c]
private def payload81 : Array Nat := #[0x7a79d087c31005d35726,0x6c7c4877e98278f137a42c7297f7d04e7c52c05d5068d0074b465a6,0x717eb487cc4a7bf3005d4f7cf557dd117e4,289197610882,221043074891,0x3d7c85f7ca636a9387bc3a7bb8c7e90874b554821f7bc217bb657e9,0x5f7e52c722187e03762805722,0x857e47f7ec556b0007a3057e1,0,0x247d18779b8d7dd814681579b197d16e7dd0279c2179c1a05d117ea,0x546a91d7c13b7c1087c11a7c1106a9,0x4d7d36d68d5505d2b7c04a7ce4b7ce157c02f7ce307ce047d31905d1168d,0x6d6287c74b2b78f1578f007e5,294085789353,0x5f7e53a7eb087d31005d1a7d3217eb,0,0x7a68e7c74b1d7d03a7e9087bb1005d1a7cd0c7d0217e9,0x447e41005d1a7bf217dd,0x727771d7be227be,0x5f7e53a7eb087d31005d1a7d3217eb,0x64791857e22b7913b7e2157911a7e246791477e2,199601903507,0x877d4497e415790007e5,0x6d7d51379406794117d5,0,255515985887]
private def payloadTablePart0 : Array (Array Nat) := #[payload0,payload1,payload2,payload3,payload4,payload5,payload6,payload7,payload8,payload9,payload10,payload11]
private def payloadTablePart1 : Array (Array Nat) := #[payload12,payload13,payload14,payload15,payload16,payload17,payload18,payload19,payload20,payload21,payload22,payload23]
private def payloadTablePart2 : Array (Array Nat) := #[payload24,payload25,payload26,payload27,payload28,payload29,payload30,payload31,payload32,payload33,payload34,payload35]
private def payloadTablePart3 : Array (Array Nat) := #[payload36,payload37,payload38,payload39,payload40,payload41,payload42,payload43,payload44,payload45,payload46,payload47]
private def payloadTablePart4 : Array (Array Nat) := #[payload48,payload49,payload50,payload51,payload52,payload53,payload54,payload55,payload56,payload57,payload58,payload59]
private def payloadTablePart5 : Array (Array Nat) := #[payload60,payload61,payload62,payload63,payload64,payload65,payload66,payload67,payload68,payload69,payload70,payload71]
private def payloadTablePart6 : Array (Array Nat) := #[payload72,payload73,payload74,payload75,payload76,payload77,payload78,payload79,payload80,payload81]
private def payloadTable (i : Nat) : Array Nat :=
  if i<82 then (if i<36 then (if i<12 then payloadTablePart0 else (if i<24 then payloadTablePart1 else payloadTablePart2)) else (if i<60 then (if i<48 then payloadTablePart3 else payloadTablePart4) else (if i<72 then payloadTablePart5 else payloadTablePart6)))[i % 12]! else default
private def tagMaskB0 : Array Nat := #[63,4032,258048,16515072,50331648,201326592,805306368,3221225472,12884901888,51539607552,206158430208,824633720832,3298534883328,0xc0000000000,52776558133248,0xc00000000000,844424930131968,0xc000000000000,0x30000000000000,0xc0000000000000,0x300000000000000,0xc00000000000000]
private def tagMaskTable : Array (Array Nat) := #[tagMaskB0]
def tagMask (i : Nat) : Nat := (tagMaskTable[i/32]!)[i % 32]!
def pop24 (w : Nat) : Nat :=
  let v := w-((w >>> 1) &&& 0x555555)
  let y := (v &&& 0x333333)+((v >>> 2) &&& 0x333333)
  let z := (y+(y >>> 4)) &&& 0x0f0f0f
  ((z * 0x010101) >>> 16) % 32

def pickRef (i t : Nat) : Option Nat :=
  let layout := refLayout i
  let other := layout % 16777216
  if (layout >>> 24).testBit t then some i
  else if other.testBit t then
    let z := ((payloadTable (i/32)))[i % 32]!
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
def slowTagCount (m : Nat) : Nat :=
  (List.range 22).foldl (fun n k => if m &&& tagMask k != 0 then n+1 else n) 0
def present (m : Nat) : Nat := PCX150.FastPresent.fast m
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem foldPresent (m : Nat) : present m = slowTagCount m := by
  change PCX150.FastPresent.fast m = slowTagCount m
  rw [PCX150.FastPresent.exactFast]
  rfl
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
    let j := h % 4096
    let o := h/4096
    if j < 2618 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i)) (one j) (two j) &&
       fits (permute o (s &&& two i)) (one j) (two j)
    then wt j else 0
def nodeOK (i : Nat) : Bool :=
  let s := mask i
  !homogeneous s && s &&& one i != s && s &&& two i != s &&
    (List.range 12).all (fun v => decide (wt i ≤ sideScore i (Fin.ofNat 12 v) false + sideScore i (Fin.ofNat 12 v) true))
private def rowRef (i t layout z : Nat) : Option Nat :=
  let other := layout % 16777216
  if (layout >>> 24).testBit t then some i
  else if other.testBit t then
    some ((z >>> (20 * pop24 (other % (2^t)))) % 1048576)
  else none
private def rowScore (i m x y : Nat) (q : Fin 12) (b : Bool) (ref : Option Nat) : Nat :=
  let s := m &&& dirMask q b
  match ref with
  | none => max 1 (baseScore s x y (sw i q b))
  | some h =>
    let j := h % 4096
    let o := h/4096
    if j < 2618 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& x)) (one j) (two j) &&
       fits (permute o (s &&& y)) (one j) (two j)
    then wt j else 0
private def rowValues (i m x y cost layout payload : Nat) : Bool :=
  !homogeneous m && m &&& x != m && m &&& y != m &&
    (List.range 12).all (fun v =>
      let q := Fin.ofNat 12 v
      decide (cost ≤ rowScore i m x y q false (rowRef i (2*q.val+false.toNat) layout payload) +
        rowScore i m x y q true (rowRef i (2*q.val+true.toNat) layout payload)))

private def runRow (i : Nat) := rowValues i (mask i) (one i) (two i) (wt i) (refLayout i) (((payloadTable (i/32)))[i % 32]!)
private theorem rowDefinition (i : Nat) : runRow i = nodeOK i := rfl
def panel (beginAt count : Nat) : Bool :=
  (List.range count).all (fun j => runRow (beginAt+j))
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
end PCX150.Scalar
namespace PCX150.Scalar
open PCX150.Chart48
open PCX150.SmallChart PCX150.Bands
open PCX150.Sparse (TestTree Triple Valid box leaves)
namespace Local
theorem labSame (r : Sample) : geo.tag r = Scoring.label r := rfl
theorem labelSame : geo.tag = Scoring.label := funext labSame
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tagSame : ∀ k : Fin 22, tagMask k.val = Scoring.tags[k.val]! := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem numSame (m : Nat) : present m = Scoring.present m := by
  rw [foldPresent]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rangeGen (g : G) (m : Nat) : quickGen g.val m < 2^60 := by
  rw [genAsRoll]
  have bs : ∀ (i : G), ∀ p ∈ parts i, p.destination < 2^60 := by decide +kernel
  have eachPart (xs : List Part) (h : ∀ p ∈ xs,p.destination<2^60) : roll xs m < 2^60 := by
    induction xs with
    | nil => exact (by decide : 0 < 2^60)
    | cons p ps ih =>
      apply Nat.or_lt_two_pow
      · exact lt_of_le_of_lt (show applyPart p m ≤ p.destination from Nat.and_le_left) (h p (by simp))
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
abbrev NodeID := Fin 2618
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rankOK : ∀ i : NodeID, nodesClass i.val < 48 := by decide +kernel
theorem maskEq (i : NodeID) : Chart48.node (classOf i.val) = bits (mask i.val) := by
  change bits (rm[(nodesClass i.val)%48]!) = bits (rm[nodesClass i.val]!)
  rw [Nat.mod_eq_of_lt (rankOK i)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskRange (i : NodeID) : mask i.val < 2^60 := by
  have h : ∀ k : Key, rm[k.val]! < 2^60 := by decide +kernel
  exact h ⟨_,rankOK i⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
    let j := w % 4096
    let o := w/4096
    let okay : Bool := j < 2618 && o < 144 && permute o s == mask j &&
       fits (permute o (s &&& one i.val)) (one j) (two j) &&
       fits (permute o (s &&& two i.val)) (one j) (two j)
    by_cases hg : okay = true
    · have pack := hg
      unfold okay at pack
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at pack
      obtain ⟨⟨⟨⟨jt,ot⟩,same⟩,f⟩,g⟩ := pack
      right
      refine ⟨⟨j,jt⟩,embedded ⟨o,ot⟩ r same f g,?_⟩
      simp only [sideScore,h]
      change (if okay = true then wt j else 0) ≤ wt j
      rw [if_pos hg]
    · left
      intro t v
      simp only [sideScore,h]
      change (if okay = true then wt j else 0) ≤ Sparse.leaves t
      rw [if_neg hg]
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
def testMask (i : Nat) : Nat := cubeValue ((testMaskCodes[i/16]! >>> (16*(i % 16))) % 65536)
private def staticFlagsB0 : Array Nat := #[544777605266688,457456971942092,557533999661056,559252338966528,422229644935168,427436456411136,368202968708352,544165919735808,380435318177792,547561085600256,422212465065984,422212465065984,281492156579840,544786009833488,383321888587776,548729316704768,427436219039744,422229644935168,299084342624256,557566757175312,383594252439842,548762074228736,559557198741536,475040567003272,545362330779648,422212465065984,548729316704256,422229644935168,378236563357696,422212465065984,531169888185344,457448380958924]
private def staticFlagsB1 : Array Nat := #[366002066395426,541965013237792,281492156579840,539974571671568,457439792595136,422212465065984,544777586655248,427436386942976,281492293071872,422229644935168,557529704693760,559247960047616,299067162755072,474989023199744,383317593620480,548725021737472,368821385082112,381603549282304,281492160774340,383321888587776,544784403415040,548729316704768,281492156579840,286698968055808,423311976693760,423311976693760,427435145297920,422229649129472]
private def staticFlagsTable : Array (Array Nat) := #[staticFlagsB0,staticFlagsB1]
def staticFlags (i : Nat) : Nat := (staticFlagsTable[i/32]!)[i % 32]!
private def oveField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def oveClassData : Array Nat := #[0x4be5f4b0bacb8b4ae09da829ead8afa96ae2acb22fca7aa0a42d0a1a993754d4d4ec003f12c0349cd033,0x2632dd0732c87352da9c514004eca1cfb44cd8b22b89da6eb4281280f8b7c9e95c7b26497222c0425041,0x3f555d4550d3744d1142d09404ef36cd935c61003252501922ac5398173900e0000d2bada0e99523d02c,0x2aaaeab2b4ae0b22f0b9a94a8ce0db55d54d4d52d494751b43d073fceb1e43b0340ad182e0051e07d02b,0x26d2914cba300a564ea64a4940544f272243e4210018da40409347a131b8986e3ea91bc96e,0x523294deb829ea5d475150b532f8042c40549c65ced54516af000064ad434faab4eb50cd93bab46f502c,0x2f6c2cf93dadd3ed02bfad4c72cd37cf0af2caca318c9bbaebb6762d895e55d56d5153d4b5200159d014,0x4f33bcd2c6b20003b34dccf4cd1b39c0f4701aa6cf93d4c94d4fcbd27116a9744ce857910e84c7335034,0x4824a241e0cc181293aad6c111f89875289486c8c18050e03e42158c03c00755b6cf66a4496c,0xa263aab53210420454a1c270a80080b315c2a5323904764a210e01612369104e3d0690c96d,0x4a511c430bc2896a1a7b106242130b45927c2644c7a85c952247915c32821ea7c0011ba352445cbfd084,0x9800559544f13ace539d5754ce91cbb0568dc0e80a314ef36ce14752d43cf92844e78136720140cd02c,0x242789f6721c676230731f27b9d6a1c9d23c8d22c892147f1946316c5514c410fc3d0dc2e5b89e00508b,0x4f206c0e0001e073f73a4994516601ca73dac0b94b33e96ca0a76a6aaca1a90184bd2ecbf2d4b6f85032,0x2f73e4ff5e56959d65585374ad2746cf5409660046b0fd7558d2f434f7144da1283616535415190ed01d,0x45510be4fa93c0643704b9e60c3ef53d30f0010e3af03b66fd1d07242cdf3c0f39fc78bbc699c05ed0af,0x4e69f4104804253b114f691141ac8649230d84c1e0e15c6c282d930ca3a1c0f8de1a008e4970,0x41303bcb10bda9c90f0e19f0ebd2f3bccf63e4fac3ee62a00501e00400750810dbd5029dc5d3df09d0b2,0x4454955a3c50763e0bc782d168c3fe3e2a03c846c23000406f1d0f0b63564aed6e9b4ca3c975,0x10abc6c446cfdc5b02401082026a40d1a9a71e44f06c3a469d90fbfcca92700bfaf2462149f70b509c,0x46a300692c84001a08ad0551f95036470a920a456100a0c5536db4d9ec73b9ccdc970a1ac96c,0x72fa5af7eed342691d6af298856693a3b6dea57467143720dee7b3eb8a000c72534e70c54904,0x4bf4dd4d50535494f536cd550b76d8cd0e6baa0653d384d34eccf320013e802f227d244cd450fab05033,0x278641e0fcc0aec3fc65988e215e593e0f9000e6392e41d06d1c0df3a46f3966496ae71a8b21d45550c2,0x40efcbe0f63cef122e1483a63000dd3a70cbd2f1bd7071761fc3f0d36a72190f43cc4b3ef0c408fad0b5,0x29542b2543ce33782d082e2004e4b411914ab3354d133ca2b3cca782ccb5a88a3a96ab56355d514ed028,0x3032fb2ccdb0f40afcc84fb3d5895f5755c5334a50cd2354004c0b10560bd734ad374903b4183f4ed015,0x4a86d25ad501a67c4ac7e853790a7e9c90aa8ba6d4445d4a22fe09c343e118dc4e3916004978,0x1c89451341c6aceea9546a957cf6732b7eb5593378e96d85065d00512f994b4536bf99b6493b,0x44c31090da42b53ca38be330f034803e40890563b270d0962b250e82a4d288a000860291496e,0x7c2f817df7531277fb7d38dec4ef3f81dee1ca0c1faf1f1783bd622e401f12c2ebcddcf3c8dd,0x43d124d132cc931c6f1a46117456208601281e510500300130c5113ab72fc4d1a838a0c672f46d33d071,0xc81a9790d321a010ec885a210310c411f9503a3c30114804924048ec0e1700495452893c96c,0x3e26b19e003bf053ceee2b622c1ce939e9f90102be4673bcea9befeb145c3d8e4b5efa322d736ad5d0c9,0xe34f4a523533364eb354cf31c885f0720011b36ccd30ce0baa80919c228cdd3a5451e95732541465036,0x741520220a40d1f8f4964e3d0b8006a1e8a48e4d24914a2436bb3d92c762afd46673135c96e,0x62b2621bfe3903737a0b329a503003479fbcdbe91912c61ca1956d6673180a4a19db603b492b,0x4851ec791c8400f8380006737b46c012cbf4dd2248acdc804d8451b4871c228cc4bf1d4e13a4e532d063,0x4ccad45ae52a0351074ea70d20005c51231a890131c1f45a3d1b8ec62cd65b1d86b95aab4973,0x1729e32ac546884caad533b63afe48d2d8b35a2b95bccda6c8006260b1f75cba2b379cbf493c,0x546b2409ad870d62b42e6f560300b6b40014e12696a26ddf117cb1dedac4c9d8cc7b43a64949,0x24699c1cfa23277c2b07c1906c26883268122c78a0d08cb52b49f104392a0da7d40d29c310ec4e00507f,0x2ca4f62ac4f29c00abd091b2e8fd363a2a1ec8e7ccf9289e82120888690131350c1b0989c976,0x4952d53f4e5354cd17334d3302fb3284b1c5254c4c93652b4bd1b314e4b3928001b47c80f33ce068d03a,0x16f7e41e028f6d1898cab5fc357ac748ac5a26187ab88aed23124fa764814872793f104950,0x118142b91caa512692c92db2c984aec541b5cfd375925d92861e94818012116c8edb36b2c96c,0x7d860da754a5845a155aa02882c9d611b138683021888d071208f47c6b1d8a07800150bc96e,0x100052d46ced292b875979364d547cfce3b8cb24bb44ceb1aa2346521411094bcd132cc6b6ab6abd041,0x46920c7944d0d42d0941cc52f4b12bca12649649858005052acfe70ca528cf33ac9ef12723b8b05dd050,0x3010370ad5cf1959afe1b278ebd002d38921650af74c1de0a2432413a6d4faa536a237a94941,0x13cef1a6668005db7ee29c056b745b37a52380df344e1358e2377043a0e7403038e902ba2e63eef950d1,0x52d314bf33527364bcba800f42971ecc94a96346508fbcc72ba6d4052932d1e7d4673ccb53bce33dd042,0x4dd32cc72427c8cc8ca74b6a64528924495c548f45b1443b1744d15ce935cd532c8937946004b92bd065,0x12351f11046051da359abb5b9ac96b52497c9ec92daa5025018b2a5c5e00af4de7c19a4c973,0x3e2f14162c2a046c00f63ccffc12f3b7c72bc04c1da6d38f03090773986b1c8003b074bc2ee1e0ecd0b3,0x3baecbb0f1a86001b455c1f09c22f5c1aed3f866c16ef41503a3c20411008ea6fc04712deedc1cf6d0c3,0x2dedd63b0ce08c001b9a699452d4d07546a112853431952e933fa431e8f44a5507138fc2c94a,0x3fefabe8eb9ba5a0e4f33a8e88f4003e50740d023f231bc0669727341aed3b902bda5e186f99cefd50ca,0x31d3e2f33ccf53f42b3ecff63587615835fd6b4ad0b2106a0012d5d4b75f5193611543d814951f4b5013,0x65a4fb6496c51389c6a7f3000d571f458554f055f91c7269472938a1902774729b3288cbc8fd,0x6478129188bb9bcbce6d92880caf1f899814bfd4a7f798034faee46cf21cfd4e6f32923dc909,0x4c132cd324cd5575313eceb38cbc338921c832370acc3d4f55551495493fd5951d133900078ce136502b,0x5a69734a403ac556a90b401609e4da66a4add8c3f2f064ad6f2890ae636261d48247251ec96e,0x4af334c52acd13529cabbdb31ccf325195755553d453f4e8cc530c2af73dd4800160ffc2f56d1537d02b,0x22cc56ea9edf2f8571eb360c0d7de84ba7d5d4d037dc984b3b89d76d40179caa034307d6c922,0x620006ba3216c7902cb46cf81bedf27f97331bac255ca1be9b592b9a87b6222d6ab760ae4932,0x3b508c0f040acef05b05bc2e8419018000ec1afe94eebc0907baaafbc0fabf50336e9fbeeec1790550c7,0x7a7cbe48cf6b99b4746b000aff06d48ddee56bd37b0dfa23131cee98739a6d060f43a2f4c8f0,0x4c730480fd2aab22fca62bb2ecc52e4b7274b12f4b3335375300150ceb3b5352dbbb3fcb32c4c92d5033,0x52cba03c0562a200c1db1ec3d105309a5e05612e35f60962912eb4d6cb33d290928c36a0c94c,0x3bb0181a710010042719422ffbf4708d60a15f17c4e6a45d11c450540cb303e4fc12b22291abf71b509f,0x4c60001748538ed53d3dd172cc154bd232f4ab38ccf304bb2bd47515435053b4e51336c6d020742fd036,0x53a835253f4c6a7cbf2f27323ccb344d6afcb52bab6a34b29fcb1304bb22cb7334e33754b51d3e005034,0x56156d3400324ba36d1855743d4d4847405d5947d0c9ea8652cff5298f3e548eec28bbcfca454f555029,0x5271a95947d232849b2949f274b34dd20003b203ce348cd7493a32f52947ccb44ca13b4a32a49b27503e,0x4a3294c54fafa004f2d6a794a52b384eb49d1f28ca92953738b44fe53f3e01137d23324cb3e91731503a,0x5020052148d1f2f49b28ca135ba348d20ce4c34dd253013b3592b36cf12f52728d1f2ecd929ca527d03e,0x3c0ef3aaedbb0ebbb8fa3c31188c002170c3dc30c34f9c2f0dbcd0cbc6ec3aafe3b2ee2c2eb40111d0b6,0x4b73c3bf5404b4e4f151497504b9314b74d41f540014ecdcec02335d3f51d494acbd53d392fd414f5031,0x54330d4552cfb51d07344d73e55a0054331d4f314f7544d130ce136d5b4d00e42d4351d45374c32fd02c,0x1381ce850d197273803a8b]
private def oveClass (i : Nat) : Nat := oveField (oveClassData[i/32]!) 11 (i % 32)
private def oveFirstData : Array Nat := #[0x1d95d89d8a48e08648e48e29239249249246003189de7689180,0x1c10810052c30034200294a5ad47828ec498c953d56,0x2a0000c6318c65294a8c2b0e52cde339ce52dcdd54a,0x218e28e48e39249156c02cb28a4114514546da69a8269979980,0x1c0181a5801919d1d8aa2ce8d199ad1a519,0x1b065ef8000c6af2bcaf1c66579cb319571990bf149,0x2381b6e375d8e19207dd8a48e391b69a00b2914514504245d80,0x1085c2dcb014673a0de5dac61996dd6ec8737584149,0x1d76082082475f7a28a289d7629248a28a38e48e46c02cb4180,0x31d8019e0199b29a1c88dcde21b1611d118,0x2b5294f7beb1b19205d950018c655616b2a0a53d4e,0x2da0014a530c675ad5b739c7b62c63190b6efce7148,0x208a19238a28e292368020a24b2904114114504514d271c7980,0x2f342103810074121528e07ad4a6a970318e62a556,0x2355700c28b2d14514945a499d70a2905146da9a69966177580,0x2975a391861d8c84923a45dd51e52285879b76485d8a29180,0x403d8e2288462d473b9cc7410e72a0a73e0c82953,0x12951993a1aa05294c6c0d0bf39b65b868331c94147,0x1e7d861e86189a85b6df76385d8638a289d8e27402894114180,0x36cb580a7c9ccded88e1dee8736c8576c860dce4147,0x1d7e16dd86385d85d72375f7238618a27c024a1d24d46977180,0x405c0ca8d94a650c05aa0a9c950b4556ab20bb394d,0x1d3c020b45145135b5d579c8c74533d95e34e37617d44e38980,0x16a800842420a638a479cec839ac5392e7260b7c153,0x1296298a85376e5f0052a0ebf108bf32c771868c547,0x1f5db55566571f91982575f7196df81d9218e48e188028a4180,0x227e086076289d74034b29145465f9597a58c93d66655655980,0x15530172b40ca32a6a782aa63d9285656ab9d17554c,0x228628a275f71c75d0062504d435679979f89248f65e48f4d80,0x1b1a20046d9ed3322912f252edd6732d516,0x12b24d2b0c68558c6335f51a94a556d6056ca62d4c,0x1d7402491d049049279b6dc8a28a21904163935228923d53180,0x264c41aa8a29a608e9aa568e266695d1118,0xcf7d8c35aa161a94fb01556aa4a9598d832528494c,0x3006312d6398c85b1be39d0756b8e718f3638c43546,0x2085986185a69a6a08218617dd75d71c7402472892904126980,0xecaa9b6542c625ac05a9545c1b6641ad54ed47594b,0x1af732b5b6780cdb9c535b6a738c6bedc6314853d45,0x118583d67d685555e86185a82185a85f6db75d0052081854180,0x216e175a7e171d0124cf81d3d25113534e16d44963dc2cf6180,0x149ac9032a1ec556aaad4104d58362592ac2957394c,0x1e85b7a285d6db6dd89d8218a17401c64d13dc85f14f4917d80,0x2661852ba01905316b8414a9364a85acc941758c94c,0x1f6c02c82d14d34db59e79419048e3d34926e28a28a24d78580,0x375041549739c61a4c8325655390d6a94d6f98c6d45,0x218216db75d75d0115142d83d86d184f56076185a85d0133d80,0x31b00d180cf24d672331eed557166eef115,0x2d60850a85ac6310d0840ca53ec0232a4539508594b,0x1f75c00a20829041241345165b6c54cf7d14d555669a6e08580,0x211519445996402eca758b6529b6b5ad57cdf1b414a,0x2051f7207d86208197d981d75e69f69d01140e3e01145145580,0xa6314f8f396e5a0ae19969d78c5d57cd42b384d44,0xf55752081481781982081a81d69f69b7402094502db8135d80,0x1e6dd8217dc5402064101104132d64505e039c8203975605180,0x8ed70100c12306eadc6e9e32d2a171915,0x1ce63735aec08444cc664cd3c39c84f969db2c54545,0x1e5d451e82082061881e81d6a081a81a69f75f6db75d3c02580,0x1275ae16b18cfb58c5291566dad6031456caccb354a,0x1f69f69a71f71d00710711049045b7e011039565b50e4904d80,0xd83131ddcf1516a929532df2f2b316e514,0x14d7d2a4228af794604d1ef856a7491291b529ad54b,0x1d7597dc01049349465a69b82080438f4cd48a2914208124580,0xb53ea65bed633dd08a8d67da1573a54b5a107d149,0x3bdcfb18f7ffadf68019c918e69ffb5dffe66f9d140,0x2081b7c05596492593547d83597d959f4d33cf7d94df59f3d80,0x9052607041242110d441e7819cc43df06b96a62950,0x14932793e01ee5bedc54f8c7ae56a4589bea95e2d44,0x9567166cebefb67f4cf3bccffefbffdc63ddd0140,0x2f7ef7dce77d9d6b1ecef906838d85992e56dcc6941,0x14c810898012b7412b7c0074c1e752530532088214f,0xd085acb48d4773e15b0d7632d6c5423634a8051549,0x21ce51bc74311e32d6b631cd68053150a8c611cfd40,0x1de9cf3eb5fdcc633ebdf7ec7798efb708c00d37140,0x486b18cf9526ca5e7d65af71c8e59d9c7ade7b940,0x1fbdb1f5beefa800bbdedefbbf7763ef3adf75ce540,0x3399035a8eb2875decad2da237500475783ab1d6141,0x1da53df6c6a96d28cf880afdd374bddf265ef6dd940,0x217adab3bde00d668a869d6732cfb4f16d575990140,0x254c0227b2e8e85acd502c68c2d661d958b1566b941,0xb14b22f846a3055d563ea98566f037384b5f5be540,0x2c2b4ad710c540]
private def oveFirst (i : Nat) : Nat := oveField (oveFirstData[i/32]!) 6 (i % 32)
private def oveSecondData : Array Nat := #[0x9bd7f59bd8c99bd84889887a9b68728987f98068988458988998247ff7ff8987f67f7a07000000a198199f39bd7ef898c000,0x2961489a3a0443b534fc898238f80589a3e0f54d6b5e0780a570dca001e072895634c86558d53401a7f3,0x80c0000000000000000000000000000000000000009f3a228c18fd86c9f3898a078188eb80d8168199f589881981c980c000,0x8b08017fe8c78988028038127fd7ffa0785a0000000000000000000000000000000009f38289db8278c180d7f1a197f2c000,0x7560b82dd782d8468c4482e0b669c1755de7052a2f8ee0108d270bf0018c7058461184271c1584cda7fc,0xa319dda378ef9408ef000000000a019e980d9f57fa804886a07a019fd9e98688689809e39e29e9a07a018eba079407fbc000,0x80a9d39439f88089bd9bd87a9d38989949809bd80789887380989885aa22a22000000000000000000000000000868a19c000,0x9dd87e80d996000000a01a19a079dba19805940a199fd91ca019e38788989f3940a31a0788681080ba07a07c000,0x9bd9bd9409a09949b68989bd8408148468ef8888139bd9bd8bd8988988ca84599f89984381283e8989f3000000000000c000,0x284e2997abd4e3134ce8dd2dd4c28001098b9c76bb4fb9c6c29989b745ca1756c1ce71409848,0xa01a07a20a07a079f59e99f58619d3898000a19a01a0781091e9f590d9e39c390aa078979b689880e91e940a19a1985dc000,0x9f5872000000000000000000a01a01a079f380b9409e980d86f80fa07a2da07a3798ea37a379dd9f396b969811839839c000,0x9d387787589887a822873820872824821a220000000000000000000000000000000000000000000000000009f59f59d3c000,0x605404803000020421f5261b01c045a81a179cf5b4190258a628620358e2080569de069d720580fa816,0x836a2da0700000000000000000000000000000082d81e81582a82700000000000000082982b86b86c819a31a07a199f3c000,0xa07a2d833832a19a1983883e000000000a01831a1998090a9f39c38358e691e8a58ea9bd8988899bd83783f834c000,0xc2e0d98a5812cfe672f9fce8556bff93c8725a409685a562e1697f2d5fd5001581f0017f983e,0xa229e98ed9f5000000000000000000a070008fd80b83b83c83a90a9f583d000a2d9c39408eea079c1c000,0x9bc8409c29c29f58b08478bda228f29f89439809bd8ee9d39bd9288988ef99f8bd9bd8988489bd000000000000000000c000,0x8d19c38da8c2000000a19a07a079e38458d5000a01898a01a19a19a198428449c3a2d8498930008db980000841898a19c000,0x8da980852a269bd8d48558b09c48fb9bd8bb8539bd98098889885885085485685f00000000000000000000085a9dd9f5c000,0xa01000a1985c98da2d90484fa19a2d987859000000a199c19b6a078989418bc99485a9f390b84e84d9869f591e898936c000,0x9bda010000000000000000000000009f58fda2d85b85e86e000000000a01a07a0784aa1284b8608518ba00090a84c857c000,0x1c64c6f2bdbf2d523519c81f0a1db96801c0e04786c64b7c7ab64e93318d2591b1a8b6659862,0x9dd9f58639408619f3980000000000a07a199e9892a01a019f3865926000a3786490a000a19866c000,0x874a1987ca31a35a078698829e58399fc9a07f09f38789f68839f89808799bd86f87687a898873875877000000000000c000,0x8989809948b09949bd8ee8ef9bd9bd0000000000000000000009ad87d8179dd9f586c867000000a19a0786a88486b885c000,0xa2d889000000a1988c9ba88b000a199c388e8409c1a150008f2a319c2a159c29f588d8f29f58988f1a22a229bda228f2c000,0x99f8c68bd8988bd9bd95d9888bb9bd9bd000000000000000000000a199f39fc88a898887000000a019fc9bc000a01000c000,0x3002335402e4e58761b0e1d86ec68086b609e6371a0101baf1a930dca2c6eb1a23616ae9895,0x9f3892a3798d9f3893a01a01000a1989400000092ba07a1591fa0192ca2d8cfa2d8cb8988910008ad898a19a19a19c000,0x9bd9bd0000000000000000000000000008869f59f599496b92288f8c4000000000000a010000008908c9000a01a07000c000,0x311c3ab47eced4b0a3f1185477661c07c4aa3b1a0eaa6be98154c4531c4e858be802907b9840,0x98d9949f889c000a01a19a2d8a38dfa018eba2da158ae00091e8e69fc8eb9ed8ec8a48e4a199868fea198a59bc8a79f5c000,0x9f5000000000a010000000000000008a69699e98728e3000000a070009e895a89f89e8df000a1900098089d00090d98bc000,0x9d29039868b68988b09bea22a22a229949048af8988b29809bd9bd9bd9888bb9bd000000000000000000000000000a22c000,0xa19901a37a198b491c97c8ae000a018ad8ac000a31964a2d8baa31994a198b18bca15a19a199449f58b58b99878b3c000,0x9ed9e99e99f58aa00080ba159d38b7a01000000a159bf8ab8a90000000009ec8b8000000a01000a019e3c000,0x9baa19a01a28980a318be9e29e38c38988bf99fa229249d38bda229289809f89439bd9bd000000000000000000000c000,0x9e59098c69bd9de9808ca988983000000000a019268c200000000000000000000093aa15a310009c1a018c0000a01a19c000,0xa2da378cb95fa37a01000a37a15a198d08988c88cf8c58c70008ce9e39d3a19a01a1990ca198cc8c98cd906928a22a22c000,0x9e88fb9369f58988d49bd9439f8a269bd8d79c48f88fa8d58f69bd000000000000000a019699259800000000000008c4c000,0x840000a01000a19a199b60009c28d8a2d9f7a19a319b69b88db8dc9f3a079e98dd9f58d6898a199ed9948de8f78da9f5c000,0x8e88ea00000000000000000000000085aa079e88d99c3000000000a01a01a370009ff9e88d286d8d399f872000a199d3c000,0x8e08e7000000a01a07a198e48e38e60000009c1a1aa2d000a198e9a019bf8e18ec9809779869878e58e28989bd9bd915c000,0x8fb9b68989439f89bd9bd9bd9bd000000000000000a19a01a19a150009baa019449409bd8f0898a228f19bd000000a01c000,0x201c00ee66c49860a92491bcc78149e00052580838094f3765b2d96b95930001969800198f5,0x9d387500000098ba319e993a938000000a01966a15a159f5000a379008fd8f4000a01a198f3a019c1a07a2d95a994898c000,0x9809839880000000000000000000000000000000000009e89b69e9000000a019cf000000a19a19a0795e9ed9e894890fc000,0x97b90890a000a37a01a2d000a3790d000a3190198ba19903a0190798e90ca319069048989059809869bd987909994a22c000,0x89891d91791690e9149f7a1d9159129869139879b59bd9bd9f59be9809be9bd000000000a01a0190200000000090ba19c000,0xa01a37a2d91887891989891b000a0190f00000091aa2da079b6000a01a07a019109bc9c3a07a3198ea31c000,0xa019e3a3192b9d392292a924a319949999209e5927a229219bda229809de9f899a0000000000000000009f89329c3a19c000,0x9a19369839a49a0980988a190000000000000000000000000000009fc000000a0791fa01929923898a01a199fd9269e2c000,0x6665703334e262336fcfe06976f8ad3732b46e4e53b9070b7a2cc200255950d92e2a858e9898,0x80b92f9d794f000000000a190000009669500000000009e293392e9fda19931959a199f59f3000a01a28c000,0x942a319459449f59b693c93d9b5a1d9f79d29bc93f9bda22940898a229b6a229be9809bd8409f89439bd9bda01000000c000,0x9e3000a31a2d9e99b79d1000000a0793b938000a01a01a01a37939a199d393e941000a2d000a01a319b8993946994a31c000,0x9769de955a2296198895d9889830000000000000000000000000009f5872937000000a01a079dd9f5000a01000000a37c000,0xccb959abec0aedd4c89f655636fc0dbd8ec0c0b05d8ed0037188b76d2e5713aa1329b7259898,0xa2da1995e94d94ca01a1ba379669d795400096700000094b97b95a9cf97994a98e98ba019e3963968a19964a37957952c000,0x9839bd9849809880000000000000000009f59db92f96994894795b000a01a01a190000000000000000009d396f000000c000,0xa37a36a19971a0198ba1997796ea1ba19a35a0797d98ca0197498a89898997ea2da3197c982976973986987985978c000,0x9989bd9999f59f79fa991992997a229f899aa310000000000000000009f098e972970000a019a496c97f000a0198d000c000,0x9a49a09f8980000a319fc995000000a1e000000990a190009f48989fc99c98fa009ffa01a01977a2799b994a31996a01c000,0x9b299d9d79dd85aa2d0009d19a9a379b19b0a199ada199e59a6a319d3a289e69ae9df9a39a599f9bd9a1a26a0f9f6a22c000,0x96d9fc96c000000000a019e296a9daa34a3199e0009fda01a079aca209e30000009af9aaa19a079a2a01c000,0x9bba19a19000000a079e59b50000009b40009c39bf9b89fc9c09b69bc840a019b39bda1d9f79f59bd9be000c000,0x9dfa1d9f59f39d29d59d99e89d49de9f89f8a1e980a229f69bd000a01000870a01000a190009c79c49c89c59bda079c6c000,0xe3eb319bffbf8315c1ece6f27a5f065f5b8de0fc7b200d6ee739a1fae633bb5c77c723ed9840,0x9fc9d69d094e000a32000a31000a359eb9829f59cb0009e39cfa019e29fda379e09f19749c9000a159f5000000a34c000,0xa1187b871a120009e4a01000a19a25a04000a19a2ea10a07a079bda0fa220000000000000000000000000000009dd970c000,0xa349d6a009ffa079e69f9a2c9e59f4a359fb9fc9eaa31a2d9ec9e89f79e79f69fa9bd9f59f80000000000000000009f6c000,0x9049ee9eb9f09f3000000000000a32879a01a319fea0f8989750000009f6a2da019f19f29eda359e6a01a01c000,0xa019809b9000a01a24a31a26a2aa2200000000087fa0387c000a01a19a01a02a2d000a1ba2da08a06a319bda1fa05a1ec000,0xa0fa2200000085a9ada0ea0c9ef000a01a19a0d000a28a21a2da26000000a09000000a0a87ea19000a38a07a0b97aa27c000,0x880000a01a1ba2da179bda18a31a14000000000000000000a119a7a129a8a13a31a2da01a25000a2da19a2e9bda10c000,0xa30a22a21a2ea24a23a2da190000009ab9f60000000009aca01a19a34000a2da01a2da2ba1da319bda1fa1ca1ea1a000c000,0xa2ba31a1e000000000a19000a29a01a33a2aa31000000000a35000000a16881a35000000000a28a25000000a31a01a01c000,0xa33000000000a01a3aa32a07000000884a01a2e000a2fa35000a30a2da36000000000883983000a34a01a2da2c9bdc000,0xa39a38000000c000]
private def oveSecond (i : Nat) : Nat := oveField (oveSecondData[i/32]!) 12 (i % 32)
private def oveWeightData : Array Nat := #[0x52c3d8016845c09015f1600583c00000100635f360000100000001d5f244528800,0x750307036300868c05053e001812000c5587213721431c310800324305055000800,0x6000000000000000000000000006a2a00002781430805211800030d71132c00800,0xf8023896c0007200005420000000000000000000350be800c1a000ac700,0x5e0155836531114705607c01734a1e51097200397c6047680262272679280f36800,0x1b4a51574f1e00000004282c5f0000090b1546528d670c834a3a1073064c8247800,0x1a1b100010cf0dfa2728405f98cd1a0949eb600000000000000037f8700,0x4050609000031280423100d2709000514120228208f1b052b2c4d1920800,0x438d8a13000d5c4d008a508e00131e186b1e060d6b1e8a000a287800000000800,0x180d1e7b6e030988361e7b8a850d6b535b17188d160a7f626e6b5c0917880043800,0x120488135c390b587f036300090019005c3854536e2c1e8e4906001e630f0370800,0x12a40000000000043d09b289bd001000eba062ade7300f13c300160a700,0x80901180900162c09000002000000000000000000000000000000000083510e800,0x180030ab000386102800a02f81004c07da259651c8b04098614005700,0x8f70180000000000000000000000264c0000000000260d3937c20027700,0x8101a0096e000000001ce3056234f068fd1474e4045095000680700,0x66000574801197935080660434849091e8f5b36767964010928730d5e090002800,0x7a9d7b8000000000004002480000023241a00df4a278805700,0x51128c458c8d8d8a5c056f8a150a8387015a2c81305a05010016000000000000800,0x8d431f5c00000d2103218d000006188c23000c00000a7c8d8400000d00000003800,0x7276004f047200148b72242a001a67551c000200020000000000000000042128800,0xc001a005583360037294e000000011a4f04725f142b10045c02024e81684772800,0x1a0c000000000000002f2a20001300000284064009000002a00bc100700,0x37004f787c700000685c61210100868916895c8b0e0a0f406a5c0f0f20688d800,0x88441868000a0f00000021236b00154305186a002f0005000c00800,0x6d35006f0019800005224d8728570005000023050405050d2800000000000000800,0xf15558d8401532705160000000000000072006f123000000000090400000000800,0x3c8d0000088d0a0000018b004d010e00534745688c8c00058b00815c890a8613800,0x208d865c6843014001160d000000000000000d1843002c8d0000450d01001500800,0x2064000f45618d2d866186008d138889680001046a6a010a050c8d6a0186800,0x2f405b000013000d0000006a21868602893c8d7c2d0f00000100230c07800,0x91e0000000000000000005c3037450768008d00000000280000002d00430400800,0x2e3f2d0800857d63006c6e7863856c2e002e00000000786c2e2e2843205a2e800,0x5a138c0000000912007d027d8d2d2e001e7d0902097d00003a2d8e1b00090009800,0x20000000c0000000000004b1f4302000019006d8e000000005c00000000782d800,0x816f0c0000000d1f5c5a556f005c000c430a0d50001600000000000000000047800,0x186f810c00168a00002800000012007c0004182100008a2f235a4300000c00800,0x225d48830000030c81000600003c0d00000000004500000000000f53800,0x3d080c3f152f0008085730002c57576f00550c278c00083d00000000000000800,0x275f000a1c0d008a2000000021550000000000000000000050001c0057002301800,0x7c3c003781450033202300370037370000001c813906515f2f373737833c1f2c800,0x810000512c000a0c6f1805000e1f00000018000000000000502c050000000037800,0x49008c000307510018004a8123181818001f0f0a1000340000186484001f1f8c800,0x27d00000000000000000408451f180000000c0683006f280031001f22005c58800,0x6c6c000028191b000202000009448d0008000209007d080808087d6c2800097f800,0x510020830a054318000000000035021963001e28413f1e0028414709000006800,0x81435118000718811881408c00200051005105861f2081438100008b00800,0x6f0c00008a18262020000081000e7c540012000000000623008c43164a00842c800,0x8e23230000000000000000000000004618220000450500000d570800648c178b800,0x6200000b7cf180f0f80267cc493e1e0313e8af80797d8b11e4601449700,0x181300000013097b1300121312004309161312880000000004643e0000003e23800,0xf871d0003006313000200000000120000007a0416000013030c121b800,0x274a002700000c698b8d002100550c050c0c216f8d000000000000603a8804800,0x50001f03500c000000000000000000008100000a0c8c0c0c30065c6f0c27800,0x271858001f00085c0381410027181f5081003872501f1f00001f000a508118800,0x3008100000000470000001f00000081001f272f001f515469000643800,0x6e0000811c0000811c51458100080000300c812c1c2705148c001c3d000000800,0x6f00505e40813200000a00000023512165005c6f0000004a000c3e1c8d008b2f800,0x5081001f008a005050000000000000000000460500000006084576000000003f800,0x188a000041008a00812700232f08000018008a8a00500000500000818100500a800,0x7c0d000000120d0d00810000000000008a00818a008a8a0681000021003c0000800,0x813131300000000000029760572000000000f001b000000000000818a0000800,0x1508290028136900007181101000135800006400133d3f1313001300001313800,0xd4300130a090d00008a0a003e0000000000003d131313000c41000000231300800,0x1f1f2703000c090d00007d00000d0d00095c1300001609280a05810d00230d0c800,0x1f818c0427008c005c000047000d2700188c13271f8c0000000a00182e278a800,0x1927110000000081428c070700002712031f23810000000018080006800,0x7b1204000003097b000000000000007a13007b1b8713007b0916437b00800,0x367d360000002500007d6c44028e6c000003003e1500000000006b00243400800,0x1918006c2644417d08000000360043002884190f5e7d00000400006a006e006c800,0x6c2800240081002d000063896c0000000031006c00006c095f00264700002d800,0xf53042700001500280f8300780753122c010f0f000000000000000000007825800,0x88e0000191202120002000000550900003d0000000043000000000000000007800,0x7300020000000000001b340f08001b288400007a123100000204002800800,0xc009001800000260000000a00640030028017c000801005b1200000700,0x43513834a000c5c13007d0009180000000000001000003708006000800,0xa000c017c00900fc18000000000003080d8030fa0c00041b820400700,0xc44c00800034dc000300900000215001d00be31d090084480dc01900700,0x7c00000000000006510081000000270000100e470000001300000041060c800,0x510000000c5d8519000012313a000904000e6c0c0000003e000000035d0024800,65347257856]
private def oveWeight (i : Nat) : Nat := oveField (oveWeightData[i/32]!) 8 (i % 32)
def ove (i : Nat) : Nat := (oveClass i <<< 0) ||| (oveFirst i <<< 11) ||| (oveSecond i <<< 17) ||| (oveWeight i <<< 29)
private def extsField (word bits pos : Nat) : Nat :=
  let base := word % (2^bits)
  let w := (word >>> bits) % 16
  base + ((word >>> (bits + 4 + pos*w)) % (2^w))
private def extsClassData : Array Nat := #[0x7bf7f8f9f67c00072d36a54a4150b9a728c45d5f5fddebe8e6e4ec79f877f77c41e1,0x4e2310bbbe1f0b8ed6eb34fb30032d8aa19d4de6d349c42e977cce66f2d95c9e4b298ec54926,0x2623205dd75bda68e564dfdf6fe966e069ef61e17276737172f573f5f477004641eb,0x1d188c244200f0e84a389cae079c05f6f98d4622d199105c00181a08864b855b19169b4a49b7,0x46a114a9b5ff3972bd6772f96ca62f5baed5eb351b462cee95abd46d000922324c74b194c925,0x657376f4f3f67477f90009c02f2445c65f605e6b68eff27677757478f906853941e7,0x421fef17ebb1e6f08b44e2f1288470761b148912881002c53898843c1c6e06e3f1f2ec83c9bd,0x3ca21198fc764118910d10ec4441e9c8f7794723116910d04a004e0750c7841bb9caea7049b7,0x34b23c3b34332ab539b02cbbae394140be3fc1bdc03ec23cc2970025a8a9b2b84254,0x4863f22200f44a190034c883f5ba191c8345a1cf0b855a35309f773a1caf175381f70e7bc9b7,0x148033b530c3b4b9b2b8c5c0c9423e3d3b3aca49c448c344cccacecc4bcdcfcd4238,0x3da331f8ec6241218b4884a1700318209f4d1e8ec7f5a25116ad46a3906be3a2a5d8e56849b7,0x38001d16bb219f8789a6140bb6bc1b4d3cbbcb4744b9343fc5cebd42cbce40cc422f,0x3a6230a84c54662000039629f6ba8d0edb57295f8e66c3960aff7abba231510059b87962c9c4,0x3b584cb64b79e0f37f3edf8f77cc01ed01001c98e5c2d968dcc362339cce560379c0d86ec9d8,0x4723d1d9045e449f82bca443000221d713813a5e5098cc7e443d091ed061c69ba54ab772c9b7,0x4000e31960f8e8692b5b41fafaf3ab8b53e40332dbebdb6c5c4c747ba45394cc23d,0x3ae1d067a38617018044625178b46c003e0d20140ab71b85ceed86b7a0ef075bf2231b1e49be,0x425252d4d1d157248f00beb6be46bc41c64dcc494bd2d1d657100c0b9d00264fc22b,0x371d6e97dbc9c3068241605093a830d4000eb4198924632dacd166b6990e870baa06dd8349d0,0x6ff36eee7400259dc0aa41bb5bbc3d2d324b1febd3eae7d7e2ded5d46a60df64c1f1,0x1f1d0442002e093d33c33245ac3cacc643c0af3bbdc4c6b9353b374a44384b48423f,0x31d88ea712fdcee66a3cdb2fa7abf6020047ac52e7b642b514d06226cb657421b8d4693fc9d8,0x2529ae313531afc2c0c5403fc5a4b2333025b529ae363cb9b6c24595000184adc24e,0x6afb6bf7faf6fbfdfe7d797edee8fec66cec6a67e8fcfc7eb4802b4354bdf4e541dc,0x219f9011a51dc2b4802219059b36383140b3b239bfb33d44c14339483e3a423ec23a,0x2993813e39c03f38373ec0cc4bc8d054d3d63c1d3a820794a48043b543535604c22d,0x4230de67e2fa76fc5b2626e2c25036a861ef60f6fc448c870049b32f353167f141e1,0x1a624d0331a4d4d1893610ed134a2d4a9e3e3ba10d06fc1e13126ab4224005cab8d49857c9c7,0x3994b0b8b465b2763fad4d6dd86c64300044a1dbaf08c8c4dce48bc65ae6d60a39cca538c9c0,683]
private def extsClass (i : Nat) : Nat := extsField (extsClassData[i/32]!) 11 (i % 32)
private def extsFirstData : Array Nat := #[0x6ecd1da3af75eff34048000921081f09408627822050082100790ce1a0340a590a2164c08734768ebdd7bfd9b040,0x8908308e13014d18b16e4813b233580b00004804504708d09809508508c08e08013118817f15218b14918914c14c14cc002,0x4103e0390ea0ea0c80c811211210910e10a10c10714514512810610610655f55f43b36c33f2f02ef2ef2ef820000092c048,0x942484e04108e1386783e1e03406710b2924208fb27894d15937d700c0140080700e0002d04f1342182a84cb042,0xc708d08d08f1312fc10f10f15915115115914d5a65a63b533633689704009408d3b533686700004b00e04f0030270b7c001,0x1064a13742f243b33f2f02ef85000000104a08004f0480960eb0ea0c814510712810655f36c43b2ef2ef85000200204ec048,0x27611911211414d10e10e5675673763472f785800a00900000705306200108805404620819f0d00d00d011014d10f10ec040,0x12e10c5655655652f52f585600907a09804904e0f010a14b45837244a7d700500700705b00004c05504d0d10f10ce0cec042,0xbc0c40c02200c30be0f70f71bc0b90da0b80b80b85115115115114e931e2a22f12a12a180204100007f0a909c2670c4c096,0x2f62f685700600800800200809700000005d08705105104a04405605904d05604e0490d20f20f20cf0cf0cf119275110c041,0x18000478af15c7104615b11833d190d519c3586710539c340828ca194328650ca67119691d23664cc999303b084,0x1054a055e55e2ef33e2ee2ee84f00100100108d00004d05405604a07f04b04504504e04e04e04e08c04e0470f60f6095c049,0x258180600f300110441101c5f00003250b400a1a2cc919f949364912463734cd1354e23c4cf33ccfa07f,0x10e2fb3472f77ae00900300300209c0520d604b0570d40500502152be0d011614d10f21214d2f78580050000e90880aec040,0x1da0e90c70c71441441275fb48043a36b2f143a2ee84f0000530cd04e04504e0390ea0ca0c72b52b40c7109111142105c049,0x4875075652f52f585605c27412e7ad00800804c0fd20619d0ce11110c5082f585600600608d0600000980d204404e0dbc042,0x38068218900240240900001223c5d0591302b943a3715a9e13c08b1163346aa31462344e68eb1d632464dbfb085,0x2ba2cc2cc27c0f22bd27621233937c50a2f799300900000705d05f0880ff0f30f22101880d011010e10e10e2f799300ac040,0xba4b85133ef2f32d480404503400609f09f09e0fc07c0c70bd2220c60f90dc2bc3202a393f00f00e00d03b00005a28dc094,0x14a10c20f12d12d12d5645642f42f49900620090630010000d30d404b0430f00cf0cd0cd1190cd11614a14a77911e5e6c043,0x4a133f33f32098b00008705a0560800a60800cd04f04304f0410960482750eb2c41170ea2742b00ea0ea2b52b526e111c048,0xbe178001890022d0009a4126690599c912236448a7e4fe370488d31a68dc6890e1aa4307161019e33ee14cdb07f,0xce0c92a72af0e92b41ff17f1181054a033e31f83d00005a08f05904a0e00a507f0cd0ce08c04504e04506f03d047036c049,0x9e07c0c80fa0c50f90c15fb50d5133203f875c09f0c927827809e0fc07c2692220dc0dc0ba2a393f04201003400028cc094,0x14274410a1255de10347e5343693694419880cd10497207d2ad2c12b226b20732e2ec7a805c00005d07d0a30401d80c7c04b,0x12047048111244c4048601c4a00000000a3340a35e88d289939a0a29ba6d32e263fa263f8c63f4fda090,0x5800a00a2970ad1840d70970ac2862771081070ea60832e40681209301e09204900800205800023708a0d42b6937021c086,0x450430f02bb0cd64c4409b20d606105f0d508c0ab08504b0ef1180cd50797a06400800000609508c05e05c05f2d514ec043,0x517f70d005b05907f0e97c20d105f0cf08607f03d04103f27472b0e90c77462f39740d20cd81100008f08f049049095c049,0xd508c11274c9c40d706505f09605e0da64b97a00600005c04d0f01e093d0050430cd4409b00d706509605e0d508c085c043,821]
private def extsFirst (i : Nat) : Nat := extsField (extsFirstData[i/32]!) 12 (i % 32)
private def extsSecondData : Array Nat := #[0x144d8021032c557c303f00213c7c895543713f4753096e32857a5512426c1900800,0x2806762a3241695837000b080e4c62468c794e0176611b0d250123091a077606803,0x37570f0a302823005b68890f481719623f093d5f4d4e771b20504618590c0524804,0x3a63231a55458d5a096c8d6e3209455604530006181e418e26261779125c81800,0x31622660688e004754600215095c5d7d290309366c267d032f444307000f273f800,0x2225104d7c883639475c0f208a55843f0578621b1d741f4b64451914003f114f800,0x7c60414f3f1e633b4d216f0b001c566a45870911014f4e8b631d2d36156b007e800,0x3f6a4d49281a190009094131794f473f3b192507687b00835c0c452e83090602800,0x841d864c604f3f50895b7d2c1e2039544d3b70346162140b000c892705780c24800,0x71c28862c7b6300862c710a158a2e4c1e453417161f28832709330602327c87800,0x8252472c348f01444e0023558804492141358605820d8a8e270e7e5819765577800,0x637449286f70140b0063391809732887798e086e814c060d8a2e811349621670800,0x265470560483001d1146463479347a0c37247b8b1c050184000e3e48732b1d69801,0x35448f040071847525503c3f208d8c8471395c090017230c32440c8412240c27800,0x575d6206616d0513690d3627187900238027210343633f1b0f503c42291d1e3a800,0x7f83281a7900722b5a002618312c12450a00826c1c282c3c182e37165357011b800,0x4f0b67127056507f1632826e1a6e0284770b3b6f41001c5b491f1e3f21693612801,0x86072147178f1809247a1002593d311e2b27014723142c167c41130a2f0020800,0x371b3d0d8f0200556d2a3322786e62851120231b1043891a278d29127b00627b800,0x7a0438016771417e6604b48a54bc7c444d2d428086f8f749d95f1844705,0x726e8d006d551a288a4e131e316f6c8b650e09488d1e37117545193455013508802,0x111d6472226e40140e563f4b011c412b1f5d0a2800490e213e3934806936821a801,0x8e2458101c28563ec2504e55d1a0409b5240a38c167e0ead76a492c7700,0x8a0681096e2235813601860200020379853408068d688372264a27583f414700800,0x253a1a1f110d8c5718397c00346324864d792d14637a1000503518171b85570f800,0x77214f6e041f626c2c305f88420c8b14000618330a1b772129375410753f413c802,0xe8945000a7d191f4f8d855724430038462805202c5b1c2846626c001a5b0108800,0x7b121f2d257a852200623e037b023f5b28642c89092d017c458565238d290965800,0xb1b00620b5b2921453f110b5c617b292a56000f713d081b0004738a5c793942800,0x7ec29332644230601f04491b9ede67e400aef9455be0b1267e0fdf9700,25]
private def extsSecond (i : Nat) : Nat := extsField (extsSecondData[i/32]!) 8 (i % 32)
def exts (i : Nat) : Nat := (extsClass i <<< 0) ||| (extsFirst i <<< 11) ||| (extsSecond i <<< 23)
private def startsOverB0 : Array Nat := #[0,9,118,206,261,405,479,512,582,650,735,804,854,917,1022,1130,1223,1271,1326,1406,1443,1463,1565,1611,1674,1721,1795,1879,1979,2036,2076,2145]
private def startsOverB1 : Array Nat := #[2176,2191,2284,2311,2368,2390,2414,2430,2453,2466,2488,2515,2525,2539,2552,2564,2569,2570]
private def startsOverTable : Array (Array Nat) := #[startsOverB0,startsOverB1]
def startsOver (i : Nat) : Nat := (startsOverTable[i/32]!)[i % 32]!
private def startsExtraB0 : Array Nat := #[0,0,26,53,66,108,135,141,163,183,211,236,248,263,317,375,421,443,465,490,502,506,545,563,583,601,629,667,722,741,755,776]
private def startsExtraB1 : Array Nat := #[785,788,833,846,875,888,902,905,920,926,935,940,947,955,957,961,961,961]
private def startsExtraTable : Array (Array Nat) := #[startsExtraB0,startsExtraB1]
def startsExtra (i : Nat) : Nat := (startsExtraTable[i/32]!)[i % 32]!
private def rowFactor : Array Nat := #[0xefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xefad74cf2e78df6c31beea689e6b6caea9258e275c6da8607de6194503ce34c5d65544d22472c62880c1140102,0xe78efadb7d74c70cf2b6cbeeaaba689649e68608e279f75c6586da5535d25942ca2481c64503ce34c105083001,0xe78d74c70efadb7cb3b6ca68964beeaab9a786075c6588e279f69b2ca2481c65535d25943cd44c40e080101143,0xd74efacb3e78c31df6a68bee9a7b6c925aea75c8e269b8606197de3cd44c40e2472c62885d65544d2043005084,0xd74e78c31efacb3db7a68b6c925bee9a7aab75c8606198e269b79f2472c62883cd44c40e5535d25940020440c5,0xebbdf6e78cf2d74c70bafaeab6c9e6a689648a37de8606da75c65859751549341138f30d1440c20402ca2481c6,0xebbcf2d74df6e78c31baf9e6a68aeab6c9258a36da75c7de86061941138f30d5975154930c11401022472c6288,0xdf6ebbe39cf2c70d74aeabafb2d9e6964a687de8a38216da65875c5125935d51440c204041138f30d28b209187,0xdf6cf2c70ebbe39d35aea9e6964bafb2da297de6da6588a382171d1440c20405125935d538c40d44f2062872c9,0xcf2ebbd35df6c31e789e6bafa29aea925b6c6da8a371d7de61986038c40d44f0c11401025975154931c918b20a,0xcf2df6c31ebbd35e399e6aea925bafa29b2d6da7de6198a371d8210c114010238c40d44f5125935d51881ca24b,0xe39db7efac70d74cf2b2daabbee964a689e682179f8e265875c6da4d549751628b2091871050830014503ce34c,0xe39c70d74db7efacb3b2d964a68aabbee9a782165875c79f8e269b28b2091874d54975160801011433cd44c40e,0xdb7e39ebbc70cf2d74aabb2dbaf9649e6a6879f8218a36586da75c4944d655710508300128b20918741138f30d,0xdb7c70cf2e39ebbd35aab9649e6b2dbafa2979f6586da8218a371d1050830014944d65572062872c938c40d44f,0xc70e39d35db7cb3efa964b2da29aab9a7bee65882171d79f69b8e22062872c90801011434d549751634f311390,0xc70db7cb3e39d35ebb964aab9a7b2da29baf65879f69b82171d8a30801011432062872c94944d655730e3503d1,0xd35cb3efac31e78df6a299a7bee925b6caea71d69b8e26198607de34f3113901c918b20a0430050845d65544d2,0xd35c31e78cb3efadb7a29925b6c9a7beeaab71d61986069b8e279f1c918b20a34f3113900020440c55535d2594,0xcb3d35ebbc31df6e789a7a29baf925aeab6c69b71d8a36197de86030e3503d10430050841c918b20a597515493,0xcb3c31df6d35ebbe399a7925aeaa29bafb2d69b6197de71d8a382104300508430e3503d11881ca24b5125935d5,0xc31d35e39cb3db7efa925a29b2d9a7aabbee61971d82169b79f8e21881ca24b0020440c534f3113904d5497516,0xc31cb3db7d35e39ebb9259a7aaba29b2dbaf61969b79f71d8218a30020440c51881ca24b30e3503d14944d6557]
private def holeFactor : Array Nat := #[0xefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0xbeeb6caeaa689e6964efae78df6d74cf2c708a382179f71d69b6195545d64933ce45030d2482ca1870c2144001,0xebbe39db7d35cb3c318e28607de75c6da658beeb6caeaa689e69645974d255441134c3ce28b1c62481050400c2,0x8e28607de75c6da658ebbe39db7d35cb3c31bafb2daaba299a79254d259751534c41138f1c628b209040105083,0xbafb2daaba299a79258a382179f71d69b619efae78df6d74cf2c705154935d638f30d4502091872ca083001144,0x8a382179f71d69b619bafb2daaba299a7925ebbe39db7d35cb3c3149351559730d38f41118720928b001083105]
private def inverseFactors : Array Nat := #[0,48,16,8,2,1,64,56,50,49,96,24,18,17,32,10,9,3,4,112,72,66,65,80,58,57,51,52,104,98,97,40,26,25,19,20,144,34,33,11,12,5,120,114,113,88,74,73,67,68,160,82,81,59,60,53,128,106,105,99,100,152,42,41,27,28,21,146,145,35,36,13,136,122,121,115,116,168,90,89,75,76,69,162,161,83,84,61,176,130,129,107,108,101,154,153,43,44,29,147,148,37,184,138,137,123,124,117,170,169,91,92,77,163,164,85,178,177,131,132,109,155,156,45,149,186,185,139,140,125,171,172,93,165,179,180,133,157,187,188,141,173,181,189]
def embedDirect (s a b j o : Nat) : Bool :=
  j<2618 && o<144 && permute o s == mask j &&
    fits (permute o (s &&& a)) (one j) (two j) && fits (permute o (s &&& b)) (one j) (two j)
def getUp (a z : Nat) : Nat :=
  let m := testMask (z % 2048)
  let t := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  let allowed := if j=0 then max 1 (baseScore full (R a) m 43) else
    if embedDirect full (R a) m (j-1) o then wt (j-1) else 0
  if t≤allowed then t else 0
def getB (a z : Nat) : Nat :=
  let m := testMask (z % 2048)
  let j := ((z>>>11)%4096)-1
  let o := z>>>23
  if embedDirect m (R a) 0 j o then wt j else 0
namespace Local
open PCX150.Sparse (TestTree Valid box leaves)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allTestSmall : ∀ k : Fin 2048, testMask k.val < 2^60 := by decide +kernel
theorem dataSmall (z : Nat) : testMask (z % 2048) < 2^60 := allTestSmall ⟨_,Nat.mod_lt _ (by decide)⟩
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem upperPaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple full (R a) (testMask (z % 2048))) t) : getUp a z ≤ leaves t := by
  let m := testMask (z % 2048)
  let k := (z>>>11)%64
  let j := (z>>>17)%4096
  let o := z>>>29
  have fullSize : full<2^60 := by decide +kernel
  have cap (w : Nat) (bound : w≤leaves t) : (if k≤w then k else 0)≤leaves t := by
    split
    · rename_i h
      exact h.trans bound
    · exact Nat.zero_le _
  unfold getUp
  dsimp only
  by_cases jz : j=0
  · rw [if_pos jz]
    have p := scorePaid full (R a) m 43 fullSize t valid (rootRaw t)
    exact cap _ p
  · rw [if_neg jz]
    by_cases ev : embedDirect full (R a) m (j-1) o=true
    · rw [if_pos ev]
      have p := boardPaid checks full (R a) m (j-1) o fullSize ev t valid
      exact cap _ p
    · rw [if_neg ev]
      exact cap 0 (Nat.zero_le _)
theorem middlePaid (checks : ∀ i : NodeID, nodeOK i.val=true) (a z : Nat) (t : TestTree)
    (valid : Sparse.admissible geo (triple (testMask (z % 2048)) (R a) 0) t) :
    getB a z ≤ leaves t := by
  let m := testMask (z % 2048)
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
def preID (a r : Nat) : Nat :=
  if a < 144 && r < 60 then
    let f := inverseFactors[a]!
    let middle := (holeFactor[f % 8]! >>> (6*r)) % 64
    (rowFactor[f/8]! >>> (6*middle)) % 64
  else 0
def col (r : Nat) : Nat := (List.range 144).foldl
  (fun z o => z ||| (staticFlags (preID o r) <<< (49*o))) 0
def everyCol : Array Nat := Array.ofFn (fun r : Fin 60 => col r.val)
def meets (m : Nat) : Nat := (List.range 60).foldl
  (fun acc r => if m.testBit r then acc ||| everyCol[r]! else acc) 0
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
def cellRow (cells : Array Nat) := Array.ofFn (fun i : Fin 16 => big ^^^ meets (full ^^^ cells[i.val]!))
def cellHit (cells : Array Nat) (n : Nat) := (cellRow cells)[n % 16]!
def packedCube (i : Nat) := (testMaskCodes[i/16]! >>> (16*(i % 16))) % 65536
def upperCube (i : Nat) : Nat :=
  let w := packedCube i
  cellHit cubePart0 w &&& cellHit cubePart1 (w>>>4) &&& cellHit cubePart2 (w>>>8) &&& cellHit cubePart3 (w>>>12)
private def sparseStops : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x300600c0180300600c0180300300000000000000000,0x300600c0180300600c0180300600c0180300600c018,0x300600c0180300600c0180300600c0180300600c018,0x300600c0180300600c0180300600c0180300600c018,0x40080100200380700e01c0380700e01c0380700e01c,0x4008010020040080100200400801002004008010020,0x4008010020040080100200400801002004008010020,0x4008010020040080100200400801002004008010020,0x4008010020040080100200400801002004008010020,0x700c01602c0580b0160280400801002004008010020,0xb0140280500a0140240480801002003c0780f01e038,0x118230460841082003c0700e01b0360680c81803005c,0x1702e05a0b41582a0520a41382604c0941282504608c,0x1e03c0780ec1d0380700d81a0330660c41883105e0bc,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f0,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f0,0x1f03d87a0f21e03c0780f01e03c0780f01e03c0780f0,0x2284488810e2184288510820c410821022003f87e0fa,0x2584a89512a250498921242444808f11c2344608b116,0x290518a21422804f89e13c2744e09b1342644c09712e,0x2c8588b11602bc570ad1582ac558aa1522a0538a614a,0x35c6a0d119c32c658c818a3085f8bc1722d85a8b4166,0x3bc778ef1de3bc760e91d2398730e31c03806e8da1ae,0x43c859072063fc7d8f71e63bc778ef1de3bc778ef1de,0x50ca093f27a4ec9c9372664bc9592724647c8d917226,0x58cb095f2ba56cac9572aa54ca894f29a52ca494728a,0x62cc297f2fa5ecbc9772ea5ccb896f2da5acb49672ca,0x1079c73826ecda9af35268cce997322]
private def sparseEntries : Array Nat := #[0x64892559d12553b12548f9253e4125338925274925198125,0x45e926307926243926167126a351258de1257d0925725125,0xd76126d14126cb2126bd5926b119269ba9266f412656c126,0xb1296b86496b24496b0bc96bae195f80295f3cc95f18095f,0xc099b767c9b756f1b747a1b730a9b725f1b71e49b70131b7,0x8971bd7589bd6019bd1cb9bd4499b81e51b808e1b80139b8,0x9d61be8979be6021be4309be3851be1fd1be0be9be0751be,0xa069c44179c43b59c405c1c4b8e9c09739c05b81c03539c0,0xc9c9c7b8f1c7afc1c7ab29c79741c78f99c784e1c76641c7,0xce61c9ba79c9a071c97281c94ab1c93b61c92901c919b1c9,0xa691ce8049ce78a1ce4f49ce2c11ce1209ce1081ce0441ce,0xc091d07d31d067c1d053d9d087e9cf5e91cf22d9cf0ef1cf,0xce59d3ba71d37eb9d35561d35d09d25871d236c1d23229d2,0xc6a9d6a371d66dd9d63e61d6d911d4ccd1d4a999d48351d4,0xa819d88c89d881d1d87a29d86331d85b89d850d1d83541d8,0xd791d9cfe9d9c6b9d9bc01d99bd9d96de9d94c39d92a89d9,0x9a51dc7d39dc53e1dc3ff9dcd169dabd81da7401da1b31da,0x8e11e164b9e15d11e136c9e1d609dcd171dcbd89dca509dc,0xda99e4d2f1e44aa9e428f9e4d919e1ccd9e1cb51e1b149e1,0x5a01e733b9e72f21e71519e7cb49e6c839e6b141e6ae31e6,0x59f9e933b1e91079e90439e9c841e7ae39e7a9a1e78359e7,0x6ad9eb3ce9eb22e1eb0ef9ebdc21eabf09ea7ba9ea5251ea,0xc6b1edc3a1ed6de1ed6ad1edc3a9ebb459eba1f9eb92a9eb,0x95b9f18669f17591f11cc1f1d479efaca9ef98c1ef8661ef,0x61a9f45259f44491f408d9f4dc29f1bf11f1b769f1acb1f1,0xa379f69ee1f63e69f639d1f6d481f498c9f48b01f47bb1f4,0xdaa1f7d2f9f7c531f7a381f77ec1f76c61f75569f73e71f7,0x7719f85879f84dc1f84619f83231f82d99f82469f81391f8,0x9ee9fa87f1fa70f9fa5e99fa39d9fa1829fa0a61fa02b9fa,0xa811fc81c9fc4611fc2461fc56e9fb4489fb30a1fb08d1fb,0x899a2e60422ed7b22d9bfa2d773a2c4de22c1e6a2b01522b,0x47c232261232ab4a318502316f923016c2308e322f64da2f,0x4c5a372aaa37217a360d9236a092343b823441a23305ea33,0x463a3c248a3c5d323b36ea3bc0ba3a67ea3a8fba38666238,0x589a413252415baa3f35623f23023e0f1a3e2dba3d13b23d,0xd62a459a72452f4244153a44a52a43401a43742a421b5a42,0xce824aba9a4aa83a4981f249b912479762477d5a46540246,0xc3ca516afa5157124f30ca4f8b224e61ca4ed93a4bccfa4b,0xb2f255914255cb7254b16a54c86253ae5a53a9c252837a52,0xd4a25a98ea5ab47a5992ca59c6da576e0a57a21a563d0a56,0x432a5e07725edc4a5dbf325dacd25c868a5cb78a5b95da5b,0x2c3262122a62c9ea61afe261a6b260806a6078c25f4f6a5f,0x9f0a6739fa67d19265bdaa6510a2640462644ad263292263,0xd00a6bbc226b88126a5eba6aa3a2693e9269c552686c8268,0x494a70279a705a226f33da6f0a826e02da6eb6026c94526c,0xa9ca7361d2730d9a73015a73dac272d31a727bd271527a71,0xc6e274c3d2748e3a748b2a742dc2741e7274d94273bc2a73,0x4c6276495276cd02759a7a758382753b8a75261a7505f275,0x8072773d1277387a7727a277b2fa769d8a76666a76635a76,0x8fc2788cb27889a27875ba7872aa786f9a789c0277850a77,0x50fa7b4dea7bc0c279976a79881a797d6279356a79230a79,0x604a7c55927c46427c1cea7c6e127b6b027b67f27b540a7b,0xbdb27dab527da6ba7d5ec27d1b627d0f227dbaa27ca8427c,0x154280123280b60a7ea5327ea09a7e5d3a7e58a27e41aa7e,0x7bda8133e281218281046a81daca80d632804ada8047ca80,0xd4aa82b48282acda8264e28213ba820a8a82dc5281d01281,0x292a85090285d7ba84b79284a222845a2a8443328410aa84,0x5282874f728719da8716ca87d32285c9f28578ca8530d285,0x98f28986928981fa893e9a893a0289249289bf3a87afea87,0x47a97016a97d19a8ac55a8a74328a71228a2f4a8a2c3a8a,0x3702981cfa98c0d297a6ca979d9a9777529713ca97078a97,0x510a9927b299dc6298d95298d64298ca0298667a98403298,0x75ca9a4c729ab61a998cc2998b3a998392995a3a99529299,0x61e29b3b9a9bc6f29aacea9aa5429aa3ba9a7efa9a7d729a,0x293a9c0f329cbab29b99029b946a9b92e29b6b129b698a9b,0x30e29d16da9dc3e29ca9da9ca0aa9c7a629c5bc29c2f5a9c,0x55a29e2ac29e915a9d68029d605a9d5ed29d3a129d388a9d,0x64f29f3eaa9fd7ca9ecb8a9ec56a9eab629e8fd29e5d4a9e,0x1e82a00a9aa0dada9fd0229fcd129faffa9f977a9f6e229f,0xdaaa102f2a17132a047daa04342a041baa02192a0200aa0,0x44caa2231aa29f22a178daa16faaa14652a12dd2a110baa1,0x95f2a36c9aa3a232a27beaa27442a272baa24aeaa24962a2,0x33f2a419eaa4d332a3bf4aa3bdc2a3bc3aa39c12a39a8aa3,0x1552a50912a5ce9aa4b492a4ae72a4820aa4636aa43d22a4,0x1242a60602a6d4baa5c87aa5c25aa5a852a5357aa51b72a5,0x851aa7541aa7b30aa6882aa68082a64dfaa6326aa61862a6,0x24a2a80c22a8d1aaa7b92aa7b7a2a7b182a78e4aa786a2a7,0x1e8aa90172a989b2a858b2a8572aa84f82a82c4aa8262aa8,0x3892ab27baabd95aaacd1aaaa9e2aa839aaa8b42a961eaa9,0x680aad5422ad8fdaac8ccaac6682ac6372ac9da2ab496aab,0x7f02af55aaafc6faaec3eaae6e2aae6b1aaec0daad7d7aad,0x370ab13272b18832b05edab02322b00f3ab0cea2afbabaaf,0x4c7ab32acab3a0b2b241c2b23ba2b2060ab25d52b158bab1,0x5112b54e02b5ab6ab4a6d2b48522b4808ab4b312b39162b3,0x6062b71d02b7b622b6a54ab69472b6403ab67a6ab5775ab5,0x2ddab913d2b9d02ab8bc42b8219ab80db2b889bab775d2b7,0x10c2bb0482bbb49aba92eaba0aa2ba02faba8e52b964fab9,0x4af2bd2942bdb7aabc95fabc434abc0792bc5a42bb33fabb,0x7bf2bf529abfd64abe9a92be47e2be2632bedae2bdd33abd,0x9c1ac13d2ac1ca0ac0b002c078e2c04f8ac0dc6abfbf52bf,0x5bcac33582c372c2c26fb2c219f2c216e2c2d7d2c1a23ac1,0x990ac586aac5c262c46992c42012c40c2ac4b932c39782c3,0xb18ac7ae7ac7a3c2c69f2ac63eb2c63a1ac6d4c2c5acf2c5,0x155ac9124ac9a85ac88212c8465ac824aac8cb92c7c882c7,0x30eacb091acbd1b2cabdcaca744aca1b7aca2f62c92c52c9,0x48acd017acdc572cc713acc6ca2cc186acc5732cb44d2cb,0x327acd30f2cd1872cd16eacd13dacd1252cd079acd0612cd,0xc702cec57aceacfaceab72cea3cace7d82ce606acd3a22cd,0x27c2cf0f42cfdc72ced962ced7daced652cecb9aceca12ce,0x92f2cf8cd2cf699acf5bd2cf5a4acf52a2cf2f6acf294acf,0x7142d06fbad047ead04662d041cad0201ad0bac2cf9912cf,0x3712d11d0ad1c0e2d0a6dad09f32d09daad078ead07762d0,0x978ad19602d16e32d16caad1668ad16502d14042d13ebad1,0x821ad27452d2511ad24afad244dad2232ad2bdd2d19c22d1,0x75dad34c82d3ceaad2b62ad2b4a2d2ae82d28b4ad283a2d2,0xd032d3cd22d3b7b2d3b192d3b00ad3a552d3852ad37f0ad3,0x358ad43402d41b82d419fad41562d40922d4daead3d1bad3,0x72cad54972d5947ad46b22d4637ad461f2d43d32d43baad4,0xc3f2d5c26ad5a9ead5a862d5a242d5a0bad57bfad57a72d5,0x4e0ad64352d624b2d621a2d61e92d60aaad6d4cad5c88ad5,0x542ad72ad2d7b31ad689c2d6883ad68092d6573ad64f92d6,0xbc4ad7b93ad79a9ad78fe2d78e5ad786b2d75d5ad755b2d7,0x2c5ad8263ad810cad80dbad80c32d80302d8d342d7bf5ad7,0x30ad90182d9916ad86812d85ee2d858c2d8389ad82de2d8,0xf4ad90dc2d90c3ad90ab2d9092ad907a2d9061ad90492d9,0x1b8ad91a02d9187ad916f2d9156ad913e2d9125ad910d2d9,0x27cad92642d924bad92332d921aad92022d91e9ad91d12d9,0x340ad93282d930fad92f72d92dead92c62d92adad92952d9,0x404ad93ec2d93d3ad93bb2d93a2ad938a2d9371ad93592d9,0x4c8ad94b02d9497ad947f2d9466ad944e2d9435ad941d2d9,0x58cad95742d955bad95432d952aad95122d94f9ad94e12d9,0x650ad96382d961fad96072d95eead95d62d95bdad95a52d9,0x714ad96fc2d96e3ad96cb2d96b2ad969a2d9681ad96692d9,0x7d8ad97c02d97a7ad978f2d9776ad975e2d9745ad972d2d9,0x89cad98842d986bad98532d983aad98222d9809ad97f12d9,0x960ad99482d992fad99172d98fead98e62d98cdad98b52d9,0xa24ad9a0c2d99f3ad99db2d99c2ad99aa2d9991ad99792d9,0xae8ad9ad02d9ab7ad9a9f2d9a86ad9a6e2d9a55ad9a3d2d9,0xbacad9b942d9b7bad9b632d9b4aad9b322d9b19ad9b012d9,0xc70ad9c582d9c3fad9c272d9c0ead9bf62d9bddad9bc52d9,0xd34ad9d1c2d9d03ad9ceb2d9cd2ad9cba2d9ca1ad9c892d9,0xdc7ad9daf2d9d96ad9d7e2d9d65ad9d4d2d9]
private def sparseStart (i : Nat) := (sparseStops[i/16]! >>> (11*(i % 16))) % 2048
private def sparseEntry (j : Nat) := (sparseEntries[j/8]! >>> (24*(j % 8))) % 16777216
private def sparseBit (i j : Nat) :=
  let entry := sparseEntry j
  if j < 1054 ∧ entry % 2048 = i then 2^(entry/2048) else 0
def exactCube (i : Nat) :=
  let a := sparseStart i
  (List.range (sparseStart (i+1)-a)).foldl (fun v b => v ||| sparseBit i (a+b)) 0
private def bandStops : Array Nat := #[0,0x410410410410410c514514518a28a30e41861861a69a69a69a69a69a69a,0x10410410410410c518618624b3cf3cf4125d75d969a6db6db6db6db6db,0x10410410410410821041041051c71c820930c30c34d34d34d34d34d34d,0x4104104104110620a28a34e49765b71e824969aaaaaaaaaaaaaaaaaa,0x4104104104104108414514514824928c39355555669b6db6db6db6db6db,0x410410410410820c30c30c30c30c30c3105186186186186186186186,0x10410410410c31061861c71cb38f3d0493514596596596596596596,0x10410410410c31461861c828a2cc34f412493514514514514514514,0x104104104108418620828a34d4924934d561b71c71c71c71c71c71c,0x104104104108310618620828d3cf451514599659659659659659659,0x410410410410410420c31041041861871c828a2cb2cb30c30c30c30c30c,0x10410410410c30c61861c820928b2cc34d3cf3cf3cf3cf3cf3cf3cf,0x10410410410c518b2cb38f51c7df8a3aaec76db6db6db6db6db6db6,0x10410410410c41c92cb41051a79f867bf1d77ebaebaebaebaebaeba,0x10410410410c514720830e41261a765a6cb2dbaebaebaebaebaebae,0x104104104108208208208218728a28d4124d6596596596596596596,0x10410410410410410831041041871c934d3d0515556596596596596596596,0x10410410410821861882092cb34f4135145d7659659659659659659,0x10410410410820820c310410520820928a28a30c30c30c30c30c30c,0x10410410410410410410410410420830c30c30c4104104104104104104104,0x10410410410c30c514724b31155869d8e49a69e79e79e79e79e79e7,0x4104108208208214518624a2cc30d3d2492492492492492492,0x4104108208210514518720c34e3904d4514514514514514514,0x410410820c310410518930d3cf411492492492492492492492,0x104104104108310518620a30d4524d45d75da71c71c71c71c71c71c,0x410410c30c51451482cd3d661b7e39659a69a69a69a69a69a6,0x4104108410418728c3d269e8a8bf2d77df7df7df7df7df7df7,0x410410410410830c310414618624d34d3d14534d34d34d34d34d34d3,0x410410820820820c514624c38e38e38e38e38e38e38e38e38e,0x410410410410420c410518720a30f3cf4124924d3555555555555555,0x10410410410410820820830c3105188208209249249249249249249249,0x410410410410820820820820c30c30c30c30c30c30c3,0x4104104210514620b39359a7e29a7b2cb2cb6db6db6db6db6d,0x410420820820831041482492cd34d34d34d34d34d34d,0x10410410410420c30c310518720a3d24d465b6db75d75d75d75d75d,0x410410820820821051451882cd34d34d34d34d34d34d,0x10410820820c30c314518924b34e38e38e38e38e38e38e,0x410410410410410410410410410410820820820c30c30c30c30c3,0x410420820830c31061ca28b34d3cf3cf3cf3cf3cf3cf,0x1041041041041041042082083106186186186186186186,0x410410410410410410410410831c7249249249249249249,0x10410820820820820c30c4104104145145145145145145,0x410410410410410410420c41041471c71c71c71c71c71c7,0x410410410820820820c30c3186208208208208208208,0x41042082082082082082082082082082082082,0x1041041041041104104104104104104104,0,0]
private def pricePrefix (read cost word : Nat → Nat) : Nat → Nat × Nat
  | 0 => (43,0)
  | n+1 =>
    let prev := pricePrefix read cost word n
    let z := read n
    (min prev.1 (cost z), prev.2 ||| word z)
private def midLimit (a k : Nat) := (bandStops[a]! >>> (6*k)) % 64
private def midPrefix (a k : Nat) :=
  pricePrefix (fun i => exts (startsExtra a+i)) (getB a) (fun z => exactCube (z % 2048)) (midLimit a k)
def extraWord (a k : Nat) : Nat :=
  let row := midPrefix a k
  if k ≤ row.1 then row.2 else 0

def tagBegin (l : Nat) := if l<4 then 6*l else 24+2*(l-4)
def tagWidth (l : Nat) := if l<4 then 6 else 2
def tagHit (m l k : Nat) := if m.testBit (tagBegin l+k) then everyCol[tagBegin l+k]! else 0
def tagUnion (m l : Nat) := (List.range (tagWidth l)).foldl (fun v k => v ||| tagHit m l k) 0
def shortTally (m : Nat) := (List.range 22).foldl (fun v l => inc v (tagUnion m l)) ({} : CountVec)
def rowQual (a : Nat) : Array Nat :=
  let r := shortTally full
  let f := shortTally (full ^^^ R a)
  let hom := big ^^^ thresh (shortTally (R a)) 2
  Array.ofFn (fun k : Fin 43 => if k.val≤1 then big else
    (thresh r k.val &&& thresh f (k.val-1)) ||| (hom &&& weightGE k.val) ||| extraWord a k.val)
private def groupSteps : Array Nat := #[562040988810,20,27,673,0,773,98971,10,35,2,13,8542,35,0,0,0,28,22,15,160,111899,0,24,12,9,15,0,0,12,10,15,802,288385,0,1123,2,275,797,50519,340,860895,275,12,30279,287130,8799,793,8783,0]
private def groupTurns : Array Nat := #[1,2,3,4,5,6,8,9,12,13,15,19,24,25,31,34,41,42,43,44,46,55,56,62,63,66,71,87,90,102,108,125,126,136,141]
def stageID (a n : Nat) := (groupSteps[a]! >>> (6*n)) % 64
def turnID (i : Nat) := groupTurns[i]!

def rawChase (o w : Nat) : Nat → Nat
  | 0 => o
  | n+1 =>
    let t := (w >>> (3*n))%8
    let p := rawChase o w n
    if t=0 then p else ((PCX150.Chart48.alongCode[p]! >>> (8*((t-1)%5))) % 256) % 144

def sendName (i o : Nat) := rawChase o words[turnID i]! 9
def rotateLanes (i w : Nat) := (List.range 144).foldl (fun acc o =>
    acc ||| (((w >>> (49*sendName i o)) % 2^49) <<< (49*o))) 0
def keepStep (a t : Nat) := 0<t && t≤35 && permute (turnID (t-1)) (R a) == R a
def spread (a w : Nat) : Nat → Nat
  | 0 => w
  | n+1 =>
    let old := spread a w n
    let t := stageID a n
    if keepStep a t then old ||| rotateLanes (t-1) old else old
def initialCover (a : Nat) : Nat :=
  let qs := rowQual a
  let seen := (List.range (startsOver (a+1)-startsOver a)).foldl (fun acc i =>
    let z := ove (startsOver a+i)
    let m := testMask (z % 2048)
    let t := getUp a z
    acc ||| (upperCube (z % 2048) &&& qs[41 - weightR a - t]!)) 0
  seen
def covered (a : Nat) : Bool := spread a (initialCover a) 7 == big
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
abbrev OptionID := Fin 49
def place (b : OptionID) (o : Chart48.ID) : Nat := 49*o.val+b.val
theorem placeRange (b : OptionID) (o : Chart48.ID) : place b o < 7056 := by
  have := b.isLt; have := o.isLt; unfold place; omega
theorem unpackEnd (a b : OptionID) (o : Chart48.ID) (good : (initialCover a.val).testBit (place b o)=true) :
    ∃ z, ((upperCube (z % 2048)).testBit (place b o) = true) ∧
      ((rowQual a.val)[41-weightR a.val-getUp a.val z]!).testBit (place b o) = true := by
  let n := startsOver (a.val+1)-startsOver a.val
  let itemAt :=  fun i : Nat => ove (startsOver a.val+i)
  let hit := fun i : Nat => upperCube (itemAt i % 2048) &&&
    (rowQual a.val)[41-weightR a.val-getUp a.val (itemAt i)]!
  have yes : ((List.range n).foldl (fun acc i => acc ||| hit i) 0).testBit (place b o) = true := good
  rcases (foldBits _ _ _ _).1 yes with bad | ⟨i,_,val⟩
  · simp at bad
  · refine ⟨itemAt i,?_⟩
    exact Bool.and_eq_true_iff.mp (by simpa [hit,Nat.testBit_and] using val)
open PCX150.PrivateGame (candidate price)
open PCX150.SmallChart (Sample acted)
open PCX150.Sparse (TestTree Valid box leaves)
def dataB (b : OptionID) (o : Chart48.ID) := acted (Chart48.orient o) (candidate b)
def upperData (z : Nat) := Chart48.bits (testMask (z % 2048))
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
    (compare : ∀ (b : OptionID) (o : Chart48.ID) z,
      (upperCube (z % 2048)).testBit (place b o) = true → dataB b o ⊆ upperData z)
    (firstTree : ∀ (a b : OptionID) (o : Chart48.ID) k, k<43 →
      ((rowQual a.val)[k]!).testBit (place b o) = true → ∀ t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) ∅) t (dataB b o) → k ≤ leaves t)
    (lastTree : ∀ (a : OptionID) z t,
      Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) (upperData z)) t Set.univ →
      getUp a.val z ≤ leaves t) : ∀ (a b : OptionID) (o : Chart48.ID),
    (initialCover a.val).testBit (place b o)=true → ∀ (t u : TestTree),
    Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) ∅) t (dataB b o) →
    Valid Chart48.geo.val (box Chart48.geo.tag (candidate a) (dataB b o)) u Set.univ →
    41 ≤ price a + leaves t + leaves u := by
  intro a b o ready t u h g
  obtain ⟨z,sub,ok⟩ := unpackEnd a b o ready
  have hh := compare b o z sub
  have hu := lastTree a z u (widenSecond _ _ _ hh g)
  have ht := firstTree a b o _ (by omega) ok t h
  change 41 ≤ weightR a.val + leaves t + leaves u
  omega
end PCX150.Scalar
namespace PCX150.Scalar
open PCX150.Chart48
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flagData : ∀ (r : Sample) (b : Bank),
    (staticFlags r.val).testBit b.val = (R b.val).testBit r.val := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flagSmall : ∀ r : Sample, staticFlags r.val < 2^49 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
theorem lookupHit (cells : Array Nat) (n : Nat) :
    cellHit cells n = big ^^^ meets (full ^^^ cells[n % 16]!) := by
  unfold cellHit
  rw [getElem!_pos _ _ (by simp [cellRow,Nat.mod_lt _ (by decide : 0<16)])]
  simp [cellRow]
theorem cubeSound (i : Nat) (b : Bank) (o : Chart48.ID)
    (h : (upperCube i).testBit (lane b o) = true) :
    ∀ r : PCX150.SmallChart.Sample, active b o r = true → (testMask i).testBit r.val = true := by
  dsimp only [upperCube] at h
  simp only [Nat.testBit_and,Bool.and_eq_true,lookupHit] at h
  intro r hr
  change (cubeValue (packedCube i)).testBit r.val=true
  simp only [cubeValue,Nat.testBit_and,Bool.and_eq_true]
  exact ⟨⟨⟨upperMask _ b o h.1.1.1 r hr,upperMask _ b o h.1.1.2 r hr⟩,upperMask _ b o h.1.2 r hr⟩,upperMask _ b o h.2 r hr⟩
theorem upperFromCube (i : Nat) (b : Bank) (o : Chart48.ID)
    (h : (upperCube i).testBit (lane b o)=true) :
    (big ^^^ meets (full ^^^ testMask i)).testBit (lane b o)=true := by
  have ok := cubeSound i b o h
  rw [Nat.testBit_xor,liveWide]
  cases e : (meets (full ^^^ testMask i)).testBit (lane b o)
  · decide
  · obtain ⟨r,cell,j⟩ := (meeting _ b o).1 e
    have width : full.testBit r.val=true := by rw [full,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]; exact r.isLt
    simpa only [Nat.testBit_xor,width,ok r j] using cell
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem sparseData : ∀ j : Fin 1054,
    testMask (sparseEntry j.val % 2048) =
      permute (sparseEntry j.val/2048/49) (R (sparseEntry j.val/2048 % 49)) := by decide +kernel
private theorem sparsePosition (i d : Nat) (h : (exactCube i).testBit d = true) :
    ∃ j : Fin 1054, sparseEntry j.val % 2048=i ∧ sparseEntry j.val/2048=d := by
  unfold exactCube at h
  dsimp only at h
  rw [foldBits] at h
  rcases h with zero | ⟨q,_,hit⟩
  · simp at zero
  · let j := sparseStart i+q
    change (sparseBit i j).testBit d=true at hit
    unfold sparseBit at hit
    dsimp only at hit
    split at hit
    · rename_i ok
      exact ⟨⟨j,ok.1⟩,ok.2,by simpa [Nat.testBit_two_pow,eq_comm] using hit⟩
    · simp at hit

theorem exactCubeCell (i : Nat) (_lim : i<2048) (b : Bank) (o : Chart48.ID) (h : (exactCube i).testBit (lane b o)=true) :
    ∀ p : PCX150.SmallChart.Sample, (testMask i).testBit p.val = active b o p := by
  obtain ⟨j,sel,pos⟩ := sparsePosition i (lane b o) h
  have e := sparseData j
  have dv : lane b o / 49=o.val := by have := b.isLt; unfold lane; omega
  have md : lane b o % 49=b.val := by have := b.isLt; unfold lane; omega
  rw [sel,pos,dv,md] at e
  intro z
  rw [e]
  exact actionBit o (R b.val) z

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tagExtent : ∀ l : Fin 22, tagBegin l.val + tagWidth l.val ≤ 60 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inLabel : ∀ (l : Fin 22) (r : Fin 60), (tagMask l.val).testBit r.val =
    decide (tagBegin l.val≤r.val ∧ r.val<tagBegin l.val+tagWidth l.val) := by decide +kernel
theorem rawMeeting (m k : Nat) : (meets m).testBit k = true ↔
    ∃ r : Fin 60, m.testBit r.val=true ∧ (everyCol[r.val]!).testBit k=true := by
  have replace (ls : List Nat) (acc : Nat) :
      ls.foldl (fun z i => if m.testBit i then z ||| everyCol[i]! else z) acc =
      ls.foldl (fun z i => z ||| (if m.testBit i then everyCol[i]! else 0)) acc := by
    induction ls generalizing acc with
    | nil => rfl
    | cons a l ih => cases h : m.testBit a <;> simp [h,ih]
  unfold meets
  rw [replace,foldBits]
  constructor
  · rintro (no | ⟨i,hit,yes⟩)
    · simp at no
    · cases h : m.testBit i
      · simp [h] at yes
      · exact ⟨⟨i,List.mem_range.mp hit⟩,h,by simpa [h] using yes⟩
  · rintro ⟨r,hm,h⟩
    exact Or.inr ⟨r.val,List.mem_range.mpr r.isLt,by simpa [hm] using h⟩
theorem tagSameUnion (m : Nat) (l : Fin 22) : tagUnion m l.val = meets (m &&& tagMask l.val) := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [tagUnion,foldBits,rawMeeting]
  constructor
  · rintro (bad | ⟨v,mem,h⟩)
    · simp at bad
    · have lt := List.mem_range.mp mem
      let r : Fin 60 := ⟨tagBegin l.val+v,by have := tagExtent l; omega⟩
      cases on : m.testBit (tagBegin l.val+v)
      · simp [tagHit,on] at h
      · have rb : (tagMask l.val).testBit r.val=true := by
          rw [inLabel,decide_eq_true_eq]; dsimp [r]; omega
        exact ⟨r,by simp [Nat.testBit_and,rb,r,on],by simpa [tagHit,on,r] using h⟩
  · rintro ⟨r,hit,yes⟩
    rw [Nat.testBit_and,Bool.and_eq_true] at hit
    have inside := hit.2
    rw [inLabel,decide_eq_true_eq] at inside
    let v := r.val-tagBegin l.val
    have vi : v<tagWidth l.val := by dsimp [v]; omega
    have vi' : tagBegin l.val+v=r.val := by dsimp [v]; omega
    exact Or.inr ⟨v,List.mem_range.mpr vi,by simpa [tagHit,vi',hit.1] using yes⟩
theorem shortTallyEq (m : Nat) : shortTally m = tally m := by
  have go (xs : List Nat) (v : CountVec) (ok : ∀i ∈ xs,i<22) :
      xs.foldl (fun s i => inc s (tagUnion m i)) v =
      xs.foldl (fun s i => inc s (meets (m &&& tagMask i))) v := by
    induction xs generalizing v with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show tagUnion m x=meets (m &&& tagMask x) from tagSameUnion m ⟨x,ok _ (by simp)⟩]
      exact ih _ (fun i h => ok i (by simp [h]))
  exact go (List.range 22) {} (fun _ h => List.mem_range.mp h)
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
  rw [foldPresent]
  unfold tally slowTagCount
  rw [foldCounts (List.range 22) f _ {} (by simp [countZero])]
  have v := rows (List.range 22) (fun _ h => List.mem_range.mp h) 0
  simpa [countZero,g,f] using v.symm
def priceStripe (k : Nat) := (List.range 49).foldl (fun n i => if k≤weightR i then n ||| 2^i else n) 0
def replicated (k : Nat) : Nat := (List.range 144).foldl (fun n o => n ||| (priceStripe k <<< (49*o))) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem priceEq : ∀ k : Fin 43, weightGE k.val = replicated k.val := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem priceLow : ∀ k : Fin 43, priceStripe k.val < 2^49 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem priceEntry : ∀ (k : Fin 43) (b : Bank), (priceStripe k.val).testBit b.val = decide (k.val ≤ weightR b.val) := by decide +kernel
theorem projectedPrice (k : Fin 43) (b : Bank) (o : ID)
    (bit : (weightGE k.val).testBit (lane b o) = true) : k.val ≤ weightR b.val := by
  rw [priceEq,replicated,foldBits] at bit
  rcases bit with nope | ⟨i,mem,hit⟩
  · simp at nope
  · have ok := ((stripe _ i b o (priceLow k)).1 hit).2
    rwa [priceEntry,decide_eq_true_eq] at ok
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
  have sz : present m=ls.length := by simpa [foldPresent,slowTagCount,ls,test] using fold (List.range 22) 0
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
end PCX150.Scalar.Local
namespace PCX150.Scalar
open PCX150.Chart48 PCX150.SmallChart
def followName (base : ID) (w : Nat) : Nat → ID
  | 0 => base
  | n+1 => let t := (w >>> (3*n))%8
           if t=0 then followName base w n else follow (followName base w n) (Fin.ofNat 5 (t-1))
theorem unitSet (u : Set Sample) : acted (Aut.unit geo) u = u := rfl

theorem traceName (o : ID) (w n : Nat) (s : Set Sample) :
    acted (assemble w n) (acted (orient o) s) = acted (orient (followName o w n)) s := by
  induction n with
  | zero => simpa only [assemble,followName] using unitSet (acted (orient o) s)
  | succ n ih =>
    simp only [assemble,followName]
    split
    · exact ih
    · rw [←actedChain,ih,followAct]
abbrev TurnIndex := Fin 35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem followChase (o : ID) (w n : Nat) : (followName o w n).val = rawChase o.val w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [followName,rawChase]
    split
    · exact ih
    · change ((alongCode[(followName o w n).val]! >>> _) % 256) % 144 = _
      simp only [ih,Fin.val_ofNat]


theorem turnInBank : ∀ j : TurnIndex, turnID j.val<144 := by decide +kernel
theorem rotationHints (j : TurnIndex) (o : ID) : turnID j.val<144 ∧ sendName j.val o.val<144 ∧
    (followName o words[turnID j.val]! 9).val=sendName j.val o.val := by
  have e : (followName o words[turnID j.val]! 9).val=sendName j.val o.val := followChase _ _ _
  exact ⟨turnInBank j,lt_of_eq_of_lt e.symm (followName o words[turnID j.val]! 9).isLt,e⟩
def actionIndex (j : TurnIndex) : ID := ⟨turnID j.val,(rotationHints j 0).1⟩
def sendIndex (j : TurnIndex) (o : ID) : ID := ⟨sendName j.val o.val,(rotationHints j o).2.1⟩
theorem shiftIndex (j : TurnIndex) (o : ID) (s : Set Sample) :
    acted (orient (actionIndex j)) (acted (orient o) s)=acted (orient (sendIndex j o)) s := by
  change acted (assemble words[turnID j.val]! 9) (acted (orient o) s) = _
  rw [traceName]
  have eq : followName o words[turnID j.val]! 9=sendIndex j o := Fin.ext (rotationHints j o).2.2
  rw [eq]
theorem laneBefore (j : TurnIndex) (w : Nat) (b : Bank) (o : ID)
    (h : (rotateLanes j.val w).testBit (lane b o)=true) :
    w.testBit (lane b (sendIndex j o))=true := by
  rw [rotateLanes,foldBits] at h
  rcases h with bad | ⟨i,_,cell⟩
  · simp at bad
  · obtain ⟨eq,src⟩ := (stripe _ i b o (Nat.mod_lt _ (by decide : 0<2^49))).1 cell
    subst i
    rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight] at src
    simpa only [b.isLt,decide_true,Bool.true_and,lane,sendIndex] using src
end PCX150.Scalar
namespace PCX150.Scalar.Local
open Chart48 SmallChart PrivateGame
open Sparse (TestTree Valid box leaves)
def pointPrice (a b : Bank) (o : ID) := ∀ (t u : TestTree),
  Valid geo.val (box geo.tag (candidate a) ∅) t (dataB b o) →
  Valid geo.val (box geo.tag (candidate a) (dataB b o)) u Set.univ →
  41 ≤ price a + leaves t + leaves u
theorem sameCost (a b : Bank) (o : ID) (j : TurnIndex) (fixed : permute (turnID j.val) (R a.val)=R a.val) :
    pointPrice a b (sendIndex j o) → pointPrice a b o := by
  let f := orient (actionIndex j)
  have mb : acted f (dataB b o) = dataB b (sendIndex j o) := shiftIndex j o (candidate b)
  have ma : acted f (candidate a)=candidate a := by
    change acted (orient (actionIndex j)) (candidate a)=candidate a
    rw [←chosenSet,←actionSet]
    exact congrArg bits fixed
  have fa : Match (acted f (candidate a)) (candidate a) := by rw [ma]; exact matchSame _
  have fb : Match (acted f (dataB b o)) (dataB b (sendIndex j o)) := by rw [mb]; exact matchSame _
  have fe : Match (acted f ∅) ∅ := by rw [actEmpty]; exact matchSame _
  intro ready t u ht hu
  have st := canMove f _ _ _ _ _ _ ht fa fe
  rw [mb] at st
  have su := canMove f _ _ _ _ _ _ hu fa fb
  rw [actUniv] at su
  simpa only [Sparse.sameLeaves] using ready _ _ st su
theorem propagatePrices (a b : Bank) (w : Nat)
    (initial : ∀o : ID, w.testBit (lane b o)=true → pointPrice a b o) (n : Nat) :
    ∀ o : ID, (spread a.val w n).testBit (lane b o)=true → pointPrice a b o := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    intro o h
    unfold spread at h
    dsimp only at h
    split at h
    · rename_i used
      rw [Nat.testBit_or,Bool.or_eq_true] at h
      rcases h with h | h
      · exact ih o h
      · let tag := stageID a.val n
        have q := used
        change keepStep a.val tag=true at q
        unfold keepStep at q
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at q
        let j : TurnIndex := ⟨tag-1,by have := q.1.2; omega⟩
        exact sameCost a b o j q.2 (ih (sendIndex j o) (laneBefore j _ b o h))
    · exact ih o h
end PCX150.Scalar.Local
namespace PCX150.Scalar.Local
open PCX150.Chart48 PCX150.SmallChart
open PCX150.Sparse (TestTree Valid box leaves)
theorem closePrices (all : ∀ a : Bank, covered a.val=true)
    (init : ∀ (a b : Bank) (o : ID), (initialCover a.val).testBit (lane b o)=true → pointPrice a b o) : PrivateGame.scoreClaim := by
  intro a b o
  have total : spread a.val (initialCover a.val) 7=big := eq_of_beq (all a)
  apply propagatePrices a b (initialCover a.val) (init a b) 7 o
  rw [total,liveWide]
private theorem prefixWordHas (read cost word : Nat → Nat) (k lane : Nat) (n : Nat)
    (bound : k ≤ (pricePrefix read cost word n).1)
    (hit : (pricePrefix read cost word n).2.testBit lane = true) :
    ∃ z, k ≤ cost z ∧ (word z).testBit lane=true := by
  induction n with
  | zero => simp [pricePrefix] at hit
  | succ n ih =>
    change k ≤ min (pricePrefix read cost word n).1 (cost (read n)) at bound
    change ((pricePrefix read cost word n).2 ||| word (read n)).testBit lane=true at hit
    rw [Nat.testBit_or,Bool.or_eq_true] at hit
    rcases hit with prev | last
    · exact ih (le_trans bound (min_le_left _ _)) prev
    · exact ⟨read n,le_trans bound (min_le_right _ _),last⟩
private theorem middleWitness (a k lane : Nat) (h : (extraWord a k).testBit lane=true) :
    ∃ z, k ≤ getB a z ∧ (exactCube (z % 2048)).testBit lane=true := by
  unfold extraWord at h
  dsimp only at h
  split at h
  · rename_i ok
    exact prefixWordHas (fun i => exts (startsExtra a+i)) (getB a)
      (fun z => exactCube (z % 2048)) k lane (midLimit a k) ok h
  · simp at h
theorem learntMiddle (p : ∀ i : NodeID, nodeOK i.val=true) (a b : Bank) (o : ID) (k : Nat) (t : TestTree)
    (good : Sparse.admissible geo (triple (domainMask b o) (R a.val) 0) t)
    (data : (extraWord a.val k).testBit (lane b o)=true) : k≤leaves t := by
  obtain ⟨z,paid,eq⟩ := middleWitness a.val k (lane b o) data
  have cells := exactCubeCell _ (Nat.mod_lt _ (by decide)) b o eq
  have same : bits (testMask (z % 2048)) = bits (domainMask b o) := by
    ext r
    change (_=true) ↔ (_=true)
    rw [cells,domainBit]
  have useful : Sparse.admissible geo (triple (testMask (z %2048)) (R a.val) 0) t := by
    change Valid _ _ _ (bits (testMask (z % 2048)))
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
      simp [rowQual,few,shortTallyEq]
    rw [array] at hit
    simp only [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at hit
    rcases hit with (⟨x,y⟩ | ⟨x,y⟩) | u
    · exact countPaid a b o k t good x y
    · exact monoPaid a b o k t good x y
    · exact learntMiddle p a b o k.val t good u
theorem resolve38 (p : ∀ i : NodeID, nodeOK i.val=true) (all : ∀a : Bank, covered a.val=true) : TreeLower := by
  intro A B ia ib ic x y z
  apply PrivateGame.allThree ?_ x y z
  apply closePrices all
  apply reachTarget
  · intro b o z bitsOK r hr
    have real : active b o r = true := by
      rw [←activeSet] at hr
      exact (domainBit b o r).symm.trans hr
    exact upperMask _ b o (upperFromCube _ b o bitsOK) r real
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
end PCX150.Scalar
namespace PCX150.Scalar
end PCX150.Scalar
end PEqualNP.Outside.L_pcx_150_aux
open PEqualNP.Outside.L_pcx_150_aux in
theorem PEqualNP.Outside.L_pcx_150_tables
    (states : ∀ i : PCX150.Scalar.Local.NodeID, PCX150.Scalar.nodeOK i.val=true)
    (roots : ∀ a : PCX150.Scalar.Bank, PCX150.Scalar.covered a.val=true) :
    ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 51) :=
  PCX150.finishFromBounds PCX150.OrbitCert.hard
    (PCX150.Scalar.Local.resolve38 states roots)

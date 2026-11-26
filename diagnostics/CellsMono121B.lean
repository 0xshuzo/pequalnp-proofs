import PEqualNP.Defs

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4813_aux
namespace Certificate
open PEqualNP.CircuitLowerBounds

def mask72 : Nat := 0xffffffffffffffffff

def perm0 : List Nat := [16,82,131,100]
def perm1 : List Nat := [32,49,128,81,116,100]
def perm2 : List Nat := [81,130,118]
def perm3 : List Nat := [128,49,100]
def perm4 : List Nat := [16,32,48,128,100,80,116]
def perm5 : List Nat := [32,83,116]
def perm6 : List Nat := [80,129,50,116]
def perm7 : List Nat := [48,129,82]
def perm8 : List Nat := [128,81,32,49,100,116]
def perm9 : List Nat := [48,33,133,118]
def perm10 : List Nat := [80,16,33,50,116,131,100]
def limbs (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def word {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (limbs xs)

def stripe4813 {n : Nat} (s : Nat) : BitVec n :=
  BitVec.ofNat n (((((1 : Nat) <<< n)-1)/(((1 : Nat) <<< s)+1)) <<< s)

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
abbrev Row := Fin 512
def inputs : List Sig := [(stripe4813 1),(stripe4813 2),(stripe4813 4),(stripe4813 8),(stripe4813 16),(stripe4813 32),(stripe4813 64),(stripe4813 128),(stripe4813 256)]
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
abbrev Move := Sig × Sig × Row
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (limbs [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (limbs [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (limbs [1,65536,0,0,0x10000000000000001])
  | 3 => (limbs [65536,0,0,1])
  | 4 => (limbs [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (limbs [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def properB (T : Sig) := T != zero && T != one
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def adjacentMask (m : Nat) : Nat :=
  (if m.testBit 0 then 50 else 0) |||
  (if m.testBit 1 then 69 else 0) |||
  (if m.testBit 2 then 138 else 0) |||
  (if m.testBit 3 then 276 else 0) |||
  (if m.testBit 4 then 9 else 0) |||
  (if m.testBit 5 then 385 else 0) |||
  (if m.testBit 6 then 258 else 0) |||
  (if m.testBit 7 then 36 else 0) |||
  (if m.testBit 8 then 104 else 0)
def columnFrom (m v : Nat) : ColumnInfo :=
  let z  := v/16%131072
  let o  := v/2097152
  let free := m%512 &&& (511 ^^^ (z%512 ||| o))
  let h := free &&& adjacentMask (m%512 &&& o)
  let r := free ^^^ h
  (z,o,z/512*512+(r &&& adjacentMask r),h,v%16)

def hardSeed : Sig := inputs.getD 0 zero &&& inputs.getD 2 zero
def chartGoal (m : Nat) : Sig := if m=1023 then graphGoal m &&& ~~~hardSeed else graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

def defaultDecor : Decor := (zero,0,0)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def page (xs : Array Nat) (i : Nat) : Nat := xs.getD (i%103) 0
def gather (w : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => w i ||| (gather w (i+1) n <<< 80)
def pick4813 (w : Nat → Nat) (b p n : Nat) :=
  let i := 103*b+p/80
  let s := p%80
  let a := if s+n ≤ 80 then w i else if s+n ≤ 160 then
    w i ||| (w (i+1) <<< 80) else gather w i ((s+n+79)/80)
  (a >>> s) &&& ((1 <<< n)-1)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let b := pos/8192
  let s := pos % 8192
  let left := 8192-s
  if len ≤ left then pick4813 word b s len else
    pick4813 word b s left ||| (pick4813 word (b+1) 0 (len-left) <<< left)

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let prod := dbin 0 (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor)
  if g.mask=1023 then ws.map (fun w => dbin 2 w prod) else ws

def targetOf (g : Forest) := chartGoal g.mask
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 5) (pos+5+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩


def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def flOf (g : Forest) (k tag : Nat) : Option (List Nat) :=
  ((g.index k tag).bind (linkedSet g (k-1))).map (fun xs => xs.map BitVec.toNat)
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  let xs := (g.index k tag).bind (linkedSet g (k-1))
  change xs.map (fun ws => ws.map BitVec.toNat)=some ys at h
  change ∃ ws ∈ xs.toList, ys=ws.map BitVec.toNat
  cases e : xs with
  | none => simp [e] at h
  | some ws =>
    simp only [e,Option.map_some,Option.some.injEq] at h
    exact ⟨ws,by simp,h.symm⟩
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def runLength (v : List Nat) := (v.map (·/256)).sum
def scheduled (g : Forest) (k i : Nat) : List Nat → Prop
  | [] => True
  | p::ps => cells g k i (p/256) (p%16) 0 (p/16%16) ∧ scheduled g k (i+p/256) ps
theorem scheduled_ok {g k i ps} (h : scheduled g k i ps) : block g k i (runLength ps)=true := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih => exact block_merge (cellsBlock h.1) (ih h.2)
def moY : Array (Bits × Bits) := #[((word [0xffffffffffffffff02,0x47102040c820c0830c11]),0x3f03f81ff800001f8000),((word [0xffffffffffffffff04,0xc1040881096109041123]),(word [mask72,0xc000000007e000007fff])),((word [8,0x882c5902104218288106]),0xfff800001ff81f8000),((word [17,0x1008902432803260820c]),(word [0xffffffffffffffff00,0x1fffe007e000ff])),((word [3,0x2102060608060410608]),(word [255,0xc0fc07e0001ff8007f00])),((word [160,0x48202088414848268d0]),(word [0xffffffffffffffff00,0x1fffe07fff])),((word [68,0x20410491010901141020]),0x7fff81fffff8000),((word [40,0x820430a040604082040]),(word [255,0xff0007ffffe000000000])),((word [208,0x30c38414021802104080]),(word [255,0xfffff800000000000000]))]
def moC : List ColumnInfo := [689165,688172,4108,524,1037,44,2061,680205,269,696589,140,681997,76,680973,2097160,28,698381,680460,958492,18445,680076,684044,786460,4194390,680012,2097671,811277,283,772109,860429,8388774,2097702,1105948,8388616,1067,34439320,843804,770124,16908,33554584,268436040,813069,57,34891,25613,180252,395,67108887,697357,2123,861197,16524,20492,4194312,761884,536871558,2097191,8388743,98332,134909992,88,933976,16781382,885005,221212,16460,119,937996,844059,294940,16777224,8388647,196891,786701,762139,34341016,1106189,106524,958733,714827,33805,24620,16777287,934925,739341,28684,221467,1097997,25100,2571,4194327,884876,134221864,442396,688776,296973,33652888,67112982,763917,960525,24716,33554457,536871047,270364,269172809,16781319,75851,1106039,442637,862221,927757,35339,268435466,34439193,648,762380,536870920,269115976,762125,122908,152,269173320,33554676,268435529,67108872,713741,33751192,4194375,876813,34829,49228,4743,147725,926733,682059,33554442,134217738,134217769,4233,4295,844813,98587,706635,843833,33554569,34316440,705549,712780,297,168,108557,221228,712748,123275,4617,684231,196877,844045,75789,1107981,1105964,761996,1106060,1171739,537,567,33555093,50189,843820,135151657,201,958776,268468808,269206088,135155752,958583,762893,959501,1106957,19467,268435977,584,67112967,221453,876572,442412,958508,1105996,442508,926220,765964,516379,876827,1179931,33835,2315,680137,737448,680520,4168,680839,8390790,812045,877581,929804,1098795,37899,343,123149,149517,1179676,73804,712844,680331,35851,5131,34341001,134221833,4120,1106151,33554645,8389029,268436053,1025037,1017869,1097868,737804,1098123,1025067,958569,33775768,34660504,4136,268436084,794893,1098765,442444,147851,76811,1105977,269206025,269394504,684424,536871431,2097446,181261,796685,270380,294988,704588,1106315,197675,25867,777,1049,884888,33996952,34431128,268452424,692264,790600,134221925,15,98573,197645,271373,706573,294956,213275,434571,18507,100619,683019,1029131,269115402,737864,682184,846360,231,2097415,716999,848407,8388998,2099238,268436165,134221877,33556692,268440260,714765,845837,1097756,180268,73868,958988,274444,147739,18699,149771,764171,928267,961035,134905866,135151626,813081,135155721,4361,684553,6153,312,268730952,2152,36904,712935,715207,2695,67113222,33554613,4194645,8391045,268440133,712973,73772,704556,925772,794764,221708,295436,705036,844300,708620,106779,794907,1171851,1291,108811,846347,134930442,34316313,294969,105,844073,885033,180761,959001,811785,861209,934937,2185,134909961,716937,33702040,552,959048,1107048,2248,134246440,134492200,134934568,844343,959031,2135,2097926,2099718,2097957,4196437,536873605,67114005,134222052,1179917,204828,589852,794652,286764,958540,123020,426124,876684,795148,880652,1101836,1098011,131467,442763,74795,222251,689195,926763,197899,443659,927819,76043,223499,297227,682251,297483,764427,52235,297995,715787,29707,54283,685067,881675,34439178,135061514,269172746,34431001,134930473,34439305,49353,1106121,196905,860457,329,786761,762633,181273,271385,689289,2073,772121,2089,762008,786584,34652312,34734232,268509768,269140552,269361736,99096,844568,1080,75976,714952,2584,938024,134254632,135065640,135147560,767112,6664,1179991,423,762759,1191,197943,1575,4631,8388902,16781574,16783366,8390821,134221989].map (columnFrom 1535)
def moA : List (List Nat) := [[],perm2,perm0,perm4,perm5,perm1,perm9,perm7,perm10,perm6,perm3,perm8]
def moD7 := page #[0x341986d552605314c120,0x403fd087f003f4127f4d]
def moD8 := page #[0x4c1206d552605314c120,0x605514c120661b560531,0x750b9605514c12074cb9,0xf4d0d5e4d5acd4f494f4,0x275b2ec4dd481dac660,0x3ff412003c002f8d309e,0x60b7c219fe84bf80000,0x38880000740308]
def moH8 (j : Nat) : Nat := 0
def moD9 := page #[0x54920440ba5495148110,0x4419854d524811032953,0x605314c12054d5260120,0x4c1202d5814c530480a5,0x661814c5304815260531,0x4c530481b5605314c120,0x481c32e5514c120661b5,0x2e5514c120710b954530,0x4c1202e58154530481c6,0x2e5b3545304818260551,0x54930480ba54d524c120,0x481c154d524c12032553,0x2e1a54c52030d9860530,0x5c1206a5b62a553480b9,0x2e98455170480cb5cd42,0xad3ee9fb51dea2fb41ff,0x74ae7a57f4afb557daaf,0xbfb17f4afe45f9abf257,0xb65eecbcd96fb2d75ff0,0x7d3af674fce9e9c6bf2f,0xb9b67db6a66ba80efa1d,0x8b8cb9b88a09b89bb308,0x13a364ba3351b325bad1,0x39b6319b8263ac17ba60,0x41b6729b6783a4583a44,0xd3a6d9390ca390bab90a,0x73a3033b0fc172ecba8d,0x23a37b1a9503b9473a31,0x9a439c4b0431b88c1a00,0x4d1b86be9e4ea7130562,0x471180b657aad49a0cce,0x3fe82400bf3f83b1d1e,0xfc00006fe84001e801e0,0x9dd04fc0b019fd007a12,0x439f813b0d059e00c246,0x10232a24180c01e704ad,0xde0090cfc803c05bf83,0xc70805da0903cccec7b,0x23099c122e4411009ce0,0x264803bcc44672410336,0xb610acc4000000005fc8,0xb0201341008604683487,0x3c604d8030080027314,0x3398b58128]
def moH9 := page #[0x48040c200000,0xa4000000018000022000,16897]
def moD10 (j : Nat) : Nat := (if j<206 then (if j<103 then page #[0x64d825481054d8254810,0x68d925481068d8254810,0x6a1935481068d9354810,0x651a3548106d59354810,0x64d53608102e95360810,0x54d92608106515360810,0x6c995608106d59360810,0x655a3608106cd9560810,0x66153604202e99854c20,0x6c553604206a55360420,0x6a552604306595260430,0x54930481105499160430,0x54951481102e95148110,0x54d52481106c95148110,0x66153481102e95348110,0x54980481106a15348110,0x695934811054d8048110,0x54d524c1106a19348110,0x2e5534c110609524c110,0x549804c1104c5804c110,0x6a5854c91054d824c110,0x64d8254910661a54c910,0x2e583549106c18254910,0x2e993549106e58354910,0x54d52601106e19354910,0x6d4a9609102e95360110,0x2e953609102a55360910,0x65593609102e99360910,0x6cd95609102e99560910,0x2a5a1609102a5a060910,0x684954c1206999524d20,0x6d0954c1206cc954c120,0x684984c1206d8954c120,0x255314c1206c4a54c120,0x2d5314c120295314c120,0x549314c1202e5314c120,0x661314c120605314c120,0x261514c1206d5314c120,0x54d514c1202e5514c120,0x609514c120605514c120,0x6c9514c120661514c120,0x6e1514c1206cd514c120,0x2a1524c120261524c120,0x54d524c1202e9524c120,0x2e5534c1206c1524c120,0x4c5804c1206c5534c120,0x255814c120605804c120,0x2e5814c120295814c120,0x661814c120549814c120,0x54d824c1206d5814c120,0x2cd984c120549914c120,0x6c5984c1202d5984c120,0x2a1a14c120295a14c120,0x661a14c120549a14c120,0x6c4954c520660954c520,0x6d8954c5206cc954c520,0x6e0a54c5206e0954c520,0x6d8a94c5206d4a94c520,0x261954c5202e9944c520,0x2e9954c5202a5954c520,0x2a1a04c520295a04c520,0x2a5a54c5202a5a04c520,0x2e5a54c5202e1a54c520,0x61d8450520661a54c520,0x2e995505206558450520,0x6a4a954d206558450d20,0x6d8a954d206c4a954d20,0x5cd425c1202a5a054d20,0x2e9545c120551535c120,0x6549360520611545c120,0x6dc93605206c49360520,0x6c553605202e55360520,0x65593605202a59360520,0x2e995611202e5a360520,0x66153645202e55364520,0x69ca3661206c49864d20,0x28da1661206d8a366120,0x2cda466120691a166120,0x69492605306549260530,0x6e092605306d49260530,0x2a552605306c8a960530,0x2e992605302a59260530,0x2a542505606559260530,0x61d42505605954250560,0x2a573505602a56350560,0x3ee87fe1fd61d7350560,0xfd97ee5f793fe3ff8ffa,0x69efa77a9bfa5ff97fa5,0xa6fe97f9ffa7fb9fde7f,0x7fe9fda7ee9f7a7be9df,0xeabeeaf7ebdeaefab7ea,0xedbfb6fadb7b5debfeaf,0xdfeb7f6df7b7dadefb76,0xecbf9afdebefafb6bbfa,0xcbfeaff6bfd2ff2bfbaf,0xc77f1bfc5ff13fc3feff,0x7ff1fec7f71fbc7df1ef,0xfb3fccfdb3eecefb2ffc,0xb57fd3ff4fed3f747fcf,0x5f7d7db5f5d7bb5dbd6f,0xd7df4f5fed7f75fcd7ef,0xee3ef7fadfe37f4dfcb7,0x7fe5ef8f] j else page #[0xfe7af9dbe75f9bbe6bf9,0xf3d7cf4efebbdbe7cf9e,0x75fdd3f72fd5bf3ebcf6,0xf3ef4f7f3df5f7cfddbf,0x3fdaff63fd6ff4ffd2fb,0x70443ff8ffd3ff1ffc,0xce1b7736a6612008ca3f,0x6f65001c193000c32e1,0x539b900646a401b9970,0x11772805c1c5016768c,0x80991950265650099dca,0x9025d660097d97026265,0x2c1459c804177200cf9b,0xb807636a01859cb05017,0x2e828f4ba090172420f1,0x9b30d16328305cca0b3c,0xb6e83850ca0e2570c353,0x14cb110170440edcb0f3,0x5064c4c05cb12376e844,0x4e9ba143f6a44d259813,0x87854c5c61ca160172c5,0x65ed83197b2e864c1c41,0x197b6cc65eda3197b64c,0xc69eda51a7b72465edc3,0xb220172c85e1831b5b6c,0x2ca5d981260932c8804c,0xca2d0732cac04cb2a017,0x72cd051c5341670cd005,0x5c53601724d40dc03501,0x56ccf519b13d3a6e0f00,0x45983e436d8f511b43d4,0x337050c39c3424d66101,0x39cb432c7190cbdc443,0x62271918c9c245327091,0x215db5472171d18b1c64,0x487666121ad98487d549,0x5289cc94a0632d2569b5,0x34c0e70d3145984a5132,0x193035c64c4f7113145c,0xb94e512e53425c84c4d7,0x2e54965b3510932d4150,0xc957782e95de0a95751,0x854d61e1c957787055de,0x9cc95a2c7196489c6597,0x7854d8129b95c766056c,0x178ca616c30d85b59860,0x62770d989dc1657854d9,0xa87dc268402e99c8dc66,0x723a6a5bc24cb6b7854d,0x1d0e9a973396ddc8e9b6,0x2791f709e04dc6760172,0x19e869c7791e711e47dc,0xc77a1271de86dc67a137,0x6a61404cb7e01721f469,0xdc1891c32a204dc6863a,0x86623525988c442ea280,0x5ca8e0870638e5a98d4,0x1271e64e9a798406c25c,0x42dc09f3d69e6c58c39a,0x8612a69855c5a50172e8,0x6e01831a3670c604dc2a,0x1b726606df0ca1b7c324,0x6df1c01b686a06df198,0xb1d2d71871f1c91b7c72,0x2c81f1531f1132c7844c,0xb823716608dc4c923113,0x54c9ca1c2257954c9161,0xccb2b1032cac3ccb287a,0x9720bd04ca2e532e4b14,0x11c2321d328c504ba301,0x19714d811c536416a4cc,0x864ca39416e8e104ba37,0x1476e0f465c53b19714e,0x14d1c844347210d1db54,0x463471518a1c54634721,0x521fca548732e51ca1c8,0x8487f65521f952487f2d,0x52d71b24b7f66121d19,0xc84c1172d2cb9c54b367,0x2e53959c84c2a7213045,0x8b94f806c939dd824e75,0xc6e14571b351562e5455,0x58b9532a3254958b9525,0x3570d50d5c1542a3254d,0x8d5c555357055571b155,0x92870564d5c856357055,0x75fd815b776056cd1c15,0x5d3171174d1c35d36705,0x978d9c15e1172d74adc8,0x55f0a7157c45cb5e3570,0x2589e553605c2e58045c,0xc56920721a03ccb632a3,0x6e9b1a4ca6a692a1a881,0x5a97052661b955986d41,0x16e1c905a972416a5c50,0x65ca752870dd4a5c1754,0x20721e011c87719721d8,0x881c57a19715e881c579,0xc19721ec81c87a19721e,0xf465c97c20701f104b97,0x7e0a32df865c87d0a721,0x20198ca8026725fd04cb,0xc8812672] j) else (if j<309 then page #[0x6a61198c483267060865,0xdb88b4c6de2c65c18641,0x93263d55958c416ea2d2,0x29c5920a72e4465c5902,0xa32e5491c6941970e4c,0x505ba9c4b6e27105a596,0x416a67811cb9d426e27,0x9011c5a3416ea8905a9a,0xaa19716a598a9a7412ea,0x780a201c4032000180a9,0x81df06c817c054412603,0x2d30ac828a0988232082,0xcd0e983780d3831d0bd0,0x11234463110841b0fd03,0x159453714604f913404b,0x98863917f45d416b458e,0x607261bfc6e01ae06881,0x85120a47f81ec07891d,0x99d259492823e48cb225,0x7c2964a2527f89d92708,0xc2e04b442c68ad22ae4a,0x32c0c5e30acc062f5cba,0x678d903590d323418cd4,0xfce6e3910e1837b4dc33,0xf363c1cef43af0e9e39,0xfd33eccf913df8f703d3,0x90415d03a408500e3fc8,0x8459513a43f10db42e90,0x4a31241482d1e146d919,0xec93964dbd3364be12c4,0xdd49151f946950453d84,0x1599558954054794f352,0x6bd5a1d64a588160a573,0xe75ef179a5d9d72e5bc1,0xf632d8a361a983c60297,0x6975a1e67959ac658190,0xd75b266c09ac96a85a92,0xa5c7d70e5bff6f69b9b6,0x5da57675d5874cdce572,0xe0077cdde5770ddb576b,0x7d796de4078c9e1b784d,0x17c11ef47b6decc7a61e,0x7db1f5f7d5df357c85f1,0xfd9fdd7f09fac7e45f7e,0x1a075818204780b20137,0xe0fd836e0cb82ee09d82,0x19c85c21588502129844,0x1188021e5873a1c086d2,0x789fa268894223588862,0x8cca30c8bc22d68aaa29,0xf423b08e5637a8d8e353,0x3a43e90764048fd23e48,0x24ea931a4b4926e47691,0x5b5964e575951252a941,0x6a9946644988a5fb9796,0x39bae6dc9b1e6af9a466,0x9e4a7709d567499c8e70,0xf281aa00a7e99f4e7b7,0x3e8baa272887a1e285da,0xe968a552918a4028f1a3,0xa08a7969cda6d299aa5e,0xc2aa66a87a98aa3da86a,0x7ae2ab65acf6b11ab96a,0xb18ac4fb0d2c0faf6abb,0x5aed3fb44ece7b2d2c88,0xeee20b7faddeb70ed97b,0xfc00f04c017e826e7db8,0x3df01fc0b007ba10007,0xfe8c9e0800bf4010064,0xe0039e04e005c1200dd8,0x187016e873c0d701403,0x17c2c00f2e08d0d3604,0x6f606d821603780805ad,0x8017800201c806bd0,0x40fb01740c781a603e06,0x1ab03e0ae01e3412e877,0x339cc0050010006002ba,0x1808066b811e05208ce0,0x4a20c10ef482300f80f,0x8c00fe05400c010a023b,0xb825b81b602212d00f00,0x95c183c012808e43982,0x35703120c000e203d868,0x3a03fe0401fc04702940,0x20ec82ad05341100e060,0x8180c50181a0aa032c01,0x30052b096e0200e4a0af,0x5a0838150d808288ad90,0x455d0c7c09e811602281,0x28b00283b0d63858e193,0x428310230086c33c1280,0xf207c50703fa29e8ff83,0x53824c0e80c6c03fc04,0x1455fe0304f012a42fdb,0x603b11e520a10a1027b8,0x868009f2d5d80c85cabb,0x200a80650cb5c0421c1,0x51813a083014860a828e,0x2532840378c02980960,0x80d2044816605d13cc06,0xfe03c069807098300e82,0x305616741a862b7a2e03,0xd507b01a] j else (if j<412 then page #[0xac1b50d0915708920302,0x4727146c22d08a19842b,0x803f9206e156c0c1220,0xa40a804b20a3c02b0292,0xe0538a8c1dfc06f021e0,0x8b80bbd0574ba0412c15,0x883699cd06559cf82ba,0x55c412c0cfe0d845cb2,0xe4350300d8121e401024,0xa1590c6437094530e04a,0x302a5c00d120e1db80ca,0xa18095c01f34f98241e0,0xc2caedabdc40faa65825,0xa1827021c0f323c0138a,0xae4eb9db02822a493060,0x259e0c41ad069039fe81,0x68680ea2940a019699db,0xe79b5e293812e6db8a68,0xd87607121c4e0a21e4e2,0x56b2498196625f0c044b,0x25870d82b24cc87729d2,0xb805e938955c8bb40082,0x912080dc15a80c512c04,0x93b3e0605d094c0c7044,0x1c1020607007f0622405,0x42a429a702220501e940,0xbb20a2196c4f82b604b,0xbb243882aa053818ec30,0x6a0268b80b6101840814,0x20ca8100a60575a0614b,0x458116083831a040810,0x5997c15b203fc53c822c,0x1858800012fb3d461980,0x400cb3801ef8c5f71,0x89003c16c00eee887efe,0x16500000f06321be635,0x299b0fe328432b61fc65,0xd48e10885022f3412228,0xab520658c3f8ca10cb8f,0x510658bd1735110a5edb,0x72045edbab51065edbab,0xf51c12291466e208aa33,0x5843a4a3e5102391d2cd,0x34517e2a38412140fc4,0xc81140f5fb81a281ebf7,0x5416403d7ee408a07afd,0x1e24d189f0ab0994819e,0x9e04913690d272341a1a,0x210a69391a0cd272341f,0x8343cb822452021f2752,0x132908ab8224521a4e46,0x3e00025f67a743a1ddcd,0xec0b3e4a401efa5f1522,0x2f9f8a916eec0b3e4296,0x8205543d498e2f660d6e,0x60596a940008fd8150a5,0x384a240cb2a2a5235819,0xe78e2a9418f043f75c20,0x70834a7fd81c23289f85,0x7454e2e1d3f00ad3f4b0,0xb3857fcd571acd0860f,0xf861010e061fbc35411c,0xc213fff8a021c0c30bff,0xe4070c241d143223e874,0x259d2834054a38d06527,0x78b221e1dc280c274002,0xe21899c6ca1801ef2634,0xf10eca40005ff74e8f00,0x2811fe8f6f00e221e6da,0x8fa6c0e72171f4d81ce4,0xa64f02848fde3c871acd,0xe198b04fde3c8722ce0,0xea670d9ff0145e105258,0x188563ff42100829400a,0x72d88007520a5562f540,0xe40984740958bd500621,0x35215ff3185d48ced,0x1293d161c4252160fe2,0x63045ecd06c6037be96d,0xc0e3122f200129b3fa01,0x6623b76fc400330af180,0x2bc903680afbca0409ee,0x403068f98030779fc009,0xf84a1870621cc0344474,0xbf843043394cba181441,0xf530225f3bbc60069006,0xe740a00061dbe1204c97,0x1d28dfea1004a4b7f83,0x1a4d1f62d100ec7a450,0xacf95ff1009b295fee00,0x8400024487979f29202,0x3c3660011a01efffc0a3,0x2a213f8f9cc80099d30e,0x188020a6a600039bb100,0x83445fcec0308c01de0f,0x41000a9bdf90006841c1,0xb8220044000c600a7f90,0x226b040ca02abf04ba7f,0xb3e794800d102fd8030c,0x1801a32bfe2300349cc1,0xed10a18a6d75903613af,0x6234f13944001d2d5f88,0xae0a1001] j else page #[0x3d5e8c2e90bc92396036,0x46ce05dfa41488c1aa73,0x4702b04c52b270fcadd3,0xa60008bf55aa06129d2f,0x4ff8234a031fd6290494,0x62322916f88c8a300003,0xdac11a5cdb1ba98637fa,0x9a6e366988c42964e079,0xd1ff0dd08a7f6094891a,0x15afff1494006adf911e,0x261ffeec111082b00cc3,0xa980cffb3c1b0a4b0986,0x911de15300061fc0d926,0x1c791434e3a7000cbb,0x21c22000000f43e45280,0xff87868c8536bc5fc30c,0x8b7df688776a6184030,0x107f5dca74653a64830,0x4c300043d2f668d174e0,0x10781e9194414c031786,0x6200f7b99545944d2d40,0x30296fc40001b3c42,0x137e5839954e38a,0x9e498ea1f629f6986000,0x69b080000000000055ff,0x1a98a682db081ff28d4,0x94621c2789361f7e9040,0x44094316b7c0e165eb18,0x787060653854e0606ab0,0x46cc2cd1d69b10dd0cd0,0x310f1642629cf8468201,0xcbe85100506e227aa0a3,0x258878b2fa345e94d883,0x378261e0d26a098e8f45,0x947638363820dd6c4183,0xf412bb3051715149f484,0xa0b711ae1689ce668806,0xa2680a5076ef28b76ba0,0x13dd0def048386715d72,0xca0bafe68a9b0271472b,0xd09985ab6c4c7c1a237,0x30da5f618e78a843b7e2,0x52382cc9fe1830033cf5,0x8e8783e14863ce283994,0xaae86ae863958b0c1786,0xa4aba122441b51c09eb0,0x5856f7d00484b3472002,0xe29dfcd18c3b4f86e43,0xa7e224361f080930f3bd,0x6cf210c1abfd27a42521,0x49c4e4000252d5fc0514,0x528a3abfdd005484ed41,0xc1029a4ad92612d07cea,0x8d05a38585ae214c1e1e,0x717e14346835f45ee068,0x8eeb02f1190b2f840498,0x51074301b36c3d246cc6,0x32aa249cae12aed05ef7,0xf119825528e4f8281a3b,0x406e60e1b105ee06133c,0x8bdc0e5c3231470d982f,0x8000effc8982629b6e12,0x84376dab306b600c3918,0x18d1df1891ce2910c77a,0x6180065f8a3caf840a39,0x97c202b7db4c3a5caaca,0x8d7914a3135b02d2526,0xeb50414e248e33c41162,0xdcd6e261d1dd06165258,0xbc01b3460127c42a9c4b,0xb0d38602d6134aa1ac5d,0x94c31ea85abf1f0af7e,0xa4317760203b4710060f,0x9bb859051389bbfd3b83,0x394be513880387f40b38,0x98a34989d31135b4d89d,0xa353fa89a300fadc5cbb,0x86b34f5154f888ff7a4,0x3e6cf4e200001c7faf] j)))
def moH10 := page #[4329575424,0x60000008400028a00000,0x23001034000000010780,0x20a800000824006,0x1a640000000000000000,262912,0x20e000000000004240,0,0x12180000000000000,0x4050003ec0000,0x246000000000000000,0xca00000145a9d000,0x10ecd200000,0xcea003976e10000000,0x3015c08861000000000,0x10200000000000000000,0x20000103c0000000,0x856000003890000260,0xb4000000000001,0x120c8400000000,0x850000000000000000,0x122607000000000000,0x44d83800000000000,0x51015200149e0400000,0x744140f80064b0000000,0x4049603980000000242e,0,0x60b0000027d00000,68550656,0x21b00000000000000000,0,0x2e00000000c0c0000046,0x680000000000000000c,0xc800658198000cf000,0,110738]
def moD11 (j : Nat) : Nat := (if j<721 then (if j<309 then (if j<103 then page #[0x54810649520418254810,0x41a35481065d5204193,0x6498204153608106a552,0x60810651820419360810,0x41a56081068d8204195,0x6a192041a5648106a582,0x54c2064d53081a564c10,0x81a854c206855308198,0x64d8108153604206a553,0x644206a581081a360420,0xc152604306859808153,0x659810c1926043064581,0x60430689810c19760430,0x44130481106a1910c1a9,0x54920441514811054120,0x48110601204415348110,0x44193481106152044183,0x68d20441984811065520,0x4c1106a120441a548110,0x441534c1105493044131,0x60930441814c11060130,0x4c9102a532441a54c110,0x441a54c9106553244185,0x2a55244182541106a532,0x5491060d524418254910,0x441a3549106815244193,0x54d8044152601104c580,0x60910689804419360110,0x441936091054d82440a9,0x68582441a06091065582,0x6091069582441a360910,0x441a960d102a583441a9,0x68993441a36491060d92,0x24d2025493481a564d10,0x481a124d206609348195,0x69c93481a624d2069493,0x4c12025530481a824d20,0x480a84c1202953048098,0x54530481314c1202a530,0x4c12054d30481524c120,0x481824c1206053048180,0x66130481954c12064530,0x4c12068930481a14c120,0x480954c5206a130481a5,0x55131480a94c52029531,0x4c52065531481944c520,0x481a94c52069531481a0,0x61141481735052054d41,0x50520651414818750520,0x481a7505206614148195,0x695434819550d2061143,0x54d2065153480a954d20,0x481a954d2068553481a0,0x54570481425c12050570,0x5c12055170481535c120,0x481845c1205cd7048171,0x61173481985c12064d70,0x5d12066174481935cd20,0x481a2601204c580481a8,0x54d81480a96052024d81,0x6112068d814819360520,0x48198611206558448187,0x54d91480986452024d91,0x64d20295934809864d20,0x4819564d2061d93480a8,0x66194481a564d2065d93,0x6612068598480a366120,0x4c19524530648914c1a4,0x694914c1a22453066091,0x605302a5814c09260530,0x4c1a060530649814c152,0x2a1914c0a56453028991,0x505602a5415819264530,0x581735056058d4158142,0x5c570581635c16059542,0x7f17f69573581425c560,0xdfd5fe7ff3fe9fbc7fe3,0xdff5ffaff57f6bf75f7a,0xbfb5fbefdd7bfbdf5dfe,0xefff7febfedfeeff57f7,0xbcfbe7bf3bf9bfcbfe3f,0xdf77fb7fcffe7fb3fb9f,0xffe7f73ef7ffbfedfdef,0x76fbafdbfeddf5ffaf7c,0xdf7efb77cfbdfdebeeff,0xfbfbbffdfeefef7efbf5,0xff7ffbf7debed5f3ff7f,0xd7f63faffd3fe97efff5,0xdffeeff57f7ffbdfdbfe,0xfc7fdffedff5ffa7fcff,0x407ffeffefff3ff7ffaf,0x536894a913012e87c017,0x2ba47016da200b6ced1d,0x3265401a32800d993008,0x1533000b597005ecb00,0x281a30112dc80206a4,0xb5023ed4011f68c09035,0xcca021f6e808137404c5,0x2068c1cdb2e087196043,0x28fb741009ba083ed184,0xa1679940b3add05326c8,0x980b36cb859c6582ceb2,55581801] j else (if j<206 then page #[0x421b81012d987896e039,0x1304dd091a6a04811742,0x88d1a6606013742e7d93,0x694750b443a09ba1a14d,0xe32c4209ba1e40d10f21,0xf2d5327aed9131b65c84,0x3b04da9c826e4e1cb264,0xaa5026cd2813667e09ba,0x6c94c11749a08ba4c04d,0xe34cb409ba5938d32c82,0x26d985f38cc2f1b69d68,0x631edb30916d1849b66c,0xcb3936d59a9b02cc55b2,0x661ac5b72d5215368165,0x136aec88ba6f6e59b7ab,0x19b77638db3b076d9d8,0x87045cc2022e5ec1174f,0xb44076da2013631008b9,0x2ea4612e71d3d428d38d,0x3b6d4a09b39e045ccd04,0x41db6b004dd56066de94,0xc004d95c836cedc41676,0x4e1026cf0413658209ba,0x64c0262a60070a9c33c5,0xd37200e9a9004ed1803a,0x4e9b80174d400ba68c05,0x270d401236a009c3460,0xd01236e808637404cdb5,0x6a411832c08d5940470d,0x1b660a8db9040adc0223,0xcd5940670c983052e819,0x774a983a36a419732e0,0x1843a6d41dd34a0ee9a3,0x6e821c36a10e1a50870d,0x997414d5a50970dd040c,0x4cdb30a74d9053369429,0xb66dd05236e82863741,0xb05b36542d1b2a16d594,0x6a42d633016b9970b60c,0x732e18c1960c46dc85a3,0xa8db30d46d4862c66031,0xe74d407236a0391b6a1,0xa87ba6cc3dd3701ce9b3,0x6a045c37020e1b21074d,0x1b742431ba1258d40938,0x68da91346cc09b864c4d,0x1546dc8a236a4511b722,0xc0b3864c591b702a8db1,0x6e458bb622c8da91658c,0x63742e8da5170add0b0c,0x8da91858cc0c236e85c,0x1a76d88d236cc651b723,0x98da36e86863743431b8,0x6e8711b5238c1961c18d,0xdb4a3aeda21d76a90e85,0xc31ba1e46d28f3a68879,0x215ccb90ae6e8811b743,0x911a36c8891b72428da9,0x66092aaa64961522418d,0xe3264a61b52450d4123c,0xd68ba2650d412bc66095,0x26b4d1935a64c9ad3064,0x193cc54c9ed3744d69b3,0x6609ec3264ee99327b0c,0x3b504f61a327b0cc13ba,0xf61b827b0d993d86a09d,0x28aac194586e49dd3724,0xc940c6e4a0c370513585,0x548a4c3745015ba2830d,0xc3745461b92a78c994d8,0x8f1852c30dd15986e4ac,0x2c46d2963c660b1e32a5,0xa963c6a0b11b5058f1a5,0x660b5e3705831b82c78d,0x1b3060a1a82f18da973c,0x415b3310adc18286a0c1,0x3392a999946d4c9c3306,0xc9a38660d1c1726831b9,0x604d6aaa66b55313570d,0x2b62708cb93818dc9bbe,0x68da93a46dc9c056e0e0,0x3b0add1da36a4ed1b507,0xc1e232e4f11b747631ba,0x6d4f51b72788da93c46c,0xd32681315340745ca023,0x230b94174dca03a6a501,0x4246d4a1232e90863728,0xca2236a50d1b748431ba,0x6c92029748e8da944185,0x636a948da94a18dca48c,0x88da94b0a5d25a32a52c,0x4c46d4a6232e93029749,0xd26a36a5351b749831ba,0x6a53919529c8dba4d18d,0x1952a28da9504654a7a3,0x88db35246d4a88c2e545,0x5646d2ab0c6e5551b64a,0x42c236a15d1b4aae8da8,0x69d692b4cb48da55a46d,0x1b50b631b85a46d42d24,0xc8d985d46cc2e2365571,0x6178cc30a46617d2b30b,0x62c2a1a1] j else page #[0x1a16230dc30986cd84c3,0x30dab1186cd88c362c4a,0x2186e18cc364c661b163,0x194c36ac861b26430d8b,0x6acd54a566aa4ab3186e,0x95266aa5cb3382e59aa9,0x70cc33556559aa302cd4,0x3556d598a36acd55a566,0xd9de172ce60b967aadcb,0x30cf359567b4c0b3d554,0x1b967aad9b3d86c99de3,0xb0543458261a0c374ce6,0x44954da2c174d160a968,0x1a2c330d149536898a9b,0x66d059b168b0d834586a,0x1ba684edd34056e9a2c3,0xaa5cb4b82e5a6a952d36,0x4d56c9a6ab62d355b069,0x5aaaa62d555b96918dcb,0x72d630b96b30d9353e60,0x9826baaa9b5d8549acc1,0x30dcb5be661ad6330d6f,0x6a8685b1e330d861ba6b,0x9b9e330db55536db0a93,0x6adf54b36f78cc37282e,0x1b36f78d8b7a82e9bde1,0x785cb8282a1c1414ae0f,0x83c661c2aaa6e1615270,0x5c9e330e2a1a87050d2b,0x72e6a0a97350d4393c2e,0x1b3742ed8ba236a5d1e1,0xadd3a106d9d09368e85,0xa966c9d4c360ea8da975,0x5d8636aec8da97618dcb,0x50f031b87620db3b236d,0xda9790a5d3ca32a5e51b,0x50543d28295e82b74f28,0xd5564de94152f48ca97a,0x5ed1952f6a1a87a50d2b,0x52f68d987b465cbd8c2e,0x1b97d6a5a3e236e5ed1b,0x6acac08c6e601ab2afe3,0x1a36ea086371048cba82,0x21863630cd59585465d4,0x63108da98846dd430c6e,0xca98a46d4c4906da2063,0x185cc5a32a62d1b53148,0x6c35ce35a969188da98b,0x23ac2a71c61b38da0c24,0x612135549030dc47d866,0xd8492a0c248986e640c3,0x86c9c9c36124e1b27250,0xabc662561aeb2a61b994,0x65863632c61b89530d8c,0x2f30b9879818d9cb186c,0xb99b18d8cc8c6e26173,0x58cc4e856c6702975363,0xe8e6de74bb633a8da99d,0x67c2b673c15ba9d1adc4,0x5340b198a04654d00c2e,0x198a246d4d08c2e6851b,0x18d8d1a32ea8d1b5344b,0x30c6e294636b4a8dbaa3,0x6a11b4b5031b9a718d9d,0x735614baab18dad40c6c,0x1b1af46d456a3686b463,0x20db580c6c6c11b4f603,0x8a368ec519476239b7b0,0xacd1b4f6450b3b246d25,0x4b688da8b346d2d9a368,0xd95b646d45aa36a2d11b,0x4cd9dba3662dd1b316c8,0xc856eae06b71708da9b8,0x6ec2975768ca9ba46d4d,0x638a8ca9c48ab2e1236a,0x163c720d8e3405cf1883,0xad864a36632602cb8f0,0xb3d6542deb7414f5b30a,0x69eb6a2ef5a5177adc8,0x5238f5ba1a7adc0d3d6a,0x5b827b2d993bd6d479eb,0x7acc145c2e8a2e172516,0x45c6a0a14b5051719828,0x4a2e3705065b828b8d81,0x7450a5ba28b8dc943d6e,0x1a52ab8ca955c54ca6e3,0xb8dd155c6e4aae36a557,0x65c6e8aee3725771b32b,0x8cab2a46571852fb8c29,0x6266f59833b2c119d660,0x5ba337adc99996e0cccb,0xacdc1a566c8d2b36268a,0xb996c8d9fb046d715235,0x4dee3606ea5a537aca99,0x3076f5a93a52dd1bbd6e,0x5b83b7ad49da96a0edeb,0x7acc1e3d6e8eccb7476f,0xf296e4f14b7078a5a93c,0x501eb727c65b33eb8d81,0x528165a340b2c9a0592e,0x5b340b2d8a0596c102cb,0x7ad4a0a96a506cb72816,0x84f5b941] j)) else (if j<515 then (if j<412 then page #[0x8427ad4a13d6a109eb30,0xa9a1bd6e908cb7484f5b,0xd6610deb26876582439c,0x14b5088a5a84352d1a1b,0x8d39534652d122a96a51,0x34632d8a35c6c119eb26,0xdd23dc6c11d4b748c65b,0x96c92d4b529665b54a52,0x1eb4a98f5954c52dd25d,0x9af4a94d32dd263d6a53,0xa4d7ad9a6bd6a535e974,0xc9a73d2e539eb749a65b,0x9695394b469ca5a14e7a,0xd4b469ef5934f32d8a72,0xa0a5a5507acaa8296953,0x9557acaaaa96a5454b52,0xcc2ea96a1694b74aaf5b,0xd6559adb02cca5b16052,0xee364cf718267b84c33b,0xd164b868b8dc33dc6cd9,0x368b2d8b429685a2b2a6,0xd8b4d96e1a2cb66d065b,0xc4c5aab370d359b269ac,0xee12ad771826ab8c0b55,0xd765526bb854b5dc295a,0x86bb8cab5bf609aeb2a6,0xd2b5dc689aee330d6f59,0x96c9aee360d771a86bb8,0xccb6ad771b36bb8d9359,0xd771b96b7adcb5dc6d5a,0x56c52d0b65654db2e374,0x5c375c2a1bae130dca5a,0x96e1d4cb70e8f59874b8,0x54b50eef5957732dabb1,0xf6a4b87b7acc3d3d261e,0x77e7adcbebd655f5eb30,0xcc4051655fe8b0eff118,0x165615e97104a5a3807a,0x94b4314f5a98932d8c45,0x1665b28a52d3c52968a2,0x38da25a46296a62de973,0xd8485c64e42e30921715,0x461e5ee3312971b990b8,0xccb6b3771b09b88c3cc4,0x3a65b59d7acacebd6e66,0x99fb6d8cfa96a67ccb71,0xd4d03d66281eb2b40f5b,0x96c6914b5344fd98a27a,0xdeb314ef593a77a5cd39,0x5265b5a852dd53bd6e69,0x1ab7acc55996d6a8cb71,0x54563d262b14b5156a5a,0x96d6d8cb6b60a4a8ae7a,0x14b4b70f595b852d95ba,0x7065b8b832dadc196c6e,0x9bb7ad4dd196cae4cb75,0xd4ddbd656eed96376f4a,0x968af149457865babb7a,0x4cb6778a5a5bc52d1de2,0x8465b5bf32dc5f196d6f,0x5c88cb1e44461f128b0f,0x228012c0002230f91196,0x838065c0530041003440,0xd980ca40bcc0a5409640,0x3bc129c112010300ef80,0x970182c170815fc14d01,0xed41db01c8c1b941a641,0x4882378224c210c1fe81,0x9882894278426c8259c2,0xe742d6c2c782b742a7c2,0x404331431c430902f8c2,0x9d038a837583640350c3,0x3e803d6c3c1c3ac83,0x56444684378423c41284,0xac849d84884478c466c4,0xf744ea04dd84cc44ba84,0x4e453e852dc51bc50c84,0xb2459fc58a8577056005,0x158602c5f005d9c5c485,0x6e865a864d4639062446,0xd406bd46a0c6930681c6,0x308724c719070206ef06,0x9e078807718750473fc7,0x1a880847eec7d3c7b607,0x6e8861c852883e482ec8,0xbf88b208a2c892088288,0xc08fe08f008e0c8d288,0x564949c936c925c91909,0xae899ac9850975c965c9,0x489f3c9e849da49bf89,0x4a0a3a4a2d4a1eca144a,0x958a810a72ca650a554a,0xe10acb8abecab24aa14a,0x27cb180b0b4afdcaf10a,0x674b5b8b4e8b3f0b338b,0xac4b9f4b900b80cb754b,0xf24be18bd38bc88bba8b,0x36cc2b4c1bcc0d8bff0b,0x780c6c0c5e8c52cc470c,0xc48cb44ca50c920c850c,0x204d108cfeccec8cd6cc,0x734d634d544d42cd330d,0x948d82cd] j else page #[0xe9cdd2cdc28db18da2cd,0x3f0e2fce1f8e114dfd0d,0x8c8e7c0e6c8e5ace4d0e,0xe30ecdcebc0eadce9f8e,0x3e4f260f164f05cef80e,0x8e8f7b4f694f584f4d0f,0xdf8fcc8fb2cfa0cf97cf,0x38d029901950068ff34f,0x7e107210659056904dd0,0xcd90b890a75097508750,0x1f910e90fa90eed0da50,0x5e914cd140d134512a51,0xb391a1918fd17b517051,0xf691ee11e4d1d411c411,0x455231522a9213d20b91,0xaed2991280d26f525c92,0xfb52ea12da92cc12bc52,0x61d34d9335131f930c52,0xc693b493a2538cd372d3,0x1c540cd3f553e653d753,0x6fd45c14495436142a94,0xc7d4b354995489947d54,0x1b950cd4fa14eb14da14,0x79556bd5569540552b15,0xd495be55afd59a158b15,0x285616560795f655e315,0x7c166c16581649d63ad6,0xca16bc96af569a168dd6,0x139702d6f656ea56d796,0x63d7561749d734572417,0xb397a497965786177617,0xf657e4d7d917cf17c2d7,0x5518421831d819d807d7,0xac189e588f187b986698,0x558f4d8e4d8d318c198,0x4dd94399371927991719,0x89597e1970d9635959d9,0xc919bc59ad999f5993d9,0xada0459f919e8d9dd59,0x529a47da399a299a199a,0xb2da9dda965a7e1a641a,0x2daec1adadacc9ac11a,0x45db385b2b1b1b1b119b,0x9b1b915b7a1b691b5bdb,0xf59be89bd69bbf5baedb,0x489c391c2c9c211c0bdb,0x975c881c7ddc655c565c,0xdbdcd21cc49cb65ca91c,0x27dd171d0c9d015ced9c,0x7add6a9d5c5d469d375d,0xb69dac5d9e5d921d86dd,0x8ddf71deb1dda1dc85d,0x58de471e395e259e195e,0xb31ea39e8f5e7b1e679e,0x7def7dee45ed45ebf1e,0x609f4fdf421f311f19df,0xb2df9e1f8d9f7bdf70df,0xee0015ff01fd35fc21f,0x6ae05c6046a036602660,0xb3a0a22093e086a075a0,0x1ca10760ef20de60cae0,0x76616561566144212ce1,0xdca1c961b8e1a1e19061,0x372229e219e20a61f3a1,0x95e282626b225ca24aa2,0xf7a2e4a2cd22bbe2a962,0x51e33c232be315e307e2,0xb4239a638e6375a363e3,0x7a3f5a3e7e3da63c623,0x5ea44f643ee42e641f24,0xb1249e648f647e246de4,0x13e502a4ece4e164c2e4,0x6f6561654be53b252865,0xd925c3e5a96591e58225,0x336626a615a603e5eb25,0x91e67b2665e655663f66,0xfea6e7a6d4a6bf66aa26,0x67a7552741a72be71326,0xbba7a2e78f677f276fa7,0xea7f2e7e9a7d6e7c8a7,0xb1688ee86c684ea82668,0xf8a8ede8e4e8dca8bd68,0x30e928a91f6910e90368,0x6c6962e959a9476936e9,0x942988697e6973e970a9,0xc169b469b029a3e998a9,0xf8e9eda9de29d629c9e9,0x1baa176a122a086a0429,0x4d6a43aa37ea286a242a,0x8a2a7daa71ea62ea596a,0xbceab4eaabaaa5aa97ea,0xf66ae9eae02ad56acdaa,0x2deb1f6b13ab0b6afeaa,0x5eeb556b496b3e2b346b,0x922b86ab7c6b732b6a2b,0xc0abb3ebadeba9eb9feb,0xeaabe4ebdcebd3ebca6b,0x332c276c162c042bf56b,0x766c65ec5aec4dec3f6c,0xb1aca5ec9a2c8e2c822c,0xeface12cd82ccbacc2ac,0x302d24ed17ed0aacfd6c,0x3ded39ad] j) else (if j<618 then page #[0x70ed652d5aad50ad486d,0x956d8cad8aad852d7aed,0xb82daf2dab6da6ed9e2d,0xe4eddaadd4adc9adc06d,0x156e0d6e01edfc2defed,0x47ee3f6e352e2a6e1e6e,0x77ae72ae65ae5aee4eae,0x9fee956e912e8d6e836e,0xddeed3aec7eeb8aeaa6e,0x18ef072efe6ef5eeebee,0x592f4baf412f32ef296f,0x96ef85ef78ef6f6f646f,0xd6efcc2fbd2fae2fa26f,0xa3002aff46fecefe36f,0x407034302ab0213018b0,0x76306a705fb054f04cb0,0xb330a4b098b0913082f0,0xeef0deb0d4b0c630bc30,0x30b126b1163107f0f970,0x62f15771537149313e31,0x9c31923185f177716d71,0xdc71d171c0b1b031a631,0x10b20531f5f1efb1e531,0x5b724a723a322f3220f2,0x9ff28f727d7271f265f2,0xcf32c7b2be32b932ae32,0xfb72ef72e6b2ddf2d372,0x33f3287319f30f330472,0x65335c73513345733cb3,0xa7f39a338e3381737433,0xf333e373d673ca33b7f3,0x2cf4247416340533fc73,0x72b4653454f448b439f4,0xb634a77498b48bf47e34,0x600ee03f0034d934c874,0xe840033c13e06e82781,0x8e06f02782002f80101,0x1ad00407201f0178079c,0x8fe06d0d0118c074110,0xc0c6870071603b015818,0x2c0803ca02b014c04e02,0xcc0db823813a08a07981,0x2807ac0ce00814806fc2,0x30701d03346403eb0418,0x8fe824a0ad1481d343bc,0x7c303505302ca02011e,0xe10701e80f0348198084,0x620ae137055802c12013,0xd714386982602f70400d,0x1ec2260430100f182d02,0x7e13682d422d0248298,0x854403501d82805008be,0x205190c107811e19b06c,0x3407825814409cc0ac02,0x650460e9054402039508,0x16c0ac25c15e05283701,0x15015604b044c16a2da8,0x15c1560c03099cc0778,0xb6a24601701807f6031,0x825645cc14d01502a866,0xec31213c180404e05057,0x2080d4180a621df0178d,0x63426619d0ea406428c1,0x3d01e782342bd02f1568,0x16b845c3bd13f0894250,0xd0348081374156088830,0x3063c5106dd0b40e346a,0x6b0d02a781804ba41608,0x18818e0c601e831408a0,0xac1b610380d03a41403,0x2901e30ace0a4a65015a,0x61dd2a28bb0a3c58a321,0x297809c02c050014c19,0x60064201418f20ce04,0xf0225c87445312e9b4c1,0xb0088c1a039586943483,0x3f20ad07749800100328,0x541a6e062a08d04e0910,0x605316f0aa89404a0325,0x41ba0de145403e06d045,0x303a8a6a8ada62043e92,0xbe89ac20616d19e8ba42,0x578226a781d307523db1,0x3fd84d653811ea00015a,0x4d308fb05423b85d06d0,0xc2360ca890902d24d097,0xeab954b840d0d0a1c08b,0xc836790225c43ae2e240,0xcc104215e30826a10008,0x3b02aa57a0d807801701,0x49c0e7900ca5ecaf649b,0x81063390b80e808281c3,0xf151418007c03022680c,0x335f2a854280f3d17023,0x208b902d08b410040ae7,0x1d60021ef40f2d543290,0x45243925972739db00ce,0x66dc2521c60774448340,0x85651884f2c69112e0e3,0xca543267c1825c150800,0x8e1630c9455e20c1040a,0x5692f6205103856c2ba2,75515393] j else page #[0xd6480dc3a29c94e8caa2,0x8046995f417acc0a8c12,0xbac9da5f825415ad0832,0x530abca80dc2024961d8,0x490e1a9ce2985516461,0x4aa09bd1bc26c0a46127,0x70610ef04da01059a0ba,0xe82041b1d2297606508e,0xbaa644100cf848124f0c,0x868b420300b9c12aed57,0x2244390ac83a0b4613f4,0xd4413bb2a6a074262594,0xa4290882ce6e2b049af0,0x18612542669222800744,0xa299404a0540b3629b2c,0x119f140809fa0589342a,0xf47208a066724352fca,0x65219d0c20d1a2ce6553,0xa0b54f1868c92a590278,0xc40989a8a44130128218,0xac770dbb0e988aca308a,0x562e81df01821acaf9a1,0xf21bc0cb824edc45020d,0x27e964372130b2659b29,0x15da8417e86b00d002b4,0xb5b846ce1a74c0b28590,0x337cd700182f82ad680,0xa0d0868036da4c0aa867,0x324af23f94048764d815,0x412d705bdca70ae48149,0x19e0ee4b4e0531558b0c,0xc5140a550600a4114074,0x10582254ba04d350509a,0x80c401b2af091e4ab24c,0xb2ed5a84ad269a10264,0x2882d23cd3b24b6c8215,0x5d260481e4240aeb34e4,0x1e853127ec82050e13d0,0x96605aee14c4f20204e4,0x691c41821b2b30235249,0xc37d18b8c3a4c372642b,0x8a4dc04833b4cad03616,0x96536a989caf02b74249,0x6fc27019583ceb0e6f1a,0x69fb1491a06b680103d8,0x621826337a401db46d3d,0xc879c475872cc54861dc,0xfdc843522ae985ac2dc5,0xbfa9d3bc93665c7663b2,0x4651f6925430a06d14e9,0x9d74cad9029b96154b1a,0xb705b4318cb2658b1f6,0x12c6cd2d7b4b844e013a,0x245223e11f0c409e26d,0xe82bc08a855c3c902216,0x70c46a21c15a1690dd0a,0xb0dcdb20999484d18d44,0x7bc2b06cd04877e34c9,0xa22610f3076771be09a9,0xf4a36281b80cbfc92ca5,0x688aaf51089a7e2b4461,0x2cf0ac3c6b3ffef49818,0xcdaa9841040d4000588e,0xb5057e8461804695eff7,0xc35500159df4b57304a4,0x4002affb8456e606517e,0x1d70006bfabed0,0xfee64960b8a614448000,0x6ac2becd3c28f05da5df,0x4fff7b0f241a442831c,0x48331b3dc9d728f06680,0x48850644d576fc5c4192,0xd246484555fff8587483,0xe3698e0d26ff0b2e24c4,0xc30d16c21813599f26c9,0x85b48c07897bfba681f5,0x985c0ac0889e7f3b349,0xff0630a6d180f128f824,0x7fd31e2db8ac086997e1,0xa8f387a4362dba620351,0x26fe6e0e80985c0ac408,0x301e2630e28d34d3810d,0x24857189ffec03840cba,0x105910c74a9f5e3b6c19,0x828b3b158eb1376ca354,0x5505166723216245edea,0x7b7aa0a2cec563ac4e3e,0x78cbe1d0580da2c048a1,0x53ecfd1552810ec05892,0xe5453fe9eb08074592c4,0x2c75893a97e189623419,0x1bcce2025ff0f84591a,0xff0f8458caecf62007cf,0x143ab04bef4848c76225,0x9b232287c7b397dcd919,0x6672e888c6a9f1ead5cd,0x753016c8f53731d365ec,0x8ea0083fb1e89b4e5aa,0x6ac1aa701efec7bb51ab,0x449132a251401dfdaabd,0x121a8c862a4004737a7,0xbc0baa869f8ff8000df,0x8623acac] j))) else (if j<1030 then (if j<824 then page #[0x1aa78a91420645fe0755,0xc8d55d5167fba407df79,0x428e690ad559eef24cc7,0x79cca93c4d1d5ed34f31,0x384bf99398c0fe0d53df,0xec032029fe59bd480b9f,0xb94660208213a9008f01,0x7fba902108c883bfff36,0x2945081041052b564ff9,0x2e8110840b13f7f5bd2f,0xeb8d81020436382dffd6,0x1279d0110002208a99fd,0x441ffe9cec10c2d30bff,0x421622181dfc0910842c,0xb082087a827c04f47688,0x8e0082085a78b4bfe6e3,0x84759c60820882a76f11,0x4e853229c3a46351ffd0,0x4d35421e688e99808d34,0xf0007b1f4e37c13998b4,0x33072f764316f60faf04,0x52ab0038ac8204b4de9,0x343f5fb7891d87401060,0x421da847fffa9ce380,0xbc84e034a7d3f99ec06f,0x7eda64318064455a191f,0x6fbf8b13086300d22412,0x27fc4998490c3007154,0xfa3e2f60021806f14379,0xe334e5e4250400254fb9,0xdffa442718c0848943ff,0xdf89f4404861802ea31e,0xf8b8367402430c049d56,0x8ad92cab98248065aadb,0x33e2b52d5ccc6b50a7fe,0xf89a5132260453bc8e3f,0x8ea4ed0e952eb0165354,0xd52001c7e47c1e3cfe00,0xa192f81d2e4851049000,0xf76001bd4dbf2cb0e406,0x2d2c0025481568666752,0x49362631c702ef4034bc,0x1fb99d61a298b0b59b44,0x82438985abe198082ae5,0xe5b41008ea802bc0000b,0x1f01975a011e00017f2b,0xde00000067ede027c,0x5447ac17ff9659600655,0x4785d0f2b9d1a0602f,0x8c00de416e990d1d9c80,0x4301af765601653a1755,0x1e456ffc5762a0c9aba7,0xe7f0c8deac7711925807,0x90c0b83a550010fffc00,0xa0a42d549781e603557f,0x9c435697fdd1e9c2e23c,0x5e97bdf4b20be051c706,0xc0fb01e81d79fc990071,0x7f1010b039ad00000043,0x421ac000018f0bede85c,0x7be2ff9cccb27,0x4b5c685b01fc40745aa0,0x72bf6341ad3186b06045,0x3022a4efceb24428306a,0x181d395fb1a0d7a0cd44,0xf0e82b0367d3f4c05005,0xeb568b700208600d484b,0x11aff779a602981c391f,0x3038857fe6c2aa80a677,0xc657460b0d2f17948c05,0xd072a4d011019d642bfc,0x168c32bce2aa192d366f,0xf4b80b4cdfb4bfec1130,0x2fb79180a6070f570016,0xc5604cec1b7f2b6604cf,0x3c364f1b4c016a2e37f2,0x9f02fca4dac8c058a6c2,0x8c062393fcc1130167b6,0x6ca2a32ac697d85dd010,0x7fb6928ba322a729ee86,0xecff240f5966c980917f,0x8584e2d8f69a084a9e60,0xd1f5212d029d1955455f,0xbd99c680194412860256,0x182293908ca61f2fed62,0x405333880ff6bcaca99b,0x1ad005191d3809fff755,0x321a6e8740ac0d9bcfe2,0x2d3f44ca59d8fc28083d,0xbe7f10d68028c0e9e83,0xc04f90c77195f0c8c605,0x5b3f8080146074c3bef5,0xc98491413facb27831cc,0x9595337bfef678dc5839,0xfd7f6b85d4c8e203fa53,0x332677bf10028c0e941c,0xae288d06245536689fd7,0x4b40146674f27b0a7c13,0xc52c513fcd604ce07fca,0xf50ac8d9e17d924e804b,0xf7c9f685a24653119a27,0xead581330473faa16066,0xc454c1df] j else (if j<927 then page #[0xadba98d436dff9ce6200,0xca61e80d71e18cc373c0,0xff6bcaca99b182293908,0x650faf07fcbca6332870,0x66c8c061b5e0ff9794c6,0x3b3969e0a14c0a1d5fb9,0x2e190c2e057edede990b,0x53a4ffe9b4c18562ebed,0x1e66198ff008f0105191,0xf67acc0c550e0f2cf7e,0x918767db29f45350c3b3,0x276fa46161fb67d93f9e,0xa7773e803d7ce63a7e59,0xd9f76918514d93a79a30,0x234bcc35af2b42c43e95,0x7967f4d230c36acda8d,0xca2b14cfbc7e54d330c0,0x232950feb71fdc7b50c8,0x5d0804650a20dfe2e840,0xaabf77c44cac244cbf94,0xffa647f110115638bf6a,0xaabf77c44ca9244f3fd0,0xafc5608e280ca95c7f6a,0xc6265ffdc91c44310c42,0xc27104978ff0791a2b60,0xe41953089b7cd2dbd1ba,0x8cc6a218661fdf145d0d,0x9f67e48e221886209ff,0xc0cc765de2dfa9818ea2,0xebb48c3a8fc102d40050,0x5013fd1a69187d42dece,0x3a9d8b266d0155c9d401,0x284ab62e7d6b58e744ed,0xa81bcd809a3416b1c659,0xd53878de6cbd8d6c6aa2,0x61d4e5b3f182a58c344e,0x4c8310d3f3d71f336186,0xd56005a60ac6abfd8f8f,0x30fe7ad008cb9234d13d,0x1d604a0a84618f99b0c3,0x7a0a7c646633dfe6116c,0x5e60be880b6c154fc3cc,0x59e2145ccca40d51854e,0x8619876b8d98268308d3,0x9f88412a8113cf5c7ccd,0x2f2e410842038bf78e6e,0xf9b6085040354ed102bf,0x1a7648a1030f57024000,0x20d01bfd72e4509188f5,0x40356067fc510b80206,0x980bbe6fd1f6651054c0,0xc01230ae7479de600246,0xfff1408c2082d29ddfd9,0x25fa7aba70421088226e,0x372fd45e961c40302372,0xea8dec5c8a4613e1e41a,0x217acd3f88c758e40608,0xdffdee25a8886cc20208,0x4b93f6d1620842108455,0x51e0ddab0c390c212145,0x4cbf172f2790861080a2,0xa215f07f50c390c21214,0xa4423423ddfdc8218420,0x110608212aaafffcb231,0x41c3369527bb89d5680e,0x845c3730fb10cb08464,0x8c8821f7e3030c8fd40b,0x516202082969f6a36916,0x9efe26c202082ae9e4ff,0xc5c7fd784b60800811a,0xa43305be2f4de0880010,0xc40008062c7f153de840,0x8b7808167173949ba0f5,0xeb5767c0830410154c78,0x5df265111085040d451f,0x3d74a205963e669440b3,0xbd091471fb99ef420522,0xfc9b281000207891fb5f,0x1fe2805019c0100c4b81,0x806a67af1a2a051e,0x380201890bffd0f5d202,0x81041041d42be4e29203,0x8803085040d3a5fce9d8,0x4ff805019c010310f7fc,0x14677affef2084210711,0x100c5cf7a1028abc68a8,0x14b2330520fa328f8800,0xe99c7508000231aa2fa5,0x8062f7a14a245ffc5e,0x806af9e3cb42f35c40,0xa4481fdcc0b6e03d4200,0x6231e5f76ebbb3d78610,0x8210abf9f7412611c61,0x317e7fdbfd0a364ca282,0x707ff756402782200040,0x4d420622d283f2210858,0x2adb86a1050eceee2467,0x5076602e5bf0040d3b3f,0x20a9eaf301739f1c0103,0x82080ea64fe055b5d818,0xa00100d4c1ead2022c20,0x40356065e069ffeab0,0x701ea100] j else page #[0xb8800100c5adfff13213,0x98500081a7b64c79681e,0x47608000230acdbffad4,0x2088b0bfd0fa0b21ca,0x806245d5b7f2fbf0610,0x100c4abddfaa374400,0x3141045544b1f922e0c8,0xfe4f90002061f8fa22c0,0xeae2ade37c2082729a5e,0xbc9024fa5d8182000088,0x2a1f83fdb9b622213692,0x7ca0040b373a24f32842,0xfd638cd3e041042b539b,0xded9fc09ffd488a05aa6,0x7203b68fc4210840314,0xdd6a5981f801eef18186,0xe4674e610846c40601ff,0x6948eae182000080ab3d,0x3b7840008162d6fff88c,0x8dd10002018917feaa51,0x32967ed44424d24f87fc,0x130fb327c8001030f9fe,0xda6e7fe46f63a2000443,0xb11109b48df945708209,0xcadac81044f521dfedcd,0x8fc40008062eeffe9f1c,0x4480100c5ab83c3f6bde,0xe210958697fda87b15f2,0x7eb302081024f1edfca6,0x55c97e02044217d1002e,0xabf30cf760acf040088f,0x95a2cbff56d48888668,0x2c3e3fa3c35793b78400,0x2000403158fe0fc20004,0xcc21080e275b3ec9bc3c,0x79fd120040c3f39c1b89,0x5bbef2e1c40008c62719,0x746eff0f514861180a27,0x10ae87c33e3fd8201108,0x44c200046314ce4a3c22,0x9de010412b4fef0fcdea,0xdde662261084471307ec,0xc4f529c7f0c888c66f7,0x22d9c083fffec937f401,0x1fd120048c307fb17522,0xc57987d02001034c6d,0x20520c8f661e2f08001,0x811e23f402052178aaf4,0x40c423ffd0a144000818,0x80010311affd54422000,0xc8c878010aa4df4fec28,0x2e292360865bfffec00a,0x1ea8f9eb1d2f00454d2e,0xa04d4e16df038466e0b0,0x2b29605d4f47e4b5612d,0xde77e4a6809698affb00,0x11444acc5e233781cc42,0xc19136086c125674dd64,0xbd8668f84d9981349ae5,0x4f2f06a18602ba8938fe,0xedfc20df048700ab1ecd,0xacb387f6b40060d233a8,0xfe3064b14134004180b1,0x1344cff06a18600da7d3,0x950afff46d0f3c31802b,0x135561fdad0710b4847,0x3cc55913f128a3d0c104,0x4454c693ffd6b6b10c60,0x3a98c0d21e4ffe95c70c,0x2c0a070e0e008d9308bd,0xf089c4a061156388f89b,0x3f66225c8a1c04d519bf,0x3a7abf03218284204a71,0x380eea06ffdd30418602,0xc30c0174f77c6e720c56,0xd2020c3011d3ddf13139,0x11b2a7ffc233046cd67f,0x46d7fc86300b850ff88d,0x7a23cbf48a61b7402c44,0xc113891fdbba0160567c,0x414746f12c8119927c60,0xc72b656608da27d78124,0x2e18effba90c3005d357,0x18431800316efe2918c0,0x41fc8c80a155fc7d96b2,0x70a8ffd9889c6300c88f,0x2018899c3912dfc8c601,0x51cc1100c403f18a3982,0xf1fb9c306005e32baffc,0x8ea4fb87d4a87006d300,0x12fa830601ae3d1fd218,0xa3e4e54431802d1bf3ee,0x12070031570ff5f3fec1,0x93860d6ff9ae7cc0f5d8,0xbfff6d18440088148a97,0x68f2ff0a08c320387f7a,0x1b9a43111536fe722709,0x57ff9d88030620ba763e,0xc1c964c58be610804316,0xa30be2f067284028757f,0x7eb3ac104238c3c09c21,0x3921bf867a3301cce02d,0xe26ff9b0] j)) else (if j<1236 then (if j<1133 then page #[0xfadc26a400c10805aa5f,0x74e1d03858b20668024f,0x435717fe6e63202440,0xd970ff4b554905bc3041,0xdee90c3002752de80580,0xc01bf68600aa7038d233,0xf524e1941860056a80d3,0x27c7a3c3103541dfe17f,0x458bfb91d990ec37dfde,0x77ff57974d2670086008,0xfe9710d2722918c0018c,0xd1010d28bfb8c60470b4,0xb0fea10ac601711772bd,0x88061c1f8c4dc1100c38,0x66506200aad5d7fe26e0,0x188ea4014fff2f2643a0,0x3f96901209026d2e7ce,0x2d107fb548039810806a,0x8881888e98bf36ce8a42,0x4e5f9b3246901b435f3b,0x89c1a0c032c789eec9bc,0x418280081cf6406ffdc,0x233079f0c488599e7fc1,0xa3338c601f119fa1890,0xc9c1ff2ec630168777fe,0x400e4dbfedea62888c61,0x1926b7f40c6406080010,0x8ec1100c42f53cc60f04,0x75dd71130414827fe099,0xcc91a406cf55e0312016,0xd99bf00ae212431a13e,0xf5860504100e3d27dd48,0xff08054608080f1d37f4,0xb0fdc4f8b129d05d10b3,0x30500438f0edfa340390,0x4aa16a03988b1fc8568e,0xc4c3023f50352171fbbf,0x69a1fff247f2542d4018,0x34080458e571a2f0300a,0xfc102f0018799f9ed69e,0xd0b9601c63c000d4fbdb,0xf4e0b485e4500a314b7f,0xf2255e1a57e015aa51ff,0x9574a27e42900753fdb9,0x73e008b938de3c102c3c,0xd080771907d486c8d50a,0xa0461e00c6a6f60067c8,0x980aa3c021c683ff0060,0xc7af18d13e20416ac1fb,0x155a10a000430450ab4f,0x5fff8e1d040574fc7f43,0x1888df553c780438a00,0xa018d383fe3c51005a0,0xb7c3c4582858bfaddcf1,0xd38dfd4dc39a99a006a8,0x6ce11437f536804ad002,0xda7675fabfc1251841,0xe201400310278454ba14,0xc71a39200c2bb5fdbffe,0xe2d6c7fe069f158b3064,0x6114d9dba3ded0a42460,0xf814c8a0001aa0f9b0fa,0x498ad10f1806be00417f,0xd262a94900ab18000f5f,0xb000484fc1e00025480f,0x423f8b11e01c8a9aeffe,0xa7cd8002d401d777c0ba,0x83e66887b4cd28002546,0x80298ebbf67cc64014c5,0x98c024d50055fc173b31,0x13c8b3e079d95c7bd4a,0x4829f7643e408c0af0c,0xd25000d1d17b4f50f8d5,0x10b245e5e2180dc66248,0xd5380ddd0f4b4b97c720,0x8071aafbe88785186ac,0x2d50b7fff7ac01c8a474,0x40a6218fed768adb66c0,0xe4e0500a69f93635eca4,0x2828421600deb18fe478,0x2dc1d9ab0fd9c36ffc40,0x808a1a61ca04fdb4aa36,0x2a751a701cb91b9cae65,0x1d7f82847232f0bae4ef,0xf90b0943b5574f100000,0x3080136569f022b3c1fa,0x5e3a9e97d5ddd0844d82,0x701cc015c67381855c71,0x69fcbc9ac8a589f220,0x478c7791822911002419,0x862818933d71b4081bf5,0xa9300a75400054ff9c6a,0x1e6723cf8057018ff955,0x793c8f980806be9210f,0x14096a0002f3233e7309,0x40eba9a82bc9ecfe2638,0xe92551ca155072337c16,0x742405480001fb5f2b1f,0x91b1d053d4e15ab03a13,0xe5bf42e399a6b3714fcc,0x8707ca338a908071aae2,0x3624afdf5a0ba5a700af,553706324] j else page #[0x103ca800af8777e0c715,0x4a4029a8082d0fa71449,0x15edc038d58da1e2e0d1,0xc027900bbfbd73f89830,0xa60ea8a6020ab003f358,0xb600598e57ffabeb1129,0x9b6080031600012fe2b8,0x1057560a1f1c07af7105,0xe3bbaa882b080287633d,0x15552ff9420d0d1400c,0x57ffabf73334c340240,0x86245f81d4e8120451,0x212cca2a7c75e076b1aa,0x58a346a00969daffe1ad,0xa7f399a5410060753e9b,0x80631237fc4302292023,0x5a500a6999f651e51c70,0xdca20c880062a2ff9a3,0x8677be01b04458fef9b8,0xf65a34f3b2e8097af59d,0x7603b1000000005bf73e,0x8119850ac0047c909ee7,0xf34d81aa0945420e7305,0x9fa9c0b2eb0074a983fb,0xe4fd4ea60240cea002bc,0xc38b4326c05805950015,0x7aa0dd170f10010071c9,0x212270fae910ac0aa9b6,0x805d4f0fd3d1914aecc8,0x8d0a0057ca6b87001e1d,0x201c6b000089fe248c02,0xcbfe0723a0565180e9a0,0x21fb5e4c0d03408081aa,0x6e7ed656300a48077505,0xdb1fcb6b027c50101035,0xfe9fe2b1a04032c74bfb,0x2dbff96c6339780cc41a,0xf90188a140faa544b0e5,0x6d4838a0c04001726987,0xec1d52ab48005a837f9b,0x32e7408e29608031aa2f,0x59bdc1919c509611947f,0x8b68e74e809aace7f0ca,0xc013252154573bc3c1cb,0x342b6622f2f77f424f38,0x31e31d4b3aadff474867,0xd09a5255b0055b3f218e,0xd94c55167e9f80d8cb38,0x82757057c7f97140ca1a,0xbffc093fd6c934138c7,0x9f665ffd219c8432388b,0x2037ece430069691d488,0xd500affd790c7168f501,0xd1745cb62c4458110d1,0x64f13f559a7169d4f6d5,0xbb24f639b59a72aa99ea,0xf8388ea597201a63c31a,0x1e2ce89cd78251e285ff,0x182b020a97df4bced0ad,0xd6c73e8c61e1c693a327,0x5fad03bde82ebbdfc83a,0xfe2f09bda83550000007,0x397f5516540000d3f006,0x3ffe004ba3823d56ff5e,0x4b4868d5700000000006,0x8fe00012dfd84e8c3,0x22a8d5fb26d4a090a6c4,0x509b1002fe00000002dd,0xe71a4551abea75282,0x30bfe679001bf80000,0x210dc449ea848006ebc0,0xacfecd18000047ff708f,0xd708ff6ca423f61c9a37,0xed82a07150e47725e527,0xc939d6a240c20e59d9d8,0x6a208ef1451baf147a70,0xf472b1ad7618a82c77ab,0x4226fce7840924412831,0x8f05dddba628477778e3,0x8112932b5e5f88659a0a,0xce844be670839312423d,0x58d110a5e9fd23a46e22,0xf37b1f2242954782f6c5,0x754ce119a590eec528e0,0xf07102218dbf5a788906,0x9c489d222c226216ce14,0xdf8786914783dbe18704,0x211ef251a8f045d10521,0x39eca5137204231b4c85,0xfd44b4420eff507049c4,0x49b8e12a3f44985b3911,0x869767618748bb088c78,0x6ad2ec824340529534dd,0x81a664bff645a3030d04,0xe1423d5b5115b1ca76e1,0xc388a77b2709a3f64f2,0x21629b6f325df43d4c3b,0xa560f081c9c701731435,0x2e43711a8e08599cd108,0x7d374a28ec71b14e081e,0xc18040b94040fd349262,0xca8b138e9708c2bcfa30,0x80898945] j) else (if j<1339 then page #[0x70fbbad570b1b91e6e39,0x983ff9212cc479f7470,0x938eb78a0c987cfe5331,0x8ba217c4647623f7d401,0x8b2c46a421f785404203,0x5fe182a5f9b0c2b9c183,0x4c8a13a4bd0e65225fd2,0x63f2283e7bd52784765f,0x714662684246279bda27,0x15b00d8ec3ffd04cf060,0xfc56e739101bf514d8d0,0xa0307f301a713947fcf5,0x8e282369bdffcd663070,0x48bbbf49a188a51bfef8,0x11c20e08c6f5e181024c,0x4b55fcbbb6219877fe05,0x649943094ac704d94309,0x44848676bc3489090d76,0xfdc3a0242390d3bb5e1a,0x9532c8d2b377ae14251f,0xd07314dc6121e34777b3,0x7ee882e0c0e2f1dbd881,0x88c5285fc6284c44e97d,0x9b1ce5c181c533e00d89,0x790611c713f63f04ec4c,0xd20e146d0848c4f5e0f1,0x2215249ad6786522b613,0x6a40193f882518877dc9,0x1455787b213a4d3b855e,0xa41130d0f98f0d18071b,0x72e044f42d622b3309fb,0x8a10cf93c34717cda514,0x1510bccca241c28bcd6c,0x56c81858beaf4965209a,0x49445fe459c142661788,0xa3f860e5fc57448285e3,0xd0cf0107939ea6786119,0x6a84dc687f5227a6932b,0x2659b4636e991cd910bd,0xc86ad49c46af95160f17,0x536c1501d1062c29c306,0xaf48d2d9447e3b290662,0xadc08838f136c85e687b,0xa07912969ae7d6e38dc4,0xfbf603604820a538dc3e,0xcc932e32f3d1a5d90b85,0x5465dbe06c090405a60f,0x72cd929e49c384ed33d3,0x9e87817abb382278fda6,0xb8c008affcc19e794a7d,0xf9300a2658387e0e7551,0x627b1933fae244107894,0x86141e12224b10b9edf8,0xd8650bf4f6e121f64596,0xe210efa8a8151f65c0f0,0x162a3b24a10a5a302966,0x6521ded10e4d5f43bd8e,0x4ffe6a3a9e4110e6fe7e,0xd89592b86decf7cc108c,0x1e808839796b83211983,0x40441ebc1ec42349821f,0x64211c2f72a780074d8f,0x4b471cfdf38028b2e140,0x2a962f164aa2154b79a4,0x9c49237c451c5e2c9544,0x142fdbb884522ef0a138,0xae25cb314b2e5fcd9646,0x107d1c4c7bd8820e57bc,0x462987ca4a461727b603,0x63d870586fbc67f281a2,0xb350b218acfe5829b08,0x16ce32bf568b64258fff,0xa9e1f02a4f1fc42588a5,0xd4e50002ea561e823962,0x163ce398dd9f8860c78,0x5e2f87d439cf1eee038c,0x2eb09667895aeaa3eb10,0x71f11ee8713c62393c6f,0x692293bebc846e1f7832,0xff92c41662b17af5b472,0x245b48d7e213c89ca5a5,0x7a63c736fc93b48db7ec,0xaffe2aa01d9a918c91e0,0xf1047e08008f9c6a4630,0x149f2436270c97f24361,0xe04ac62dea6179d0c6a1,0x8f34e7d4389795719646,0x1a6c5efbf3c5402c1e31,0xc3727db89a7426798c5a,0x9fee17dad1288b474e9b,0x462164ffeb1543401466,0xc4cbb53563a1a5e54adb,0x18716251b1f87d6465e3,0xf5a015584a29fd7d1fbc,0x89e7fe14629518a6fb85,0xbf8387ac70453e91400f,0x405944c8571f50f164e1,0x6a44237e14e6640fc71e,0x762120d8fc29666961ea,0x918922838c123139cdc,0xf371c3030e08e59141c6,0x1e9c46a388e23d010b93,0xc3588c21] j else page #[0x3070389676281780e971,0x209318dcc9b3a611e7c8,0xfe87908e174b03ebde70,0x56834ba503f2ae316188,0x838929ed554b4d64ab2f,0xb2c7f9ff5269bd5583c6,0x16a74a93fd362920a595,0xfccaccee2d6a966f0da7,0xd4586376fba889eb8729,0x31f1150eeb6f76123788,0x1085953b4d1657dc6308,0x91104a5e796f66138fee,0xbe1cfec4ef9d87c343f1,0x4ef9a88db9d8573d152d,0x677e69f534dadbe1cfec,0x2038b63fa822b0e214b,0xdfa1ea1101a545c07bd4,0xb07940000022bc368f2a,0x47eff4358e00000055fb,0x19359f371847800001,0x26fd4f51b58c2bc00] j))))
def moH11 (j : Nat) : Nat := (if j<103 then page #[0x123100210001000100,0x320131000c21101004,0x11030010013302000510,0x3104517172001202230,0x810011081501011510,0xe705900001140a202300,0x23300842450433001019,0x738000041c073040311,0xd2000000040d70000000,0xd260ab477013c84e51,0x882024f03080002,0,70338478080,6467060448,0x5483ec0000000c0b8000,0x5bc04c0475179800042,0x325800000000000102f5,0,0x8318000000000,0x79800081b191740000,0xbc0300a000001e8000,39680,0x400060af000000000000,0x760002092a086000052a,0x1c3e28458000e0,0x13f00013cb00000,0x8400000000000801e000,0x293960c49e,0x292280000001818d0690,0x1824000000000000000,0x40d70ad9668c27b00,0x425600010048,0xad02f474e207d01ac000,0xe60002065000000,0x105ce630000000000000,0x8a000000000008104000,0x209d002e00,0x520480a80000,0x11b8400000000000000,0,0x12ac6e0e00000000,0xa0000000000000000000,0x123e11901400002120c1,0x12a008e7816f803821d6,0x28000000000000000029,0x2f9c193b0b4000000041,0x120ac804c11b80d00002,0x8000000066680000000,0x32550023d1,0x20108000000000000000,0x5d034400008e2909a000,0x1342c000006aa5,4306501632,0,0x1001c000000000,0x20790000000000033310,0x6e241800000000000000,0x420000000009c00009e,0xc22000000000,0x93a8000000008c2000,95644881664,0xc0000000000000000000,71,0x4070000207e000000,0,0x104a00000043806a000,0x3e0000000346b000000,0x4000443241e023dc0000,0xea00000000000095a826,0x9f402600032a22f05c5,0xc9410414000000022542,0x6ee50ea243,0x843c000000000,0xd64560e551d9814f69d8,0x5c00000000000000183d,0x101dc0006039c1,0x40000000000000000000,0x3439000049cb807,0xe3ac83e243966b807500,0xc000000050e7846a207c,0xb600000006a7b0001836,0x1030089210d84,0x61e07a000000000000,1941504,0x4b740ce0001074483800,0xeb2000000000000,0xb7328d00c8145825ea45,0x84b4000408140,0x208e4040817734fa04d0,0x14000000000008178000,0x86100000455800041,0x761e0000000000000000,0x60000000049130000bb1,0xd800000002008800001,0x60e0000000000005,0x740000000000001b4000,0x181ca43600005a,0x705380000000000277f8,0xa0000209ee7c811f038,0xf07c0e29b80000000000,0x435c0fe097a00000004,0x181380004c91804882e,0x3c614300] j else (if j<206 then page #[0x80db09b8000000000030,1,0x6ce4b198a892e341a800,0x308732b418ae093e4,0x20000000382ea41b0000,33571520,0xb4580000000000000000,0x60000000213b8cd94a7e,0x1d230a0001a3c0000604,0x20860000415501f21,442,50487296,0x308bec8d40a200000,0x2001c08b40cc,0x93627a00000000000000,0x144a8000915e00014,0,0xb000000000001072000,0xbaf40000000000000020,0x39f86d48dd19a4,0x958000d0500000000000,0x12ee95c0000000000034,0x826190e0000290b0001,0,0,0x107400000000000,0x83000000000000000000,0xa40006126d15000030,0,0x182a3486800,0x816c01a00,0x610b0000,0x43800000012be6081800,0x486d824800026,0xc66de0000,20480,0x80010756064000000000,0xb000000022030000d266,1034,0x202d0000000000000,0x102fc00000000000,0xbec1eb82c4024000,0x100e022b000000000,0x10c20000000206f0276,0x23841051fa83d837a52b,0x26e9000000020,0x81520002098e281c22c,1304576,0,0x24b012cd100000,0x6a0000c0c20000000000,0x380000000000000,0x199ac0006e5d0000,0x40cd19b80000000000,0x91f600000,0x8258000000000000000,0x3680000001b9b4000000,0x287f0001005e9,0x30000000000070d90000,0x6a000000000001a41e6e,0x1e00018be36,0x50000000014000000000,1032,0x84b80000000000000000,0x84230000207c00000001,0x7faccf0000000000042b,0x1495290a109c28000010,0x1a2a000000000000001,0x2f808e015a84e4077800,0x9080000001c1db0,0x590c00004746e721066,0x214200003ce0000000,0,0x40e60000,0x5d000080b00000000711,7790243504,0x1e00000952,0x24a63700000000000401,0x5400032abc19dbae20,0x264580000001,0x1041000000000203f000,0xa2cb33380000001b4660,0x9000000000000000812c,0x41110000028221a012,0x2d547f0000000000000,0x50000000000000004867,0x84000000000000000410,0x760000000000020,0x103680000000,0x40fe0000000000,0x1784a06291ed03e40,0x3121889d802c80005a22,0x5a000000000000026c08,48,0,0x19046481800,0x83b90560860413800000,0x3b00000001,0x6040c80000013c000000,16,0x5808000006380009d68,0x25000098760000000000,141440] j else page #[0x405a9b7c27360600,0xd6689e0f180560000475,0xe020000000011ed9f1ca,0xe9ca000000001021,0x200000000a3e8000,0,0x8542000000000000,0xcc0000000000092cc09e,0x30348000006582,0,0xf0000000000000000000,0x215820211ee46a00018a,0xc2680002846c6364,0x282f000000000000000,0x88b08b516d8c55c1c600,12,0xbc000000000000000000,0x419000018,0x367e1c62000104e80000,0x8220000,0x4ef7411800,0xc27d046400040d30,0x88000000041d700c647e,0xdda000104f0000000090,0x20d9c12e000000004e48,0,0x2089506800,0xdf0000000249680000,0x50000000000000000000,0x28800000000000894a81,0x41140000835437569158,13,0xf2000002a8000000000,0x18e800020de4,0x243a000000000000000,0x1a2b2482c409803600,0x89c46706640b20,0x45065a412000080f5082,0x14b84d4257a4ae000002,0x4974000000004208,0x4000000040ae0000000,0xe910d40005246000105,4,0x362e000000000000000,0x4298000000,0xc85e000000044050,0x6962000000000000000,0x242d0000807784,0x80000000812c00040280,26818092,0xc600000002033591800,0x1a19800600005,268451840,0x7e00000000000000000,0x606c8131150e25600008,0x304a800080a4033c000,0x4400000000000000000,0xd185240000209900008,0,0x10508000000000,0x80e800041150,0x2053000021b80000000,0,0x80000000000000000000,0x6000042f20000000334b,179,0,59457536,0x4041000000,0x8266000000000000,0x170512665405e3452959,0x1c4000000040fac10e83,0x54f4000000000008,0x13d80dc041e09b,0x1d16c000400b000000,8859813456,0x609340f6000020e,0x1108c0000000000000,4427612160,0x4c5e00000000000,8507904,0x40058bc605180000,12944,0x6e000000fc012000000,0xc0060000000000000000,9333,0x31500000010800,0x80600000000011b0,273186926] j))
def moD12 (j : Nat) : Nat := (if j<309 then (if j<103 then page #[0x64c10648106081054810,0x644206042054c2065c10,0x64430604306602064c20,0x4c9104c1104811065830,0x60910601105491054110,0x24d2064d106491060d10,0x505204c5204c12026120,0x5cd205c12054d2050d20,0x6112060520601205d120,0x661206512064d2064520,0x50560645306053024530,0x5c5605c1605916050960,0xcffbffbbfb7f9ff5cd60,0xfddfbdf7defddfdbfd7f,0xffaff7ff7eeffdffdfed,0xffcffbffaff7ff6feffb,0x94012c980a6480fffffe,0x3054c90206a402b2e021,0x4ccb027654143280a59,0x94d28406a41233009597,0x2c98a568c44b4a1a9a80,0xc89406a462330301a915,0x11806a4a2b2e51996296,0x9ec64cdb2a46e15134cd,0x602a530152881a93c054,0x269970352a00a9500d4a,0x54d9b2a4cd131642d3ae,0xa5d4328d80a9698cc334,0x1e7ae6f3d717aca13c02,0x10352f95977debabcf5d,0x153481a98c054c406a6,0xb09681a9b22b25602a6b,0x2605d82000d4e0565ef8,0xa0b59305ad480368c06b,0x135a509ad482368c16b2,0x8da115acc0ad69436b50,0xda319ac98cd6a451b502,0xa521ad40ed54c76b5230,0x9286d114d648a6b424b5,0x372a81b94c0d6b505b5a,0x72c19b9600dcaa66dd52,0x2ca9b964cd6b266e5853,0xd29b968cdcb306b59837,0x89d96a0d1b506e5a5346,0x9cd660ecb00755533aa9,0x2d6a4f1b4a7b5953c6d2,0xd6a511b528b59346ec12,0x65536b269b4a94dac9a4,0x4d56b52a35a94c6d4a6d,0x156b46ab59855acaaad6,0x66b4ab35a259acc2cd6a,0x6b30bb5955da4aaed6a1,0xb42c0da85c6d2ae36857,0x4ace4986724ab2368d81,0x2cd53167254b392a19c9,0xce58066aa9b375499caa,0xe595672c8b396099cb02,0x5a2672d0b3966196b30c,0x9469a54b596a19cb4ace,0x46dad4b43695acb40d35,0x6dacc36d655b9b28dcd8,0x1acc38d655c9b08e0da7,0x2a0bcd6a5d6952e8da57,0xb8bd9551ecaa6f65517b,0xc3d964decb08f41737a0,0xbf061df82e8fe59879ac,0xd66201b52fc1977dac9,0xe6622195310da2846d44,0x6a636b2b1b5a9886d4c4,0x6246b272349891a49c83,0x256b2f2b59595a4c4ad6,0x76b433b4a39dacc4cd66,0x6b3143595a1ac950d692,0xb5348da8a06d2d0368a8,0x855b598a9acad4d64aa6,0x374963ba4b2d9258eb9a,0x7c187be4b2df258ef82e,0xe953074d180369706b31,0x9a8174d08ba6941d3460,0xa22b4a915a68c6d2a636,0x5374cc1ba64cdd2a66e9,0x3b4c09da548ed3506e9a,0xf4c29fa694ed33076982,0x4c121a6a4fd34a7e9953,0xc9a3a60d1d3448699343,0x8a5a6a51d3468e9a0474,0x25a64d2d2a6969524b49,0x7a64d3d2a69e8a94f4d1,0xa68d3d3429e9a04f4caa,0x60d5d352a69a94f4d2a7,0x8d5d330ae995574c9aba,0x96d330b69a8574d2aba6,0x7d32abe9a85b4d2ada68,0xd2a6ce95267498b3a661,0x330ce995674c133a6059,0x4ad68956b4d2b3a6859d,0xad69946b4aa35a2a5ad1,0xde9a96b4d2b5a681ad32,0xe9956f4c3b7a5cdbd2a6,0x8a9774cc39a655cd330d,0xa1774d03ba651dd2e8ee,0x47f4cc3da54ded352ee9,0xd308fe95] j else (if j<206 then page #[0x2630e998834cc3fa64df,0x27169a2874d0c3a60a1d,0x1169988b4c9c5a54e2d1,0x1e9878f4d4c5a68e2d34,0x6998934c9c9a54e4d331,0x8a59744c4ba6a24d3472,0x97974cacba61e5d1512e,0x7974d2cba6865d3312e9,0x9f451cfa6626d3512e9a,0x744953a6927d3473e9a1,0x4d053a64a9d2a54e8a9a,0x5455a296ad145569a9a7,0x155a662ad32b56992ab4,0xd9a5cebd351569a5ab4d,0x1a6970d3097e942bf4c3,0x3880284011000034d4e,0x8d407d006e805a40494,0xe3c0d540c6c0b180a30,0x13681244117c10440f30,0x18a817e816b015881460,0x1dcc1ce41c501b501a1c,0x22242160208c1f6c1e7c,0x27c8262424e023a422e0,0x2cd42bb02aa029782864,0x354433a4321c2fb02de4,0x3c603b28399c386036bc,0x438c429c40ac3f643dc0,0x4a2848e04790469c44d8,0x50684edc4df84cec4ba4,0x561c54cc53c8529051a8,0x5c545ac859a858945780,0x628c616c60345eb85da4,0x690867b86684655c63e0,0x6ff06e2c6d706c146a68,0x7510746c73b072b87154,0x791c7878777876bc75f0,0x803c7e647cbc7abc79f0,0x86dc85b4843482a48160,0x8c588b608a50894087d8,0x92009104901c8ed08d84,0x96249564949893f49338,0x9ab899d098e497e096f8,0xa0b49f009db89cec9ba4,0xa7b8a670a50ca364a25c,0xadf8acc4abb0a9e0a8f8,0xb5d8b430b2b8b0f4af90,0xbbd8babcb95cb804b6e4,0xc2c4c0f0bf94be40bd20,0xc954c7ecc65cc4f0c3d8,0xd180cffcce6cccfccb40,0xda30d7a4d5e8d49cd32c,0xe388e184dffcddbcdc04,0xeb6cea40e8d4e790e5f4,0xf334f22cf070eed0ed20,0xf8e4f7d8f700f628f48c,0xff68fe70fd78fba8f9fc,0x5dd041502f501dd00a0,0xddd0c010a71090d0799,0x145d130d11d510a90f55,0x1ac919b1188d16e11595,0x26f5241d21291e5d1d0d,0x31dd2f9d2dd92b452959,0x378536a135b534a932cd,0x3db93cd93b5d3a4d3881,0x43e942e541a9408d3f85,0x4bc54a51496947cd4601,0x533d514950654ef54da5,0x5abd59b9581956355481,0x630561255ef95d015bfd,0x694167b56641655d6451,0x70b96f496ded6c256a91,0x76197505742972b971e9,0x7b0579f178fd78217731,0x7f417e857d897cad7be5,0x88d9874185258369811d,0x8df98cf18be18ae189d5,0x939d92b1916d8fb98ee9,0x9b4d991196c595b194b1,0xa3a9a24da1019f919df5,0xab3da9dda825a64da489,0xb4adb259b0a9ae91acc1,0xbd5dbaddb89db77db62d,0xc3f1c23dc0ddbf91bead,0xcac1c7c5c6edc635c561,0xd0bdcfadce9dcd6dcc45,0xd6b9d475d395d2b5d1cd,0xdaf5d9d9d961d899d7a9,0xdfeddf21de01dc9ddbe5,0xe5e5e489e36de23de101,0xed21ec11eb11e949e77d,0xf2f1f211f0e5efbdee3d,0xfd8dfa61f7b1f4c5f3d9,0x2f03701f002028a0041,0x781a06180d80b00403b,0x284008c06686b0570460,0x8a704e09287282705381,0x182904904604a87605a,0x30b206e0db0260b410a1,0x605409f0c205105382,0x580e105405f042809081,0xa0800a21050930cf03d0,0x6109407c8280f80dc07,336783403] j else page #[0x983211280e0e80d40870,0x8a81e1141a00aa12b00,0x168ba9520ae81709a8fd,0x30d10148148080ec1e98,0xe50628302469329240f,0xfb0331411228c913d030,0xc1c613612295d8698741,0x82e0960441d50ac1701e,0x6818698c87097e9ba966,0x31602d209a98819480c1,0x11a93898d93992590c85,0x9a08906c23ea581e40f4,0x403c0aca871bf1450cd0,0x6c0bea008a49898b801,0xc17998d1a81a524d0ab,0xa882ac22516f15581b0,0x11c87714d9301581282b,0xb282100d2ed20a15a174,0x43718209c221a13ea119,0x2341481fc26cb8e8c71f,0xbd0db2071921921620d2,0xc11020c240180af22a03,0x81e9b090e0c4406a7995,0x4805a0a91930c41cb088,0x13b201526219c0900800,0x8429b690eb403d1824b5,0xc70c9a7d87181d128324,0x800c02822a2fe30b0ad0,0x9d89642198fc93123800,0x3c31029436831f21439e,0xc320be83988561a88b90,0x96511115847aa7c2b697,0x7e3372302cd00329d8a5,0x89b00301c128c2918119,0xa72a76a702502381a89b,0x442a914515704b058364,0x19cc3a40d80b4afa1561,0x21c120b55008a6609e03,0x58cb223846ab30af6af4,0xdadd9b630046c4f8c44a,0x28a80ae4804a5cbee03,0xdc2988c523121514d223,0x9708a109c1991c03761,0x2ea16d2e11be33b1050d,0x1b84438300430588c36,0x724b2c49242bab880213,0x16d1603a03945870e82d,0x284621d53dc11413419f,0x50202544f431602934ca,0xb40cada104544e495c23,0xd85a921902ab0cb84b45,0x6c1e3f8830402a5da019,0x1432c89523490ca2e230,0xd93072c132d2490c0391,0x822c5490a04144e8d3eb,0x1ad2a04f12ea260470a6,0xcc4d0ca4d3833d1702bc,0xa35a2ceba919d12d9883,0x4bc4d917510111513640,0x5866401806c688d31488,0xc6d4594591dec9b413c5,0x9da034c1eb8035db8335,0xb52926021f600229e0b0,0x142d4c93cb1746685bf0,0xa8841223e3101741dc05,0x1af9c94268c9824c062,0x71036c4e096d0edb881,0xb305ae196528bb53e436,0x247087050186ee50c824,0xcbf46ac5b0e2c408ca0e,0x4ec8206c44506c0e1882,0xa470c465c99a89af04c4,0xc2fc352beea82ae41d05,0x60e28c8fca00adc30428,0x5a43137d29c6103f2adc,0x92c10b12c53d4636c803,0xc80a78a053352c93ad32,0x2c6953396483b91f4334,0x594f3282203f8e285bb3,0x2812e525c3184dc58f09,0xac44d48c58122926a2a9,0x870040cdd83783c84fd2,0x458e22a0684d84301a81,0x1d9b9b468120ed5d53e0,0xab908c8ed8951eccce2,0x3f1951c853585790b617,0xf2390c3d3b8e1d644e16,0xd21eb45a71a76440ca93,0xb44cc0daa3b85b53f92f,0x418104b12aadb942bc0a,0x7759843489ffec900446,0xea0dd04caaa7ab728479,0x28479156899983501f7f,0xff8006401cf15622d4b7,0x19a4838070359d0769b3,0x156235567f20e01ddace,0xcd19a50fbdf8180001cf,0xbb884aa000e01dda,0xeed668cd287f0ecfe0b,0x1c03bb59a33480070,0x2a7aa023fef0c2c15e6d,0x301531d4bdffde204060,85046304] j)) else (if j<515 then (if j<412 then page #[0xc2448b42ebf16170cf7e,0xe8f187c60cd30be2b9d8,0x39c8968d62ad8019a6b7,0x94e7225a538a678b9b65,0xe3023a018d0e299e2e6d,0xab13654a324aa5960266,0x15c0000d2b9d55a8c941,0x58099b8c08faac687140,0x209d8ee7405d314cb29e,0x1ffc3458004fb41f74c2,0x200010d0f7ff84613050,0x58008800042112cffed2,0x99d5c9fc90020b0ceffc,0xbf304040a407f6580021,0x10854b6346f002199c7,0xf89ea4effd0230e1c00,0x8016470007fea8189124,0x6bf966d10022141f04a,0xc901200e4427da741a65,0xabe4809003489a7fbbf8,0xf57c80801000e209f8b8,0x29d3f0bb8329005a245f,0xc7d4e400ac3b9200d638,0xac0076acd06b47ab9018,0x19f7351000525c00c7fe,0xfe58006c0034506800a0,0x5cd68d948c0471aefc12,0x22fa8001c7a3c0097f9b,0x41460006d1f80dad035a,0xaaffa301a2e39ea22e80,0xf82dc3805d7367a01251,0x451c051c80212a40cfe9,0x827cf44e201311b17e43,0x41220004a917f46037d8,0xa4ad2681eaacf23ead14,0x59a002dc00008ed69781,0xc5e007f47fdf62827f2b,0x22c37fce5a0490221f0b,0xf9a6e63a922d825e90db,0xa1f8869118dcffc00503,0xef06b72f97a4ed17733d,0x9f0fe0ddfcb508e26396,0x862d58c00000000010fd,0x243e8854d6ab0515d640,0x5ad04b19ea881333a666,0x182119258c92065e0ec3,0x9604d50bfff06d900593,0x6660d577ea41b2592dc0,0x7b59d70696e50ef255a2,0x6000073c5590d5855a00,0x32fac27a923fca6e160,0xeeb356694bfe6a3e0b,0x5c1c810180a8e2a40236,0x15ffe20600a95a723fd,0xf8bf815cc5e602bcd114,0xc3cc4f39b4e7632d19a,0x5cc001400e591caa1d83,0x89839804a024f7239d44,0x5bacc60cd3239f73b184,0x5cee2f4cad628e38849a,0x8127a655046c24d14d53,0xc678b9a676b12d124489,0x5f0091ef1f24d0429618,0xa4219b51602983b54bbc,0xf7fbd9baa3c25a6551f7,0xfc33f56e234101432516,0x6cd174023e9098d1a31d,0xf689ec50aed4d50ef37e,0xcdc604742ab1aa4535cc,0xc4cecd46c5ca1978aa64,0xe50004600002058ce7f0,0xe084600002578e0029ff,0x113c6019e2f800afff,0x810a61ffda0128c2130,0x1084000040d1e7a7fa3,0x926a80ef07c0002bffe,0x25565fff48c980088000,0xbd3fff00c81c11000010,0x810a475ebf016002104,0x4b0fbaa0408537ff854,0x8580085126ff724e5408,0x2254cbffc2a040a52bfc,0xdd50225295ff84aa9600,0x81526fff672a040a547,0x2441400101522bfc8580,0xb8fe5ff0757071598c54,0x94654600b04800004095,0x4e409800010247b1ffa7,0x420d8017f578be0173fe,0x8422fbf90c150b8000,0x105d633e5f750ce3800,0x5f9f42166fa8b3831000,0xf1bc6ac5203100001515,0xf6ffd70038001044485f,0xaab02ff295f20042ed32,0xb0f8bf5198c862000020,0x99a83f0c3e998000809a,0xa0131be70d07d04008,0x3bb00008ea892becb1e4,0xa92200010445c1ece972,0x84900008862f9b7fee81,0xfccc00402942f4dffddc,0xbb50f1e] j else page #[0x842a73f0507e7001,0xe15020429dbf5ba1e70e,0x241493eea810214dff,0x955bff0a8108152ff216,0xf9002104abfbf9ca8100,0xda9c30000841a87707b,0x41294dbbf3e80103a5d7,0xa6fc831871dc1efe4008,0x80029391403a54839f69,0x920e5c39405ccfb7e6fd,0x90ffa46d426756f0071a,0xc0daa03a949d0802f2b,0x6a2704a80264775f5b07,0xc1f118ecfe0b321b541b,0x5459004956fee9648ce3,0xb5427e6408aa506d50a,0xa7ef85fd018d88120401,0xaabd1cef53d9611e01a2,0x857f77370c8070900478,0x4000a42d9728b7440158,0xf003811a024c19299012,0xe61c202c16af42a5ae5f,0xef7ffbb30ae924a032c4,0xa20644611044141002d8,0x59512121060125bb1fff,0x7e22800c00a5737eabff,0x3aab036e7604180000d,0xb6eea6f7e8680aa11030,0x81d512221d1004880096,0xfe3f7b8a428394ba3fe0,0xa7feb404af42d01b352d,0xdfffeb66248000c001b6,0xfe022b201c0020093161,0xf01fef6858140aed76ff,0xc3cff605de810a0466c6,0x91ffa844ec92500d6243,0xdfed5420474440c00d6a,0x30f37eed1f304c003d57,0xdea436451d6602b2bc00,0xa49012d400065c04b020,0x28654c0356b33ff36088,0x6ac09f29000e2c3b778b,0xf202280691b6f37faa48,0x8105180d71f39b862f67,0x3c84a8c04e1939f9ddcc,0xb8fec1d1a81077908c07,0xb488010034eb808fff21,0xe6ddd7fb6089a3d1922,0x591f5fd408344ddfee4a,0xf168bd42335326e400e7,0xc834c05d57200c91a051,0xd28a3880216b40016bfe,0x10f1857e219fa100086,0xf5201757fe04f0ccea72,0xaecbf9564aa1c14a800a,0x134fd24ec505d520039,0x403dd937812b4c00079c,0x3e1f4410d800345031cc,0x59f8a80a01f2bc00ff32,0x3c780075fc013168a87,0x380d83fbd622dfd0a80,0x61a067f880025290f0,0xa037f83df2fe590006e1,0xbe2f35a36710504408d1,0x5b34680d044042c8e3f9,0x159647fcbd9f27d1ad03,0xa2818c0028067dcd4400,0x574783ffffc0a8ac001,0x8e56414e8e7564c0008,0x3c187ec430240301e62c,0x5ec8213875134a05cc6c,0x8fff51d1b4008e2516c,0xd681ad1179020009204c,0xc4708022ab446c527c06,0x4a38000afd38877b8301,0x8c527c06d69d65117403,0x258a2268470802d6b9de,0xae11c5354ed7fd1cb690,0xe181f8d55145a58197f,0x115201812f1d4ffc707c,0x96a28667fddf9f4ad209,0xec5eca850b1a0dc5c40f,0xd437cfcd7820850056a4,0x6f5ba7ff7d19b24c012,0x6fc8ef644a0108b51c40,0xe36b86f58c6401e59103,0x5478019c604bffc10681,0xf8ae265e000718052fe8,0xffe2c5ce7640a0a96b25,0xffc3b527e590282a1aeb,0x594fc500d8062002b8e5,0xdc817ae5046d780404c3,0x13d073f9f59038cc0807,0x9ec400200b31f0f270,0x900b58cb7c3ecffe1008,0x27548fffc08271c80050,0xb26fbdf37e225250c401,0x34bf97236271aa8c0026,0x36c02020880296bd8f6,0x13d0956b7809624ddaf4,0x2d500b7a9f9d343da519,0xa8014d0f2fc2214644f1,0xbf6227bc] j) else (if j<618 then page #[0xabec44f2054b1eb7e52a,0xf7fb113c615200000097,0x6fb113c815347e000001,0x600a30289d50000002de,0x2a50312e3b4f9b8ae30,0x2cd9effffe4060253008,0xf45932be1692e808c4f8,0x98008394903d0d68acaf,0xf83cfb2929b9780ddfa2,0xf08bcf24a554000000c7,0x11ec694293727e2e6a48,0x12fcccadf271d020800,0x6519c000000001ff678,0x4097064f5f013403a8c6,9661580092,0xf220f402fbf9d0331380,0xc0016b1a45960860656b,0x231e0a2914a8000d7f,0x6778012e077cdf1,0xdf12463c144e291063fe,0x824c000005bc14e077dc,0xa4c1b930ae074bdc88c0,0x4ae06bfea063b4586002,0xade01993019b3080de8a,0x835fd19e2015d26001e7,0x1cff800227e4f1c30,0x175f5e6de908e998cd00,0x4af440a18b4600009f58,0xd47c16065b3ca813f36a,0x69a6aa17615c58153c5c,0x4f723553c5cca42e1918,0x4ea612689eba0e65202,0x2950059f812a010d6070,0xbb42d5737a655046c24d,0xaa6bbfb00ab454dcf942,0x800080b7123c0ba6156a,0x27ffdbff865b20207488,0x9125f4f2ca120614235,0x12b24ed7fe2071005005,0x7141b52ffe1ff4066604,0x808b12fc7d46a30,0x9ff628082f825800a208,0xc818c3848801022b8aff,0x8091a00057d2ff2e9,0x4957c1ffb3ecd30e41c4,0x4409963141ff2bc64273,0x857f3fff8a021bd255c,0xfe503cf9a0b14c100001,0xdb8630000104458067ce,0x94820000114d5821fddf,0x880004343a1fcbf56ce,0x490440400008109127f8,0x523162e0fedfe7ab0cd2,0xb4a395f94d87db104410,0x8fe0e8f560a686504010,0x3692531000010157c3e,0x2028d00afc5b3f5148,0x747a7fff7821a3744640,0x40d5217e005b9000086a,0x10d1117fad83c6480000,0xa001026c01f17e614000,0x63dc3e2a12760018618a,0x1e04014a8000848922be,0xb9abfffffecbf8230888,0x97e891ab332056000404,0x6d67122150b687bb75ff,0xc8b5238809af3ffc93b5,0x6679380e002298b1cab7,0x4da3f078d42500008423,0x8da08300000108567bb,0x91800008062defe061c,0x7118000805bc58b97ff9,0x100c7d7ffc7ff754ea9,0x13ff36afb7c0e81d6380,0xff80da08400004035426,0xc1c41220000212aa398f,0xb08600002018a3bf37ff,0xab7eedae01058601bd7f,0xfffa748c98418000408a,0x48b54ffec421a20149a3,0x202926aec7ffe8420321,0xa10805a6bf8cbfc206,0x35fe108e02209a23e7b6,0xa49aa397f848440404d,0x843100a4d7f1c76dca08,0x9237fac60c40a46d3ff8,0x678025c6c37ffa890404,0xea4dff780ab37afe6816,0xafca9818820040a0126b,0x4246b0490ef87ffbae90,0x7e1197f16878a23c2262,0x3b344025808b728ffff8,0x33c887ce21f49db0db,0xfcf0fb6230a0a1104483,0x37662864085c25ff9bff,0x2d9784bcf90475fc1a1e,0x6416482cb350f98f4348,0x3e78489213209a83c348,0x9e7f7e3d0d28325e12d9,0x23a6fbb593e774980ae,0x96a36c23677303ff4466,0x331971b0a3807690287,0x76e1675e] j else page #[0x1995a9799233004f5224,0xb1297ff8600280769a6a,0x40162350fe45aa994806,0x88050196251fe2c81c01,0xa8c83280244a43f1e54c,0xffff96dde671b8fb6a3d,0x328f724118043a4c0097,0x6fff1ff1747c6722207d,0x3eceb2667d52260390f9,0xf0c7fdca180de1ec813d,0x431e1b894014025d6f7f,0x8a08030e6ac2f37c547,0x3640126aa2fc6e1fd44e,0x6014f51780167d2306b5,0x982c87233ffe14b29c46,0x252d7808f907422fdd3,0xab216ff88182ff103b06,0xc03111f8e20862f20181,0x1d3c49806004c853ff06,0xc016b196b7e6b79e8cef,0x80de8fccbb169e29956,0x33f3b2c2c3edfab670d0,0xff550608b01b52503ea4,0xa292108582c59e2e0360,0x2fff751c972450044200,0x1b6ccd9328ef80298f03,0xacc0e00ce9466cff2097,0xf9304a6b046ba282ee0d,0x37cfa020151198fffbb,0x4aa014f1154ff2b4dfcc,0x819c54d510fe4fd537af,0x4688601d72696065fe02,0x5fc9fd43e0aaa06700c6,0x85442321100072caffff,0xff678741c02269e2121d,0x6e2081c4400c516077ff,0x7ebc437056ce930ffd91,0x7fa888ac89e1120012ab,0xdc26f4a5c90890041569,0x144524208600055b77c,0xa48a3856a9afffb1a715,0xac0f5a20f81d2fe99998,0xd01fecb58163327d1745,0x5300f94e87cba2a2607c,0x810e2e52a862204cd4a,0x40037fffe08ea372f2ae,0x6cff4c0f211842402963,0x36f4c44908604b457bf4,0xff8fb0da2400908112ef,0x5177e33068550843150e,0x4315177e3306dc004431,0xc2a02d0f77e330685508,0x9e1d203681153315671f,0x43d9f1f794aa5016535,0x9024ec0455ba3348030,0x6e50c7469026fa943920,0xbfddaa1b68aaa7af8c96,0x43f0a0e74f7f8327c489,0x3427ff64cf7e20c746af,0x99a33e6ec815b09101e,0xee318400011211999ee9,0xf20b433018e249ff1436,0x135f9567010599e9f407,0x9caa6dfc5339d622242d,0x11d91b7f4a379d842062,0x21478fa3b06bfcae1432,0x864210c90003568bf143,0x5710c714e6a000462de2,0xdeffeaef74840b006032,0x3d64b20831464861c475,0x914c258e328fc3e27837,0xae9f5f1019ff01336aec,0xc91c129dafb3f8c14605,0x3028642cf1ccffe22128,0xb79c2009121184bacfbc,0xbc850c0d9cffffa6a361,0xeef124283636be178db7,0xeb3f1112a61cbf801947,0xe87360ffdf384e9a1c5e,0x4081924e1bfcb6128231,0xb106c4a9314c37c1ca31,0x640097ff66a0073eba15,0x8d589be1a989de0aead2,0x31ffe12fa3d085479,0x2d21b426b45111bda7c0,0xff941fb53318d473b36b,0x208e0f3200000000000f,0x2f3485a80a06a4cc685b,0x822ce5ffec474fe66350,0x68a00cf6e84a19b46080,0xc1846caf012fee000c3f,0xf7bdd528e4200c611ae7,91] j)))
def moH12 (j : Nat) : Nat := (if j<206 then (if j<103 then page #[0x4c16054000080408805,0x82200802004010b827,0x3007040000680006000,0x600003c2400c0f0d018,0xc2e078010000c00000,0x1c01004520140601c02,0x1d4000780201000,0xc16254010280f01804,0x12400124040502705400,0x342c044210080910026,0x1b048170041d00006,0x442004080100100000,0x7016018180200f00c0e,0x44020000f1282d16810,0x909802010000583b,0x2025004190080903c15,0x40902202c2400005,0x1282f750450344c0240b,0x380b004030285b07c46,0x3c6f00c0c0841700000,0x1001024070101c078ca,0x24022503a028000d00c,0x117c090008b1980c,0x2c06044010080005c02,0x8120040a01c0207003,0x40b0043706c560bc71,0x10112300000c060e867,0x500201c2a1381201967,0x888294041040012417,0x24162c8000181a07001,0x40400c410300b00002,0xb1600c0183503415,0xa011000070145b0000a,0x40000006368a00cc21,0x2c02065fa0a01908400,0x24097008010500c35c29,0x14060282400c2d,0x14450008401cd500408,0x781f358013643c00821,0xb014310210c99a17c2e,0x2c2600024020831b419,0x44230243d0ac1e1041d,0xd82803c031543d1798f,0x8040201d28cd759016,0x3c0a1240001c4e0c033,0x582a068170201a00003,0x100030400aa0064f002,0x9c63000ef0600a03827,0xbc110041c8a0e92104a,0x14022f0221f0063c805,0x128000dc1303c4849801,0xa4072442d0243f29405,0x7b003000281480906c3b,0x242b3e8280145c23c13,0xb4d908a40f1300008405,0x1371c1f09e5210710ec,0x1150065138f14588131,0x73e0a350c9e084d04f8,0x13920b53430c0a460203,0x8ff00cc000300999b03,0x299c805f0000309f0,0x90a90df097409d523a8,0x1508a3ba4455084b69b7,0x45c3092b4bdf5a1a00b7,0x5910b28096bb7230dd8,0xc306bf05b40c8b8c8b,0x38201e7088a14630ab9,0xdd4166b256324f4ba89,0x50808180a6b020807d8,0x8ddc010400030c8323cb,0x70d000000a09469e20dc,0xb9201031394000306ba,0x23dc1a5f0846037521cf,0x8300c952dba7c3c0aea,0x85e8c7443114889,0xad9f01ec202b0b0156b4,0x4be8063b09b59bd300d1,0x6788615809f673a00002,0x74e02b57c54768c7cc9,0x73037e013e0616ac2c,0x735800be466949bd09fd,0xc0000000003222546b2,0xd6e7c1246c505290a5d,0x23b52c44473a02d50786,0x5dd40002251d99d4ab67,0x6010000207a3298c0001,0x97946e205dc00010b10,0x2a120583064471340001,0xc2802b10a0108cc0000,0x2e648410d3c6d050b15,0x1c35d9b1aa37daa0982,0x2dbe221c5cac000004ac,0x7ce424b80002114503c2,0x660b01be009400000003,0x9d15900001646749c8,0x8380b3643bd034405b0,0x4142006aa63399e00003,0x7d7e04db02c279d50584,0x15c40dc9ae8,0x3da07ce0bf000010c18,0x2553afcbbcf48e62534,0x31a08f50c8f0543ab6f,0x6d60935] j else page #[0x45e6a80062f897c0000,0x3492a7415ceaa66094b,0xb970063f4cb5679e9cc8,0x16f4cbd033a03530817,0x1277812bbf05f80566,0x48a87bdd07b1015107ed,0x1c930653069e06604bfc,0x67f20f002f0769008c7,0x79e148ac75e1073b0a95,0x7661b21001905690a90,0x757191001a000000001,0x18a2e033f07e50063,0xc4a749b474400023bc8,0xd7500e6052d25390501,0xbae748e7d1821ab740d,0x43d20bc70d9705e1499e,0x329bd035d0d4002b9,0xd47a40c019446aa0798,0x891ba6609970dcd6a70,0x74680c1c000204590158,0x2349a061a0dc70d83,0x510050d0998676907d4,0xa850bdf0003034d066e,0x3119ab4d73bbcbaba,0x342088f16a000000bc0,0x811015700fd04d20c61,0xbbe00cb06410578,0x201ac000207590128,0x7600003067928167d48,0x14ee06811883736c21b5,0x102ee464b4c6c048d,0x64c7b9c000302a702dc,0x2c800014c9806fc0570,0x65bc091d0462203c6a76,0xbbbd171661800c852ab1,0x29d00002075d0d4a00e9,0x76762b5a2a5f079203ca,0x35bf80001043903f7,0x8ef03a843276d7d0778,0x43e31431003d05b80d5d,0x31b1000030c6e0574,0x116a40002080009bc,0x4e143d800000003b860,0x46e70bd94d090c540ab5,0xac1799d30440024c94cd,0xb21091802fc09df043c,0xb559a3f10a9db4d02514,0x2772964036f16f84749,0x980001330bea3bba7611,0xcd90c7a7beb049530ee,0x313a55450b1d0270488c,0x134b11864c1a08250768,0x85105abbabf45b506e8,0x7f1039d46c805fc9519,0xde200a1051e483d,0x72d49016c82643543cc,0xa49695500fb09914c13,0x37323ad090701d60045,0x115442a7d24fd04dc,0xce678df49e413854838,0xcb909242b3509521718,0x2976a2d056000000001,0xa1f0c726b112b30bb84,0x147e01b234b1634b79cb,0x10ac000030ccf0747,0x20391bf4000207e30abc,0xa96501b40b5967734c63,0x1f7a0000018bb00160,0x6cf7cb804a51486057c,0x47cb049c000224270881,0x30bc800022a560479,0xac0c021702230a8048b0,0x22070afe4122ab42070d,0x3828361c64310a2d23e0,0xa04a94f205f07d00000,0x4bbd9a6c04b800014743,0x46f243c643aa4c20101b,0x4c4602650d167a442a44,0x42c50420041c00013781,0xad067004cb03d10145,0x26327d465b2328b80303,0x9c665f1660e026e026b,0x879d874d07b547fe085b,0x3bc008265fd5414,0x62b06940356296c0000,0x64806d30ad002456800,0x694e667214ae26cc09ab,0xcec9b0d0d220ce001e0,0x60eb147609cf02292203,0x67900361294e2ad64915,0xbd00000032b05e70d57,0x204605540003011ba142,0x667a46eb08290400767b,0x6bf4029a00b3bb3a19c8,0xa5b09b0468805d0020c,0x48208c80000146c0900,0x4c4cbb3464c77d9c0db6,0xabfd0b4a6bb20a2845bb,0x6c8b0dbc06b305c0300b,0x30c5070d4000215d4,0x12dd20a41071f941c,0x7ada52c440403a0,910118052] j) else (if j<309 then page #[0x6c860cdd06c68de109fb,0x8755674c0002b4bf3186,0xd650b2c45fc0db0017e,0x47000014be72b240002,0x4d6006e04bc20283002c,0x4c0d48f82a2561346757,0x34ff0182a8b94d248ad5,0x5bd08970d9936980aa8,0x88bb05a200ef7d14477e,0x6d8fa6d0167d0da447fb,0x87b0751c07110d510c77,0x9ad4ca3207b079500d4,0x42b0aad087529d853f3,0x3639007e09ef64ef253f,0x13902f60124768000de,0x4509247997f906e708b5,0x773203079403016809db,0x6c24740490aca30c47,0x44f5096616b709d0263b,0x77f829ef112f03a4771c,0x44eac50021909600c39,0xc7c04b4913d09410078,0x167908dcba2b00a47400,0x469743ae7a0642d4baee,0x58bbb8d0bb566160dc9,0x449e0bbb025866070143,0xb887ace00d908627c51,0x541c0c0d04c67cc2183f,0xc93080f0bfe0c120445,0x6be34180019908d20c14,0xc6602626953091404ec,0x6890d1c6c90a567053a,0x6560172078399f30cd6,0x14d8db409e2852d79d1,0x14490be406f448c175d8,0x61205220cc702bd7a4b,0x20868000148da2b3c,0x3c400030b9f2a4006a4,0x3627464d02ac5c0d395d,0x19cbe01c5b4c22a39,0x2b2b6a8d0c2f0d2d07dc,0x4d2b06ab0958b8036610,0x225e74747171008d56c2,0x6300659029c4d3129e4,0x97c9afc06a323e40001,0xacb0d021a39017b0d3b,0xb65456d0af202843637,0x24b30ba7677e07eb7832,0x95eaa078b7d03e464af,0x21b040d8772867b30621,0x30a20e746fb6a890840,0x1fa736a09382b0608f1,0xbb7104360930087eab86,0x7cd5aa2d011e028c01bb,0xbb43202f0a1b73baac49,0xcada9fe02f9bdd007c5,0xd7c079c03119bf0aa01,0x3afaa412b4fd0b566a6e,0x13f4339f000f491b0c69,0xba606c6c01aa678479f2,0xb6f10cb70aa5032c1428,0xcd12db4204200750d8f,0x6ca1725431e0a727656,0x362e04a16d8565ea9c98,0x46c2b3b221004b0133c,0x970000101490599061e,0x160b4d5b083f068d967a,0xdde245376b620ed49f2,0x9bb0c9946712ba333b1,0x35b207416c337b7036a,0x1f71a2d0b99056d07fc,0x5f40dbb0da90c245a12,0x45321f30507247200f5,0x6ef0a621cfd05a708e4,0xa9905d5249e0b3b0175,0xb327a590b6208874bd0,0x673633f743b446ac23f4,0x8a9a6c023a4040a0024,0x7834082e750376952058,0x20501481066804e86776,0x8ae469320255a2dbb69,0x487bdd97cdd078b8b09,0x45cb846248b89c0d0253,0x17201bf833e2030c34ae,0x67764a77cea0234b3d1,0xf2058f02a32444bab4,0x4680a3829cb19f40835,0x217f5a0c0003089824ec,0x4fe14e001a44d3e21d9,0x4bd400010a500acd2a53,0xd070516b52e3bc21664,0x170100ba08d400036c9f,0x76dc2b9c072a092e05cb,0x549c03670b0c02794c6b,0x247c46dc1503089f4cc3,0x249b48f265ed00596764,0xaf708bf046716982af7,0x2dae7cec433b07f47c2a,0x94c20320ad9078d04d5,0x2040001713e0b79183a,0xa7f081d29e0ac3b149a,0x7c2038849b927c60b87,0x4c857c0d] j else (if j<412 then page #[0xb3c0c3d43dd0da3080a,0x3330956467a2b0b0b7c,0xc2208640003039921b8,0x53509c80b1b29e80cfd,0x53c0741052402434c38,0x615142f74c005a1d0cbc,0xac57d3a082305ec0391,0xa7167d1c00001d9a0bf4,0x9eb072729fa00082bc8,0x55d73740dd3148b70c4,0x4100001a55b2a23418c,0x7ce170cd134001cd0720,0x11919264145b22229,0xbcf19060b5e40e11800,0x4157acb03230ae3ab9c,0x34f42bc6367f0aed7bec,0x40ae1af1076ebc0f01fc,0x4bd0af9acf74685038f,0xbf940b66a78032703ff,0xaa510a2502cf5dd12048,0x91c10b42780302933642,0x87904a884ec165315d1,0xc092d9a734b2a700d69,0xab83ba6b21ca17e60c4f,0x22070456a548e8195d,0x4128588102d20d0f047f,0x30adf1b290ca60913,0xadb70085921687580288,0x473d03f14bd800564c49,0x1c99a2c1b26010a0805,0xd5836b4000103de0035,0x48a10b2708e32c8c099d,0x24ea4bcf041b2da8abbf,0x5a6f04cc0b0b003319b1,0xaa0a07bb197b07020600,0x7624470d67992b200635,0xa3000014d4d6c78486e,0x77be3429031401d14737,0x242302aa2a0623f8090c,0x2d960d08000000010a3c,0x2eaaa6321ea2a6d9836,0xab727d3d613345a8ba6c,0x1af4000008b000010a75,0x69305300001bc5606de,0xd700594ada800020c58,0x4a2c0000860b0bd70233,0x24a9735034e3021d541a,0xbaaf0ce90a130a4f0ca9,0x21be7464000000017cbc,0x3bc61729055934ec0c34,0x93eab7d413b098a,0x208e9878977070090,0x2afc03e32ada29cc0870,0x347a780d0b6d3c0f2468,4525786865,0x2061ba934c701a4ca844,0x308c006da03370c42,0x2a4943d7bde3010c0000,0x1a3e06ad9cec252a0112,0x3a2f0ba10bee031f8dda,0xbe0000105cf085699c6,0xd84037b06c18b1005eb,0xb8cbb74038638020b06,0x86c09a61d068db3054e,0x410802d803cc000120da,0x2c50018816ab48103a3a,0x4bc66c0d0d9146b8070a,0x226400022aeb0b4c8c0c,0x23d9b2ae0023e,0x24a4001707cb4d6b0038,0x14080003735e0a0e0d4c,0x9c13098e059d09a00003,0x316492a2f08bb8432,0x7a4204240003221b0b74,0x1027c000000000002,0x1df47c6ab68021164bc,0xad7431900e000014623,0x413423c40a1405440002,0x5b1209c304e51da70c07,0xa2308f86af1096c0002,0xd37465a06fb0d3175de,0x6250c5d675b66000002,0xab04bed0cb2004203ef,0xdaf0d9c0001860304f4,0xcc07bf00000000007bf,0xd27782000030d8b0737,0xcf0a54c0b8000030609,0xd134cd827b609230475,0x1687f688140b26d8b,0xd794124060ebbe57c04,0x2a5805ac00005a160baa,0xca10549248779c46a27,0x60e664a803d600530a65,0xbc5c004d4637019c0bb3,0xb940aa3b54c8d040001,0x8b6a03b503940cf40164,0x22e0cf81389485004f3,0x1200000000303b10d61,0xb6b23b8670cbafb4cec,0x946b04c2049a93b57cc4,0x49ee0a8f463b417d6750,0xcc929c18881bad60d28,610339653] j else page #[0xba2c0001018f0048,0xaa68069801f307ab0730,0x1c0c0000008b7d420771,0x1074aadb000014910,0x3ad747a07f907140774,0x119e065e281e05db0227,0xa5503b84c7c00030404,0x7a64d9b05520947,0x49c4000304495dbd05c4,0x1d90a880003018726b4,0x3ea025e5de10a7802c4,0x44fc00000a6c06840607,0x71b040e80e5455e225b,0x6da3550a69651c890248,0x4cf4012c098503f808da,0x28193bd92b0d06b6413c,0x75305187965a6cd0d1b,0x20c33045521e7005d,0x466548037710000200a8,0xae62035002b04323652,0x6a2075642c0d06650192,0x6a3f077f00c400067ac4,0x4be1ab8901ea023b1b16,0x7a2d24d508a0042f2d9c,0xb706bb602e2048a4af6,1] j)))
def moD13 (j : Nat) : Nat := (if j<103 then page #[0x581404c1204403008010,0xfefeffdfbbef7bedfd7f,0x4ca0364c23243ffffefd,0x912ac9856480b2c81970,0x4e1206ac8a5660ab2655,0x2b29217090984564dab2,0x597b2c9d963eea0e5662,0x9954ccb0425520acbf6,0x7299394c1ca40e58152c,0x58372c139601caa4e550,0x6124989249c964dcb24e,0x24aa7254392a0c94c64a,0x96064b01257492b9c95c,0xcc496524b27259192c24,0x2f2a0f9646cb036491b2,0xe584f2b9f95c7cae1e54,0x5881d80760009663cb2f,0x5182410fb06a42ce1010,0x1f90ed470e3531918b5c,0x4c845bc29e937094444c,0xc425a010f7a7773969b0,0x654069b84ada42d19688,0xf65d2ad4d64aaf155029,0x891b34d6167d31dd858b,0x628143f19eecf1974f3,0xc7ee36f15b8884386123,0xf587a75d14a771327944,0x604900606812041002b9,0x2a1141b21a45d02e0381,0x19c1101b43a931272498,0x12c8018a6872088480ba,0xc04005b04e18203c0c9b,0x3f404110252544208240,0x4bf82207c180290b051a,0xa1de3ea5740f0c82b229,0x4444318369b90541409,0x128bf88309a462318443,0xd653a9da4926311c13c,0x10820ea40c330cb01659,0xda9883502b10d0322883,0x14c4280001a29c1629f4,0xa582ea56ea717007d060,0x108a02b04a0b11096332,0x8990aa0204c1018100c2,0xa216c691272442e2658,0x35c4380a18415432455,0x2858108162248848f50a,0x770b21d637c658321183,0xc0a5a2a592182a022338,0x69bf29c724d704e83102,0x665f4b99712ee5d0b92f,0x51e7c942a145280180c0,0x2703f03a27424809a93,0xa4248680991918e29a13,0x5b891162324258401601,0xea260550a811f1be15c,0xcaf9512a1428af05d0ab,0xd422d011b0084d21564,0x3da9e50284d05acc57a5,0xa9701ebec1183b5c4b0c,0xc30452cde85c5408055c,0x9b140bf8b33646bcbe0f,0x3d4c818f1b2444383211,0x1c2cc09512a75d09a11,0x691ff98016604a894bfc,0x20122b6463d241140243,0x104d538817c33f00fde6,0x960001f002f846b5b40b,0x12a358f5fe00e16604a8,0x2936cefff8f48005620,0x3014a36027f3506f64d6,0xa980a51b1be194f98155,0x40b10536d91f0ca7cc0a,0xe38b11b1a91045f04f5b,0x1b02913e38b506c02933,0x7af1541e980d4400beb1,0x4e06d602c2e6fc00d537,0x413aa80182181f5bc000,0xe1bbc06a3301887aff5a,0x7dbfb7fc09b,0xdfe79ebde01ad8000,0xaa96800000000005fe00,0x5e1557d71a0060b,0xcf3d7bc035b9ffffe000,0xbfc00001bf,0xb824009295d200ea1b90,0x2905ef828ac56787c001,0xa49a23320605120073c1,0xf00b0c2007190c4805f,0xbc82e3a85d04e240,0x95cb80000392ada6fa91,0x881054a5d7ff1cdf1020,0xb4900108c51165e1ffe7,0x480004004badc007bff2,0x500318662b3feffe92f8,0x1000804bea0ce0e7e965,0xdc83308350ff9f0b1f8d,0xaf006010662c3e1f5a5a,0x8e2d41b00a483df013c0,0x180851602fac46c0a44f,0x603945800007e0761dd4,0x880a0e00018eec0cbbe6,0x99ff8fe7] j else page #[0xeeeff1c8da185c800822,0x41204c02680006008018,0x60860c27000efff6f4e0,0x438037ffffe44113000,0x602008d79c7c02c54181,0xc33e70094ab048205212,0x28151b60039d0002bf,0x14750ffff800006401a5,0x6d01241398a000182180,0xd040010000436a7fff1f,0x137a401a8b4ffffff60c,0x301c00f54b7cbb71810,0x70cda37fcfc21a124288,0x5e16bfc03472f5cb20b1,0xef53135440180e0b7a8c,0x19fcca2425f35fe1423e,0x520722f1a00000001bf8,0x7231120f800066015b0d,0x600822cf2003b043cd20,0xbe9f0048400a0926e000,0x1340182c13f2f8077fc0,0x4ffc2e04fe0a2068989a,0xa141005d05e4f43ffffc,0x3ff64f4a800270048252,0xa27100b9c86f8d657400,0x4fffffa81fe04c2cc7d,0x850640b0b901f81125d0,0xa37ffffc2fbf9c6df106,0x30b02684d0060b0726b,0x13bfffff9ff85c09f851,0x6b1ccffb7406a1e14a4f,0x25fe2067259934a] j)
def moH13 (j : Nat) : Nat := (if j<206 then (if j<103 then page #[0x6000220001001100210,0x12500013001001002010,0x40101030010301001203,0x56011014402310003150,0x640280245200101200,0x10000000c00001610001,0x1113130020210b810430,0x45132070000005072a30,0x2273302020132127400,0xd3400412246035106000,0x2d2880f4000600,0xbd100000000d1a112a80,0x460000303b00000000,0x7a207708da9084000409,0x392815b8000000000010,0,0x3a8959000034c745d800,0x9c0d0550000000012c71,0x27c41000001,0x409124f8b0a009000,0xbcdc00000000000bbb80,640745472,0x54800000000003288800,0x25f21f4f714d6800000,0xb01900419a3d00008006,0x2c120d914,0x844c45680000001056c0,16529,0,0x808c04d0000000100540,0x6e0e0000000011984da,0x5a010ac15e0000000000,0x83080006039000000000,1,0xc1be0000000000,0xb00000000015f00,0xa19c00060d20000,307200,0xb2840000000000000000,0x8000005f000000000000,0x606c00000002021814,0x82d40000000000106000,0x104f000000000000,0,0,0x494e0000,0x408a00000000000000,0x82ac00000,0xc1105be8000692a0000,0x10330000000,1068160,0x985f051c00000000000,0xa00000ca360000000000,0x242d4f40c80400030,4252,0x98c046d26600000006f7,20,4294974054,0x8100000000,0x82060108000511c00000,0x401c040400000000001,0x868000e9f59a52014800,1788913,0x95730720000,0,0xa2c874b8000000133540,0x6099c0cd,0x2dfe000145e000,0x23275730000000000000,0x70a800081fc,0,4670357504,0x40001022400061240000,17028097,0x2800000000816381700,0x4000131bc05680000000,0x39c2b444c4000000060e,0x344600000000857d0,0,0xd551263000,0x9538c4e23200,0x184b400000008150,0,0x307e80000001525c0,0,0x33800000000000000000,0xa5e00011186b,0x1824800000000000,0x70e600000138000000,801130368,0x488e4000000020740000,1905,0x833e0a08000012a00000,0xba9e1317f16b00000001,0xae80000000000000054e,0x85c00042fcc1fe00030,0xa000180fc000204c49b7,0xd05054a506a80f,0xa2f9110b467000184ac0,0xd8ea0001041a14ad94b,0,0x1c40000000516800000,0x8ae0000] j else page #[0xa000000000000000344e,0xaa2925,0x80000001142eb3976710,0x1c06e2d3500000000465,0x21818000000001,0x610f0000000000000000,0xfa02b800000018298000,0xd1b00006107822e45,0xe13000010412048cf420,2199,0x1b0000029800,0xa8f0a88518500000,0xfc0002084821c0000000,0x221a51055e0000407501,0x28bf000139aa00304790,0x40e40000000,0,0x269700000,0x62000000000001235,0x8c44baa086e034000000,4,0xb80000000d26f88b4000,0x4800010a78000000184,0x818400000000,0x2b600000000000,0x94680a80000000000000,0xbd0000000000000005,0xfc000616742460000000,0x94483c800020e0000110,0x8e7b81580515a8c00005,0x340000000c25e840a098,0x171000000012c,0xe03000012b0875980000,0x10000245dd2ae000207b,0x119300000001cd,0x42c6000000040a20,0xb000000000001db85002,0x29200000000000000139,0x829c0000000c,0xb80006b5600010178000,0x1f7225400000000001ba,267576,0x685b00000000000,0,0,0x2495800000000000000,0,0xa1281ca8000000780000,0xe40006267000000030ab,0x493a00012c,0xe6f8c9e6000000060980,0x51350000000102e,0x1b1b80002897000000,0x4254000000016ec0,0x1b15c14d00ac0000000,0x120b805fe923000000,0x5864000000e00000,0xac00000000000000130d,0x2a000000000000009382,0xc11f000184cc00000000,0x60500001821d03c,0x8de00200000939407c00,0xc07d00000000000217ac,12303,0x6017268200,0x41140000a26000001460,0xac0000000e1e40000000,1076233,0xc296000000000ea0,0xda22d800002ed004c000,0x3a66b68000000084,9717153792,0x365e40056ae20d2c000,0x23498000022c00,0x202f822a29d70b500000,0xfc000000000000000000,0x84dc00000000000b3,0x217b000082939a000000,0xd60001102c000,0x2d000016b80000c8dc00,133204,0x60cd00000000000,0x256c0000000000000,45216,0xad300000000,0x83012a9e09b000000,0x80000001807b419600c0,0x30a8e0dd0000000006c,0xeb000024798000000000,0x80f60000000341480005,0x140840000d9d18966468,0xd48000233766b2000094,0xc2c2000000000004,0xb974431,0x899000000,0,0x9d480000000,0x24a007c0000917400,0xc2e30000048400060a10,0x2a000000000002022,0x8a3c0000000000000,0x516a5be369900000,536883372] j) else (if j<309 then page #[0x42c800000000000827,0x28528330000db7c00000,0xa00000002960c0b20002,43337741,0x41880000000000000000,0x50a59708000004f04e2,0x2540a424f0000029f81b,0x4b4f45d0000000264920,0x5cc494c16e00000002,0x20618000000,0x444e00024b580,0x374aa26eddf20000,0x4b423804880220000000,0x4300000000000160e00,0xa3da0008000020a0001,0x46000002e6b190000000,1667751,0,0x94ce00000000000000,0x85ac0670000000000000,0x3a5ce493013a13d4,4456448,0x4600000000000000000,0x10aaa0d000000003,0xd5520000000606b000,0x60eb82d680ad0b600,0x81460000,0x8f00010564000600b000,0x3ac20c0a0,0xc000000000002ae00000,0x3841b40000000000002b,12768,0x10059089530f86040000,0x244deeaf000,0x6962000183b220400,0x3634f6b90000814c,0x98a9cbcc0000000000,0xaa0051c0b0000000000,0x8000000000000001d299,0x44d800032318000894,0x294581c7027800000,0x1806d02a800000000000,0x2ed10c00000198000000,0x1d80000000000376be2,0x2f0b88ca0002,0x83980000000000,0x9a80b30000000000000,0x301e0a94095d5277c1df,0x4180b6000000020f1d28,0x66740000000277980,0xa00030bbe89400000000,0x28400000004cfe20e,0x5d200327abf80,0xa000123649240001022c,0x13bca0310000614,0x52800088bc000229c80,0xd8183049b2b300000001,0x3c000000000000000d93,0xb340372a8e000000070,2,0xd381dea5240000000000,96,0x8003a80,0xf800000000000211a000,34,0xa05700000000ae2a0000,0x1068e0bba1c,0x180000000103a80,0x80000000608200000000,42371103,0x2ac1017c81f843f80,0x180760ba000000000000,0x20000000000,0x948000000182e000000,0x20003639000000000000,0x8a0e0000000000080d,0x650000000000000,0x41d000000000000,0xfe00018129a89a064de3,0x221e0ce000181a811944,0x102f800000000001,43433984,0xdb0000000000000,0xc00000000000ccca0000,0xadd200020380000c05,0x4152416e808800000,0x4c700001ad2c,0,3292160,0xc02c900500000000a044,0x92c684600000000c1d,0x20c70000000000000,0,0,2144384,0xe00000000000ddda0000,0x9800000000000007c81a,0xc61732da46934,0xa000201ac0b600018238,0x829c839e169800042d,0,0x184b66e00000000,1053] j else page #[0x105e0d80000184ec00,786976,0x68000000083780000000,0x53f49e8103c286000144,0xd1e00003393000000002,0xa800009c000000000000,0x209f6cbb000000010b,0,0x400000001838769c0000,121,0x1063000040340,0x41a92d340000518,0xb4c00008f70000000000,0x105a4000000000012,0x58223000000000000000,0xc00000000c1ca000206,0x4ae391f800036770001a,16393,0xb000000002ada000000,24,0,0x27f003800041c5a33c00,8,0x409e00000000000,0x25000000000000000000,0x85680004f6d00013,3812,0x9811e00000000a2e400,0x1c38f200a56d48e28,273302540,0x49400000001dc48cb400,0xc85785e4000166f82cb8,0xc402880dc00b40000000,103,0x119b23c7274a8a985280,0x24fa24c07c8000,0x413f0000000000,0x185c00000000418a0,0x80000413800000000000,0xa54770000042fa000307,0x1a501018895100004,0x20c10000a07a443d02e,0xbac00000009a96000000,0x10960672815c5,0x68000c94c0001777ad7c,0x5c800000000000000342,0x3383000000000,0x16f455284440000000,0xca400000000000000000,5,0xb80000000000309a0000,9447843,0x103b40000000c27a0,0x6f63a000000000000080,0x3d449700000a5013ec1a,0x4ae00002084800000008,0xb1f4272,0x109d25060000000000,0xc96c0000032c11a0,0x100000001842c00010e4,0x3037a17f009a000202,0x8064000000000000,0xc8000000000000000000,0x1b8900000000000270,0x18bf800000000,0x6020000090400000000,0xb4000000,0x9caa0ad712e422f02180,0xc0000d135004146a0000,0x172dc12082c485110b,0x84ca937c08d8000c23a0,0xd0000007800000006b09,0x1a603de0f30000000205,0x266f832a755e4975a689,0x48b4049aa4dc81b,0x44a7a0967a00d0000000,5] j))
def moD14 := page #[0x50130481100c020043ff,0xb1eeca4d188600059160,0xe100ba11037d1bac,0xb05818824228ce49012,0xa0060010060501e068a0,0x2609c1f83a4e834248ec,0x9384a28848208262990a,0x58901b0803b8742d902,0x600a080020a8220a030,0x6bc0d04292a39f2a1214,0x4619458212841ea3e94e,0x7029a591d66f96265864,0x2054b81d43616e4e05c,0x17fe00190c05617fe060,0x26242400007ff2f09a16,0x499fc055100a38000fe,0xbf2a0c06404fe000b95,0x97991d6494e800fff000,0xe010944e400000002fff,0x7ffffe000017]
def moH14 := page #[0x81c0084222500080020,0x8000114000100510020,0x244800181f00c6008805,0x62e000088d000,0,0x91a800000000000,0x103503d10cc0b00000,0x24800008d80035340000,0x4c380000006c860bc,0x2060e8000000,0xe0000000000000000406,0xa315e000105800208308,304087106,0xaf05a0000002cdc0000,464226304,0x6040b30037c07c002262,0x206c000014407,0x16e101000000105,0x6000001480006151a065,0x17000102f03900064534,0x69160ca1363b70,84413668,38,4730880,0xc5114000000000000000,0xb9000000000000000020,0xc5cc274000b,0,0x10580000009140000000,0,0x63b836000000000,0x3a000000000245600000,0x98003078000c8d00020,0x536000516e8a80000000,0x20c00000000000000,0x3750000000000145c000,0x40c8000001905490800,0xac65c000811808800000,0x401c000000e990c,0xfc00000001f00000000,0x20000248000a290006,0x8000a300004020000000,0xc19c474108000801,0xa1c0cb968800,0x4800000000000,20447232,0x60d20238200,0xc028000,0x8000000000000300c232,227,0x9800010be8a000000000,0x48c228720400000028,0xf400000000000020420,0xc3d45680010760000006,0,0x40004478000000000000,0xb8002410000000000205,0x8155ca08d000081c24,0x2201800088e6a840,0x65000000000010160000,0xa24021bab10120000,0x173a92a812c0b102511f,0xf1074e2801b30d892800,9793122970,0xa000000000000000000,16,0xb8d00060d400000041c0,0x800000000010b16ef035,3335]
def moD15 (j : Nat) : Nat := (if j%103=0 then 0x4030301011ff else 0)
def moH15 := page #[0x66000000000000000400,3,0,0x9800000,0,0,0x3080000000000000,0xc040000000000,0x3510000000000000,0x1860000000000000,0x21002530000000000000,0x1740000000000001,0,0,0xc0c00000,0x24600000000,469958656,0,0x3a70000000000000,0,0xe98000000000000000,1248,0,0,0,0,0x5dc000000000000000,0xd1c000000000318000,0x540000000000000000,0x29300000000,0x85c0000000000,0x24000000000000000edc,0xc440000000000,0,0x10000000000000000000,0x900000000000001,0,0x894000000000000000,0x7300000000004dc00000,0x14000000000000000003,0x27000000000000000001,1,0x61c000000000000000,0x84c0000000000,1331200,0x5c40000000000000d0,0x6002310000000000000,0x951970000095f,0x500000000008cc00000,2,0x6700107c08,0x22000000000000042000,3162114]
def moLevels : Nat → Packing
  | 7 => (1,8,9,65537,0,0,4099,moD7)
  | 8 => (5,7,9,327684,50,6,4104,moD8)
  | 9 => (31,6,9,1835032,85,9,4128,moD9)
  | 10 => (326,5,9,8454315,136,14,4486,moD10)
  | 11 => (889,4,9,6095050,120,16,4887,moD11)
  | 12 => (386,3,9,1769521,86,16,4753,moD12)
  | 13 => (66,2,9,655368,67,13,4360,moD13)
  | 14 => (9,1,9,65537,0,9,4180,moD14)
  | 15 => (1,0,9,65537,0,0,4099,moD15)
  | _ => emptyPacking
def moIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 1 2 0 2 0 0 moH8
  | 9 => lookupShort 1 29 0 7 3 2 moH9
  | 10 => lookupShort 17 257 2 11 5 4 moH10
  | 11 => lookupShort 152 1523 4 15 9 4 moH11
  | 12 => lookupShort 437 1901 10 16 10 4 moH12
  | 13 => lookupShort 199 1993 4 15 9 4 moH13
  | 14 => lookupShort 40 409 5 13 7 4 moH14
  | 15 => lookupShort 12 431 1 10 4 4 moH15
  | _ => fun _ => none
def mo : Forest := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,moLevels,moIndex⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem monoProbe : block mo 12 0 121=true := by
  change block mo 12 0 (runLength [15946,15179])=true
  apply scheduled_ok
  simp only [scheduled,cells,boxes]
  all_goals repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
end Certificate
end PEqualNP.Outside.L_meta_4813_aux

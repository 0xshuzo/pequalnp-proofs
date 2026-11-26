import PEqualNP.Defs

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4813_aux
namespace Certificate
open PEqualNP.CircuitLowerBounds

def perm5 : List Nat := [32,83,116]
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

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
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
def ecY : Array (Bits × Bits) := #[((word [0x108380004061f0c00,0xdc0661804078f001f]),(word [0x908380004021f0400,0xd40260804078b004f])),((word [0xc10040c83828e03c27,0xde85c999e1ffc070cf1f]),(word [0xd00046c82aa0a0a825,0xde80888161318020e310])),((word [0x6078001c009003018,0x120600060878700fe0]),(word [0x2078001c009001008,0x100200060878500c80])),((word [0xf888000e0031ffc1e0,0x18e437e007f1bf80f1fc]),(word [0x5888100a0100c701a1,0x180515f000e083021178])),((word [0x3000f0003e000240,0x60f83801f801c000fe00]),(word [0x3400f0003c000240,0x60f02801f0014000ee00])),((word [0xc000ffffc0000380,0x7f003ffe0001ffff0000]),(word [0xc1005cf180800080,0xb003fd84481f0644400])),((word [0xffff0000000003ff,0x80003ffffffe00000000]),(word [0xd9980080000203da,0x377c9ecc22080001])),((word [0xff00000000000003ff,0xffffc000000000000000]),(word [0xfd0000000000140377,0xf4efc000000000000000])),((word [0xfffffffffffffffc00,0]),(word [0xa72664a1063f18a804,0x20400001010004008882]))]
def ecC : List ColumnInfo := [28,76,283,2123,33554457,57,268435529,201,537,1049,4120,33554584,268436040,1080,4194327,67108887,134217751,16777287,231,567,4295,4631,5143,134217782,134217926,4195350,67109910,16778310,67112982,134221846,16781382,4149,134217957,134218293,33555093,33555605,1253,134221877,134222021,134222357,67114005,5173,16782405,5317,4324,4660,268437092,134222052,134222388,33559188,5684].map (columnFrom 1023)
def ecA : List (List Nat) := [[],perm5]
def ecD9 (j : Nat) : Nat := (if j<103 then page #[0x4ca98c31bfed9a1a6053,0xf2dd9860d6318717ecc3,0xa558c61e5bb66cc2c630,0x736fd3326c18c38bf663,0xa9b2030e2fd98e998318,0x3db660d6364061adf36c,0x59590186b7ddaac6c80c,0x1adf766b2b2030f67985,0x30ac80c35beed9836406,0xd6f9b3e1990186b7ddb,0x1a3e1861adf36bc33203,0xc737bd4f4cc09038bf66,0xcb1b0298c3ffb86a5654,0x631bfed9a960531f5ab0,0x9e99814c797bcb70cc0a,0x318dff6cd4b0a98e6f4a,0xb3434c2631bf6dba1655,0x98c6ffb66a7854c637fd,0xe396e1931cdef2cd0f0c,0x54f1fbcc342432a74bf6,0x74c8922a9e3df9868c86,0x2a71bfee996259538fef,0xb86a56354e1ffdd3304c,0x953b79b644c306a9c3ff,0xdb3434c2a74bf6db98a1,0xab1e3fb986808558e37f,0xe61a621563c7bf30d190,0x558f0ffcc34e42ac78bf,0xf74cc130b1c77fba6549,0x1ac79bded9a12616387f,0x5b12618658ede6d9130c,0x4d81b1fb6e4c30cb1daf,0xfdb35229b039bd259a11,0x6c0e6fb966808360637,0xfe59a420d81cddf2cd11,0x8360733fcb34a41b039a,0xfb4fcb106c0e67f96a94,0x49b031bfeeb9620d81c9,0xffa8259536063efdd326,0x54d8197f360542a6c0e2,0x7edb752a9b032bf6d8a8,0x326c0c6feba259936063,0x3f69c9694d818dfd75cb,0xa5360637fdb35329b039,0xdef2cd0cc6c0e4fda7e5,0x3cab075bd6c4a3e5981c,0x6ffb66869894e37fdb34,0x858e6195f970d32a730c,0x73eda950b1cc33bd6c4a,0x1b0330cef5b1aa163986,0x3bd6c7a660e619de974b,0x8595a0e37edb752a9d03,0x8dfb73d330398c6fdb6e,0x52a9ec31bfee996d4731,0xe3ff986869854e1ffdc3,0xa1e0d539dff6cd0d30a9,0xe77fdb343c1aa78ffe61,0xcc2a6b0d3ffb865b9154,0x36fdee15360561adff6c,0x2a15360757fd412ca9b0,0x1b5fb6c542a6c0dbf9b0,0x306a9b032ffae8a854d8,0xfb5e85a0d53607b6fcb,0xb8654d81edbf2d41aa6c,0x737ed472ca9b032ffae,0x1cb2a6c0e6ffa8e59536,0x39bfe59a5a0d81d5ff5,0x3a168360797e4b50b41b,0x81cdff2cd2d26c0dbddb,0x4330a9cc35bf6d6a3e59,0x30dafcb8699539871ffd,0xc78654e61e5fb31c32a7,0x986f6ed9f0ca9cc37bd6,0xca9b0330cefdbae1953,0xe636fdee15360661f5ef,0xc14006400337fd332ac0,0x62c55044c3c035c2f821,0x789ec9608d48207946b8,0xcd48cbcc58bccb68b04a,0x2cfa0f3ced8e74e10da,0x112852211bd1590f5091,0xd59152d4c946540139d3,0x8ed88982579970d68161,0xf9b95b31acda419b5951,0xdf19eb5dd9d25cc1c5db,0x1d617210e0aa045fe1f7,0x824f646a3b632a29e23a,0x687a81678a6fe69a60e5,0x9ce99297e91a9068ca8b,0x72b5eb22ae6aaaa46a0a,0xec8ac4ec3abd6bc2baeb,0xd3ed2ad16d02cc6cb2c9,0x2f83e00added7ad66d52,0x102c0d941b44c164481a,0xa285f081b058a1430be,0xd1122a0fc1f004890502,0xb141b84fc305a12068c0,0xf0e120a061460ba10360,0x84c2a18558282de18345,0xf0c1a1835e1e0a6a13c3,0xf0c5506860de0a6a0c55,0xf802f050510360b0a83,0x7c105c7e] j else page #[0x80205bc10347e0f80206,0x7c01783e00bc1f005e0f,0x82080fc10385e07822f0,0x7c01783268bc193440cf,0x83e00bc1f005e08382f0,0x408782a48dc3f08141f,0x822f03c11783240bc1f0,0x40df800c0fc19205e07,0x4140586c4f83e00fc1f0,0x1220521710320a420307,0xfc21c15e18bc1f005e0b,0xbc3828523f81e18ec391,0x5e1a142f07c01783e00,0xc16050152783448bc1f0,0x7c0102a0a02fe182c507,0x83448bc10645e00302f0,0xbc1f005e0f802f07c017,0x87e0f802f03c11783e00,0xc4a201de0b0a3e17c112,0x81d181de0b0a364f85f0,0x7c3074607782c28e0d84,0xa305fc1c147e07822a1,0x92104921f07c0102fe0e,0x38141438484008492204,0x40140648083410681c10,0xa020a25051001448,0x486122000000001008] j)
def ecD10 (j : Nat) : Nat := (if j<412 then (if j<206 then (if j<103 then page #[0xbe58d901872fd9858c61,0xee19901876f96564061d,0xea5812072fd98e1861db,0x598320f75d9560c839fd,0xd8621a7dfa960c83db76,0x9321a6ffa961886d3f65,0x854e6ffa666131db7619,0x54e7f5a1261539fe6809,0x4e3fca8659539bf69898,0x66fda6e45538ffea1965,0x7f9a0261639bfe999858,0xeda2261639fd6849858e,0x786606619df6949858e7,0xa1e1a61cbf66386987af,0x5614319bfe9991e0eef5,0x618539ff6a5850c777d9,0x58539ff6a58614f6fd96,0x8539ffea19614e7ffa16,0x539ff6a68614f6fd96a1,0x1df764d531867fda1a60,0xbbf699531873fd9854c6,0xffa61531867fda954c61,0x760d631867ffa954c61c,0xe95631876fd9858c61fb,0x4d831876ffa958c61bbf,0xd8318777d9560c61df76,0x831873fd9860c61d7f65,0x318777e9560c619ff6a5,0x1877f95364061bbfe998,0x877f98564061dfe60d90,0x77dda864c61df7695931,0xefda3e1861cff68d9818,0xfda961463ddf6558518e,0xd95a14639ffea19518e7,0x9354c819ff6a68518f77,0x954c819ff6a5532077dd,0x60481fbde99812067ffa,0x4483dfd6959120f7f7a9,0x483ddf6859520f7f5a66,0x83dbf6859620f77da665,0x1df76959321b6fda5658,0xbfd684854c6ff9a02153,0xf768c854c6feda221531,0xf69c854c6efda621531b,0x6a5514c67fda921531b7,0x19634c6ff7a154d319ff,0x1634c77dd9858d31fb76,0x634c6ff7a158d31df7e6,0x54c67fda959531ff5e85,0x4c67ffa959531dbfe596,0xc7ef4a660531ff528d81,0x7fd56360531dfd2a5814,0x7f59560531efd619814c,0xfda960531dfd659814c7,0x78660531ff598d814c67,0x9660531dfde55814c7bf,0x360531bf7e8d814c77f7,0x60531bbfe99814c7fd7a,0x19319ff6a5854c7ef7a6,0x5319ffe85954c67fda96,0x319ffe99954c77f7a165,0x1dfde85964c67ffa8655,0x9ffea1964c67ffa56593,0xffe8d984c76fca666131,0xfe95984c77dfa3661319,0xe99984c67ffa6661319f,0x62634c76ffa666131bbf,0x6654c6ff5a199531df76,0x814c77f595a05319ff6a,0x54c67fda9a1531bfd6a2,0x4c6efda6a5531bfb68a9,0xc6fdda3d45319ff68698,0x6ff5a1d4d31bbf69b514,0xff5a1e0d31bf768f814c,0xfda9e1531bfd687854c6,0xda9e1931bfd687864c67,0xa6e5531dbfe5b864c67f,0x5e59319ff6a3954c67fd,0xe61319ff6a3964c67fda,0x19539ff69b984c67fda5,0x953bfd6848654eff9a02,0x539ff6a48654efdda321,0x39ffaa48654eff6a1219,0xdfd6449154f3ff982195,0xffaa49654f6fd9625953,0xe6809854f3fd98261539,0x6849854e7fda126153bf,0x849854eefda626153bfd,0x49854eefea626153bfda,0x6354e7fda958d539ffaa,0x354ef7fa558d53dbfe59,0x54ff5d8560d53ef72618,0x4e7fda960d53df765983,0xf7df9660d53fd7a15835,0xbdf9860d53cffe618354,0xfda961953dbf6598654f,0xca8659539ffaa58654e7,0x9665953cff2a19654ebf,0x3659539ffe859654f6ff,0x65953df7e8d9654e7ffa,0x5953affea19654e7ffa8,0x153cffe619854f3ffa86,0xe7ffa166] j else page #[0x7dd96a0d539ffe999854,0x5e85a0d53bf76a28354f,0xd96a1953df7e5a8354ff,0xa9a19539ff6a68654f6f,0x8a4553cffe628654e7fe,0xa4553affaa29154ebfda,0x6153dbfe5a9654f7f791,0xd53cffe629854e7fda1a,0x53dbfe5b6354ef7da5d8,0x3cffe638354ef7da5e0d,0x9ff6a78654efdda3e195,0xff69b9154e7fea9e1953,0xf69b9154eefda6e45539,0xa9b9154e7fda8e4553db,0x879654f6fea6e4553bbf,0x79854e7fda8e59539ff6,0x535867fda6e61539ff68,0x3586ff9a020d619ff6a4,0x586feda220d61bfd6848,0x86f7da520d61bef69083,0x6dfda720d61bbf698835,0xf7ea520d619ff6a48358,0xf7a6605619ffea553586,0xfa6661619ffe8d98587e,0xa994d61b7f69e535876f,0x1e0d619ff6a6835867fd,0x215639ff6a783586ff5a,0x1563bfd6848558eff9a0,0x563bf768c8558efeda22,0x63b7f69c8558eefda621,0x39ffaa48558e7fda9215,0xddf6549558f3ff982156,0xfe6809858f3fd9826163,0xd6849858e7fda126163b,0x6949858efeda226163bf,0x949858edfda726163bdf,0xd6558e7fea926163bdfa,0x8358fbdc9860d63bf7e8,0x358e7fda960d63fb7619,0x58f7df9560d63fb7a198,0x8fbdf9860d63cffe6183,0xe7fea961563bf7e85835,0x3ff9861963ebf2618658,0xfca865563ebfe618658f,0xf9866163affea19558eb,0xa5661639ffe859858f3f,0x599563bf768e6558e7ff,0xa0d63fb761a8358f77f9,0xd63bf76a28358efdda1,0x563df7e568358fede86a,0x639ffaa68558e7fda9a1,0x3bbf6a28658f3ff98a15,0x9ff6869858f77f95a556,0xbf69b8358f3ff98a6163,0x768f8558f3ff98e0d63b,0x6a78558eefda6e1563bf,0x8f8658e7fea9e15639ff,0x79158f3ff98e1963bf76,0x9558e7fda8e45639ff69,0x558e7fda1e5563dbf61b,0x58f6fe86e55639ff6a39,0x67fda5e61639ff68798,0x6ff5a114d81dbf258536,0x7fea914d819ff6a45360,0xf9a020d81dbfe5853606,0xda420d81bfb68883606f,0xa620d81bdf69483606fb,0x520d81b7f69c83606efd,0x20d819ffaa483606f7ea,0x4d81dbf258936076ff96,0x981dbfe58936077dd932,0x81dbf25953606efea925,0x19ff2a553606bfca854d,0xdbfe59536067fea954d8,0xffea553606bffa854d81,0xf619636067fca958d819,0xe59636067fea958d81eb,0x59836067ffa958d81dbf,0x9836077df9360d81dbf2,0x86607aff8661981dbfe5,0x3607aff9661981dbfe59,0x6076ff9664d81dbf2599,0x76fc9694d81bbfe9993,0x6dfda794d81bfd686536,0x7fea994d819ff6a65360,0xf5a198d81dbfe5a53606,0xea998d819ff6a663606f,0x96a0d81dbfe5a636067f,0x3a0d81bfd686836076fc,0xa4d81dbfe5a836077df9,0x4d81bbf69a936076fc96,0x581dbfe5a936077df93a,0x81fbde5b816076ff96e0,0x1ebfe5b866076ff96e0d,0x9ff697936076fc96e4d8,0xbfe5b936067fda6e4d81,0xf687966076fca3e5981d,0x68f966067fda3e5981db,0x87966076fea3e5981dbf,0xf96607ef7a1e5981dbfe,0x9160eefca664583dbfe8,0x660efdda3a1583bbfe99,0x3bf768e8] j) else (if j<309 then page #[0x9ff69b9160e7fda5e458,0xff69b9560e7fda1e5583,0xf6979660e7fda1e59839,0x6879361a7fda3e45869f,0x55538c67fda5e4d869ff,0x5818c6ff7a154e31ddf6,0x838c7ef7a660631dfd65,0x48c67fda961631cff661,0x8c77bf8565231def6159,0xc73fd98e0e319ffe9598,0x6ff5a1e1631bfd687838,0x6fd96596539ff6a7858c,0xdd9660e53bf7e8d6594f,0xd9661a53cff6618594f7,0xa961a53d7f65d8694f6f,0x865a539ffe859694e7fd,0xa1a53dbf65a8694e7ffa,0x62539ff6a68694f5fd97,0x653dbf65b6594e7fda1a,0x61bbf69953986fdda3d9,0x19ffea5539867fda954e,0xfb760d63986efca858e6,0xbfaa1639876fd9858e61,0xfe9563987ef7a158e61b,0x64d81987ef56360661bb,0x9981987ef78660661dfd,0x9839867fda960e61fbde,0x989867ffa366261bbfe9,0x3986ff5a1e0e61dbfe99,0x9876fd98e1a619ff6a78,0x86efda3e1a61fbd68786,0xf7dd9560e63dbf6a7869,0x7fda961663ddf6558598,0xffa165663cff6618698e,0xda3996639ffea19598e7,0xa9a1663ddf6568598efd,0x954e819ff6869898e7fd,0x60e819ffea553a067fda,0x5683dbf65986a0f7dd93,0xa839ffe9995a0e7ffa16,0x839ffe9596a0e7ffa165,0x3dbf65a86a0efdda3a16,0x9ffe9593a1afdda3a1a8,0xf766163cc7edd8658f31,0xf6a565cc76fd9659731d,0x65981cc67ffa9597319f,0x6181cc73fd9860731dbf,0x981cc6fdfa360731cffa,0x85cc777d9561731bbfe9,0x5cc67fda961731dbf659,0xcc76fd9661b31dbfa598,0xc67ffa6657319ff6a586,0x76fca565b319ffea195c,0x6fda565b31dbf68596cc,0xfea565b31dbf6a196cc7,0xfa565b31dbfe8596cc76,0xa865b31dbfe9596cc67f,0x699731dbfea196cc67ff,0xa17319ff6a665cc76fd9,0x1731dbf65a85cc777d95,0x731dbfa5a85cc67fda9a,0x61bf768f51cc76fd96d4,0x19ff6a453d86ff5a114f,0x9ffea553d867fda954f6,0xff6a583d877dd9360f61,0xfea193d867ffa564f619,0x6a653d86dfda794f619f,0xa683d877dd93a0f619ff,0x585d8f3fd9860f639ff6,0x95d8e7fda961763ddf65,0x5d8e7ffa865763dbf619,0xe067fda9a1763ddf6568,0x67fda954f81df764d53,0x67ffa954f81affea153e,0x7dd9358f81ebf61963e0,0xfda958f81dbf65963e07,0xca6647839ffea563e067,0xa6647839ffe9591e0f6f,0x664783bbfe9991e0e7ff,0x60c619ffe8d91e1b6ffa,0x531ffd615814c77fd95,0x531dff661854c7ff6856,0x31ffd616814c77ff9861,0x1bff6a2854c77fd98a15,0xbff696984c77ff98a153,0xff697814c6ffda8d4531,0xf697864c6ffda5e0d31b,0xe856354effda126153bf,0x869854efffa165953bff,0x78654effda1e0d53bff6,0x9154f7fd63e4553bff68,0x154f7fd96e4553dff61b,0x587fdd8354d61bff69b9,0x86ffda854d61dff66153,0x6fffa854d61ff7a0d535,0xffda594d61ffd54d8158,0xfc9654d81bff69683586,0xd8354d81eff2a153607e,0xa854d81eff61953607fd,0x654d81ff7a0d53606ffd,0x54d81dffe5953607bff8,0x4d81bffea153607eff96,0x7bffa85] j else page #[0x6ffda5a0d81bff696536,0xffda5a4d81effa168360,0xfda5a4583bff6868560e,0xd9560e31bff6869560ef,0x8354e61dff6159194f7f,0x654e61dff66153987fdd,0x54e61bff6a153987efda,0x661bffea153987eff86,0xe81dff65583987ff5536,0x81bff6a153a07fdd8354,0x3dff65583a06fffa854e,0xeffa1a85a0f7fe856468,0x6d006400037fd9560731,0xc58159024e038c04f80,0x9f0125021803de06f4,0xe707460d5819202f2058,0x27504b8090c115021103,0x418f82fd05ad0ad21470,0xa00ea61ccc37786bd0d0,0x45f088c10b420583ed87,0x627044be8954124423c0,0xdb156429dc5198a1313e,0x5ea8ba316f42d205820a,0xc331864e8c59184e2ff8,0x41b92365c6ae0d2a19c,0x7760eb11d2239a071b0e,0xa404c7e78fa61ec43c78,0x63226243b485d9077208,0x9451258244c47888cf11,0x4d1499292fc25a64acc,0x5628364fec9f213b2270,0xa9a94f1297e5234a3b14,0x5778adf159e2aea5554,0xef2d9e5a2cb2396302c2,0xbfd97c02f2e5d04b8c16,0x66440c6198a330ac60fc,0xfd339666accc5996b329,0xd651aaa3514693cd1319,0xe6e38db71b45364a6c14,0xd5396a71a0e169be0376,0xef99d9d3afa7508e7f1c,0x7bd8f621e923cc078b8,0xec3faa7eb0fc61f5a3e5,0x53a07e40bc808d0019f,0xc86cd0c5214f42168365,0xfa459089ed124a21743d,0x1eca39546c68ce918d22,0x292e124c246f487a9075,0xdb4b7696012a2a50a49c,0x354267f4cbe98b5306a5,0x29e1d3aaa7354e069b45,0xbc5114a119405a7eb4f7,0x4d2298452a4a43947728,0x6aa7953aaa435446a77d,0xdc571ead2d595ab0b55d,0x654ac8058c0b10160bab,0xeb6b16b8ad3f5a2cb349,0x995d04b9417182e105bc,0x7c0af585e3abbf57612e,0xcc1a5820300e5fcabef1,0x8c62d8c50d891b0fa616,0x935b24b6432c7c18e3b1,0xcd7199532f8659eca51,0x7f68bed0fda0233d2674,0xaca35506a3cd3b1a6634,0x6dac9b44b63c6c02d761,0xba6f10dd7db96b7046db,0xc5eb89470b2e0c1bfab7,0xae76dcd4b9777254e3e1,0x347604eb41d4f3a5a741,0xe1bbc057770ee61dbc3b,0xaf5c1e963cfa7990f1c9,0xf67d76f9ddf1e3e017b7,0xebfd97f3cfd8df98be,0xf03f2060c0a180f10186,0x70847d07ea0d6c160826,0x1ddc36e86670b9a15a42,0xb12b2241c451881b0f6e,0xbd8b29158a29cc52289a,0x37fc6df8d37193a300c5,0xb200a3f147a78eeb1d0e,0x40920b239645e4881907,0x50fc9f693ad264a4b949,0xf2c1e56f4aac9507298e,0x697a92ed25c14b3e964,0x67bccaa98f1311a6134c,0xd392e715cdde9b2334ee,0x899eaf3d027874ec19d0,0x84f506ca0753fda7ddcf,0x5473a8c55158a23b438a,0xfaa5a34a7e936d244a42,0xa0353dda7574d9e9a3d2,0xb546ea7954c9a90b50e2,0x23ac07576aacfd56daa9,0xb8156c7ad6159d6b2ad6,0xd6016bee5798aef15cd2,0xdb1b762eec40584eb05,0xcf659c3b323655ac96d9,0xd6b52d4cda5eb46b6832,0xdcb7796e2adac5b2fb60,0xe66dca4b8d37102dfe5b,0x57766ed3dd6cba757422,0xede2bbc0] j)) else (if j<618 then (if j<515 then page #[0xdeef9bdef3bd717a62f2,0xc14581e701adffabf917,0x961c0c32f854f090e0ef,0xb231546264c489884b0f,0xc7df8e8b1af632cc6078,0x764b3c92791cf229e421,0x8332e4658dca93945f27,0xcdd79ae733ae643cc479,0x2e7dccf679de33a7e71d,0x46b478e8add0f7a0bb40,0xd483a81b4e1697ed287a,0x66b83d67fac5b56dea8e,0xc7611ec0cd7d9af335d,0xd95bb25b63fec68d8a3b,0xded3bda37b3ef66decc4,0x8376fb6dd6db7fb6136a,0xdd25b9ef72dee4ddc6db,0xe6f05ddddbb5f7576e97,0xef37ce6f7cdea7bcf378,0xe0b9c0f380e6ffcdfcbb,0xe7105e1cbc317857708e,0x6878c5717ce2b9c4cf88,0xe45fc83f8f371d8e383c,0x7f2cfe54dca1b9337246,0x305b8630e1048bcc3f97,0xfc309942c09a170c6012,0x4e254282f0c2c70b5085,0x1424d2485e170c2c7144,0x87c20a142bc3e1034285,0xa142c15e1f082850b057,0xc20a0351840b05787c20,0x81a1428541bc3e1050b,0x88662821e1f08e15e1f,0x8414285b86c20a850a27,0x5785c30b050a160af0f,0x70883e9b88c3f0b86164,0xf8460883f118712f0f84,0x109b860d289e8a191370,0x6162a3786c20a850a27e,0x3784c30a054a150a70b8,0xfe1f09014e105786162e,0x85c3069c2c5506950321,0x9510bc3e1203a192a953,0x50cc5387c238582e0e2a,0x91c243a37860f38422b4,0xb942687e1237860f3028,0xc20a70c207e122386140,0x23868838382e30701511,0xa124c09070142107e14,0x87e170c9a60451785c3,0x401308e1f08240e38401,0x2090a0a89e1f08261e28,0xa1689c4b8625282787c,0x1f0826142a2787c20907,0x4160d9c34090d888889e,0xf84121814501405e178,0x74286c463e1c485030b7,0x83660d52113c30970822,0x10482c8c204c1fc30970,0x212e1044e05e106c5e4e,0xd13c209054a0f0470d1,0x2e18485050d70ca98527,0xc3430250a121b1790134,0x89e13c3e104c3c504f0,0x41b179034c8e1c2425c2,0xa37860f3e14a81b18278,0x20a237860f282891c243,0x9050403e0fc2e1c34dc,0x421f85c3469b848de185,0x80f2f0f848d09850a0f0,0x8f85c30a2349c3e12342,0xfe1f082a14069a2b140f,0x8240e385787c209064a1,0x1854240f3935901ce1f0,0x7e170c2a20206193c2e,0xc2e50e32385c30b0482,0xe1f08290d08960fc20af,0x3250e85113c36104c3c7,0xb0f84130f1c91c3e1050,0x6e1f0828130d943a14c4,0x8261e38582fc3e104c28,0x10502611387429892370,0x87e1437861c284013c3e,0x83c17203e0fc207078a,0x3e107a1a4e107a1a3e1f,0x832110b8e0fc20f0349c,0xe1874a110570a1bc30e1,0x408e1f0a1a1e2844100d,0xb0481c60b0385830a064,0x22017083c19185787c20,0xf041c50984815c10c943,0x8e1f0a1a12071c380a06,0x38140c8f84120c8c1e0,0x21f04321d18b02a12141,0x868782f0b82192c341c1,0xe170c387070b04170744,0xa08e170c3a7088401c09,0x7041c446f0c6230883e1,0xc2e1a51bc1080648110e,0x42e4080200e110783b1b,0x881f850de1870c0e06f0,0x820883c43c286f0c3a70,0x41140385] j else page #[0x642230803c1208e1a1f8,0x48441c08e170c388090,0x2430782385c346840c10,0x4848323048385830883a,0x1c3e14343c5038384030,0x341c12243786120e109,0xe18401213e170c386e1,0xd1a0e30441d12184424,0xe890e1a0e090c1e08e17,0x41c121844260e09102e0,0xe105032408f081c12243,0xf040278614e104500f,0x8391c20e01c1bc107182,0x4108c241107823850de1,0xf84123a37821d0d13871,0x107386193040120807f0,0x5c30e2782190e8c2207e,0x34206088401c09038178,0xe1b089a14283c11c2e1a,0x9a11293787c20a068a88,0xf0f844d0a03cbc3e1050,0xc226850a49e1f0826142,0x7061186073874d2e2387,0xb0e88934508870845088,0x501c6e1870443088c441,0xc270c382218582bc3e10,0x11c3e11342850d70c441,0x1f08287c470f844d0a17,0xc226f0c386080380a1ae,0x1c38607c1c3a1b202a0f,0x58478414204387c2894,0x841b0e943bc3e1070285,0x240a14e170c1e80e02b,0x1d187787c20e050a1007,0x8381b270822141f0836,0x30e1c1417e1860385e1f,0x31c30b9c22100701785c,0xe143411188c38080d708,0xc500060384e1f082e180,0x103dc00d8609c10705c6,0x70e70b8625305c00180e,0xc1008d3785c30e18238,0x446230570f84170c07,0x21a0b8c200e04f0c6250,0xf082838902b86180e178,0xc3838749c2e1c1c5040d,0xc38505517861b0e1439,0x30d14121b0e8c23c226f,0x9bc3e1048385a687037c,0x1888383e1f089a140794,0x60e386823c262f0c386e,0xb861c28441e05e105b8,0x81f0f844d0c070a11a4f,0x1408e170e0e1a3878341,0x1050749e170c38112844,0x870701787c20a068c1be,0x40323080380b49e1f082,0x31890200e26f0c625e08,0x3c1c0701785c340389bc,0x6f0c6230d06c44308024,0xbc3e106c347e08382e32,0x381207e170c388080380,0x881f841ce185cc11080,0x4616468607c246f0c3a4,0xc6902cc30c6349c10723,0xe47e105b878d385b8618,0x1331a50b70c208d20541,0xf047091bc307188fc20b,0xc3a42411f8416e1e34c0,0x886060ee08347c246f0,0x1a26103431c2e1884bc0,0x1237860e37091bc30e93,0xbc307181dc1468c1e08e,0x1b86c20a08480f047091,0x20a084848e1864a7c20a,0x828172f0f8414109187c,0x8208dc20a084848e1f0,0x1e38441c48e194f8414,0x778748203b861429f089,0x8e184028424074303088,0x385c307234c1d0f08c6c,0xf08c819e08744640782,0x46310877861e11943ac3,0x1050dc3e10504240e878,0xf0ec343040783b8621e,0x82825285817c208874a,0x40511bc2e1840e1ce1f,0x822728718a14e106ca0f,0x5238707e1044d07e10a3,0x48e10511a30e84446308,0x5061c0701c0a1ee170c3,0x12846910de1840bc30b8,0x841708858e180a427862,0x70f841d0d85ce0fa470f,0x8d07182348e184080fa4,0x11c2e187100f0470b86,0x20221bc30e901c050884,0x81ce18584040d434301d,0x4823c20a143dc209064,0x1283870bc346c1c4e40e,0x81c53e1f08301c306387,0xe1d2080ee114c91c30e1,0x8183c1d] j) else (if j<721 then page #[0x21b0e86081ce170c1a14,0x874a0f0470b868d07184,0x20e0460e10404691c2e1,0x91c30c7082250491787c,0x185c2850a03c3a110b16,0x802f0c29c208a01fc2e,0xc1c05a470f8414383c1c,0xe1840a070e704210d283,0xe11e1437861c2d20370d,0x8461e0783811c2e1c34,0xc2e1871008070907c30e,0xc39c30d141c050f07411,0x483c11c2e1a341c66286,0x1108038120702f0b861c,0x824192d2387c28a234a,0x492387c209038e08e1f,0x4050802491c3e111d010,0x181d050c52387c28a1c1,0x509058c1f6170c2a120b,0x85c30a8482c70ff09861,0x7f85c30a8482c60f811,0x4c0b143fc2e185424163,0xf87c2240482c60ff0824,0x8a9c3fc20af0c2416307,0x514469c200ea3f081bc3,0x8b48120c883416a470f8,0xc3141b820e0f8e8fc2e1,0x786150a094c160da3785,0xe187100ae18944440b01,0xfc3e1202210050240bc2,0x17861c384215050cd228,0x70278631285f121ee00,0xa0f0502013c31288ce10,0xf0a1a184078420de1894,0x20e8604260883c1408e1,0x1007e170e1a0e401f87c,0x3f08365e14503630b83c,0x480cc1787c28a1c380e2,0x583040af0c1a140b143b,0x20da20bc30c85c81ce18,0x1c2c106a240ea423787c,0x170e281a2837820e1290,0x9c2091c1fc20906488de,0xf841207205820c48989,0xe70f841240401e0804f,0xa18e1f0a2870a0401208,0x8481c70711c4a3075220,0x3e111c6050782387c286,0x628682f0f8514109413c,0x370824191d2051c2e1a3,0x7c28a1c3847e1883801e,0x23868da5981d48828638,0x20c8c1bc10709481a8a5,0xb140752387c20c184a1,0x3c541b141c5787c282c5,0x60d18401d1506f0f8514,0x70c3870770b862d20678,0x4e006c303070440fc20d,0x787c24a084a0ee170c5a,0x8c3430342f041c17221,0x90850c70f84943860322,0x6a50695e1f081a942839,0x3141f0f841d0c084a950,0xa1f841b2f0823141f082,0xf40710fc226844a08e1,0x207080240a0ee1f0828,0x470c1c90782387c22685,0x14082024110803c13c20,0x7860e4038100507f0f84,0x868423090441e08e113,0xa0e303c1016e170e1a6e,0x82dc307a01e08e170d1,0xe12360e1c28380e0508f,0x5a0de084c385110785c3,0x12342260761f85c31694,0x13e1237860f3d238707e,0x50a9486c2f861328440e,0xe1437860f384e09c386a,0x548e1a37841130440e13,0x850a1f0e708288d08982,0x7a470b868d387c1fc246,0x8bc2080710e1a383c220,0x10508928470c301c2c22,0xe503f0a11c30794241ce,0x5119c21013841ce18502,0x70200a1ce1f08281040,0xb07e170c347838382e3,0x6928bc3e105034508038,0x4de1f08281a2f08288ca,0xc200f0402787c2090390,0x10928a85e1f0838870d1,0x38589f0e241d270c3887,0xa951bc3188c23c246f0c,0xc286f044e60491b87122,0x48aa3e1f08242720508f,0x2138f87c20e848425e1c,0x441f0c85b8612139b871,0x285b8455e1834a860906,0x7c246844f050b704321d,0x844fc32a084612078238,0x10e86480f0404b87c286,0x4321d182782190e920bc,0xc1a542f0] j else page #[0xb15785c342950dc22af0,0xbc2e1a14a85e1e14a830,0x70b86140d1037c20a0ca,0xc308141c05e1f08281a3,0x847c246f0c4e403f0a1b,0x70e10901b0d0609c30e0,0x1c05e1a1f841b370c908,0x9070a0f0470b868d0718,0x2446f0c2431223787c20,0x7385c30a05ca8d097082,0x30e86861007027863128,0x83907e1868f070705c7c,0xa190e18e185480e8970,0xbc34389c9c20d0878649,0x5ca1103f0a1bc30e189,0x3e1f08290d285b87c20a,0xc385047090e0de1874c2,0x270f850d13110fc286f0,0x7c286a1c1c50b7041c25,0x89460a03f0a1bc3071b8,0x7c445387c282860c0e43,0x82870702891c243f0c34,0xa70c1e8a44143a19e1f0,0xc346850a10070240bc20,0xc1449e121f8621352385,0xd101e08e170e1a14081,0x20807f0f85074237821d,0x943307e170c4e5080381,0x20ef0c2e706f083bc310,0xcbc2e18504240cb220fc,0x2f041c171c1f841de1a4,0xfc10c884607e1437861c,0x86460f0470f850d83874,0x4a470f840d43874dc10e,0x7864843870a072406034,0x44143a19e170c2948387,0x507838200943f0b8648,0x1785c3139785c3468529,0x303e2440386f0c62343c,0x415c246f0c386e085c46,0xe10451a51086c3420204,0xc0f0470f848d089c8e1c,0x858e1103f0a1bc30e182,0x3c488041107c378421e1,0xf861c4691c2c5e08684a,0x89422070782385c3469,0xc8d07f0c2c5e1c1f848d,0x8602c446f0b86160c143,0x40f61f850de1870dc306,0x387c24686088d2470c38,0xe1f08280f403b841b0a1,0x3890bf0c385080381205,0x10200e0481787c20a1c2,0x6e1070290d207386170b,0xa1a11387387c20684028,0x470b870d383c1014e1f0,0x15e170c1c4d30400e0f0,0x4200902f082bc307a035,0x883c1408e170c9a10404,0xc1f20662b45e1f0a2860,0x2029c3e143422704f041,0x20741c6130903c364078,0x204890789c6120741c61,0x120709121c108c2a1078,0x708240e11201c20e0204,0x1c38483c423090384120,0x10389a30384c92311070,0x44942838c0a249141e41,0x44200d185c1c20983c1,0x4d10c4200d24902c101,0x381a21103c1c324042,0x81a20b0381b09203b1a2,0xa4287060e0f881c0d103,0x14619428582e40d89441,0xa44c14822050a061a070,0xa06890707c6190808320,0x50d038a1a0507060e028,0xe0a851068260e1888140,0x808882411070c3448070,0x3c6130781c2242284444,0x24110c321d1074212070,0x40338d212821908085c,0x248184c1e2848643a30a,0x380a1c18380a3118c42,0xc3090381030983c0e112,0x868541c31409c4] j)))
def ecH10 := page #[0xaa04010178e0e0000100,0x9540a2e003020214b820,0xda0b3cdc00e261c36137,0xc33f1f529aed00073a28,0x157101262a331c147601,0x7d5cb8b352d6b80a0447,0xb3838f321f2896dd5b28,0x3d790a6035d33e424125,0x23906703f36c5059467,0xf56932258bddc4b5da05,0x3b508e45f59b0c34fc66,0xe6e114e3142f642c631,0x72300d31a309000a2d00,0x941a070000006628a8,0x8c1ec36000000000c350,0xea7d64a4c53c251b0ee6,0xd55465b0f83789e957,0xc4dddf00000011ba4e0,0x5ea48000930a1700,0x6174342a31185ae00f70,0xa1886f63400014a0,0x620303e54b4900000000,0x86ad12000853,0x2a1d0009408e655f0000,0x36900000000091300052,0x2d7192782b000dbb606,0x6c8aa2e00000051982c0,918657]
def ecD11 (j : Nat) : Nat := (if j<206 then (if j<103 then page #[0x94186fbb2630dfe64061,0xdf7a4c619fecc0c37bd,0xcc81077bd942067fd303,0x20efdb2441dfd64483bf,0xbf65883bbeca9077bd94,0xa9077f69120ebfb2e41d,0xaff320435bfa5883bbf4,0x65086beec990d7f59121,0x37de9321afed22435ef,0x7b2918dbfe5981b7e4b3,0xb31b7ecb6635fd9794ef,0x7fd980c6ffb2a18dbfa5,0x2c29dff64453bff4c063,0x1bff4c0a77fd9814effb,0xd98186ffb2630fbf58c6,0x31fbfe1861bff4c0c37f,0xff4c0c77fd9818effb2a,0x8206ffb2640ffd60481b,0xdff64483feec19077fe9,0x4c1077fd9620effb2a41,0x1affb26437bf61886bff,0x758d31bfe4c2637fe982,0x2637fd954c7feb0298ff,0xfbcc698dff66131bfecb,0x5531bff4c263ff6814c7,0x77ff984c6fff2c98dffe,0xb2ca9ff760d53bfe4c2a,0x53fef41aa77fd9854eff,0xff9654efff22a9dffa61,0xb0ffd60561bffcc2a77,0xbfe4c2c77fe98586ffb3,0x9858fdfb0cb1ff760d63,0x1fbfa1963fef41ac77fd,0xfcaac77ff9158effd30b,0x607df92cc0dffe6163bf,0xffe1981ffbc0b03bfd86,0xb3037ff96606fff26c0e,0xefff22c1ff7e0d83f7fc,0xe1986bffcb3077ff9560,0x637ff9361afff22c37bf,0xfb2b18dff64e31ffac0c,0xe53bff4c4637fd988c6f,0x7fd9594effb2329ff760,0x3129dff66253bfecb4a7,0x1ffac0cc3efd63986ffd,0xe98986ffb3130dff64e6,0x31ff760e63f7fc34c37f,0xfecb4c77fd9598effb23,0x3a06ffd3131dff66263b,0xffde0681bfecc5037fd9,0xcb5077fd95a0effb2341,0x1bfbf0741dff66283bfe,0xfe1a86bfecc50d7fd93a,0x6637fd95cc7fbac798fb,0xffd3198dff66331bfecb,0x6361bfecc6c37fd93d86,0x77fd95d8fdfb0db1dffa,0xb0dc0dffa6363bfecc6c,0x81bfecb7037fd93e077f,0xfd95e0effb23c1effe1b,0x7c35ff64786bfecb7077,0xffec30a7ffd850c6ffb2,0x83187ffaa630fffa1853,0xfffa1463ffec28c7ffd,0xea8a63ffc854c7ffaa64,0x4c7ffac698fff54d31ff,0xff60d31ffec0a63ffd65,0xaa63ffd864c7ffb0a98f,0x7ffb3098fff65931ffec,0xa5531fff42a63ffe654c,0x63fff514c7ffd3098fff,0xff0698fffe0531fffa9a,0x953fffc3263fff854c7f,0xffc9654fff922a9fff21,0x6a9fff58d53ffe4c2a7,0x3ffec8aa7ffd8654fffb,0xe8654fffb30a9fff6595,0xa9fffa5953fff48aa7ff,0xffc1aa7fff6354fffd30,0x654ffff22a9fffe1953f,0xfff14d61fffcc2a7fff9,0xc1ac3ffd53587ff906b0,0x87ffd06b0fff94d61ffe,0xf25563ffe42ac7fff835,0xac7ffd6558fff930b1ff,0xffb0cb1fff61563ffec1,0x6163ffecaac7ffd9158f,0x7ffe8558fffccab1fff6,0xf06b1fffa6163fff4aac,0x63fffc32c7fff8558fff,0xff9858ffff2ab1fffe45,0x6c0fff20d81ffe29b03f,0xffeb1b03ffd53607ff92,0x93607ffb0cc0fff60d81,0xfff94d81ffecb303ffd,0xf49b03ffe83607ffcc6c,0x607fff06c0fffe0581ff,0xffe5981fffc9b03fff86,0x8b07ffd8660fffb0ac1f,0xfffb2cc1fff65583ffec,0xa4583fff43307ffe8560,0xdffe9660fffd2ac1fff,0x86ffec8b] j else page #[0xfd538c7ffd26c37ff64d,0x718fff61631ffec1c63f,0xffeb2ca7fff858c7fff0,0x8694fffb0d29fff61653,0xfff54e61fffb2ca7ffe,0xec2cc7fff83987ffb073,0x98fffccb31fff61a63ff,0xff60e81ffea9d03ffe85,0x2d07ffd86a0ffff0740f,0x7ffacb98fffa1a83fff4,0x61b31ffec2e63ffd81cc,0x63ffe85cc7ffccb98fff,0xfaa7b0fff14f61fffa8e,0xf61fff29ec3ffd83d87f,0xffd85d8fffb07b1fffa0,0xc7c0fff54f81fff42ec7,0x6fff48f07ffd91e0fffa,0xaf00f400f40007ff6478,0xd8018302bc04a407600,0xc0ae4142024f04340794,0xcf07440dd41a4031305c,0x254048308ac10841fe03,0xc15c42a2051709d41314,0xbf0cf418f430005d30b4,0x3ec07a30ebc1ca437a06,0xc2344452087710942054,0xf13a426544ac092b11f,0x5880acb153c29c45220a,0xc31e46160be717342d34,0xc71b1435346840cdb194,0x7a00f031d6c39a47120d,0xc42e483a101f1f843dd4,0x6f243447148c4112b21f,0x9d81353261c4b6495212,0xc53a4a56147728644ff4,0x472c045714acc156b2a5,0xbbc17432dfc5ac4b3e16,0xc6224c2a18272fd45eb4,0x733a46674cac1913318,0xd941af3358c6a24d261a,0xc70e4e021bc737246d54,0x8f3a947434e701ca338d,0xf601e833c8c7864eee1d,0xc7f44fca1f573e347bb4,0x3f41f4831504c204b400,0x12c221b43cc86a50be21,0xc8e051a222ff458489f5,0xd74924915521423f3476,0x30025db4afc950528a24,0xc9be536a26a74cd498d5,0x4f50449fd53e8279b4ec,0x4c4294b521ca38545228,0xcabc555a2a5f53f4a715,0x4757f4af355c02b3b561,0x6ac2d1b59ccb3056462c,0xcb9a57162df75b74b615,0xa75ea4bc9577c2ebb5d2,0x858307b608cc0457ee2f,0xcc7a58d6316f6254c375,0x476604cb159443253643,0xa2c342367cccea59c233,0xcd685ab234f76964d215,0xf6dc4dab5b38363b6b9,0xc3038236fccdee5ba237,0xce5e5ca6390f71b4e255,0xd77504e955d183a03739,0xde83b9b76eced05d823a,0xcf365e4e3c5f7844eff5,0x177bd4f6d5ebc3d3b7a1,0xf9c3f0b7dacfa65f263e,0xd01060063fc77f34fd95,0xb782f504f608040ab80d,0x18842e3853d09a610e41,0xd10461ea439f86e50d16,0x878a951456268448b887,0xb09892102e1849e2da45,0x61661613120905c3c238,0x48170b0c24e2c26120b8,0xa098482e183e11c584c,0x1b8616415090514c3c23,0x3e1e1184858570c2ca2a,0x1216154307c23090b0a8,0x1f0f08c242c2a0e09866,0x890b0a83e1e118485854,0xf85861a5121607c20c2,0x1869448581c230f08c2a,0xa5151442c30d28a83e16,0x54530b0c34a2a2985861,0x40905c3c230a86e18590,0xb0c3482a0f85861a5151,0x130dc30b206e1e10c5b0,0x141f0f08a28240f84185,0x2c31330a03e161869452,0x4a1187841a2850a0d07c,0x68461e1091c1f08370c5,0xa1207c208c3253900a2,0x58c564c1225878410288,0x619861091814201f0b0c,0x2c8161309c3c2123058b,0xf0850c501226240b8586,0x9c96142e18b1c2414570,0xa2850a1cc3c2070d3144,0xa1187841] j) else (if j<309 then page #[0xe10a868a141f08370c54,0x841a28508c3c20d142e1,0x1091f0f08585450a2b87,0x7c2c315390028b0ae1e,0x22a240f85862c7271612,0xe18b1414581f0b0c54c4,0x28515c3c20d1428a8a06,0x5b0b0c544902b85861a,0x38889611861869c1c181,0x71e050a1912c3c22f48,0x221c151a26258586509,0x17a44428204b089f0c35,0xd1228a090884048ce1e1,0x262985861a24630c3c20,0xe61e10920505b0b0c54a,0x27c2c30d123850310468,0x61028411b87842470a08,0x201c18101458570f0851,0x8388840a14616198a024,0x9880a87111c4d25c3c24,0xe2a28120a2251858662,0x1e10a188848570f081ca,0x719c24dc3314828a8b6,0xb0f103585864ab090a08,0x5308a30c894100e36140,0x93616186a01c24147820,0x72726c2c30d412870513,0xc5962b87841a28516080,0xc24201c18101454530b0,0xc32150388848a6161981,0x642a2725071e0d1416c2,0xc0c4e4a22100a2c29858,0x6113e18698485b0f081c,0x1a8051415c2c31630d8a,0xb0cc160e141057846186,0x824ac903c241c2a361f0,0xd304838f04468a61619,0x24185861a8162d2cc2c3,0x170854530c58c4a322c4,0x3304128c8a8a6161869c,0x85861a70508118d14c2c,0x434b70f08b0a100e4e4d,0x4dc3c2143e18b0ae10a1,0xa4c9035878428808260e,0x8b1820170c870850c120,0xdc2c3164c2e10a8a61,0x8e6585862c8282108072,0x8785308c30c34c100a22,0xdc31338a09e186e1091,0xe263d85861a71c0a87c2,0xe10a1b08570c3450a610,0x44d88c3c212393441461,0x141210240e5187849201,0x28684a230c97081d044,0x153130489441461e10a2,0xf864f842460516c3c207,0x9464589c9b0b0c350120,0x30d38f0509e1e106891c,0x87841a28527071326c2c,0x10a14255709530e14c2b,0x80dc330c212384e1986,0xc34e151b87840e6060a,0xe198610a1828201f089f,0x2460515c3c2071630446,0x4530b0c34e2827861b84,0x1238ae1e1068a1494385,0x451864480820144dc3c2,0x941f0b0c8521210240f8,0xa8961e10a1c9c242048,0x861a715c3c207162930b,0x308370c58e221029844f,0xd2e10ae1868a14a0545,0xa0f845186447c20730c3,0x1c201c509f0b0c34e151,0x2c315318841346e1e10a,0x103d8461861a8168d07c,0x4201c8308370c5928e14,0xc31630ae161868a14a08,0x491844d861a81e87c20d,0x207a1f08370c58e0e1e1,0x20dc31638ae161868a14,0x4c2b1b8784286281514c,0x68a10a0545308370c58e,0x9151914c2c325461618,0x5900a2d0e6185862a705,0x61869c20146e1c870b0c,0x58dc3c21430b870a8a61,0xc1e2b851b8628267181,0x461a68a1458530b0e208,0xe8090c0bc2c312283e14,0x3450e171036291387845,0x61c6a40a143d20570b0e,0x3cb0c0b8dc2c3121c3e1,0x403a282512161b878426,0xde1e1090f18344c48388,0x45e71207c20d1e243040,0x344838bca1e10241b878,0x2fc2c36e1090a089028,0x615120e89490f48871e3,0xf084878c2d8625845440,0xe2f28906871210644f0,0x4d4258784905e50d1412,0x84530b0c] j else page #[0xe1e1090f1c492624bc78,0x1c748c3c2121928c8586,0xf084878e281187841a24,0x461e10689071c2c206f0,0x43cc4814c3c2121b3052,0x3a1e1d1292902429878,0x3920704a230f08345144,0x118605a6e1e10a0d1e48,0x8a1186509a364454dc33,0x3e10f24291508302f0c8,0x14113128807848904618,0xa8a3d0e2d85865090807,0x883848684f0b0c711110,0x4113120d08a6e1618e18,0x870e2c37849b86506151,0x126e18e14302d370f084,0xa3c70a451ac31131308e,0xc206cc4c0e103587849,0x8403a2851461989d142b,0x3412364440f0e4dc3312,0x693146828201f0c7088e,0xaa47c2c38d272e1e1244,0xc4428222c1e908f85871,0x61c6931851230f0a3498,0x64807c2c38d2632403e1,0xf085084c144f87851a4c,0x2348413e1909194342f0,0xa3a8240a420b270dc31e,0x5044ace221e100f85861,0x438ae161981c48241f08,0x4260907c2c316213448f,0xf08746c84c25843a1b86,0x38b0a0ee1e10d909c230,0xf864281107c248c30d1d,0x5f086c74f123d0e2b844,0x4253e1e10a10902d230c,0x8784284a7070927c3c21,0x4241f0f085084c120e4f,0x8c12123292838690119,0xa423a1586120e3c46827,0x14b0962480530f092049,0x6a38ae161929c983924,0x298784d05c3c2473028b,0xa4512924a3c1c910a38,0xa61179c781c370b0cc0c,0xc3c230162f3442402e18,0x3b0c94c281a241c5e50d,0xe240961e10a385834a4,0x7302930724829612c490,0x900e0b87845e70dc3c24,0x71835201f0f0838bcf10,0xc215141640a8a6161868,0xf87842a1a2861f0e12c3,0x9294381478530b0cc0e3,0x726c2c3141550560868c,0x8428542c5e6894985452,0xa089890504b0844bcb87,0x49028a1614c2112b28a8,0x6c98a4f12928a4c43878,0xa426e1e10a089f085124,0x224c40b45c3c2141b305,0x9460370b0c5884c2984,0xc7c2c3162120a61618b1,0x85044e1f0411871a163,0x4382e161981c2e230e37,0x2650b05c3c2143030a8f,0x41f08307080f1b878428,0x30603c2e1618a8d1e0c2,0xb862834507c216c32028,0x89260e1f09343070d849,0xd263910a078b09e1e146,0x8784244e6148848c3c28,0xb1094570b0e1cc0a1413,0x48c3c20d871d303e1618,0x370f0849011858628425,0x2461e1468a188870504e,0x862c4078dc3c212152c4,0x8870b0d20515100e5185,0x3e161a6931c9e2525149,0xf0807c3c20d263c4140,0x85191187841a0e1c5e7,0x24543c3925201498c30f,0x140b4403e1618c0695a6,0x86262880748c3c20d263,0x1c370cc4b12924c4385,0xc328295e1e1244690182,0xa0d842912365e51b8dc2,0xe1618b101c241f0b0c80,0x349c214118d262a41403,0x5904e3c2b0e2d851b86,0x10a1420847a1e370b0d2,0xc20d14273070403c2e1e,0xa3e8b87842a282c707c3,0xae18a0b9b0d37084854,1761] j))
def ecH11 (j : Nat) : Nat := (if j<103 then page #[0x4086ac0048100020c301,0x90c0c200668c1801,0x400285005548a1c,0x2810204f2a0400086020,0x8018009030408088040d,0x312381072238182146c0,0x2207ab02043010004e0,0x408d8100240800a08b03,0x80141600e8426207020,0x870c001c58d000c1092e,0x320c78d080024091020,0x2702c4009c0c0800030,0xc08108180830200b40c7,0xa2cf9a0a2cb8902529c,0x23468c1a0000e0038006,0xa20068f3a30eec10b0,0x4fe0ec06e800404a030a,0x86c2902e3b2b5ba0c1b9,0x72e800064000001,0x84000127c24579887000,0xc2740000c,0x825e2a98000d23a0000,0x5cc164000348c0000000,0x112752ea0001c5860,0x3009307200018174,0x5300000953c9408cc000,0x624cb19d63b6c2858,0xa65586bcd0f200018664,0x5f00000001cec096fe3f,0x4a28000000001048d0d8,0x400030e280004c3d433d,0x82019246c52dc1256745,0x45ce85a40740498028e1,0xa0003ceea0fbf3e8e13d,0x2fd8a540c400010d4b81,0x529b93d3aca44972e02a,0xc1120a1a03584aaa468,0xd1c562f907c2a04000,0xc53e1c3f093c66cc4280,0xc6370000198d803c46a9,0x8b5a3723e4000623101b,0x3df0acb1,0xb80f2c1df80b23a4c2fc,0xa3fdc97f12de46,0x804f9800000003800000,0xb2470a7bd880b29358e5,0x402c4348374ebc836f21,0x11940000426cce3f9,0x400010dd1a46000082a4,0x4e0000d0ec449d8f0248,547049,0x4c52fc3e80000000c630,0x340000a944000000029f,0x71aa5700018964c38cc,0x38eb0000000081ec,0x160406a28ec922c4eb09,0x4e0d0dd5969697f0c851,0x5e84381a094800018392,0x1606690d7d76117,0xc25dc5082fed55329280,0x3813f9ea0001e87e,0x1fe962a4462372152000,0x105506e311ed6738d6f1,0x830d8ce229390000a960,0x47602c000000041333b1,0xc59b00f1ac123baac97a,0x3ecfb89600014920,0x308b09269341b8c8f000,0x8733a2ec3cc622303f14,0xe81510dd620186223b1,0x680000000261948a0000,0x4149a010d21e9,0xb48a000000000000d1e4,0x41930231b706df50c534,0x112e616421de234c3699,0xc8488e62ea4a5339885a,0x41a7455c87790b6147,0x4947f8e096c400000,0x31cc00000000,0x62c0de00000001222518,0x23800091120001855e0,0x1a267518785900000000,0xf000000006155000,0x4d74984f030e0e561c00,0x6977878c249634e0003,0x37822a0001a47087c915,0x520e161000102b186d39,0x1080a652000172b0,0xc4e3920001d04120b000,0x10371930000a88400038,0xe057a4b9820f00000001,0xf8000153da01f0000a18,0x980000b3f052804,0xa4162852f8920001646c,0x1fb345735391b0000915,0x88000080c0000000050,0x5e76c000000000000001,0xb28c00018f4f36,0x510508af0ee00,0x29a8ec80d180,0x8c291a767480d8000000,0x632c0f339ac000181520,0xa22f82ab] j else (if j<206 then page #[0x7a0e22e4f6e910c0000,0x18dcd7fe230000926000,0xc13c85ebc50c0634b34d,0xd19000008df84ab,0x5604f4f907020607b000,0x53ab059b4e690d26aaa8,0x40000b46600010fde151,0x6a451028697b91096b64,0x30ebc833c4180000001e,0x8000a49dc22909e00c6,0x2084755ea2da000103,0x43c320b6cf2b93a00000,0x79740000987764188d7,0x7e1c3838730000245349,0xe0ee000000014af0c486,0xc2142342a0001b268886,0x20400055d4000150010d,0x323c0002f14c8fe59646,0x8a033a37d57e98b8a4d2,0x6f40bf3a131252000289,0x4870000715de2a82,0x57854b020f2f4295ed59,0x92eac780007402a61f6d,0x112211a60001a,0x57c33000088980000000,0x2466906ce458f22600,0x1376663e4ca8000707e0,0xd00004966029b0bdb808,0x8018000000142f524,0x531200020a340e7fbc20,0x5717dc046219d4b2b94d,0xe201120568200317847,0x1a32de2980000001c,0x504ab0860001c87d9b9,0x520b284400,0xbaae515bd0bb9f518840,0x13a2450cd68e1851243c,0x20b56e15b0d600008e,0xcaba67034a6798600000,0x800061aa9642cf3f005,0x2e9611790001278af0,0xa8072033d26800000000,0xb000000000003cb1f8c2,0xa311a6c38d,0x98d00000000589500000,0x80e130001886400054d3,0x9804b480005029622d44,0xc87a04fc688000b0d1c,0xa61ed890306394dba16e,0x57d50f000073a896d444,0xb3bd098790900008,0x7782cc46868778ff2801,0x2df0f7e227f32e000182,0xc27e88508e571124cb36,0xd3cbc726aa7cac5a6207,0x48609b0000400dc42e03,0x148dc89f60e833c64,0xd20eb38cda5ac000792b,0xf48e9f021fadae7f30e,0xa96ee28c23af1ec2,0xe189f72ce0000000387f,0x87069f9f11de3d607,0x1330c7cc000423be4240,0x21960c473c244000425e,0x7ec08cc82e4194000126,0x38ce0a3012e4fb62197,0x31223a1a00003d22b23d,0x180e515ad804a6ae42,0x798f43f4691581161f40,0x3509d0a5502fabebdb0,0x7fc0bb125c0001021000,0x20482054c83254922d9c,0x12295c504359ca201c8,0x1d0519197c136915a50d,0x41be28f2462c14a00010,0x6e0f6ae800028b2589c,0x5700003842f00463670f,0x89a2d7eb3962,0xf4c2c0000000000069ce,0x22bcc28000000185df82,0x33dc7a04bc000050ca9,0x549d113258628000684d,0x7e80001826e2e000036b,0x1630c000000050aea,0x2387998a8f0940000000,0x5c4432485b517195e908,0x42c400028d1d2520000d,0x779bcb3ec00bc00059b5,0x1300000000a01b2647c5,0x295ae4b0c14de1f63356,0x2041a54df1b0000,0x7412000000,0x232d76d085e04f900000,0x713260340000000399f,0x409a2247c6b000,0x1e0acaa3f49000000,0x98000b405c4e00006cd5,0x8c8000000000000000c8,0xc177e54000040c1747f7,0x22400000277c0005055,0x3832000021a800,0x1b8ad3128000833a0,0x7cf58000] j else page #[0x14d4b424049d00001a39,0x180b913bf2,0x80e8000c16a000072d0,0x8aa01d516e44f649e000,0x12e000000028f8800080,0x1870d8300b0200010e79,0xb600028956d463af8610,0x1e453ee00018f701b352,0xd3bdb97b474e] j))
def ecD12 := page #[0xffc63ffc61ffc53ffc31,0xffd31ffc86ffc83ffc81,0xffd81ffd63ffd61ffd53,0xffe53ffe31ffd86ffd83,0xffe83ffe81ffe63ffe61,0xfff63fff61fff31ffe86,0x1b000fff86fff83fff81,0x1c532c5808e0e616e1cc,0xd600b455126c488870fa,0x451ce224157b0e89b9b3,0x4c3c28634f54a874d19,0x291214a12110e1074141,0x431a6101cb1324161431,0x20395290a18d388281e1,0x34e244052458ac3841d2,0x724361c23080e54a4286,0x28634a242880f0e11840,0xd8708a2038d8708a203c,0x330910143948708e2038,0x987850c6984072c3614,0xc69c4852848443841d02,0x28361c20e6101c992850,0x841d020393250a18d388,0x396850c6984880a50943,0x1431a610506c3841cc20,0x1204160f0a18d3080e5a,0xe561c2496101ca941b0e,0x95283614341412202960,180739]
def ecH12 := page #[0x124053c000100030602,0x6000c0600010402,0xd4b060f07010f000b00,0x131b2e000001180e2c,0x4a2d0018256305152301,0x113f0b01049e110e0006,0x100000a3402000f0a,0x2360f106000f804,0x171302083e0335070545,0x80208610127032d04,0x477a8fc3030206092200,0x8f1098a90001830c8b6,0x622650ea2bd4ac149f9d,0xfbcba9e344d8ec000126,0x2ac89d33fb1a508a074,0x6bcad8a76eaa0003c630,0x926bc69c05070e23,0xeb71010d20003075000,0xc0d210251930251e941c,0x4e033635208c4a8015b6,0x60fd30800034f10002ea,0x3d3c36438212fa2a8000,0x54c8f000000000000005,0x284c329dc5adc7407d72,0xaa800002b20000000a11,0xc55000328eebd1,0xfa2d0e4782f7493a4c40,0x1c6f321b046040e8e,0xbc3ca334100f57324e02,0x364620003f0200033153,0x1ca210d7c07b0ac070f2,0xc8e412c8bddc39000,0x30000151c00000000000,0x36278000e45000000015,0x98f0d1253b8cb1000080,0x3aefdc8e48362fbb31,0xc09c0009417c3b4,0x73132a1a90b90c400000,0x732244fd35d03dd39,0x721c0003acd6917c80,0xb00020d69079eab00000,0xd2208b814ba410e25ba3,0x1cd8052b2aae2ac30000,0x98811a336c5bb03c0004,0x1891832d043e40089de3,0x4b9415c533112b00440a,0x9c22af4c764082740001,0x91357e55c911cdf00034,0x33286e69b5b83841ee70,0x1cf2aae94e3dab8000,0x9e6cb41f8000e084a040,0x20f7e1c88f3000304194,0x8ed427cfb31e98f8231,0xa62bec8f6a1989268b44,0xbc4b4a00000c6a00014,0x62e9f240000000000000,0x9c8000784f0686897461,0x12a000045910828582,0xa49690c2297c6e00,0x8b0000000fcbeea3000,0xec5c0002819490c1b4,0x300014fc626c00000000,0x40349167a8b09293e785,0x25d524c42a43eac4204b,0x4c000c4466ece06971c0,0x21224e800018db90,0xf16f3f5c710002caf000,0x120c7a852abe645d34ac,0xcc134000e8fa0e7f8468,0xe18046b1095864000202,0x150cd8413800041d8a00,0x9380e00b80063008c0b2,0xd216231ac1714d2d19c3,0xc1b01fc41510f38c3b48,0xdcac96424017f2e7794a,0xf219dcb5e2b24a1c976a,0x134c00043534e28c6189,0x4199186950ead8379d1b,0x422d5d4a1321a1b34809,0x5449b058000a1e70b624,0x30ab251c8c00014e1031,0xcc7cb0000d43cd1a7ae3,0x6c407c5e130747c0000c,0x80999214c4400093fbeb,0xd000002c10d180656bb,0x9000000000dd6adc000a,0xe82f23646ed20b6447d8,0xd1500026febcaca9602e,0x17d2c8322299c00052ce,0xad0a88320cab8d023c31,0x434000d115cbc33ffc8,0x34650000037,0x9b6d7a0734e9b3080000,0x48160a693208073266a,0x922807c70f4b77c1d41e,0x7b86808a060c3343eb,0xe6373c82533a0bfd2140,0xfcbb85cf482d1d285050,0x3b49290002c519007898,0x6d3d0272d4e,0xa4b790e80009bd951f00,0x385004b54a482b]
def ecD13 (j : Nat) : Nat := (if j%103=0 then 3180031 else 0)
def ecH13 := page #[0x1560000000010,476053504,0x53000e4400f200016000,0x5022310c00,0xd96b3000000000000000,992,0,0xa4800610cf75c00,0x15adc0000000,0,693,0x5a800b9c00002ef0018e,0x141001d900000,0x5b00000309ee400f4000,0xb8d000000000002c00,0xc4e6e05000bc400,0,810549514,0x287c680000000]
def ecLevels : Nat → Packing
  | 9 => (114,4,6,0,0,12,0,ecD9)
  | 10 => (609,3,6,0,0,15,0,ecD10)
  | 11 => (309,2,6,0,0,15,0,ecD11)
  | 12 => (27,1,6,0,0,11,0,ecD12)
  | 13 => (1,0,6,0,0,0,0,ecD13)
  | _ => emptyPacking
def ecIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 32 163 7 12 7 1 ecH10
  | 11 => lookupWord 191 1049 7 15 10 1 ecH11
  | 12 => lookupWord 105 521 8 14 9 1 ecH12
  | 13 => lookupWord 10 149 1 10 5 1 ecH13
  | _ => fun _ => none
def ec : Forest := ⟨1023,13,fun i => ecY[i]?.getD (0,0),ecC,ecA,ecLevels,ecIndex⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sampleCells : block ec 10 0 121 = true := by
  change block ec 10 0 (runLength [7193,23866]) = true
  apply scheduled_ok
  simp only [scheduled,cells,boxes]
  all_goals repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
end Certificate
end PEqualNP.Outside.L_meta_4813_aux

import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9838.Grammar
abbrev W := Fin 153
abbrev Gate := Fin 113
abbrev Raw := Fin 40
def physical (i : Gate) : W := ⟨i.val+40,by omega⟩
def input (i : Raw) : W := ⟨i.val,by omega⟩
def truthOp (isOr : Bool) (a b : Bool) := if isOr then a || b else a && b
def bitsOp (isOr : Bool) (a b : Nat) := if isOr then a ||| b else a &&& b
def code (a b : Bool) : Nat := (if a then 1 else 0)+(if b then 2 else 0)
def original : Array (Bool × W × W) := #[(true,8,4),(true,5,40),(true,18,41),(false,24,42),(true,13,14),(true,17,8),(true,45,44),(false,33,46),(true,11,15),(true,6,12),(true,48,49),(true,4,50),(false,31,51),(true,2,8),(true,0,11),(true,7,54),(true,53,55),(false,27,56),(true,3,12),(true,8,58),(true,59,9),(true,1,60),(false,28,61),(true,18,7),(true,63,14),(true,64,15),(true,9,65),(false,34,66),(true,7,10),(true,6,1),(true,68,69),(false,26,70),(true,17,16),(true,9,11),(true,72,73),(false,36,74),(true,7,19),(true,76,4),(true,3,77),(true,17,78),(false,23,79),(true,10,16),(true,15,81),(true,8,19),(true,83,82),(false,35,84),(true,13,0),(true,86,15),(true,3,87),(false,20,88),(true,10,9),(true,13,2),(true,91,90),(true,4,92),(false,29,93),(true,6,2),(true,16,95),(true,18,3),(true,97,96),(false,22,98),(true,19,6),(true,5,0),(true,100,101),(true,102,9),(false,25,103),(true,0,18),(true,10,17),(true,12,106),(true,107,105),(false,37,108),(true,10,11),(true,14,110),(true,3,5),(true,111,112),(false,30,113),(true,13,7),(true,5,115),(true,16,12),(true,117,116),(false,32,118),(true,12,19),(true,2,120),(true,14,121),(false,39,122),(true,1,13),(true,19,18),(true,11,125),(true,124,126),(false,38,127),(true,17,2),(true,15,129),(true,1,5),(true,130,131),(false,21,132),(true,62,128),(true,104,133),(true,85,80),(true,136,47),(true,57,109),(true,138,75),(true,89,114),(true,137,99),(true,119,94),(true,139,142),(true,141,143),(true,140,67),(true,43,52),(true,145,123),(true,144,134),(true,146,148),(true,135,149),(true,71,147),(true,151,150)]
def root : W := 152
def relation : Array Nat := #[4,4,4,4,4,4,2,4,1,4,4,4,4,1,1,4,4,1,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,8,1,1,1,1,1,1,12,12,12,1,13,13,13,13,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,1,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,12,1,12,12,12,1,12,12,12,12,1,12,12,12,12,1,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13]
def ranges : Array (Nat×Nat) := #[(13,12),(12,13),(12,13),(1,13),(13,13),(13,13),(13,13),(8,13),(12,12),(14,12),(12,14),(12,14),(1,14),(12,13),(12,12),(12,12),(13,12),(1,13),(12,12),(13,12),(13,12),(12,13),(1,13),(12,12),(12,13),(13,12),(12,13),(1,13),(12,12),(14,12),(12,14),(1,14),(13,12),(12,12),(13,12),(1,13),(12,12),(12,12),(12,12),(13,12),(1,13),(12,12),(12,12),(13,12),(13,12),(1,13),(13,12),(13,12),(12,13),(1,13),(12,12),(13,12),(13,12),(12,13),(1,13),(14,12),(12,14),(12,12),(12,14),(1,14),(12,14),(12,12),(14,12),(14,12),(1,14),(12,12),(12,13),(12,13),(13,12),(1,13),(12,12),(13,12),(12,12),(13,12),(1,13),(13,12),(12,13),(12,12),(12,13),(1,13),(12,12),(12,12),(13,12),(1,13),(12,13),(12,12),(12,12),(13,12),(1,13),(13,12),(12,13),(12,12),(13,12),(1,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13),(13,13)]
abbrev Chunk := Fin 2
def w0 : Array Nat := #[8796093023232,545267712,134283264,16908288,274878955520,281474976710784,2207613190152,17179871232,2251799813685312,294912,4398046511106,1073741828,4194560,16,2097152,268451840,4503599627898880,67109376,34359738400,70368777732097,9007199271519232,268435584,562958543486976,17592253153281,72057594038976544,18014398543036424,8390656,35184506306564,36028797555835136,2147483664,1125899908939778,144115462953779200,140754668748800,4294967360,288230410511482880,2251937252642816,549756076032,68719477248,1099511635968,576460752307683328,2252074692640832,2533549669351616,2533584029090016,1048608,2097168,2251799880794688,2251799882891856,64,1342193668,2207617384712,2208959578380,2483838533900,274877923328,2251799947968576,8797166765060,8814346636292,2260614294604868,134217732,21102848,2251799834788160,2251799835083072,2251800380350784,536871168,51539609632,51541706784,51810158624,51810453536,34359771136,4415226382338,2208158457864,6623384840202,8390656,4503599695008256,1074036740,4503600769044996,262144,70385957603329,70660836558849,70660853467137,70660920576513,67108865,4507997674409986,4507997942861826,2322168591417409,6830166534279235,2251799813689344,8796093023248,8796361475088,8796378383376,16778240,4398046806018,134283280,4398181089298,4673060044818,16,2207747473416,4505807375372296,34376646688,4505841752018984,8590065664,72576390922249,290271069734016,362847460656265,362847460951177,33554440,8830452761632,4398113620482,4398117815042,13228570576674,512,4399120252934,4399122350086,281474993619072,285874115969158,2097154,17179871248,281492156582032,4503599632093440,4785091788675472,17180393472,70368781926657,70368916209921,70368918307073,4259840,545267728,70403137470497,70404211212325,70404756480053,8192,201392640,469844480,281475521978496,281475991822976,268435584,536879360,301990024,2251799880798209,2251799880798273,134218244,134480388,18875394,2251808470863937,17180393488,17314873876,2251825785737813,34378646530,274878971936,34382906370,2251826322617173,2252101201589109,2252101503579133,34391297026,2252135894876159]
def w1 : Array Nat := #[0,512,1024,16,1,0,0,64,0,2304,0,8,4096,0,16384,128,4,0,8192,0,0,2,0,0,0,256,32,0,0,0,0,0,0,0,0,0,4,0,8,16384,1,1,8193,0,16384,0,16384,0,136,4096,4232,4233,0,1024,8,72,1096,0,4112,4112,6416,6928,0,8256,24640,24768,27072,0,64,512,576,0,4,2312,2316,4,64,65,81,81,0,4,132,0,132,0,0,128,144,0,2304,1024,3328,3329,0,1024,1028,8208,9236,0,0,0,0,2304,256,8192,0,4096,12288,0,8,16392,16,16408,0,64,64,4100,4164,0,4096,5120,21504,16384,512,8192,8200,8712,8,1024,1152,512,1664,0,8,256,0,0,0,4,0,0,0,4,4,0,0,16384,12,12,268,16384,16652]
def ws := #[w0,w1]
def positive : Nat := 8589934656
def negative : Nat := 8590827199
def op (i : Gate) := original[i.val]!.1
def leg (i : Gate) (which : Bool) : W := if which then original[i.val]!.2.2 else original[i.val]!.2.1
def word (c : Chunk) (i : W) : Nat := (ws[c.val]!)[i.val]!
def range (i : Gate) (side : Bool) : Nat := if side then ranges[i.val]!.2 else ranges[i.val]!.1
def rel (i : W) : Nat := relation[i.val]!
def subset (a b : Nat) : Prop := a &&& b = a
def upper (u v : W) : Prop := ∀ c : Chunk, subset (word c u) (word c v)
def approx (u v : W) : Prop := upper u v ∨ upper v u
local instance (a b : Nat) : Decidable (subset a b) := by unfold subset; infer_instance
local instance (u v : W) : Decidable (upper u v) := by unfold upper; infer_instance
local instance (u v : W) : Decidable (approx u v) := by unfold approx; infer_instance
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4096

structure World where
  wire : W → Bool
  saved : ∀ i, wire (physical i) = truthOp (op i) (wire (leg i false)) (wire (leg i true))
def comparable (u v : W) :=
  (∀ x : World, x.wire u=true → x.wire v=true) ∨
  (∀ x : World, x.wire v=true → x.wire u=true)

theorem wordData : ∀ c : Chunk, ∀ i : Gate,
    word c (physical i) = bitsOp (op i) (word c (leg i false)) (word c (leg i true)) := by decide +kernel
def probe (c : Chunk) (t : Nat) : World where
  wire i := (word c i).testBit t
  saved i := by
    rw [wordData]
    cases b : op i <;> simp [truthOp,bitsOp,b,Nat.testBit_or,Nat.testBit_and]
theorem sub_of_bit {a b : Nat} (inc : ∀i, a.testBit i=true → b.testBit i=true) : subset a b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases h : a.testBit i with
  | false => simp
  | true => simp [inc i h]
theorem bit_of_sub {a b : Nat} (inc : subset a b) (i : Nat) (hi : a.testBit i=true) :
    b.testBit i=true := by
  have eq := congrArg (fun z : Nat => z.testBit i) inc
  simpa [Nat.testBit_and,hi] using eq
theorem approx_of_comparable {u v : W} (h : comparable u v) : approx u v := by
  rcases h with h|h
  · exact Or.inl (fun c => sub_of_bit (fun t => h (probe c t)))
  · exact Or.inr (fun c => sub_of_bit (fun t => h (probe c t)))

theorem inputData : ∀ i : Raw, (rel (input i)).testBit (code (positive.testBit i.val) (negative.testBit i.val))=true := by decide +kernel
theorem ports : ∀ (i : Gate) (s : Bool) (q : W), q≠physical i → approx q (leg i s) → subset (rel q) (range i s) := by decide +kernel
theorem compose : ∀ (i : Gate) (a b c d : Bool),
  (range i false).testBit (code a b)=true → (range i true).testBit (code c d)=true →
  (rel (physical i)).testBit (code (truthOp (op i) a c) (truthOp (op i) b d))=true := by decide +kernel

inductive Derives : W → Bool → Bool → Prop where
 | raw (p : Raw) : Derives (input p) (positive.testBit p.val) (negative.testBit p.val)
 | node (i : Gate) (u v : W) (a b c d : Bool)
     (nu : u≠physical i) (nv : v≠physical i)
     (lu : comparable u (leg i false)) (rv : comparable v (leg i true))
     (left : Derives u a b) (right : Derives v c d) :
     Derives (physical i) (truthOp (op i) a c) (truthOp (op i) b d)

theorem invariant {i a b} (e : Derives i a b) : (rel i).testBit (code a b)=true := by
  induction e with
  | raw i => exact inputData i
  | node i u v a b c d nu nv lu rv left right ih1 ih2 =>
    exact compose i _ _ _ _ (bit_of_sub (ports i false u nu (approx_of_comparable lu)) _ ih1)
      (bit_of_sub (ports i true v nv (approx_of_comparable rv)) _ ih2)
theorem ruled_out : ¬Derives root true false := by
  intro e
  have absent : (rel root).testBit (code true false) = false := by decide
  have hit := invariant e
  simp [absent] at hit
def edgePairs : List (Nat × Nat) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]
def target (m : Nat) := edgePairs.any (fun e => m.testBit e.1 && m.testBit e.2)
theorem actualRows : target positive = true ∧ target negative=false := by decide +kernel
theorem no_target : ¬Derives root (target positive) (target negative) := by
  simpa only [actualRows.1,actualRows.2] using ruled_out
def modes : Array Nat := #[2,2,2,1,3,3,3,7,3,2,2,2,1,2,3,3,2,1,3,2,2,2,1,3,2,2,2,1,3,2,2,1,2,3,2,1,3,3,3,2,1,3,3,2,2,1,2,2,2,1,3,2,2,2,1,2,2,3,2,1,2,3,2,2,1,3,2,2,2,1,3,2,3,2,1,2,2,3,2,1,3,3,2,1,2,3,3,2,1,2,2,3,2,1,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3]

def canFeed (i : Gate) (side : Bool) (q : W) : Prop :=
 q≠physical i ∧ subset (rel q) (range i side)
local instance (i : Gate) (side : Bool) (q : W) : Decidable (canFeed i side q) := by unfold canFeed; infer_instance
def permitted (i : Gate) (mode : Nat) : Bool := modes[i.val]!.testBit mode

theorem cmpFeeds {i : Gate} {s : Bool} {q : W} (ne : q≠physical i) (h : comparable q (leg i s)) :
    canFeed i s q := ⟨ne,ports _ _ _ ne (approx_of_comparable h)⟩
theorem flexibleBinary : ∀ (i : Gate) (isOr a b c d : Bool),
   permitted i (if isOr then 1 else 0)=true →
   (range i false).testBit (code a b)=true → (range i true).testBit (code c d)=true →
   (rel (physical i)).testBit (code (truthOp isOr a c) (truthOp isOr b d))=true := by decide +kernel
theorem flexibleNot : ∀ (i : Gate) (a b : Bool), permitted i 2=true →
   (range i false).testBit (code a b)=true →
   (rel (physical i)).testBit (code (!a) (!b))=true := by decide +kernel
theorem oldPermitted : ∀ i : Gate, permitted i (if op i then 1 else 0)=true := by decide +kernel

inductive Flexible : W → Bool → Bool → Prop where
 | raw (p : Raw) : Flexible (input p) (positive.testBit p.val) (negative.testBit p.val)
 | bin (i : Gate) (isOr : Bool) (u v : W) (a b c d : Bool)
   (allowed : permitted i (if isOr then 1 else 0)=true)
   (lu : canFeed i false u) (rv : canFeed i true v) (left : Flexible u a b) (right : Flexible v c d) :
   Flexible (physical i) (truthOp isOr a c) (truthOp isOr b d)
 | inv (i : Gate) (u : W) (a b : Bool) (allowed : permitted i 2=true)
   (lu : canFeed i false u) (arg : Flexible u a b) : Flexible (physical i) (!a) (!b)

theorem flexible_invariant {i a b} (e : Flexible i a b) : (rel i).testBit (code a b)=true := by
  induction e with
  | raw p => exact inputData p
  | bin i isOr u v a b c d allowed lu rv left right ih1 ih2 =>
    exact flexibleBinary i isOr a b c d allowed (bit_of_sub lu.2 _ ih1) (bit_of_sub rv.2 _ ih2)
  | inv i u a b allowed lu arg ih => exact flexibleNot i a b allowed (bit_of_sub lu.2 _ ih)

theorem no_flexible_target : ¬Flexible root (target positive) (target negative) := by
  intro der
  have obs := flexible_invariant der
  have lost : (rel root).testBit (code true false)=false := by decide
  have bad : (rel root).testBit (code true false)=true := by simpa only [actualRows.1,actualRows.2] using obs
  exact (by decide : false≠true) (lost.symm.trans bad)

def portsOn (i : Gate) (s : Bool) := ((List.finRange 153).filter (fun q => decide (canFeed i s q))).length
def arcCount := ((List.finRange 113).map (fun i => portsOn i false+portsOn i true)).sum
def opCount (mode : Nat) := ((List.finRange 113).filter (fun i => permitted i mode)).length
def exchangeCount := ((List.finRange 113).filter (fun i => permitted i 0 && permitted i 1)).length
theorem census : arcCount=24755 ∧ exchangeCount=47 ∧ opCount 2=1 := by decide +kernel
end PEqualNP.Outside.L_meta_9838.Grammar
namespace PEqualNP.Outside.L_meta_9838.Grammar
open PEqualNP.CircuitLowerBounds
abbrev PhysicalGate := PEqualNP.CircuitLowerBounds.Gate
def inRow (r : Nat) := List.ofFn (fun p : Raw => r.testBit p.val)
def runG (gs : List PhysicalGate) (r : Nat) :=
 gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) (inRow r)
def newValue (g : PhysicalGate) (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
theorem run_append (gs : List PhysicalGate) (g : PhysicalGate) (r : Nat) :
 runG (gs++[g]) r=runG gs r++[newValue g (runG gs r)] := by simp [runG,newValue,List.foldl_append]
theorem run_length (gs : List PhysicalGate) (r : Nat) : (runG gs r).length=40+gs.length := by
 induction gs using List.reverseRecOn with
 | nil => simp [runG,inRow]
 | append_singleton gs g ih => rw [run_append]; simp [ih]; omega

def atWire (gs : List PhysicalGate) (k r : Nat) := (runG gs r).getD k false
theorem wire_old (gs : List PhysicalGate) (g : PhysicalGate) {k r : Nat} (h : k<40+gs.length) :
 atWire (gs++[g]) k r=atWire gs k r := by
 unfold atWire
 rw [run_append]
 exact List.getD_append _ _ _ _ (by simpa only [run_length] using h)
theorem wire_new (gs : List PhysicalGate) (g : PhysicalGate) (r : Nat) :
 atWire (gs++[g]) (40+gs.length) r=newValue g (runG gs r) := by
 unfold atWire
 rw [run_append,←run_length gs r]
 simp

inductive Allowed (lab : Nat → W) (n : Nat) : PhysicalGate → Prop where
 | bin (i : Gate) (b : Bool) (j k : Nat) (hj : j<n) (hk : k<n)
   (site : lab n=physical i) (ok : permitted i (if b then 1 else 0)=true)
   (left : canFeed i false (lab j)) (right : canFeed i true (lab k)) :
   Allowed lab n ⟨if b then GateOp.or else GateOp.and,[j,k]⟩
 | inv (i : Gate) (j : Nat) (hj : j<n) (site : lab n=physical i) (ok : permitted i 2=true)
   (left : canFeed i false (lab j)) : Allowed lab n ⟨GateOp.not,[j]⟩
inductive Admitted (lab : Nat → W) : List PhysicalGate → Prop where
 | base : Admitted lab []
 | step (gs : List PhysicalGate) (g : PhysicalGate) (head : Admitted lab gs) (legal : Allowed lab (40+gs.length) g) :
   Admitted lab (gs++[g])

theorem realized {lab : Nat → W} (rawLabel : ∀ p : Raw, lab p.val=input p) {gs : List PhysicalGate}
   (h : Admitted lab gs) : ∀ j, j<40+gs.length →
     Flexible (lab j) (atWire gs j positive) (atWire gs j negative) := by
 induction h with
 | base =>
   intro j hj
   have h40 : j<40 := by simpa using hj
   let p : Raw := ⟨j,h40⟩
   have rr := Flexible.raw p
   rw [←rawLabel] at rr
   simpa [p,atWire,runG,inRow,List.getD,List.getElem?_ofFn,h40] using rr
 | step gs g head legal ih =>
   intro j hj
   by_cases old : j<40+gs.length
   · rw [wire_old gs g old,wire_old gs g old]
     exact ih j old
   · have slot : j=40+gs.length := by simpa using (show j=40+gs.length by simp at hj; omega)
     subst j
     rw [wire_new,wire_new]
     cases legal with
     | bin i b u v hu hv site ok lu rv =>
       rw [site]
       have out := Flexible.bin i b _ _ _ _ _ _ ok lu rv (ih u hu) (ih v hv)
       cases b <;> simpa [newValue,atWire,truthOp,GateOp.eval] using out
     | inv i u hu site ok lu =>
       rw [site]
       simpa [newValue,atWire,GateOp.eval] using
         (Flexible.inv i _ _ _ ok lu (ih u hu))

theorem physical_obstruction (C : Circuit) (lab : Nat → W) (rawLabel : ∀ p : Raw, lab p.val=input p)
    (h : Admitted lab C.gates) (out : C.output<40+C.gates.length) (labOut : lab C.output=root) :
    ¬(∀ m : Nat, C.eval (inRow m)=target m) := by
 intro computes
 have d := realized rawLabel h C.output out
 change Flexible (lab C.output) (C.eval (inRow positive)) (C.eval (inRow negative)) at d
 rw [labOut,computes,computes] at d
 exact no_flexible_target d
end PEqualNP.Outside.L_meta_9838.Grammar

import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9740.DonorChecks

def a (g : Nat) := g%256
def b (g : Nat) := (g/256)%256
def isOr (g : Nat) : Bool := decide (65536≤g)

def evaluate (gates : Array Nat) (initial : Array Nat) (add : Nat → Nat → Nat) (clamp : Bool := false) : Array Nat :=
  gates.foldl (fun w g =>
    let j := 2*(w.size-40)
    let l := w[a g]?.getD 0 ||| add j (a g)
    let r := w[b g]?.getD 0 ||| add (j+1) (b g)
    w.push (if isOr g then l ||| r else if clamp then 0 else l &&& r)) initial

def raw (x bits : Nat) : Array Nat :=
  ((List.range 40).map (fun i => if x.testBit i then bits else 0)).toArray

def out (o : Nat) (w : Array Nat) := w[o]?.getD 0

def visible (gs : Array Nat) (o : Nat) : Bool :=
  let (_,cone,must) := gs.toList.foldr (fun g (acc : Nat × Nat × Nat) =>
    let (i,c,m) := acc
    let id := i-1
    let up := if c.testBit id && isOr g then c ||| (1 <<< a g) ||| (1 <<< b g) else c
    (id,up,if isOr g then m else m ||| (1 <<< id)))
    ((40+gs.size,1 <<< o,0) : Nat × Nat × Nat)
  (cone &&& must) == must

def oneBit (x : Nat) : Bool := (x &&& (x-1)) == 0

def test (gs : Array Nat) (o : Nat) (neigh : List Nat) : Bool :=
  let pos := neigh.map (fun i => 1 <<< i)
  let bad := 0 :: ((List.range 40).filter (fun i => !neigh.contains i)).map (fun i => 1 <<< i)
  let pp := (1 <<< (2*gs.size))-1
  let labels := (1 <<< (40+gs.size))-1
  let rejected := bad.foldl (fun v x => v ||| out o (evaluate gs (raw x pp) (fun p _ => 1 <<< p))) 0
  let safe := pp ^^^ rejected
  let groups := pos.map (fun x => out o (evaluate gs (raw x labels)
    (fun p w => if safe.testBit p then 1 <<< w else 0)))
  let disjoint := (groups.foldl (fun (acc : Bool × Nat) s =>
    (acc.1 && (acc.2 &&& s)==0,acc.2 ||| s)) (true,0)).1
  let isolated := (pos.zip groups).all (fun q => out o (evaluate gs (raw q.1 1)
    (fun p w => if safe.testBit p && !q.2.testBit w then 1 else 0)) == 0)
  let init := ((List.range 40).map (fun i => (pos.foldr (fun x v => 2*v+(x.testBit i).toNat) 0))).toArray
  let narrow := (evaluate gs init (fun _ _ => 0) true).all oneBit
  visible gs o && narrow && disjoint && isolated

def both (gs : Array Nat) (o : Nat) := test gs o [20,24,26,36,39] && test gs o [0,1,4,14,16]
def net0 : Array Nat := #[74260,75797,72468,74527,75030,75288,74265,74010,72987,75036,77341,73495,74774,72984,74520,74780,79666,74007,71958,75287,76313,80164,71189,74522,81701,72213,82214,81447,82460,81173,74266,80933,76585,77090,72731,78880,18176,73749,83483,75291,84534,83237,73751,80679,74013,74521,84268,85796,75554,75551,72726,20753,86606,18447,82736,73245,86049,88596,24066,89920,80431,90391,25354,88352,88097,23559,87072,91422,27395,93277,91953,14345,87379,28691,91167,79155,17409,94555,92692,24584,29444,22034,29190,95334,95782,31757,73240,96375,28172,98425,97133,92190,84771,33808,33550,87838,97869,90700,100377,98941,101242,100127,36107,35333,102021,102255,102537,103029,102761,103295,103564,104065,104341,104582]
theorem sample0 : (both net0 153)=true := by decide +kernel
end PEqualNP.Outside.L_meta_9740.DonorChecks

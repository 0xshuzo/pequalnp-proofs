import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.BlockPrice
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def opr (d : Bool) (a b : Nat) := if d then a ||| b else a &&& b
def mask (n : Nat) := 2^n-1
def sp (n a : Nat) := a &&& ((mask n) ^^^ ((a >>> n) &&& mask n)) &&& mask n
def scan (n : Nat) (s : List Nat) := s.foldl (fun v a => v ||| sp n a) 0
def want (n : Nat) (s : List Nat) := decide (scan n s = mask n)
def keepers (a b x : Nat) (tail : List Nat) := [x::tail, x::a::tail, x::b::tail, x::a::b::tail]
def distinct (s : List Nat) (h : Nat → Nat → List Nat → Bool) : Bool :=
  match s with
  | [] => false
  | a::r => r.any (fun b => h a b (r.erase b)) || distinct r (fun b c rem => h b c (a::rem))
def walk (n : Nat) : Nat → List Nat → Bool
  | 0, s => s.contains (mask n)
  | k+1, s => if s.contains (mask n) then true else
    if s.length > k+2 || !want n s then false else
    s.any fun a => s.any fun b => decide (a < b) && [false,true].any fun d =>
      let rem := (s.erase a).erase b
      let x := opr d a b
      if s.contains x then false else
      (keepers a b x rem).any fun child =>
        decide (child.length ≤ k+1) && want n child && walk n k child
def base2 : List Nat := [1431633935,858980592,2863271695,3435983088,286392064]
theorem block2 : walk 16 4 base2=false := by decide +kernel
def base3 : List Nat := [(255 + (93824992236885 <<< 48)),(65280 + (56294995342131 <<< 48)),(16711680 + (16557351571215 <<< 48)),(4278190335 + (187649984473770 <<< 48)),(1095216725760 + (225179981368524 <<< 48)),(280375481794560 + (264917625139440 <<< 48)),(281474959933440 + (1103823438081 <<< 48))]
theorem block3 : walk 48 7 base3=false := by decide +kernel
def base4 : List Nat := [(32767 + ((0 + ((187833230819328 + ((93847899428202 + (187652847872685 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(1073709056 + ((0 + ((168994933833728 + ((56308739656921 + (112591708723611 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(35183298347008 + ((0 + ((149048501731328 + ((264921667584967 + (33115208448120 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(246290604621824 + ((4095 + ((140192010731520 + ((17524001357760 + (2190500169720 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(32767 + ((134213632 + ((93641729114112 + ((187627077282453 + (93822128837970 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(1073709056 + ((4397912293376 + ((112480026099712 + ((225166237053734 + (168883267987044 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(35183298347008 + ((277076930199552 + ((132426458202623 + ((16553309125688 + (248359768262535 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(246290604621824 + ((4095 + ((141282965978624 + ((263950975352895 + (279284476540935 <<< 48)) <<< 48)) <<< 48)) <<< 48)),(0 + ((281474976706560 + ((549789368319 + ((68721573952 + (8590196744 <<< 48)) <<< 48)) <<< 48)) <<< 48))]
theorem block4 : walk 120 10 base4=false := by decide +kernel
end PEqualNP.Outside.L_meta_9792.BlockPrice

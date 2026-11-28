import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10007.ShortenedField
abbrev W := BitVec 31
def columns : Array W := #[184551458,369102916,738205832,1476411664,805339681,1610679362,1073875077,266507,533014,1066028,2132056,4264112,8528224,17056448,34112896,68225792,136451584,272903168,545806336,1091612672,35741697,71483394,142966788,285933576,571867152,1143734304,139984961,279969922,559939844,1119879688,92275729]
def ones (x : W) : Nat :=
  let bytes : Array Nat := #[0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8]
  bytes[x.toNat%256]! + bytes[(x.toNat/256)%256]! +
  bytes[(x.toNat/65536)%256]! + bytes[x.toNat/16777216]!
def one (a : Nat) : W :=
  (if a.testBit 0 then 279889869 else 0) ^^^
  (if a.testBit 1 then 3154076 else 0) ^^^
  (if a.testBit 2 then 1683739149 else 0) ^^^
  (if a.testBit 3 then 8832257 else 0) ^^^
  (if a.testBit 4 then 1961193681 else 0) ^^^
  (if a.testBit 5 then 277397892 else 0) ^^^
  (if a.testBit 6 then 1077416468 else 0) ^^^
  (if a.testBit 7 then 1142665860 else 0) ^^^
  (if a.testBit 8 then 72929284 else 0) ^^^
  (if a.testBit 9 then 1413612688 else 0)
def three (a : Nat) : W :=
  (if a.testBit 0 then 1957568729 else 0) ^^^
  (if a.testBit 1 then 335655488 else 0) ^^^
  (if a.testBit 2 then 69273164 else 0) ^^^
  (if a.testBit 3 then 538566720 else 0) ^^^
  (if a.testBit 4 then 606556 else 0) ^^^
  (if a.testBit 5 then 812758080 else 0) ^^^
  (if a.testBit 6 then 1339969 else 0) ^^^
  (if a.testBit 7 then 1074022216 else 0) ^^^
  (if a.testBit 8 then 1627362384 else 0) ^^^
  (if a.testBit 9 then 343381208 else 0)

def allowed (x : W) := columns.foldl (fun n c => if x &&& c == 0 then n+1 else n) (0 : Nat)
def check (x : W) (limit : Nat) := decide (ones x ≤ 20 ∧ ones x * allowed x ≤ limit)
def page (n : Nat) := (List.range 32).all (fun i =>
  check (one (32*n+i)) 48 && check (three (32*n+i)) 49)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p0 : page 0=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p1 : page 1=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p2 : page 2=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p3 : page 3=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p4 : page 4=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p5 : page 5=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p6 : page 6=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p7 : page 7=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p8 : page 8=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p9 : page 9=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p10 : page 10=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p11 : page 11=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p12 : page 12=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p13 : page 13=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p14 : page 14=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p15 : page 15=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p16 : page 16=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p17 : page 17=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p18 : page 18=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p19 : page 19=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p20 : page 20=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p21 : page 21=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p22 : page 22=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p23 : page 23=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p24 : page 24=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p25 : page 25=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p26 : page 26=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p27 : page 27=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p28 : page 28=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p29 : page 29=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p30 : page 30=true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
theorem p31 : page 31=true := by decide +kernel
theorem checked (n i : Fin 32) :
    ones (one (32*n.val+i.val))≤20 ∧ ones (one (32*n.val+i.val))*allowed (one (32*n.val+i.val))≤48 ∧
    ones (three (32*n.val+i.val))≤20 ∧ ones (three (32*n.val+i.val))*allowed (three (32*n.val+i.val))≤49 := by
  have p : page n.val=true := by
    fin_cases n
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
    · exact p7
    · exact p8
    · exact p9
    · exact p10
    · exact p11
    · exact p12
    · exact p13
    · exact p14
    · exact p15
    · exact p16
    · exact p17
    · exact p18
    · exact p19
    · exact p20
    · exact p21
    · exact p22
    · exact p23
    · exact p24
    · exact p25
    · exact p26
    · exact p27
    · exact p28
    · exact p29
    · exact p30
    · exact p31
  have h:=List.all_eq_true.mp p i.val (List.mem_range.mpr i.isLt)
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp h
  have x:=of_decide_eq_true a
  have y:=of_decide_eq_true b
  exact ⟨x.1,x.2,y.1,y.2⟩
end PEqualNP.Outside.L_meta_10007.ShortenedField

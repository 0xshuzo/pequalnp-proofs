import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_120_cases
set_option maxHeartbeats 4000000
def axis : List (Nat × Bool) := [(7,false), (56,false), (448,false), (3584,false), (9,true), (65,true), (72,true), (513,true), (520,true), (576,true), (18,true), (130,true), (144,true), (1026,true), (1040,true), (1152,true), (36,true), (260,true), (288,true), (2052,true), (2080,true), (2304,true)]
def violates (x : Nat) (s : Nat × Bool) : Bool := (x &&& s.1) == (if s.2 then s.1 else 0)
def badMask (x : Nat) : Nat :=
  ((List.range 22).filter (fun i => violates x (axis.getD i (0,false)))).foldl
    (fun a i => a ||| (1 <<< i)) 0
def hit (mask x : Nat) : Bool := (badMask x &&& mask) != 0
def inside (mask x : Nat) : Bool := (badMask x &&& mask) == badMask x
def parity (f x : Nat) : Bool := (((List.range 12).filter (fun i =>
  (f &&& x).testBit i)).length % 2 == 1)
def witnesses : List (Nat × Nat) := [(3,84),(3,98),(3,140),(3,161),(3,266),(3,273),(2,532),(2,546),(9,596),(9,610),(1,644),(8,652),(12,660),(0,672),(7,673),(11,674),(16,676),(1,770),(8,778),(0,784),(7,785),(10,786),(17,788),(18,802),(2,1036),(2,1057),(1,1092),(6,1100),(14,1108),(0,1120),(5,1121),(13,1122),(16,1124),(15,1164),(15,1185),(1,1281),(0,1288),(4,1289),(13,1290),(17,1292),(14,1297),(18,1313),(2,2058),(2,2065),(1,2114),(6,2122),(0,2128),(5,2129),(10,2130),(19,2132),(20,2146),(1,2177),(0,2184),(4,2185),(11,2186),(19,2188),(12,2193),(20,2209),(21,2314),(21,2321)]
theorem witnesses_private : witnesses.all (fun d => badMask d.2 == (1 <<< d.1)) = true := by decide +kernel

def blocked (f owned x : Nat) : Bool := (List.range 22).all (fun i =>
  !(badMask x).testBit i || owned.testBit i ||
  witnesses.any (fun d => d.1 == i && parity f d.2 != parity f x))
def closed (P : Nat → Prop) := ∀ a b c, P a → P b → P c → P (a ^^^ b ^^^ c)
structure Profile (f m n t : Nat) (A B : Nat → Prop) : Prop where
  ac : closed A
  bc : closed B
  sa : ∀ x, inside m x = true → A x
  sb : ∀ x, inside n x = true → B x
  au : ∀ x, A x → hit (3 ||| m) x = true
  bu : ∀ x, B x → hit (3 ||| n) x = true ∨ A x
  root : ∀ x, blocked f (3 ||| m ||| n ||| t) x = true → hit (3 ||| t) x = false → A x ∨ B x

theorem case0 (A B : Nat → Prop) (h : Profile 0 66576 2529892 1597832 A B) : False := by
  have e0 : (A 628) → (¬ A 631) := by
    intro hu
    intro hv
    exact (by decide : hit (3 ||| 66576) 785 ≠ true) (h.au 785 (h.ac 679 676 786 (h.ac 628 631 676 hu hv (h.sa 676 (by decide))) (h.sa 676 (by decide)) (h.sa 786 (by decide))))
  have e1 : (¬ A 631) → (B 514) := by
    intro hu
    rcases h.root 1132 (by decide) (by decide) with ax | bx
    · exact (hu (h.ac 1498 676 1289 (h.ac 1132 676 786 ax (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))).elim
    · exact (h.bc 1050 532 1036 (h.bc 1114 532 596 (h.bc 1132 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide)))
  have e2 : (B 514) → (A 620) := by
    intro hu
    rcases h.bu 1306 (h.bc 770 532 1036 (h.bc 514 532 788 hu (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) with outside | atX
    · exact ((by decide : hit (3 ||| 2529892) 1306 ≠ true) outside).elim
    · exact (h.ac 1196 676 1124 (h.ac 1306 676 786 atX (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide)))
  have e3 : (A 620) → (¬ A 628) := by
    intro hu
    intro hv
    exact (by decide : hit (3 ||| 66576) 778 ≠ true) (h.au 778 (h.ac 700 676 786 (h.ac 620 628 676 hu hv (h.sa 676 (by decide))) (h.sa 676 (by decide)) (h.sa 786 (by decide))))
  have e4 : (¬ A 628) → (B 514) := by
    intro hu
    rcases h.root 628 (by decide) (by decide) with ax | bx
    · exact (hu ax).elim
    · exact (h.bc 578 532 596 (h.bc 628 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide)))
  have e5 : (B 514) → (A 628) := by
    intro hu
    rcases h.bu 793 (h.bc 1324 532 1057 (h.bc 820 532 1036 (h.bc 564 532 788 (h.bc 514 532 546 hu (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) (h.sb 532 (by decide)) (h.sb 1057 (by decide))) with outside | atX
    · exact ((by decide : hit (3 ||| 2529892) 793 ≠ true) outside).elim
    · exact (h.ac 1497 676 1289 (h.ac 793 676 1124 atX (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))
  by_cases v : A 628
  · exact (e3 (e2 (e1 (e0 v)))) v
  · exact v (e5 (e4 v))

theorem case1 (A B : Nat → Prop) (h : Profile 7 66576 39524 393216 A B) : False := by
  have e0 : (A 632) → (¬ A 632) := by
    intro hu
    exact ((by decide : hit (3 ||| 66576) 675 ≠ true) (h.au 675 (h.ac 1294 676 1289 (h.ac 974 676 1124 (h.ac 632 676 786 hu (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))))).elim
  have e1 : (¬ A 632) → (B 526) := by
    intro hu
    rcases h.root 675 (by decide) (by decide) with ax | bx
    · exact (hu (h.ac 1493 676 1289 (h.ac 789 676 1124 (h.ac 675 676 786 ax (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))).elim
    · exact (h.bc 1083 532 1057 (h.bc 547 532 1036 (h.bc 675 532 660 bx (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) (h.sb 532 (by decide)) (h.sb 1057 (by decide)))
  have e2 : (B 526) → (¬ B 525) := by
    intro hu
    intro hv
    rcases h.bu 652 (h.bc 1209 532 1057 (h.bc 673 532 1036 (h.bc 545 532 660 (h.bc 535 532 546 (h.bc 526 525 532 hu hv (h.sb 532 (by decide))) (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) (h.sb 532 (by decide)) (h.sb 1057 (by decide))) with raw | atX
    · exact (by decide : hit (3 ||| 39524) 652 ≠ true) raw
    · exact (by decide : hit (3 ||| 66576) 652 ≠ true) (h.au 652 atX)
  have e3 : (¬ B 525) → (A 632) := by
    intro hu
    rcases h.root 1123 (by decide) (by decide) with ax | bx
    · exact (h.ac 1493 676 1289 (h.ac 1123 676 786 ax (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))
    · exact (hu (h.bc 1045 532 1036 (h.bc 1109 532 596 (h.bc 1123 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide)))).elim
  by_cases v : A 632
  · exact (e0 v) v
  · exact v (e3 (e2 (e1 v)))

theorem case2 (A B : Nat → Prop) (h : Profile 7 66576 2529892 384 A B) : False := by
  have e0 : (A 632) → (¬ A 632) := by
    intro hu
    exact ((by decide : hit (3 ||| 66576) 675 ≠ true) (h.au 675 (h.ac 1294 676 1289 (h.ac 974 676 1124 (h.ac 632 676 786 hu (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))))).elim
  have e1 : (¬ A 632) → (B 525) := by
    intro hu
    rcases h.root 1493 (by decide) (by decide) with ax | bx
    · exact (hu (h.ac 1493 676 1289 ax (h.sa 676 (by decide)) (h.sa 1289 (by decide)))).elim
    · exact (h.bc 1045 532 1036 (h.bc 1301 532 788 (h.bc 1429 532 660 (h.bc 1493 532 596 bx (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide)))
  have e2 : (B 525) → (¬ B 523) := by
    intro hu
    intro hv
    rcases h.bu 1290 (h.bc 786 532 1036 (h.bc 530 532 788 (h.bc 525 523 532 hu hv (h.sb 532 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) with raw | atX
    · exact (by decide : hit (3 ||| 2529892) 1290 ≠ true) raw
    · exact (by decide : hit (3 ||| 66576) 1290 ≠ true) (h.au 1290 atX)
  have e3 : (¬ B 523) → (A 632) := by
    intro hu
    rcases h.root 2531 (by decide) (by decide) with ax | bx
    · exact (h.ac 2190 676 2130 (h.ac 3875 676 1289 (h.ac 2531 676 1124 ax (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))) (h.sa 676 (by decide)) (h.sa 2130 (by decide)))
    · exact (hu (h.bc 2069 532 2058 (h.bc 2325 532 788 (h.bc 2453 532 660 (h.bc 2517 532 596 (h.bc 2531 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 2058 (by decide)))).elim
  by_cases v : A 632
  · exact (e0 v) v
  · exact v (e3 (e2 (e1 v)))

theorem case3 (A B : Nat → Prop) (h : Profile 63 66576 39524 393216 A B) : False := by
  have e0 : (A 632) → (¬ A 632) := by
    intro hu
    exact ((by decide : hit (3 ||| 66576) 675 ≠ true) (h.au 675 (h.ac 1294 676 1289 (h.ac 974 676 1124 (h.ac 632 676 786 hu (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))))).elim
  have e1 : (¬ A 632) → (B 526) := by
    intro hu
    rcases h.root 675 (by decide) (by decide) with ax | bx
    · exact (hu (h.ac 1493 676 1289 (h.ac 789 676 1124 (h.ac 675 676 786 ax (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))).elim
    · exact (h.bc 1083 532 1057 (h.bc 547 532 1036 (h.bc 675 532 660 bx (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) (h.sb 532 (by decide)) (h.sb 1057 (by decide)))
  have e2 : (B 526) → (¬ B 525) := by
    intro hu
    intro hv
    rcases h.bu 652 (h.bc 1209 532 1057 (h.bc 673 532 1036 (h.bc 545 532 660 (h.bc 535 532 546 (h.bc 526 525 532 hu hv (h.sb 532 (by decide))) (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) (h.sb 532 (by decide)) (h.sb 1057 (by decide))) with raw | atX
    · exact (by decide : hit (3 ||| 39524) 652 ≠ true) raw
    · exact (by decide : hit (3 ||| 66576) 652 ≠ true) (h.au 652 atX)
  have e3 : (¬ B 525) → (A 632) := by
    intro hu
    rcases h.root 1123 (by decide) (by decide) with ax | bx
    · exact (h.ac 1493 676 1289 (h.ac 1123 676 786 ax (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide)))
    · exact (hu (h.bc 1045 532 1036 (h.bc 1109 532 596 (h.bc 1123 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide)))).elim
  by_cases v : A 632
  · exact (e0 v) v
  · exact v (e3 (e2 (e1 v)))

theorem case4 (A B : Nat → Prop) (h : Profile 63 66576 2529892 384 A B) : False := by
  have e0 : (A 632) → (¬ A 632) := by
    intro hu
    exact ((by decide : hit (3 ||| 66576) 675 ≠ true) (h.au 675 (h.ac 1294 676 1289 (h.ac 974 676 1124 (h.ac 632 676 786 hu (h.sa 676 (by decide)) (h.sa 786 (by decide))) (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))))).elim
  have e1 : (¬ A 632) → (B 525) := by
    intro hu
    rcases h.root 1493 (by decide) (by decide) with ax | bx
    · exact (hu (h.ac 1493 676 1289 ax (h.sa 676 (by decide)) (h.sa 1289 (by decide)))).elim
    · exact (h.bc 1045 532 1036 (h.bc 1301 532 788 (h.bc 1429 532 660 (h.bc 1493 532 596 bx (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide)))
  have e2 : (B 525) → (¬ B 523) := by
    intro hu
    intro hv
    rcases h.bu 1290 (h.bc 786 532 1036 (h.bc 530 532 788 (h.bc 525 523 532 hu hv (h.sb 532 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 1036 (by decide))) with raw | atX
    · exact (by decide : hit (3 ||| 2529892) 1290 ≠ true) raw
    · exact (by decide : hit (3 ||| 66576) 1290 ≠ true) (h.au 1290 atX)
  have e3 : (¬ B 523) → (A 632) := by
    intro hu
    rcases h.root 2531 (by decide) (by decide) with ax | bx
    · exact (h.ac 2190 676 2130 (h.ac 3875 676 1289 (h.ac 2531 676 1124 ax (h.sa 676 (by decide)) (h.sa 1124 (by decide))) (h.sa 676 (by decide)) (h.sa 1289 (by decide))) (h.sa 676 (by decide)) (h.sa 2130 (by decide)))
    · exact (hu (h.bc 2069 532 2058 (h.bc 2325 532 788 (h.bc 2453 532 660 (h.bc 2517 532 596 (h.bc 2531 532 546 bx (h.sb 532 (by decide)) (h.sb 546 (by decide))) (h.sb 532 (by decide)) (h.sb 596 (by decide))) (h.sb 532 (by decide)) (h.sb 660 (by decide))) (h.sb 532 (by decide)) (h.sb 788 (by decide))) (h.sb 532 (by decide)) (h.sb 2058 (by decide)))).elim
  by_cases v : A 632
  · exact (e0 v) v
  · exact v (e3 (e2 (e1 v)))

end PEqualNP.Outside.L_pcx_120_cases

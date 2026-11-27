import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9750.Replacement

abbrev Row := Fin 4096
def positive : List Row := [66,96,129,144,160,264,272,516,520,544,1026,1028,1040,2049,2050,2056]
def negative : List Row := [63,93,142,204,295,325,390,531,593,771,898,1065,1097,1224,1313,1857,2100,2132,2340,2500,2640,3360,4032]
def includes (a b : Nat) : Bool := (a &&& b) == a
def target (r : Row) : Bool := positive.any (fun e => includes e.val r.val)
def encode (r : Row) (substitute : Bool) : Nat :=
  let x := r.val.testBit
  let w12 := x 0 || x 1
  let w13 := x 0 || x 10
  let w14 := x 3 || x 5
  let w15 := x 8 || w14
  let w16 := if substitute then w14 || x 4 else !(x 9)
  let w17 := w15 && w16
  (r.val &&& 4094) ||| (w12.toNat <<< 12) ||| (w13.toNat <<< 13) ||| (w17.toNat <<< 17)
def examples (rows : List Row) : List (Row × Nat) := rows.map (fun r => (r,encode r false))
def pos : List (Row × Nat) := [(66,4162), (96,131168), (129,12416), (144,144), (160,131232), (264,131336), (272,131344), (516,516), (520,520), (544,544), (1026,13314), (1028,9220), (1040,9232), (2049,14336), (2050,6146), (2056,133128)]
def neg : List (Row × Nat) := [(63,143422), (93,143452), (142,135310), (204,131276), (295,143654), (325,143684), (390,135558), (531,12818), (593,12880), (771,13058), (898,4994), (1065,144424), (1097,144456), (1224,140488), (1313,144672), (1857,14144), (2100,133172), (2132,2132), (2340,133412), (2500,133572), (2640,2640), (3360,142624), (4032,12224)]

theorem labelsPos : pos.all (fun v => target v.1 && (v.2==encode v.1 false))=true := by decide +kernel
theorem labelsNeg : neg.all (fun v => !(target v.1) && (v.2==encode v.1 false))=true := by decide +kernel

def check (r : Row) : Bool :=
  if target r then pos.any fun v => includes v.2 (encode r true)
  else neg.any fun v => includes (encode r true) v.2
def part (q : Nat) (j : Fin 64) : Row := Fin.ofNat 4096 (q*64+j.val)
theorem p0 : ∀j, check (part 0 j)=true := by decide +kernel
theorem p1 : ∀j, check (part 1 j)=true := by decide +kernel
theorem p2 : ∀j, check (part 2 j)=true := by decide +kernel
theorem p3 : ∀j, check (part 3 j)=true := by decide +kernel
theorem p4 : ∀j, check (part 4 j)=true := by decide +kernel
theorem p5 : ∀j, check (part 5 j)=true := by decide +kernel
theorem p6 : ∀j, check (part 6 j)=true := by decide +kernel
theorem p7 : ∀j, check (part 7 j)=true := by decide +kernel
theorem p8 : ∀j, check (part 8 j)=true := by decide +kernel
theorem p9 : ∀j, check (part 9 j)=true := by decide +kernel
theorem p10 : ∀j, check (part 10 j)=true := by decide +kernel
theorem p11 : ∀j, check (part 11 j)=true := by decide +kernel
theorem p12 : ∀j, check (part 12 j)=true := by decide +kernel
theorem p13 : ∀j, check (part 13 j)=true := by decide +kernel
theorem p14 : ∀j, check (part 14 j)=true := by decide +kernel
theorem p15 : ∀j, check (part 15 j)=true := by decide +kernel
theorem p16 : ∀j, check (part 16 j)=true := by decide +kernel
theorem p17 : ∀j, check (part 17 j)=true := by decide +kernel
theorem p18 : ∀j, check (part 18 j)=true := by decide +kernel
theorem p19 : ∀j, check (part 19 j)=true := by decide +kernel
theorem p20 : ∀j, check (part 20 j)=true := by decide +kernel
theorem p21 : ∀j, check (part 21 j)=true := by decide +kernel
theorem p22 : ∀j, check (part 22 j)=true := by decide +kernel
theorem p23 : ∀j, check (part 23 j)=true := by decide +kernel
theorem p24 : ∀j, check (part 24 j)=true := by decide +kernel
theorem p25 : ∀j, check (part 25 j)=true := by decide +kernel
theorem p26 : ∀j, check (part 26 j)=true := by decide +kernel
theorem p27 : ∀j, check (part 27 j)=true := by decide +kernel
theorem p28 : ∀j, check (part 28 j)=true := by decide +kernel
theorem p29 : ∀j, check (part 29 j)=true := by decide +kernel
theorem p30 : ∀j, check (part 30 j)=true := by decide +kernel
theorem p31 : ∀j, check (part 31 j)=true := by decide +kernel
theorem p32 : ∀j, check (part 32 j)=true := by decide +kernel
theorem p33 : ∀j, check (part 33 j)=true := by decide +kernel
theorem p34 : ∀j, check (part 34 j)=true := by decide +kernel
theorem p35 : ∀j, check (part 35 j)=true := by decide +kernel
theorem p36 : ∀j, check (part 36 j)=true := by decide +kernel
theorem p37 : ∀j, check (part 37 j)=true := by decide +kernel
theorem p38 : ∀j, check (part 38 j)=true := by decide +kernel
theorem p39 : ∀j, check (part 39 j)=true := by decide +kernel
theorem p40 : ∀j, check (part 40 j)=true := by decide +kernel
theorem p41 : ∀j, check (part 41 j)=true := by decide +kernel
theorem p42 : ∀j, check (part 42 j)=true := by decide +kernel
theorem p43 : ∀j, check (part 43 j)=true := by decide +kernel
theorem p44 : ∀j, check (part 44 j)=true := by decide +kernel
theorem p45 : ∀j, check (part 45 j)=true := by decide +kernel
theorem p46 : ∀j, check (part 46 j)=true := by decide +kernel
theorem p47 : ∀j, check (part 47 j)=true := by decide +kernel
theorem p48 : ∀j, check (part 48 j)=true := by decide +kernel
theorem p49 : ∀j, check (part 49 j)=true := by decide +kernel
theorem p50 : ∀j, check (part 50 j)=true := by decide +kernel
theorem p51 : ∀j, check (part 51 j)=true := by decide +kernel
theorem p52 : ∀j, check (part 52 j)=true := by decide +kernel
theorem p53 : ∀j, check (part 53 j)=true := by decide +kernel
theorem p54 : ∀j, check (part 54 j)=true := by decide +kernel
theorem p55 : ∀j, check (part 55 j)=true := by decide +kernel
theorem p56 : ∀j, check (part 56 j)=true := by decide +kernel
theorem p57 : ∀j, check (part 57 j)=true := by decide +kernel
theorem p58 : ∀j, check (part 58 j)=true := by decide +kernel
theorem p59 : ∀j, check (part 59 j)=true := by decide +kernel
theorem p60 : ∀j, check (part 60 j)=true := by decide +kernel
theorem p61 : ∀j, check (part 61 j)=true := by decide +kernel
theorem p62 : ∀j, check (part 62 j)=true := by decide +kernel
theorem p63 : ∀j, check (part 63 j)=true := by decide +kernel
set_option maxHeartbeats 1600000 in
theorem indexed (q j : Fin 64) : check (part q.val j)=true := by
  fin_cases q
  · exact p0 j
  · exact p1 j
  · exact p2 j
  · exact p3 j
  · exact p4 j
  · exact p5 j
  · exact p6 j
  · exact p7 j
  · exact p8 j
  · exact p9 j
  · exact p10 j
  · exact p11 j
  · exact p12 j
  · exact p13 j
  · exact p14 j
  · exact p15 j
  · exact p16 j
  · exact p17 j
  · exact p18 j
  · exact p19 j
  · exact p20 j
  · exact p21 j
  · exact p22 j
  · exact p23 j
  · exact p24 j
  · exact p25 j
  · exact p26 j
  · exact p27 j
  · exact p28 j
  · exact p29 j
  · exact p30 j
  · exact p31 j
  · exact p32 j
  · exact p33 j
  · exact p34 j
  · exact p35 j
  · exact p36 j
  · exact p37 j
  · exact p38 j
  · exact p39 j
  · exact p40 j
  · exact p41 j
  · exact p42 j
  · exact p43 j
  · exact p44 j
  · exact p45 j
  · exact p46 j
  · exact p47 j
  · exact p48 j
  · exact p49 j
  · exact p50 j
  · exact p51 j
  · exact p52 j
  · exact p53 j
  · exact p54 j
  · exact p55 j
  · exact p56 j
  · exact p57 j
  · exact p58 j
  · exact p59 j
  · exact p60 j
  · exact p61 j
  · exact p62 j
  · exact p63 j
theorem allRows (r : Row) : check r=true := by
  let j : Fin 64 := ⟨r.val%64, Nat.mod_lt _ (by decide)⟩
  let q : Fin 64 := ⟨r.val/64, by have := r.isLt; omega⟩
  have same : part q.val j=r := by
    apply Fin.ext
    change ((r.val/64)*64+r.val%64)%4096 = r.val
    have sum : r.val/64*64 + r.val%64 = r.val := by omega
    rw [sum,Nat.mod_eq_of_lt r.isLt]
  rw [←same]
  exact indexed q j

theorem transfer (post : Nat → Bool)
    (mono : ∀ a b, includes a b=true → post a=true → post b=true)
    (computes : ∀ r, post (encode r false)=target r) :
    ∀r, post (encode r true)=target r := by
  intro r
  have h := allRows r
  unfold check at h
  cases ht : target r with
  | false =>
    simp only [ht,Bool.false_eq_true,if_false] at h
    obtain ⟨v,hv,le⟩ := List.any_eq_true.mp h
    have lab := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp labelsNeg) v hv)
    have orig : target v.1=false := by simpa using lab.1
    have wire : v.2=encode v.1 false := beq_iff_eq.mp lab.2
    cases act : post (encode r true) with
    | false => rfl
    | true =>
      have hit := mono _ _ le act
      rw [wire,computes,orig] at hit
      contradiction
  | true =>
    simp only [ht,if_true] at h
    obtain ⟨v,hv,le⟩ := List.any_eq_true.mp h
    have lab := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp labelsPos) v hv)
    apply mono _ _ le
    have wire : v.2=encode v.1 false := beq_iff_eq.mp lab.2
    rw [wire,computes,lab.1]

end PEqualNP.Outside.L_meta_9750.Replacement

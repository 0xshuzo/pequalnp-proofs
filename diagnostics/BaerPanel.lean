import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.Panel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Raw := Fin 27
abbrev Port := Fin 332
def masks : List ℕ := [0,1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,16512,17408,18432,20480,32768,32896,33024,33792,40960,49152,50176,65536,65664,66048,69632,73728,81920,82048,98304,106496,131072,131200,132096,133120,135168,163840,163968,196608,200704,262144,262656,263168,264192,270336,278528,279552,294912,295936,311296,312320,327680,328192,393216,395264,524288,524416,524544,525312,532480,540672,540800,589824,589952,606208,606336,655360,656384,786432,794624,1048576,1048704,1049088,1052672,1056768,1064960,1069056,1081344,1081472,1179648,1179776,1212416,1212544,1310720,1318912,1572864,1581056,1835008,1843200,2097152,2097280,2097408,2097664,2099200,2113536,2113664,2129920,2130176,2162688,2162816,2179072,2179200,2228224,2230272,2359296,2361344,2490368,2492416,2621440,2621568,2637824,2637952,2686976,2687104,2703360,2703488,3145728,3146240,4194304,4194432,4194560,4194816,4196352,4210688,4212736,4227072,4227200,4259840,4260352,4325376,4325504,4358144,4358272,4456448,4456960,4521984,4522496,4718592,4718848,5242880,5243008,5275648,5275776,5373952,5374080,5406720,5406848,8388608,8388864,8390656,8392704,8396800,8404992,8409088,8421376,8429568,8454144,8462336,8486912,8495104,8519680,8521728,8650752,8652800,8781824,8783872,8912896,8913152,9437184,9441280,9453568,9457664,10485760,10487808,10616832,10618880,10747904,10749952,10878976,10881024,12582912,12583168,13107200,13107456,16777216,16777472,16777728,16778240,16781312,16793600,16797696,16809984,16810240,16842752,16843264,16908288,16909312,17039360,17039872,17104896,17105408,17301504,17302528,17432576,17433600,17825792,17829888,17842176,17846272,18874368,18874624,18907136,18907392,20971520,20972032,21037056,21037568,21233664,21234176,21299200,21299712,25165824,25169920,25182208,25186304,26214400,26218496,26230784,26234880,33554432,33554688,33556480,33558528,33562624,33570816,33572864,33587200,33587456,33619968,33624064,33685504,33689600,33751040,33755136,33816576,33824768,34078720,34086912,34340864,34349056,34603008,34611200,34865152,34873344,35127296,35135488,35389440,35397632,35651584,35651840,35684352,35684608,37748736,37750784,37765120,37767168,50331648,50331904,50364416,50364672,52428800,52429056,52461568,52461824,67108864,67109376,67109888,67110912,67117056,67125248,67127296,67141632,67149824,67174400,67182592,67207168,67215360,67239936,67240960,67633152,67634176,67764224,67765248,68157440,68157952,69206016,69206528,70254592,70255104,71303168,71305216,71319552,71321600,75497472,75505664,75530240,75538432,75563008,75571200,75595776,75603968,83886080,83887104,84017152,84018176,84410368,84411392,84541440,84542464,100663296,100665344,100679680,100681728,104857600,104859648,104873984,104876032]
def low : List ℕ := [134061188,133637536,133051024,133962884,66596354,133178784,132133520,125832128,125832128,83900680,100669185,67123464,11778]
def high : List ℕ := [134077572,133670304,133116560,134093956,66858498,133703072,133182096,127929280,130026432,92289288,117446401,100677896,67120642]
def signal (i : Port) (j : Raw) := (masks.getD i.val 0).testBit j.val
def board (x : Raw→Bool) (i : Port) := decide (∃ j : Raw,signal i j=true ∧ x j=true)
def targetEdges : List (ℕ×ℕ) := [(0,7),(0,11),(0,13),(0,24),(1,7),(1,8),(1,12),(1,18),(1,26),(2,8),(2,9),(2,13),(2,14),(2,17),(3,7),(3,9),(3,10),(3,23),(3,25),(4,8),(4,10),(4,11),(4,16),(4,20),(5,9),(5,11),(5,12),(5,15),(5,19),(6,10),(6,12),(6,13),(6,21),(6,22)]
def want (x : Raw→Bool) := ∃ a b : Raw,(a.val,b.val)∈targetEdges ∧ x a=true ∧ x b=true
def word (w : ℕ) (j : Raw) := w.testBit j.val
def lo (k : Fin 13) := word (low.getD k.val 0)
def hi (k : Fin 13) := word (high.getD k.val 0)
def ok (k : ℕ) (x : Raw→Bool) := ∀ j : Raw, 14≤j.val → j.val<14+k → x j=false
def select (k : Fin 13) : Finset Port := Finset.univ.filter (fun i => board (lo k) i≠board (hi k) i)
def alive := word 129
theorem geometry : ∀ k : Fin 13, ok k.val (lo k) ∧ ok k.val (hi k) ∧ ¬want (lo k) ∧ want (hi k) := by
  unfold ok want
  decide +kernel
theorem retained : want alive ∧ ∀ k : Fin 13,ok (k.val+1) alive := by unfold want ok; decide +kernel
set_option maxHeartbeats 4000000 in
theorem omitted_bits : ∀ k : Fin 13,∀ i : Port,i∈select k → ∀j : Raw,signal i j=true → 14≤j.val ∧ j.val<14+(k.val+1) := by
  decide +kernel
theorem quiet (k : Fin 13) (x : Raw→Bool) (clean : ok (k.val+1) x) (i : Port) (m : i∈select k) : board x i=false := by
  apply decide_eq_false
  rintro ⟨j,e,on⟩
  obtain ⟨a,b⟩ := omitted_bits k i m j e
  rw [clean j a b] at on; contradiction
theorem agree (k : Fin 13) (i : Port) (m : i∉select k) : board (lo k) i=board (hi k) i := by simpa [select] using m
def finalMap (i : Port) : Option (Fin 14) :=
  let j := ([14,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,7,10,11,12,14,7,8,10,13,14,10,14,7,9,12,13,14,7,14,13,14,7,10,11,12,14,7,14,12,14,9,10,11,13,14,10,14,10,14,10,14,9,14,11,14,7,8,10,13,14,7,14,7,14,7,14,10,14,13,14,7,9,12,13,14,12,14,7,14,7,14,7,14,13,14,13,14,13,14,7,8,9,11,14,7,14,8,14,7,14,7,14,11,14,11,14,11,14,7,14,7,14,7,14,7,14,9,14,7,8,9,11,14,11,14,7,14,9,14,7,14,7,14,9,14,9,14,8,14,7,14,7,14,7,14,7,14,8,11,12,13,14,12,14,13,14,13,14,13,14,11,14,11,14,11,14,8,14,12,14,12,14,11,14,11,14,11,14,11,14,8,14,8,14,8,9,10,12,14,12,14,8,14,9,14,10,14,9,14,9,14,10,14,10,14,12,14,12,14,8,14,8,14,9,14,9,14,9,14,9,14,12,14,12,14,12,14,12,14,8,11,12,13,14,11,14,8,14,12,14,12,14,12,14,13,14,13,14,13,14,13,14,13,14,13,14,13,14,8,14,8,14,11,14,11,14,8,14,8,14,8,14,8,14,9,10,11,13,14,11,14,13,14,13,14,13,14,10,14,10,14,10,14,9,14,9,14,9,14,11,14,11,14,13,14,13,14,13,14,13,14,10,14,10,14,10,14,10,14,11,14,11,14,11,14,11] : List ℕ).getD i.val 14
  if h : j<14 then some ⟨j,h⟩ else none
theorem retained_port : ∀ i : Port,∀ j : Fin 14,signal i ⟨j.val,by omega⟩=true ↔ finalMap i=some j := by decide +kernel
def lift (x : Fin 14→Bool) (j : Raw) := if h : j.val<14 then x ⟨j.val,h⟩ else false
theorem final_clean (x : Fin 14→Bool) : ok 13 (lift x) := by intro j lo _; simp [lift,Nat.not_lt.mpr lo]
theorem final_read (x : Fin 14→Bool) (i : Port) : board (lift x) i=(finalMap i).elim false x := by
  cases h : finalMap i with
  | none =>
    apply decide_eq_false
    rintro ⟨j,s,on⟩
    by_cases b : j.val<14
    · have eq := (retained_port i ⟨j.val,b⟩).mp s; rw [h] at eq; cases eq
    · simp [lift,b] at on
  | some j =>
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro yes
      obtain ⟨r,rr,on⟩ := of_decide_eq_true yes
      by_cases b : r.val<14
      · have eq := (retained_port i ⟨r.val,b⟩).mp rr
        rw [h] at eq
        have id := Option.some.inj eq
        simpa only [lift,dif_pos b,←id] using on
      · simp [lift,b] at on
    · intro on
      exact decide_eq_true ⟨⟨j.val,by omega⟩,(retained_port i j).mpr h,by simpa [lift,j.isLt] using on⟩
def Fano (x : Fin 14→Bool) := ∃ p l : Fin 7,(p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
theorem final_target : ∀ x : Fin 14→Bool,want (lift x) ↔ Fano x := by
  intro x
  have form : ∀ a b : Fin 14,(a.val,b.val)∈targetEdges ↔ ∃p l : Fin 7,(p=l ∨ p=l+1 ∨ p=l+3) ∧ a=Fin.castAdd 7 p ∧ b=Fin.natAdd 7 l := by decide +kernel
  constructor
  · rintro ⟨a,b,ab,pa,lb⟩
    by_cases da : a.val<14
    · by_cases db : b.val<14
      · obtain ⟨p,l,e,eq,eq'⟩ := (form ⟨a.val,da⟩ ⟨b.val,db⟩).mp ab
        exact ⟨p,l,e,eq ▸ (show x ⟨a.val,da⟩=true from by simpa [lift,da] using pa),eq' ▸ (show x ⟨b.val,db⟩=true from by simpa [lift,db] using lb)⟩
      · simp [lift,db] at lb
    · simp [lift,da] at pa
  · rintro ⟨p,l,e,pa,lb⟩
    let a := Fin.castAdd 7 p
    let b := Fin.natAdd 7 l
    exact ⟨⟨a.val,by have := a.isLt;omega⟩,⟨b.val,by have := b.isLt;omega⟩,(form a b).mpr ⟨p,l,e,rfl,rfl⟩,by simpa [lift,a.isLt] using pa,by simpa [lift,b.isLt] using lb⟩
end PEqualNP.Outside.L_meta_9743.Panel

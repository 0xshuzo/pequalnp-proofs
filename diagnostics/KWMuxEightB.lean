import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9939.Rectangles
variable {I : Type} [DecidableEq I]

structure View (I : Type) where
  pos : Finset I
  neg : Finset I
def band (a b : View I) : View I := ⟨a.pos∩b.pos,a.neg∪b.neg⟩
def bor (a b : View I) : View I := ⟨a.pos∪b.pos,a.neg∩b.neg⟩
inductive Tree (I : Type)
  | pin : View I → Tree I
  | both : Tree I → Tree I → Tree I
  | either : Tree I → Tree I → Tree I

def evaluate : Tree I → View I
  | .pin a => a
  | .both a b => band (evaluate a) (evaluate b)
  | .either a b => bor (evaluate a) (evaluate b)
def leaves : Tree I → Nat
  | .pin _ => 1
  | .both a b | .either a b => leaves a + leaves b
def allowed (B : View I → Prop) : Tree I → Prop
  | .pin a => B a
  | .both a b | .either a b => allowed B a ∧ allowed B b

-- The two coordinates track accepted lower-extreme and rejected upper-extreme
-- assignments at the eight addresses. Either operation partitions one side.
structure Price (I : Type) [DecidableEq I] (B : View I → Prop) where
  value : Finset I → Finset I → Nat
  leaf : ∀ a, B a → ∀ x⊆a.pos, ∀ y⊆a.neg, value x y≤1
  splitX : ∀ x z y, Disjoint x z → value (x∪z) y≤value x y+value z y
  splitY : ∀ x y z, Disjoint y z → value x (y∪z)≤value x y+value x z

theorem price_sound {B : View I → Prop} (p : Price I B) (f : Tree I) (bank : allowed B f) :
    ∀x⊆(evaluate f).pos,∀y⊆(evaluate f).neg,p.value x y≤leaves f := by
  induction f with
  | pin a => exact p.leaf a bank
  | both a b ia ib =>
    intro x hx y hy
    let left := y ∩ (evaluate a).neg
    let right := y \ (evaluate a).neg
    have leftSub : left⊆(evaluate a).neg := Finset.inter_subset_right
    have rightSub : right⊆(evaluate b).neg := by
      intro i hi
      have hh := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hy hh.1)).resolve_left hh.2
    have combine : left∪right=y := by
      ext i
      simp [left,right]
    have sep : Disjoint left right := by
      rw [Finset.disjoint_left]
      exact fun _ l r => (Finset.mem_sdiff.mp r).2 (Finset.mem_inter.mp l).2
    have la := ia bank.1 x (fun _ h=>(Finset.mem_inter.mp (hx h)).1) left leftSub
    have lb := ib bank.2 x (fun _ h=>(Finset.mem_inter.mp (hx h)).2) right rightSub
    have h := p.splitY x left right sep
    rw [combine] at h
    exact h.trans (Nat.add_le_add la lb)
  | either a b ia ib =>
    intro x hx y hy
    let left := x ∩ (evaluate a).pos
    let right := x \ (evaluate a).pos
    have leftSub : left⊆(evaluate a).pos := Finset.inter_subset_right
    have rightSub : right⊆(evaluate b).pos := by
      intro i hi
      have hh := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hx hh.1)).resolve_left hh.2
    have combine : left∪right=x := by
      ext i
      simp [left,right]
    have sep : Disjoint left right := by
      rw [Finset.disjoint_left]
      exact fun _ l r => (Finset.mem_sdiff.mp r).2 (Finset.mem_inter.mp l).2
    have la := ia bank.1 left leftSub y (fun _ h=>(Finset.mem_inter.mp (hy h)).1)
    have lb := ib bank.2 right rightSub y (fun _ h=>(Finset.mem_inter.mp (hy h)).2)
    have h := p.splitX left right y sep
    rw [combine] at h
    exact h.trans (Nat.add_le_add la lb)

theorem one_shared {B : View I → Prop} (h f : Tree I) (pre : allowed B h)
    (tail : allowed (fun v => B v ∨ v=evaluate h) f) (p : Price I B)
    (q : Price I (fun v=>B v ∨ v=evaluate h)) :
    p.value (evaluate h).pos (evaluate h).neg + q.value (evaluate f).pos (evaluate f).neg ≤
      leaves h + leaves f :=
  Nat.add_le_add (price_sound p h pre _ Finset.Subset.rfl _ Finset.Subset.rfl)
    (price_sound q f tail _ Finset.Subset.rfl _ Finset.Subset.rfl)
end PEqualNP.Outside.L_meta_9939.Rectangles

namespace PEqualNP.Outside.L_meta_9939.Cube
open PEqualNP.Outside.L_meta_9939.Rectangles
abbrev Id := Fin 8
def pack (ord : List Id) (s : Finset Id) : Nat :=
  match ord with
  | [] => 0
  | i::is => 2 * pack is s + (if i∈s then 1 else 0)

def parts : Nat → List (Nat × Nat)
  | 0 => [(0,0)]
  | k+1 => (parts k).flatMap fun p =>
    [(2*p.1,2*p.2),(2*p.1+1,2*p.2),(2*p.1,2*p.2+1)]

theorem pack_add (ps : List Id) (y z : Finset Id) (d : Disjoint y z) :
    pack ps (y∪z)=pack ps y + pack ps z := by
  induction ps with
  | nil => rfl
  | cons i rest ih =>
    by_cases hi : i∈y <;> by_cases hj : i∈z
    · exact False.elim (Finset.disjoint_left.mp d hi hj)
    all_goals simp [pack,Finset.mem_union,hi,hj,ih] <;> omega

theorem pack_parts (ps : List Id) (y z : Finset Id) (d : Disjoint y z) :
    (pack ps y, pack ps z) ∈ parts ps.length := by
  induction ps with
  | nil => simp [pack,parts]
  | cons i rest ih =>
    apply List.mem_flatMap.mpr
    refine ⟨(pack rest y,pack rest z),ih,?_⟩
    by_cases hi : i∈y <;> by_cases hj : i∈z
    · exact False.elim (Finset.disjoint_left.mp d hi hj)
    all_goals simp [pack,hi,hj]

def bank : Array Nat := #[0x0,0x20c621886220c62188411886218862188621884120c621886220c62188411884118841188411884120c621886220c62188411886210441188621044120c621886220c62188411884110441188411044120c621886220c62188411886218862188621884120c621886220c62188411884118841188411884120c621886220c62188411886210441188621044120c621886220c621884118841104411884110420,0x31082310823108228c6131082310823108228c6131082310823108228c6128c6128c6128c6128c6131082310823108228c6131082310823108228c6131082310823108228c6128c6128c6128c6128c6131082310823108228c6131082310823108228c6131082310823108228c6128c6128c6128c6128c6131082310823108228c6131082310823108228c6131082310823108228c6128c6128c6128c6120840,0x394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61314a4290832948320c61310a328c822908320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61394c4310a32948320c61314a4290832106318c41310a328c822106218840,0x498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81414c330ca2414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81498e4390c3414c330c81414c330ca2390a228860,0x5a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc4310815a526498e449cc43108152105414c3418a328c60,0x5a14751d264a106418e451d2649905418e5394c34a106418e541ce5394c3418e4394c3394c3310a24a106418e541ce5394c3418e5390c3394c430ca241ce5394c441ce5394c3394c330ca2394c330ca25a14751d264a106418e451d2649905418e5394c34a106418e541ce5394c3418e4394c3394c3310a24a106418e541ce5394c3418e5390c3394c430ca241ce5394c4318a429082394c330ca22908220860,0x6a56759d465a1465190459d465192549905414e35a1464990559d25494e351904414e3494e3410c25a1265190559d25494e351905410e34950438cc259d254950459d25494e3494e338cc2494e338cc26a56759d465a1465190459d465192549905414e35a1464990559d25494e351904414e3494e3410c25a1265190559d25494e351905410e34950438cc259d254950451904410c2494e338cc2410c230880,0x41ce6398e5398c5314c4398c5314c4314a4290a339cc5318c4318a4294a3318a4294a3294832108239cc6314c4318a5290a3318a5290a32948420c8239cc5314c4318a4290a3318a4290a32948320c82398e6398e5314c5314c4314c5314c4290a4290a3318a4318a4294832948329483294832106221062318c6290a4294a520c83294a520c83210841886229484210842106318c622106318c6218c4210840,0x521064190649ce5394e4418e5394e4394c4310c3521064190549ce5394c3418c4394c3394a3310a2521064190549ce5394c3418e5310c3394c428ca2521064190549ce5394c3418c4310c3394a328ca249d0641906418e5394e4394e5394e4310c4310c349ce5418e5418c4394c3394a3394a3310823108249d06394e5418e5310c3394e528ca3310c42088249ce5394e4418c4310a2394a328ca23108220860,0x6252662526520e551ce451d0551d05418c4414c36252652105520e5498c351ce4498c3418a3414a2625265a105520e5498c351d05498e4418c4390a26252652105520e5498c351ce4498c3418a3390a26252662526520e551ce451d0551d05418c4414c35a1055210549cc4498c3498c3498c33948239482625265a105520e5498c351d05498e4418c4390a25a10551ce449cc4414a2498c3414a23948230c60,0x6ad695a54752106418e4629485212649ce5394c35a9284a1064a0e5398c35250641ce441cc4314a25a9284a1064a0e6394c352507418e441cc5310a25a9284a1064a0e5394c352506418e441cc4310a26ad695a54752106418e4629485212649ce5394c35a9284a1064a0e5398c35250641ce441cc4314a25a9284a1064a0e6394c352507418e441cc5310a25290741ce539ca5294824a0e5394c33148320c60,0x7b1a96a5676254751d046a9685a14651d05414e372d885a12662526498e36254651d0451ce4414c272d686212662526498e3625475190451d05390c272d685a12662526498e3625465190451ce4390c27b1a96a5676254751d046a9685a14651d05414e372d885a12662526498e36254651d0451ce4414c272d686212662526498e3625475190451d05390c26a96759d255a105414c25a125494e3498c330c80,0x62d6a5254852928421065254841d0642106318c45292842106420e6318c442106318c4318c4210825ad4a4a52852928421064a52839ce542106318c45292842106420e6318c442106318c4318c4210825a96a525484a528421065254841d0642106318c44a5284210639ce5318c442106318c4318c4210825294a4210842108318c542108314c5318c62108342108318c6318a521083318c5210832108310840,0x7b1cb625686ad89521266256851d2652126418e46ad89521265a94741ce452126418e441ce4314a2731aa625686ad89521266256849d0552126418e46ad89521265a94741ce452126418e441ce4314a272dcb6256862969521266256851d2652126418e462969521265252641ce452126418e441ce4314a26a9aa5a1485a54849d055a1484150549d06310a35a54849d064a105398c349d05310a3398c320c60,0x8bdeb7b1897b189629467b1896a9676252651d047b189625266ad47520e46294651d04520e4418c28b9cb7b1897b189629467b189625466252651d047b189625266ad47520e46294651d04520e4418c28b9cb7b1897b189629467b1896a9676252651d047b1896252662926520e46294651d04520e4418c2835aa72d6872d685a52572d685a12562526498e372d68625265a50549cc35a525498e349cc331080,0x7358b62d496b16a5a92762d49525475a9284a1056b16a5a92862d49525065a9274a1055250641ce46b16a5a92862d49525065a92849d0552507418e462d49525075a9284a0e552506418e44a0e5394c362d49525485a9284a0e552548521474a10741ce55a9284a107524e641ca44a0e541ce541ca4398a35a9284a10752507398a44a107394e541ce6290a35250741ce64a0c531483398a4290a33148320c60,0x839ab731697356a62d27731696ad4762d285a5057356a62d286b1495a90662d275a5055a906520e47b58a6ad486b1495a9066ad48625265a90751ce46b1495a90762d28524e55a90651ce4524e5498c3731696ad4862d285a4e56ad486a9475a907520e562d285a9075a8e64a0a45a4e5520e54a0a441ca36ad48629275a90749cc4629275a105524e6418a35a907524e6524c53988349cc4418a33988331060,0x941ec7b1898398b62d27839cb72d68731695a505839ab6ad487356a5a9067b589625266ad47520e4839ab6ad487356a5a9067b589625266ad4851ce47356a5a9076b149524e56ad4751ce462926498c3839cb72d68731695a505839aa6a94872d48521057b58a629276ad274a0c4731685a1056290641ca37b58a629276ad2849cc4731685a10562907418a36b149524e65a8e6398835a526498c349cc431060,0x945ee7b9ac7b98b62d497b9ac6b18962d49525267b98b62d496b1495250762d49525265250741ce47b98b62d496b1495250762d49525265250741ce46b1495250762d284a0e65250741ce44a0e6398c38c1cd7358b7356a5a9287358b62d685a9284a1057356a5a92862d284a0e65a9284a1054a0e6398c37356a5a92862d284a0e65a9284a1054a0e6398c362d284a0e64a0c5314834a0e6398c33148320c60,0xa4a2f8bdec941ed7b5898bdec7b1a97b18962546941ed7b189839ab6ad477b589625466ad4752104941ec7b589839ab6ad477b589625466ad4851d04839ab6ad487b58a629266ad4751d0462926498e39c60e839cb8b9cc73168839cb72d8872d685a1258b9cc72d687b56962926731685a1256292649ce38b9cb731687b58a5a526731685a12562927498e37b58a629276ad2749cc45a526498e349cc431080,0xb5291a464fa4a2f8bdeba464f93e0d93dec7b1a9a4a2f93dec941ed7b5898bdeb7b1a97b58962946a4a4f8bdec941ed7b5898bdec7ada97b58a62546941ed7b58a839ab6ad477b589625466ad4751d04a4a4f93e0d8bdec7b1a993e0d835cb7b1aa6a9678bdec7b1aa7b569629267b1a96a96762926520e48bdec7b1aa7b58a5a5267b1aa6a56762948498e47b58a629486ad2749cc45a526498e449cc431080]
def descriptors : Array Nat := #[0,1,23,2,45,68,3,4,89,25,112,26,46,48,92,5,133,156,179,180,201,202,6,7,8,9,229,10,251,76,11,12,265,223,288,224,30,185,31,32,311,28,312,29,339,33,120,34,134,356,378,181,405,164,187,188,427,231,296,232,13,14,36,15,441,245,52,207,464,246,53,494,509,50,537,55,510,51,54,56,552,400,361,582,598,203,209,210,625,253,79,80,648,254,498,81,135,138,273,363,449,407,167,168,666,16,693,17,715,105,740,18,136,139,274,364,758,408,586,169,671,281,784,194,454,216,19,20,661,96,333,317,531,515,94,99,728,97,334,802,532,98,95,100,267,141,270,385,446,605,38,39,669,299,429,300,627,476,61,40,772,383,422,824,713,123,341,124,686,319,313,320,846,806,342,125,268,142,271,386,451,564,149,238,868,828,430,301,674,41,326,42,442,603,691,57,620,472,539,58,708,517,736,102,511,518,540,59,444,560,275,146,447,606,677,260,670,652,872,63,628,477,524,64,664,143,780,278,450,762,850,107,667,457,694,348,716,546,741,108,137,144,276,147,452,565,150,152,672,282,785,284,455,460,680,21]
def orders : Array (List Id) := #[[0,1,2,3,4,5,6,7],[1,0,3,2,5,4,7,6],[2,3,0,1,6,7,4,5],[0,2,1,3,4,6,5,7],[3,2,1,0,7,6,5,4],[1,3,0,2,5,7,4,6],[4,5,6,7,0,1,2,3],[0,4,1,5,2,6,3,7],[0,1,4,5,2,3,6,7],[0,2,4,6,1,3,5,7],[1,0,5,4,3,2,7,6],[2,0,6,4,3,1,7,5],[5,4,7,6,1,0,3,2],[1,5,0,4,3,7,2,6],[1,3,5,7,0,2,4,6],[3,1,7,5,2,0,6,4],[4,5,0,1,6,7,2,3],[5,4,1,0,7,6,3,2],[4,6,0,2,5,7,1,3],[5,7,1,3,4,6,0,2],[6,7,4,5,2,3,0,1],[2,6,3,7,0,4,1,5],[2,0,3,1,6,4,7,5],[2,3,6,7,0,1,4,5],[3,2,7,6,1,0,5,4],[4,6,5,7,0,2,1,3],[4,0,5,1,6,2,7,3],[6,4,2,0,7,5,3,1],[6,7,2,3,4,5,0,1],[6,2,7,3,4,0,5,1],[7,6,5,4,3,2,1,0],[7,5,3,1,6,4,2,0],[7,6,3,2,5,4,1,0],[3,7,2,6,1,5,0,4],[6,4,7,5,2,0,3,1],[5,7,4,6,1,3,0,2],[3,1,2,0,7,5,6,4],[5,1,4,0,7,3,6,2],[7,3,6,2,5,1,4,0],[7,5,6,4,3,1,2,0]]

abbrev Row := Fin 22
def lookup (r : Row) (y : Nat) : Nat := (((bank[r.val]?.getD 0) >>> (5*y)) % 32)
def defaultOrder : List Id := [0,1,2,3,4,5,6,7]
def descriptor (x : Finset Id) := descriptors[pack defaultOrder x]?.getD 0
def rowId (x : Finset Id) : Row := Fin.ofNat 22 (descriptor x % 22)
def order (x : Finset Id) : List Id := orders[(descriptor x / 22)]?.getD defaultOrder
def value (x y : Finset Id) := lookup (rowId x) (pack (order x) y)
theorem order_len : ∀x : Finset Id, (order x).length=8 := by decide +kernel

def good (r : Row) := (parts 8).all fun p =>
  decide (lookup r (p.1+p.2) ≤ lookup r p.1 + lookup r p.2)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good0 : good 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good1 : good 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good2 : good 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good3 : good 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good4 : good 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good5 : good 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good6 : good 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good7 : good 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good8 : good 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good9 : good 9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good10 : good 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good11 : good 11 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good12 : good 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good13 : good 13 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good14 : good 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good15 : good 15 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good16 : good 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good17 : good 17 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good18 : good 18 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good19 : good 19 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good20 : good 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem good21 : good 21 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem each_good : ∀r : Row, good r = true := by
  intro r
  fin_cases r
  · exact good0
  · exact good1
  · exact good2
  · exact good3
  · exact good4
  · exact good5
  · exact good6
  · exact good7
  · exact good8
  · exact good9
  · exact good10
  · exact good11
  · exact good12
  · exact good13
  · exact good14
  · exact good15
  · exact good16
  · exact good17
  · exact good18
  · exact good19
  · exact good20
  · exact good21

theorem splitY (x y z : Finset Id) (d : Disjoint y z) : value x (y∪z) ≤ value x y + value x z := by
  have hp := pack_parts (order x) y z d
  rw [order_len] at hp
  have h := List.all_eq_true.mp (each_good (rowId x)) (pack (order x) y,pack (order x) z) hp
  change lookup (rowId x) (pack (order x) (y∪z)) ≤ _
  rw [pack_add _ _ _ d]
  exact of_decide_eq_true h

def datum (i : Id) : View Id := ⟨{i},{i}⟩
def selector (j : Fin 3) (bit : Bool) : View Id :=
  ⟨Finset.univ.filter (fun i => i.val.testBit j.val=bit),
    Finset.univ.filter (fun i => i.val.testBit j.val≠bit)⟩
def primary (v : View Id) : Prop := (∃i,v=datum i) ∨ ∃j b,v=selector j b
def cheap (v : View Id) : Prop := ∀ x∈v.pos.powerset, ∀ y∈v.neg.powerset, value x y ≤ 1
instance (v : View Id) : Decidable (cheap v) := by unfold cheap; infer_instance
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem cheap_datum : ∀ i : Id, cheap (datum i) := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem cheap_selector : ∀ j : Fin 3, ∀b : Bool, cheap (selector j b) := by decide +kernel
def repr (x : Finset Id) : Fin 256 := Fin.ofNat 256 (pack defaultOrder x)
def decode (i : Fin 256) := Finset.univ.filter fun j : Id => i.val.testBit j.val
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem decode_repr : ∀ x : Finset Id, decode (repr x)=x := by decide +kernel
def symBlock (k : Nat) : Prop := ∀ i : Fin 16, ∀j : Fin 256,
    let v := decode (Fin.ofNat 256 (16*k+i.val)); let w := decode j
    value v w = value w v
instance (k : Nat) : Decidable (symBlock k) := by unfold symBlock; infer_instance
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym0 : symBlock 0 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym1 : symBlock 1 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym2 : symBlock 2 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym3 : symBlock 3 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym4 : symBlock 4 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym5 : symBlock 5 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym6 : symBlock 6 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym7 : symBlock 7 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym8 : symBlock 8 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym9 : symBlock 9 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym10 : symBlock 10 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym11 : symBlock 11 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym12 : symBlock 12 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym13 : symBlock 13 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym14 : symBlock 14 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sym15 : symBlock 15 := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem all_sym : ∀ k : Fin 16, symBlock k.val := by
  intro k
  fin_cases k
  · exact sym0
  · exact sym1
  · exact sym2
  · exact sym3
  · exact sym4
  · exact sym5
  · exact sym6
  · exact sym7
  · exact sym8
  · exact sym9
  · exact sym10
  · exact sym11
  · exact sym12
  · exact sym13
  · exact sym14
  · exact sym15

theorem symm (x y : Finset Id) : value x y = value y x := by
  let i := repr x
  let k : Fin 16 := ⟨i.val / 16, by have := i.isLt; omega⟩
  let t := Fin.ofNat 16 (i.val % 16)
  have ident : Fin.ofNat 256 (16*k.val+t.val)=i := by
    apply Fin.ext
    change (16*(i.val/16)+(i.val%16)%16)%256 = i.val
    have := i.isLt
    omega
  have h := all_sym k t (repr y)
  dsimp only at h
  rw [ident] at h
  change value (decode (repr x)) (decode (repr y)) = value (decode (repr y)) (decode (repr x)) at h
  simpa only [decode_repr] using h
def price : Price Id primary where
  value := value
  leaf := by
    rintro v (⟨i,rfl⟩|⟨j,b,rfl⟩) x hx y hy
    · exact cheap_datum i x (Finset.mem_powerset.mpr hx) y (Finset.mem_powerset.mpr hy)
    · exact cheap_selector j b x (Finset.mem_powerset.mpr hx) y (Finset.mem_powerset.mpr hy)
  splitY := splitY
  splitX := by
    intro x z y h
    rw [symm (x∪z) y,symm x y,symm z y]
    exact splitY y x z h
theorem whole (f : Rectangles.Tree Id) (fit : allowed primary f)
    (pos : (evaluate f).pos=Finset.univ) (neg : (evaluate f).neg=Finset.univ) :
    22≤leaves f := by
  have h := price_sound price f fit (evaluate f).pos Finset.Subset.rfl (evaluate f).neg Finset.Subset.rfl
  rw [pos,neg] at h
  have root : price.value Finset.univ Finset.univ=22 := by decide +kernel
  rwa [root] at h
end PEqualNP.Outside.L_meta_9939.Cube

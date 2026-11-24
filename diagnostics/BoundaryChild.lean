import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.Boundary2706

/- Wire monotonicity follows the proofs in L-meta-1572 and L-meta-1353. -/
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp

/- Wire substitution follows L-meta-4671. -/
def wire {n m : ℕ} (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

lemma wire_lt {n m i s : ℕ} (f : Fin n → Fin m) (hi : i < n + s) :
    wire f i < m + s := by
  unfold wire
  split
  · exact lt_of_lt_of_le (f _).isLt (Nat.le_add_right _ _)
  · omega

def renameGate {n m : ℕ} (f : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire f)⟩

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma read_wire {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (tail : List Bool) (i : ℕ) :
    (List.ofFn x ++ tail).getD (wire f i) false =
      (List.ofFn (x ∘ f) ++ tail).getD i false := by
  by_cases h : i < n
  · rw [wire, dite_eq_left h,
        List.getD_append _ _ _ _ (by simp),
        List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, Function.comp_def]
  · rw [wire, dite_eq_right h,
        List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt h)]
    simp

lemma fold_read {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (gs : List Gate) (tail : List Bool) (i : ℕ) :
    ((gs.map (renameGate f)).foldl step (List.ofFn x ++ tail)).getD (wire f i) false =
      (gs.foldl step (List.ofFn (x ∘ f) ++ tail)).getD i false := by
  induction gs generalizing tail with
  | nil => exact read_wire f x tail i
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun j => (List.ofFn (x ∘ f) ++ tail).getD j false)
    have value : (renameGate f g).op.eval ((renameGate f g).inputs.map
        fun j => (List.ofFn x ++ tail).getD j false) = b := by
      simp only [renameGate, List.map_map, b]
      congr 1
      exact List.map_congr_left (fun j _ => read_wire f x tail j)
    simp only [List.map_cons, List.foldl_cons, step, value, List.append_assoc]
    exact ih (tail ++ [b])


set_option maxRecDepth 12000
set_option maxHeartbeats 0

def edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def pairs : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
def flags : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
def holes : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
def reps : List ℕ := [257, 514, 4100]

def row (m : ℕ) (v : Fin 14) : Bool := m.testBit v.val

def edge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

def edgeB (x : Fin 14 → Bool) : Bool :=
  pairs.any fun e => x e.1 && x e.2

theorem endpoints : ∀ u v : Fin 14, (u.val, v.val) ∈ edges ↔ (u,v) ∈ pairs := by
  decide +kernel

theorem edge_iff (x : Fin 14 → Bool) : edge x ↔ edgeB x = true := by
  simp only [edge, edgeB, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u, v), (endpoints u v).mp he, hu, hv⟩
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    exact ⟨u, v, (endpoints u v).mpr he, hu, hv⟩

def em (i : Fin 21) : ℕ := (#[129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : Array ℕ).getD i.val 0

theorem identify : ∀ u v : Fin 14, (u.val, v.val) ∈ edges →
    ∃ i : Fin 21, ∀ t : Fin 14, row (em i) t = true ↔ t = u ∨ t = v := by
  decide +kernel

theorem em_pos : ∀ i : Fin 21, edgeB (row (em i)) = true := by decide +kernel

def codes : Array ℕ := #[62129658859368976, 28502781892209031, 44113344757904656, 19739888947399591, 28236708652362631, 10224775401876871, 57872487274582576, 61863585619522576, 56814765646943536, 61285436010815776, 27658559043655831, 19458470543477431, 44394738918768976, 57309670649717536, 27673884024752311, 57377566031496016, 23682793682557591, 10787583906584791, 61809915973428256, 28183039006268311, 18665726970351031, 57904236474876496, 56778619465458976, 28464437227211191, 43865878104720976, 23151742498299031, 19791360102669271, 39610651371778561, 5983774404618616, 48622094084486401, 15240416800312186, 14726953397169016, 5724272496061816, 39859136720409091, 48353830364328961, 47810667325166851, 48304283870127106, 14677406902967161, 5161125742759291, 39891916679430661, 47777613536847106, 5950583650240891, 39367436716361221, 14150736569687161, 15289826321144701, 34265925617410306, 639048650250361, 1449243258178171, 35391671472701701, 34794786431001346, 655404390074491, 34860620178342661, 1167909463841401, 1781424067352701, 39047814681346081, 5420937714186136, 47496460952166481, 13833369324148666, 13882710483048376, 5442858152216536, 39014897748955171, 47509587450208321, 47529240918499411, 47178638792396866, 13551761825236921, 4598309235304411, 38203471099736101, 47214784966570066, 4543540351567771, 38241815764275301, 13587907999410121, 13601376681371581, 34547311775531026, 920434808371081, 323614185936811, 33984644179517461, 34513364084412466, 373986103564171, 34016393387122741, 886487117252521, 937201218799501, 56481626508821041, 22854749541661096, 57013772988056881, 27889267288669066, 18878984180562856, 18355599512927656, 60987283442237971, 52505861147722801, 43500925339698451, 52491361589593186, 18864484622433241, 9295633061543371, 60932446071358021, 43485395022841186, 22804035322673611, 51928669867935301, 9858518055681241, 27868582944209821, 42692651450171746, 9065774483011801, 22542343043906251, 60671848977924421, 51700808497234786, 9029559822153931, 51661501443212101, 18073931530074841, 27079125037185181, 39309507069756961, 5682630102597016, 48281538008212561, 14091776046914746, 14936051259251896, 5964052449184216, 38746634138441251, 48562928226411841, 48844274083570771, 47702023459575106, 14075146492415161, 5914437475609051, 39260097431483941, 48264839967028306, 5070210684390811, 39822922059092581, 14637962999868361, 14919695401987261, 34806813683630866, 1179936716470921, 584211279370411, 34774102086542101, 34244005178921266, 1428422065101451, 35336902588506421, 617128211761321, 1461681181411981, 43549992669299986, 9923115702140041, 22837983006480811, 61003639174750741, 52522011544933426, 9379952662977931, 52031612178933301, 18895134577773481, 27955101028699021, 57059747924493601, 23432870957333656, 56496951482606161, 27338486029277626, 18384050984754616, 18946879555029976, 61528171501147171, 52010927951914561, 43021329187808851, 51677788813792066, 18050911846632121, 9098554442033371, 60722220888240421, 42705777940902226, 22556568780049051, 51750218018067301, 9078900973742281, 27110874237479101, 57325821054239521, 23698944087079576, 57295171091587921, 27607844824668346, 19441772502293176, 19481216404933336, 61268669482946851, 53068649469453121, 44345123945193811, 43818256279356946, 10191379312197001, 23105151431204011, 61797477932753941, 52263604821710386, 10436578995182731, 53349930900005941, 18636727854550441, 28486152212957581, 52209935182927426, 18583058215767481, 10421254013627611, 61776656739677221, 43766785123628626, 23085429483539611, 53335705163863141, 10139908156468681, 28431383328762301]
def picks : Array ℕ := #[0, 0, 8, 4, 1, 9, 5, 2, 26, 12, 25, 33, 17, 30, 22, 6, 13, 10, 21, 18, 14, 36, 0, 48, 41, 38, 54, 40, 37, 49, 69, 46, 58, 57, 66, 62, 50, 45, 42, 44, 61, 53, 72, 84, 0, 77, 74, 90, 93, 102, 86, 105, 94, 82, 76, 73, 97, 85, 80, 89, 81, 98, 78, 112, 117, 109, 0, 116, 108, 134, 110, 113, 120, 133, 141, 126, 122, 129, 121, 114, 118, 130, 125, 138, 149, 162, 146, 144, 0, 156, 158, 174, 165, 177, 166, 154, 170, 150, 153, 152, 157, 161, 169, 148, 145, 185, 198, 182, 180, 192, 0, 193, 181, 184, 213, 190, 202, 205, 197, 188, 189, 194, 186, 206, 201, 210, 225, 220, 217, 242, 218, 221, 0, 224, 216, 238, 246, 233, 234, 230, 237, 226, 222, 229, 228, 249, 241, 270, 257, 254, 266, 282, 273, 252, 0, 264, 277, 253, 256, 278, 258, 261, 269, 265, 260, 285, 262, 274, 306, 293, 290, 301, 289, 292, 288, 300, 0, 314, 318, 309, 313, 305, 296, 294, 302, 297, 321, 310, 298, 328, 333, 325, 336, 349, 357, 350, 329, 326, 0, 332, 324, 330, 337, 334, 338, 342, 345, 346, 354, 341, 365, 378, 362, 393, 382, 370, 374, 381, 390, 360, 0, 372, 373, 368, 377, 366, 386, 369, 385, 361, 364, 401, 414, 398, 429, 406, 418, 409, 400, 397, 396, 408, 0, 410, 405, 402, 413, 421, 404, 422, 426, 417, 441, 433, 436, 458, 434, 437, 450, 446, 453, 454, 449, 462, 0, 440, 432, 465, 444, 457, 438, 442, 445, 486, 470, 473, 482, 498, 489, 494, 474, 477, 493, 472, 469, 468, 0, 480, 478, 501, 490, 481, 485, 476, 522, 506, 509, 517, 505, 508, 529, 521, 512, 530, 525, 534, 504, 516, 0, 526, 537, 514, 518, 510, 513, 558, 542, 545, 553, 544, 541, 554, 549, 546, 566, 570, 561, 573, 550, 562, 0, 540, 552, 565, 548, 557, 585, 577, 580, 602, 581, 578, 582, 589, 586, 598, 606, 593, 588, 601, 609, 576, 0, 584, 594, 597, 590, 630, 614, 617, 626, 633, 642, 625, 620, 629, 637, 613, 616, 645, 634, 622, 624, 612, 0, 638, 621, 618, 657, 652, 649, 674, 653, 650, 660, 673, 681, 670, 665, 678, 654, 661, 658, 669, 666, 662, 0, 648, 656, 702, 689, 686, 697, 688, 685, 717, 694, 706, 710, 705, 714, 698, 693, 690, 692, 709, 701, 684, 0, 696, 738, 725, 722, 734, 741, 750, 753, 742, 730, 745, 724, 721, 733, 728, 737, 729, 746, 726, 720, 732, 0]
def name (k : Fin 189) (v : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (((codes.getD k.val 0) >>> (4 * v.val)) &&& 15)
def pick (i j : Fin 21) : ℕ := picks.getD (i.val * 21 + j.val) 0
def code (i j : Fin 21) : Fin 189 := Fin.ofNat 189 (pick i j / 4)
def second (i j : Fin 21) : ℕ := reps.getD (pick i j % 4) 0

theorem alignment : ∀ i j : Fin 21, i ≠ j →
    second i j ∈ reps ∧
    (∀ t : Fin 14, row 129 (name (code i j) t) = row (em i) t) ∧
    (∀ t : Fin 14, row (second i j) (name (code i j) t) = row (em j) t) := by
  decide +kernel

def good (k : Fin 189) : Bool :=
  (flags.all fun m => edgeB (row m ∘ name k)) &&
    (holes.all fun m => !(edgeB (row m ∘ name k)))

theorem table : ∀ k : Fin 189, good k = true := by decide +kernel

theorem transport (k : Fin 189) :
    (∀ m ∈ flags, edge (row m ∘ name k)) ∧
    (∀ m ∈ holes, ¬edge (row m ∘ name k)) := by
  have h := table k
  simp only [good, Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · exact fun m hm => (edge_iff _).mpr (h.1 m hm)
  · intro m hm he
    have hp := (edge_iff _).mp he
    have hn := h.2 m hm
    simp [hp] at hn

lemma exclusive (C : Circuit) (hAO : AO C) (s t : ℕ)
    (hcov : ∀ x, edge x → value C x s = true ∨ value C x t = true)
    (hex : ∃ x, edge x ∧ value C x s = true ∧ value C x t = false) :
    ∃ i : Fin 21, value C (row (em i)) s = true ∧ value C (row (em i)) t = false := by
  obtain ⟨x, ⟨u, v, he, hu, hv⟩, _, hfalse⟩ := hex
  obtain ⟨i, hi⟩ := identify u v he
  have hle (z : Fin 14) (hz : row (em i) z = true) : x z = true := by
    rcases (hi z).mp hz with rfl | rfl
    · exact hu
    · exact hv
  have ht : value C (row (em i)) t = false := by
    cases h : value C (row (em i)) t with
    | false => rfl
    | true =>
      have hcontr := wires_mono C hAO _ _ hle t h
      rw [hfalse] at hcontr
      contradiction
  obtain hs | hs := hcov (row (em i)) ((edge_iff _).mpr (em_pos i))
  · exact ⟨i, hs, ht⟩
  · rw [ht] at hs
    contradiction

theorem boundary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = x1.size ∧
      a < 14 + D.size ∧ b < 14 + D.size ∧
      let read : ℕ → ℕ → Bool := fun k m => (D.wires (List.ofFn (fun z : Fin 14 => m.testBit z.val))).getD k false
      (∀ m ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ), read a m = true ∨ read b m = true) ∧
      (∀ m ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ), read a m = false ∧ read b m = false) ∧
      read a 129 = true ∧ read b 129 = false ∧
      (∃ m ∈ ([257, 514, 4100] : List ℕ), read b m = true ∧ read a m = false) := by

  intro C u v hmono hu hv
  dsimp only
  intro hpos hneg hl hr
  have hAO : AO C := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmono g hg
  obtain ⟨i, hia, hib⟩ := exclusive C hAO u v hpos hl
  obtain ⟨j, hjb, hja⟩ := exclusive C hAO v u (fun x hx => (hpos x hx).symm) hr
  have hd : i ≠ j := by
    rintro rfl
    rw [hia] at hja
    contradiction
  let f := name (code i j)
  let D : Circuit := ⟨C.gates.map (renameGate f), wire f C.output⟩
  have hsize : D.size = C.size := by simp [D, Circuit.size]
  have dm : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp (show g ∈ C.gates.map (renameGate f) from hg)
    simpa [renameGate] using hmono g' hg'
  have reads (m k : ℕ) : value D (row m) (wire f k) = value C (row m ∘ f) k := by
    simpa only [value, D, Circuit.wires, List.append_nil] using fold_read f (row m) C.gates [] k
  obtain ⟨hm, hi, hj⟩ := alignment i j hd
  have ei : row 129 ∘ f = row (em i) := funext hi
  have ej : row (second i j) ∘ f = row (em j) := funext hj
  obtain ⟨hp, hn⟩ := transport (code i j)
  refine ⟨D, wire f u, wire f v, dm, hsize, ?_, ?_, ?_, ?_, ?_, ?_, second i j, hm, ?_, ?_⟩
  · rw [hsize]
    exact wire_lt f hu
  · rw [hsize]
    exact wire_lt f hv
  · intro m hmem
    change value D (row m) (wire f u) = true ∨ value D (row m) (wire f v) = true
    rw [reads, reads]
    exact hpos _ (hp m hmem)
  · intro m hmem
    change value D (row m) (wire f u) = false ∧ value D (row m) (wire f v) = false
    rw [reads, reads]
    exact hneg _ (hn m hmem)
  · change value D (row 129) (wire f u) = true
    rwa [reads, ei]
  · change value D (row 129) (wire f v) = false
    rwa [reads, ei]
  · change value D (row (second i j)) (wire f v) = true
    rwa [reads, ej]
  · change value D (row (second i j)) (wire f u) = false
    rwa [reads, ej]

end PEqualNP.Outside.Boundary2706

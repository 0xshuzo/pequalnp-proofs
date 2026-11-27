import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.Guarded
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp

def separates {k : Nat} (X Y : Fin k→List Bool) (T : Finset Nat) :=
  ∀ i,∃ t∈T,(X i).getD t false≠(Y i).getD t false

def useful (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge : GateOp → Nat
  | .not => 0
  | _ => 1

def mass (gs : List Gate) := (gs.map fun g => charge g.op).sum
def inverters (gs : List Gate) := (gs.map fun g => 1-charge g.op).sum

theorem mass_split (gs : List Gate) : mass gs + inverters gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have cap : charge g.op≤1 := by cases g.op <;> simp [charge]
    change charge g.op+mass gs+(1-charge g.op+inverters gs)=gs.length+1
    omega

theorem mass_snoc (gs : List Gate) (g : Gate) : mass (gs++[g])=mass gs+charge g.op := by
  simp [mass,List.sum_append]

theorem use_sound (g : Gate) (v : Nat→Bool) :
    g.op.eval (g.inputs.map v)=g.op.eval ((useful g).map v) := by
  rcases g with ⟨op,args⟩
  cases op <;> cases args <;> rfl

theorem use_count (g : Gate) (h : g.inputs.length≤2) : (useful g).length ≤ charge g.op+1 := by
  rcases g with ⟨op,args⟩
  cases op <;> simp_all [useful,charge]

theorem trace (k m : Nat) (X Y : Fin k→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (S : Finset Nat) (sep : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+mass gs := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,sep,by simp [mass]⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : Fin k) (w : Nat) (ne : w≠last) :
        (run (gs++[g]) (X i)).getD w false ≠ (run (gs++[g]) (Y i)).getD w false →
          (V i).getD w false ≠ (W i).getD w false := by
      rw [run_snoc,run_snoc]
      change (V i++[_]).getD w false≠(W i++[_]).getD w false → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have old : ∀ a∈gs,a.inputs.length≤2 := fun a ha => fan a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ (useful g).toFinset
      have rsep : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := sep i
        by_cases eq : w=last
        · subst w
          by_contra! blocked
          have same : (useful g).map (fun t => (V i).getD t false)=(useful g).map (fun t => (W i).getD t false) := by
            apply List.map_congr_left
            intro t ht
            exact blocked t (Finset.mem_union_right _ (List.mem_toFinset.mpr ht))
          change (run (gs++[g]) (X i)).getD last false≠(run (gs++[g]) (Y i)).getD last false at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false≠(W i++[g.op.eval _]).getD last false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          exact diff ((use_sound g _).trans ((congrArg g.op.eval same).trans (use_sound g _).symm))
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,st,card⟩ := ih old R rsep
      have maxfan := fan g (by simp)
      have usable := use_count g maxfan
      have len := List.toFinset_card_le (useful g)
      have union : R.card≤(S.erase last).card+(useful g).toFinset.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_add_one mem
      exact ⟨T,st,by rw [mass_snoc]; omega⟩
    · have oldSep : separates V W S := by
        intro i
        obtain ⟨w,ws,h⟩ := sep i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) h⟩
      obtain ⟨T,st,card⟩ := ih old S oldSep
      exact ⟨T,st,by rw [mass_snoc]; omega⟩

theorem manyPrice {k m t : Nat} (X Y : Fin k → List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (single : ∀ (w : Nat) (i j : Fin k),(X i).getD w false≠(Y i).getD w false →
      (X j).getD w false≠(Y j).getD w false → i=j)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2) (port : Fin t → Nat)
    (detect : ∀ i, ∃ j,(run gs (X i)).getD (port j) false≠(run gs (Y i)).getD (port j) false) :
    k≤gs.length+t := by
  classical
  let S := Finset.univ.image port
  obtain ⟨T,sep,bound⟩ := trace k m X Y lens gs fan S (by
    intro i
    obtain ⟨j,hit⟩ := detect i
    exact ⟨port j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hit⟩)
  let f := fun i => Classical.choose (sep i)
  have ok (i) := Classical.choose_spec (sep i)
  have cap : (Finset.univ : Finset (Fin k)).card≤T.card :=
    Finset.card_le_card_of_injOn f (fun i _ => (ok i).1) (fun i _ j _ eq =>
      single (f j) i j (eq ▸ (ok i).2) (ok j).2)
  have small := Finset.card_image_le (s:=Finset.univ) (f:=port)
  change T.card≤(Finset.univ.image port).card+mass gs at bound
  simp only [Finset.card_univ,Fintype.card_fin] at cap small
  have eq := mass_split gs
  omega


def balanced : List Gate := [⟨GateOp.or, [20, 34]⟩,
⟨GateOp.or, [21, 40]⟩,
⟨GateOp.or, [20, 27]⟩,
⟨GateOp.or, [31, 35]⟩,
⟨GateOp.or, [22, 37]⟩,
⟨GateOp.or, [24, 38]⟩,
⟨GateOp.or, [25, 34]⟩,
⟨GateOp.or, [26, 33]⟩,
⟨GateOp.or, [27, 29]⟩,
⟨GateOp.or, [28, 37]⟩,
⟨GateOp.or, [29, 46]⟩,
⟨GateOp.or, [23, 31]⟩,
⟨GateOp.or, [22, 36]⟩,
⟨GateOp.or, [24, 29]⟩,
⟨GateOp.or, [24, 35]⟩,
⟨GateOp.or, [28, 36]⟩,
⟨GateOp.or, [50, 55]⟩,
⟨GateOp.or, [23, 33]⟩,
⟨GateOp.or, [22, 25]⟩,
⟨GateOp.or, [23, 38]⟩,
⟨GateOp.or, [25, 42]⟩,
⟨GateOp.or, [36, 57]⟩,
⟨GateOp.or, [21, 22]⟩,
⟨GateOp.or, [26, 35]⟩,
⟨GateOp.or, [37, 63]⟩,
⟨GateOp.or, [21, 26]⟩,
⟨GateOp.or, [38, 65]⟩,
⟨GateOp.or, [39, 62]⟩,
⟨GateOp.or, [28, 66]⟩,
⟨GateOp.or, [21, 61]⟩,
⟨GateOp.or, [26, 34]⟩,
⟨GateOp.or, [37, 60]⟩,
⟨GateOp.or, [41, 43]⟩,
⟨GateOp.or, [34, 45]⟩,
⟨GateOp.or, [27, 28]⟩,
⟨GateOp.or, [32, 52]⟩,
⟨GateOp.and, [0, 71]⟩,
⟨GateOp.or, [21, 32]⟩,
⟨GateOp.or, [27, 70]⟩,
⟨GateOp.or, [27, 38]⟩,
⟨GateOp.or, [54, 74]⟩,
⟨GateOp.or, [37, 69]⟩,
⟨GateOp.or, [23, 32]⟩,
⟨GateOp.or, [39, 59]⟩,
⟨GateOp.or, [29, 33]⟩,
⟨GateOp.or, [25, 35]⟩,
⟨GateOp.or, [44, 73]⟩,
⟨GateOp.or, [36, 79]⟩,
⟨GateOp.or, [34, 39]⟩,
⟨GateOp.or, [31, 39]⟩,
⟨GateOp.or, [22, 28]⟩,
⟨GateOp.and, [17, 81]⟩,
⟨GateOp.or, [78, 82]⟩,
⟨GateOp.and, [15, 72]⟩,
⟨GateOp.or, [48, 67]⟩,
⟨GateOp.or, [29, 30]⟩,
⟨GateOp.or, [33, 80]⟩,
⟨GateOp.or, [20, 90]⟩,
⟨GateOp.and, [2, 94]⟩,
⟨GateOp.or, [64, 95]⟩,
⟨GateOp.or, [47, 58]⟩,
⟨GateOp.or, [23, 97]⟩,
⟨GateOp.and, [10, 99]⟩,
⟨GateOp.or, [32, 89]⟩,
⟨GateOp.or, [33, 88]⟩,
⟨GateOp.and, [7, 92]⟩,
⟨GateOp.or, [32, 84]⟩,
⟨GateOp.or, [30, 101]⟩,
⟨GateOp.and, [3, 107]⟩,
⟨GateOp.or, [93, 108]⟩,
⟨GateOp.or, [49, 103]⟩,
⟨GateOp.and, [9, 56]⟩,
⟨GateOp.or, [83, 85]⟩,
⟨GateOp.and, [19, 112]⟩,
⟨GateOp.or, [31, 100]⟩,
⟨GateOp.or, [51, 53]⟩,
⟨GateOp.and, [1, 68]⟩,
⟨GateOp.or, [91, 113]⟩,
⟨GateOp.or, [20, 106]⟩,
⟨GateOp.and, [8, 96]⟩,
⟨GateOp.and, [4, 115]⟩,
⟨GateOp.and, [18, 86]⟩,
⟨GateOp.and, [6, 114]⟩,
⟨GateOp.or, [102, 116]⟩,
⟨GateOp.or, [38, 118]⟩,
⟨GateOp.and, [13, 124]⟩,
⟨GateOp.or, [24, 30]⟩,
⟨GateOp.or, [119, 120]⟩,
⟨GateOp.and, [12, 110]⟩,
⟨GateOp.or, [121, 128]⟩,
⟨GateOp.or, [109, 123]⟩,
⟨GateOp.or, [30, 104]⟩,
⟨GateOp.or, [35, 75]⟩,
⟨GateOp.and, [16, 132]⟩,
⟨GateOp.and, [14, 131]⟩,
⟨GateOp.or, [30, 87]⟩,
⟨GateOp.or, [77, 126]⟩,
⟨GateOp.or, [76, 98]⟩,
⟨GateOp.or, [25, 136]⟩,
⟨GateOp.or, [125, 130]⟩,
⟨GateOp.or, [122, 139]⟩,
⟨GateOp.or, [31, 135]⟩,
⟨GateOp.and, [11, 141]⟩,
⟨GateOp.and, [5, 138]⟩,
⟨GateOp.or, [133, 142]⟩,
⟨GateOp.or, [111, 143]⟩,
⟨GateOp.or, [137, 144]⟩,
⟨GateOp.or, [117, 146]⟩,
⟨GateOp.or, [105, 145]⟩,
⟨GateOp.or, [127, 147]⟩,
⟨GateOp.or, [140, 148]⟩,
⟨GateOp.or, [129, 150]⟩,
⟨GateOp.or, [149, 151]⟩,
⟨GateOp.or, [134, 152]⟩]
def oldPins : List Nat := [0, 14, 3, 7, 1, 5, 19, 20, 15, 9, 12, 13, 18, 8, 16, 11, 4, 10, 17, 6, 28, 31, 24, 27, 22, 26, 40, 41, 35, 29, 33, 39, 25, 36, 37, 32, 30, 38, 34, 23]
def tags : List Nat := [9, 5, 12, 12, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 7, 12, 8, 12, 12, 12, 0, 12, 12, 12, 1, 12, 2, 12, 12, 12, 12, 12, 12, 12, 12, 12, 3, 12, 12, 4, 0, 0, 0, 12, 12, 1, 12, 2, 12, 12, 12, 12, 3, 1, 1, 3, 3, 12, 12, 12, 0, 3, 12, 2, 2, 2, 2, 4, 2, 3, 2, 0, 0, 1, 12, 3, 9, 12, 2, 12, 1, 3, 12, 4, 12, 12, 1, 3, 4, 4, 12, 12, 2, 12, 4, 12, 1, 0, 12, 2, 2, 0, 12, 4, 4, 12, 12, 0, 12, 12, 4, 12, 4, 12, 2, 1, 12, 12, 0, 12, 12, 12, 12, 12, 0, 12, 1, 12, 12, 12, 12, 4, 3, 12, 12, 3, 1, 9, 1, 12, 12, 3, 12, 12, 12, 12, 9, 9, 12, 9, 12, 12, 9, 9, 10, 11]
def probesX : List Nat := [268435460, 4194308, 1099511627780, 1073741828, 8388612, 2113536, 2097154, 2162688, 2097168, 268435457, 268435460, 2113536]
def probesY : List Nat := [4, 4, 4, 4, 4, 2097152, 2097152, 2097152, 2097152, 268435456, 268435456, 16384]
def bankOn (x : Nat) : List Bool := run balanced (oldPins.map x.testBit) ++ [x.testBit 2, x.testBit 21]
def actual (x : Nat) : Bool := ([(0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (Nat × Nat)).any (fun e => x.testBit e.1 && x.testBit e.2)

def px (i : Fin 12) := probesX.getD i.val 0
def py (i : Fin 12) := probesY.getD i.val 0
def sepCheck (i : Nat) : Bool :=
  let x := bankOn (probesX.getD i 0)
  let y := bankOn (probesY.getD i 0)
  x.length == 156 && y.length == 156 &&
    (List.range 156).all (fun w => x.getD w false == y.getD w false || tags.getD w 12 == i)

theorem checkBank : (List.range 12).all sepCheck = true := by decide +kernel

theorem correctProbes : ∀ i : Fin 12, actual (px i) ≠ actual (py i) := by decide +kernel

theorem suffixBound (gs : List Gate) (out : Nat) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (correct : ∀ x : Nat, (run gs (bankOn x)).getD out false = actual x) : 11 ≤ gs.length := by
  let X := fun i : Fin 12 => bankOn (px i)
  let Y := fun i : Fin 12 => bankOn (py i)
  have checks (i : Fin 12) := List.all_eq_true.mp checkBank i.val (List.mem_range.mpr i.isLt)
  have data (i : Fin 12) : (X i).length = 156 ∧ (Y i).length = 156 ∧
      ∀ w < 156, (X i).getD w false = (Y i).getD w false ∨ tags.getD w 12 = i.val := by
    have ok := checks i
    simp only [sepCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      List.mem_range] at ok
    exact ⟨ok.1.1,ok.1.2,ok.2⟩
  have detect (i : Fin 12) : ∃ j : Fin 1, (run gs (X i)).getD ((fun _ : Fin 1 => out) j) false ≠
      (run gs (Y i)).getD ((fun _ : Fin 1 => out) j) false := by
    refine ⟨0,?_⟩
    change (run gs (bankOn (px i))).getD out false ≠ (run gs (bankOn (py i))).getD out false
    rw [correct,correct]
    exact correctProbes i
  have single (w : Nat) (i j : Fin 12)
      (di : (X i).getD w false ≠ (Y i).getD w false)
      (dj : (X j).getD w false ≠ (Y j).getD w false) : i = j := by
    by_cases hw : w < 156
    · apply Fin.ext
      exact (((data i).2.2 w hw).resolve_left di).symm.trans (((data j).2.2 w hw).resolve_left dj)
    · have xl := (data i).1
      have yl := (data i).2.1
      rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)] at di
      contradiction
  have total := manyPrice X Y (fun i => ⟨(data i).1,(data i).2.1⟩) single gs fan (fun _ : Fin 1 => out) detect
  omega

end PEqualNP.Outside.L_meta_9743.Guarded

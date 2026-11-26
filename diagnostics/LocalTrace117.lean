import PEqualNP.Defs
namespace Prefix96
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

theorem price {k m : Nat} (X Y : Fin k→List Bool) (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (unique : ∀ (w : Nat) (i j : Fin k),(X i).getD w false≠(Y i).getD w false →
       (X j).getD w false≠(Y j).getD w false → i=j)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (root : Nat) (correct : ∀ i,(run gs (X i)).getD root false≠(run gs (Y i)).getD root false) :
    k≤mass gs+1 := by
  classical
  obtain ⟨T,sep,bound⟩ := trace k m X Y lens gs fan {root}
    (fun i=>⟨root,Finset.mem_singleton_self _,correct i⟩)
  let f := fun i => Classical.choose (sep i)
  have ok (i) := Classical.choose_spec (sep i)
  have cap : (Finset.univ : Finset (Fin k)).card≤T.card :=
    Finset.card_le_card_of_injOn f (fun i _ => (ok i).1) (fun i _ j _ eq =>
      unique (f j) i j (eq ▸ (ok i).2) (ok j).2)
  simp only [Finset.card_univ,Fintype.card_fin] at cap
  simp only [Finset.card_singleton] at bound
  omega
def target (x : Fin 40 → Bool) : Bool := (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)
abbrev R := Fin 22
def pre : List Gate := [⟨.not,[27]⟩,⟨.or,[4,18]⟩,⟨.or,[9,18]⟩,⟨.and,[8,40]⟩,⟨.or,[9,6]⟩,⟨.or,[0,13]⟩,⟨.or,[3,18]⟩,⟨.or,[5,12]⟩,⟨.or,[2,14]⟩,⟨.or,[16,43]⟩,⟨.or,[16,17]⟩,⟨.or,[19,10]⟩,⟨.or,[11,18]⟩,⟨.or,[11,14]⟩,⟨.or,[0,11]⟩,⟨.or,[9,50]⟩,⟨.or,[13,9]⟩,⟨.or,[5,19]⟩,⟨.or,[5,15]⟩,⟨.or,[5,10]⟩,⟨.or,[4,3]⟩,⟨.or,[11,55]⟩,⟨.or,[8,12]⟩,⟨.or,[1,52]⟩,⟨.or,[16,7]⟩,⟨.or,[13,47]⟩,⟨.or,[8,41]⟩,⟨.or,[1,58]⟩,⟨.or,[17,60]⟩,⟨.or,[3,62]⟩,⟨.or,[5,66]⟩,⟨.and,[36,61]⟩,⟨.or,[19,63]⟩,⟨.or,[15,49]⟩,⟨.or,[13,72]⟩,⟨.or,[15,45]⟩,⟨.or,[17,67]⟩,⟨.and,[38,74]⟩,⟨.or,[0,44]⟩,⟨.or,[3,53]⟩,⟨.or,[10,12]⟩,⟨.or,[6,46]⟩,⟨.or,[4,2]⟩,⟨.or,[19,68]⟩,⟨.or,[59,79]⟩,⟨.or,[9,1]⟩,⟨.or,[3,75]⟩,⟨.or,[2,7]⟩,⟨.or,[10,82]⟩,⟨.or,[18,80]⟩,⟨.or,[7,83]⟩,⟨.or,[8,87]⟩,⟨.and,[23,90]⟩,⟨.or,[17,89]⟩,⟨.or,[14,42]⟩,⟨.or,[14,6]⟩,⟨.or,[4,11]⟩,⟨.and,[30,84]⟩,⟨.and,[20,86]⟩,⟨.or,[1,6]⟩,⟨.and,[24,70]⟩,⟨.or,[51,73]⟩,⟨.or,[0,93]⟩,⟨.or,[2,76]⟩,⟨.or,[77,100]⟩,⟨.or,[7,99]⟩,⟨.and,[21,103]⟩,⟨.or,[10,105]⟩,⟨.or,[57,78]⟩,⟨.or,[16,81]⟩,⟨.or,[13,95]⟩,⟨.and,[37,102]⟩,⟨.or,[2,109]⟩,⟨.or,[19,48]⟩,⟨.or,[12,113]⟩,⟨.or,[17,110]⟩,⟨.or,[98,104]⟩,⟨.and,[22,112]⟩,⟨.and,[26,107]⟩,⟨.and,[39,114]⟩,⟨.or,[64,65]⟩,⟨.and,[35,101]⟩,⟨.or,[54,91]⟩,⟨.or,[43,115]⟩,⟨.or,[7,94]⟩,⟨.or,[56,88]⟩,⟨.and,[33,123]⟩,⟨.or,[15,124]⟩,⟨.or,[6,96]⟩,⟨.or,[15,128]⟩,⟨.or,[69,85]⟩,⟨.and,[34,127]⟩,⟨.and,[29,125]⟩,⟨.and,[32,120]⟩,⟨.and,[25,108]⟩,⟨.or,[40,122]⟩]
def lo : Array Nat := #[2,16,362924737837,1,1,1,2,2,4,4,4,8,8,32,64,128,256,512,2282710570,1,5117757505,52747710546]
def hi : Array Nat := #[268435458,2147483664,362924741933,33554433,134217729,137438953473,2097154,67108866,4194308,536870916,549755813892,8388616,1073741832,4294967328,8589934656,17179869312,34359738624,68719477248,2282743338,1048577,5117757507,52747710802]
def columns : Array Nat := #[6597322997820,14294463021249,7532971780,1125298477060,8796103507970,1133888413700,13262862172160,137438986240,9070987771908,1649267834880,1099528667140,4398047559680,8796111896576,9895607009280,5497559449600,5497559187456,1099511889920,14293654568960,1099511889920,5497559449600,2199023255552,268435456,1073741824,8589934592,4398047559680,33554432,536870912,9895674118144,4398051753984,4400195043328,8813274988544,1099537055748,4432407298048,68719476736,8933550850052,9070973026304,549772591108,134217728,16777220,4294967296,7696511926271,9895615397890,1649267834880,274894749700,14912130007040,16492930007100,1125298477060,9929983533060,5505092421380,1374406639620,14293654568960,5497576226820,5497559449600,5497559449600,6597322997820,14843410513920,10445362954240,5531935973380,5531935973380,1133888413700,9921401985030,14843410513920,9070989869060,14294464069825,1236950876160,9929983533060,10170510147590,14328840593605,14319449544710,10196271568900,10204869894150,549755813888,14294464069825,5772454199300,14294464069825,16492930007100,14328840593605,0,17111405445180,5523346036740,9895623786500,14388160649220,8803636479750,14319449544710,5557705783300,14844218966209,16518699817020,144971958020,9903148369670,9895623786500,14456888530950,9215942952708,8589934592,14293671346180,6047315394560,14362374062080,13194151067650,17179869184,2199023255552,14363183562945,0,5772454199300,16492930007100,14336356788165,0,14500622549185,268435456,14500639326405,17145765191740,14388160649220,14362374062080,134217728,14395676843780,5505092421380,14301187540740,14362374062080,2199023255552,1073741824,536870912,4294967296,10067422519300,274877906944,15813249173308,14637268811780,6184754380800,10452904314630,68719476736,6184754380800,13262870560770,14362382188546,15144883525829,137438953472,2147483648,34359738368,33554432,16492672057343]
def label : Array Nat := #[22,20,22,22,22,22,22,22,21,22,22,22,2,22,22,18,22,22,22,22,19,6,8,11,22,3,7,4,0,9,12,1,13,14,15,16,17,5,22,10,4,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,17,22,22,22,22,22,22,22,22,22,22,22,22,22,20,22,22,22,22,22,21,11,22,22,22,22,12,19,22,22,22,22,22,22,22,6,22,22,22,22,5,22,22,22,22,19,8,7,10,22,16,21,22,22,22,14,22,22,18,20,15,9,13,3,21]
def sample (v : Nat) (i : Fin 40) := v.testBit i.val
def X (i : R) := run pre (List.ofFn (sample lo[i.val]!))
def Y (i : R) := run pre (List.ofFn (sample hi[i.val]!))
theorem outputs : ∀ i : R,target (sample lo[i.val]!)≠target (sample hi[i.val]!) := by decide +kernel

def trace (b : Bool) (i : R) (w : Nat) := columns[w]!.testBit (i.val+(if b then 22 else 0))
def rawword (b : Bool) (i : R) := if b then hi[i.val]! else lo[i.val]!
def app (b : Bool) (i : R) := run pre (List.ofFn (sample (rawword b i)))

def audit (V : Nat → Bool) : Nat → List Gate → Bool
  | _,[] => true
  | n,g::gs => (g.inputs.all fun j => decide (j<n)) &&
      decide (g.op.eval (g.inputs.map V)=V n) && audit V (n+1) gs

theorem audit_sound (V : Nat → Bool) (gs : List Gate) (w : List Bool)
    (checked : audit V w.length gs=true)
    (old : ∀ j,j<w.length → w.getD j false=V j) :
    ∀ j,j<(run gs w).length → (run gs w).getD j false=V j := by
  induction gs generalizing w with
  | nil => exact old
  | cons g gs ih =>
    simp only [audit,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
    have ha : g.inputs.map (fun j => w.getD j false)=g.inputs.map V := by
      apply List.map_congr_left
      intro j hj
      exact old j (checked.1.1 j hj)
    apply ih (step w g)
    · simpa [step] using checked.2
    · intro j hj
      by_cases hj0 : j=w.length
      · subst j
        simpa only [step,snoc_last,ha] using checked.1.2
      · rw [show (step w g).getD j false=w.getD j false from snoc_other _ _ _ hj0]
        exact old j (by simp [step] at hj; omega)

theorem gates_ok : ∀ (b : Bool) (i : R),audit (trace b i) 40 pre=true := by decide +kernel
theorem pins_ok : ∀ (b : Bool) (i : R) (j : Fin 40),
    sample (rawword b i) j = trace b i j.val := by decide +kernel
theorem app_length (b : Bool) (i : R) : (app b i).length=136 := by
  rw [app,length_run,List.length_ofFn]
  decide
theorem replay_pin (b : Bool) (i : R) (j : Nat) (hj : j<136) :
    (app b i).getD j false=trace b i j := by
  apply audit_sound (trace b i) pre (List.ofFn (sample (rawword b i)))
  · simpa only [List.length_ofFn] using gates_ok b i
  · intro q hq
    have good : q<40 := by simpa only [List.length_ofFn] using hq
    rw [List.getD_eq_getElem _ _ hq,List.getElem_ofFn]
    exact pins_ok b i ⟨q,good⟩
  · change j<(app b i).length
    simpa only [app_length] using hj

theorem classify : ∀ (i : R) (w : Fin 136),trace false i w.val ≠ trace true i w.val →
    label[w.val]! = i.val := by decide +kernel
theorem lengths (i : R) : (X i).length=136 ∧ (Y i).length=136 := ⟨app_length false i,app_length true i⟩
theorem uniqueColumn (w : Nat) (i j : R) (h : (X i).getD w false≠(Y i).getD w false)
    (h' : (X j).getD w false≠(Y j).getD w false) : i=j := by
  by_cases wr : w<136
  · have diff (t : R) (d : (X t).getD w false≠(Y t).getD w false) :
        trace false t w ≠ trace true t w := by
      change (app false t).getD w false≠(app true t).getD w false at d
      rwa [replay_pin false t w wr,replay_pin true t w wr] at d
    exact Fin.ext ((classify i ⟨w,wr⟩ (diff i h)).symm.trans (classify j ⟨w,wr⟩ (diff j h')))
  · exfalso; apply h
    rw [List.getD_eq_default _ _ (by have := (lengths i).1; omega),
      List.getD_eq_default _ _ (by have := (lengths i).2; omega)]
theorem signed_prefix_price (tail : List Gate) (out : Nat)
    (fan : FanInTwo (⟨pre++tail,out⟩ : Circuit))
    (works : ∀ x : Fin 40→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=target x) :
    117+inverters tail≤(⟨pre++tail,out⟩ : Circuit).size := by
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (x : Fin 40→Bool) : (run tail (run pre (List.ofFn x))).getD out false=target x := by
    have h := works x
    change ((pre++tail).foldl step (List.ofFn x)).getD out false=_ at h
    simpa only [run,List.foldl_append] using h
  have required := price X Y lengths uniqueColumn tail ft out (fun i => by
    change (run tail (run pre _)).getD out false≠(run tail (run pre _)).getD out false
    rw [sim,sim]
    exact outputs i)
  have plen : pre.length=96 := by decide
  have total := mass_split tail
  change 117+inverters tail≤(pre++tail).length
  rw [List.length_append,plen]; omega
end Prefix96

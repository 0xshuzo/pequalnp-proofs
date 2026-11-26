import PEqualNP.Defs
namespace Prefix9838
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
abbrev R := Fin 39
def pre : List Gate := [⟨.not,[27]⟩,⟨.or,[4,18]⟩,⟨.or,[9,18]⟩,⟨.and,[8,40]⟩,⟨.or,[9,6]⟩,⟨.or,[0,13]⟩,⟨.or,[3,18]⟩,⟨.or,[5,12]⟩,⟨.or,[2,14]⟩,⟨.or,[16,43]⟩,⟨.or,[16,17]⟩,⟨.or,[19,10]⟩,⟨.or,[11,18]⟩,⟨.or,[11,14]⟩,⟨.or,[0,11]⟩,⟨.or,[9,50]⟩,⟨.or,[13,9]⟩,⟨.or,[5,19]⟩,⟨.or,[5,15]⟩,⟨.or,[5,10]⟩,⟨.or,[4,3]⟩,⟨.or,[11,55]⟩,⟨.or,[8,12]⟩,⟨.or,[1,52]⟩,⟨.or,[16,7]⟩,⟨.or,[13,47]⟩,⟨.or,[8,41]⟩,⟨.or,[1,58]⟩,⟨.or,[17,60]⟩,⟨.or,[3,62]⟩,⟨.or,[5,66]⟩,⟨.and,[36,61]⟩,⟨.or,[19,63]⟩,⟨.or,[15,49]⟩,⟨.or,[13,72]⟩,⟨.or,[15,45]⟩,⟨.or,[17,67]⟩,⟨.and,[38,74]⟩,⟨.or,[0,44]⟩,⟨.or,[3,53]⟩,⟨.or,[10,12]⟩,⟨.or,[6,46]⟩,⟨.or,[4,2]⟩,⟨.or,[19,68]⟩,⟨.or,[59,79]⟩,⟨.or,[9,1]⟩,⟨.or,[3,75]⟩,⟨.or,[2,7]⟩,⟨.or,[10,82]⟩,⟨.or,[18,80]⟩,⟨.or,[7,83]⟩,⟨.or,[8,87]⟩,⟨.and,[23,90]⟩,⟨.or,[17,89]⟩,⟨.or,[14,42]⟩,⟨.or,[14,6]⟩,⟨.or,[4,11]⟩,⟨.and,[30,84]⟩,⟨.and,[20,86]⟩,⟨.or,[1,6]⟩,⟨.and,[24,70]⟩,⟨.or,[51,73]⟩,⟨.or,[0,93]⟩,⟨.or,[2,76]⟩,⟨.or,[77,100]⟩,⟨.or,[7,99]⟩,⟨.and,[21,103]⟩,⟨.or,[10,105]⟩,⟨.or,[57,78]⟩,⟨.or,[16,81]⟩,⟨.or,[13,95]⟩,⟨.and,[37,102]⟩,⟨.or,[2,109]⟩,⟨.or,[19,48]⟩,⟨.or,[12,113]⟩,⟨.or,[17,110]⟩]
def lo : Array Nat := #[1,2,2,4,4,4,16,32,64,128,256,154669230094,2165008015,19797844000,362924737837,8,8,677007394,584384391409,2,512,103620300963,27934655503,4463182874,13254297620,176228942418,17234541570,36608303116,579854142490,2,1,550330599810,103483195504,1,8690964508,73019213075,1,588956043331,562716510721]
def hi : Array Nat := #[33554433,67108866,268435458,4194308,536870916,549755813892,2147483664,4294967328,8589934656,17179869312,34359738624,154669230222,2165008079,19797876768,362924741933,8388616,1073741832,677008418,584384391921,2097154,68719477248,103620309155,27934786575,4463184922,13254297628,176228942422,17234541571,36608303132,579854404634,274877906946,134217729,550330665346,103483719792,137438953473,8690964764,73019213107,1048577,588956059715,562716510723]
def lower : Array Nat := #[(18050682393198593+17867068164096*2^64),(9223373136366403586+11579233932552*2^64),(9223373136366403586+11579233932552*2^64),(282574488338436+1970874752434176*2^64),(282574488338436+1970874752434176*2^64),(282574488338436+1970874752434176*2^64),(1152924803141730320+4379639892*2^64),(1008948153530974240+18141942911050*2^64),(18691697672256+2667451716354048*2^64),(1099511627904+10995325992961*2^64),(4612258863985459456+137573171812*2^64),(12823825271257901070+4339398967467835*2^64),(13542171249551828623+4357265528184635*2^64),(3426852308133814304+4346232635400027*2^64),(6794781011952534829+2032860364003966*2^64),(1152992972862652424+316659421839408*2^64),(1152992972862652424+316659421839408*2^64),(17198543290163154978+4040606015395194*2^64),(13831952519318087921+2668282521771359*2^64),(9223373136366403586+11579233932552*2^64),(2413952490014769664+17593261899776*2^64),(14871344569546461347+4040468722736491*2^64),(13461084491796251663+2035093749096249*2^64),(13600103420005893146+4339677494484860*2^64),(13002251677775202324+2006477453565788*2^64),(12799535981448413778+4356856788997468*2^64),(16860528143574907906+3460064970644794*2^64),(12805254401803837452+4328506424991094*2^64),(13292448547317222426+328655855129980*2^64),(9223373136366403586+11579233932552*2^64),(18050682393198593+17867068164096*2^64),(16498384730853640578+2263796411834237*2^64),(11399127530822975600+4357132235232606*2^64),(18050682393198593+17867068164096*2^64),(17651796076006840348+2006477453631359*2^64),(16026951050947249427+4040610465832828*2^64),(18050682393198593+17867068164096*2^64),(11560871674299811907+2668282296589644*2^64),(11957188415268882945+335219554180940*2^64)]
def upper : Array Nat := #[(18050682426753025+17867068164096*2^64),(9223373136433512450+11579233932552*2^64),(9223373136634839042+11579233932552*2^64),(282574492532740+1970874752434176*2^64),(282575025209348+1970874752434176*2^64),(283124244152324+1970874752434176*2^64),(1152924805289213968+4379639892*2^64),(1008948157825941536+18141942911050*2^64),(18700287606848+2667451716354048*2^64),(1116691497088+10995325992961*2^64),(4612258898345197824+137573171812*2^64),(12823825271257901198+4339398967467835*2^64),(13542171249551828687+4357265528184635*2^64),(3426852308133847072+4346232635400027*2^64),(6794781011952538925+2032860364003966*2^64),(1152992972871041032+316659690274864*2^64),(1152992973936394248+316668011774000*2^64),(17198543290163156002+4040606032172410*2^64),(13831952519318088433+2668282523868511*2^64),(9223373136368500738+15977280443656*2^64),(2413952558734246400+17593261899904*2^64),(14943402163584397475+4040468722736491*2^64),(13461084491796382735+4286893562781497*2^64),(13618117818515377178+4339677494484860*2^64),(13002251677775202332+2006477453565820*2^64),(12799535981448413782+4356856931603804*2^64),(16860528143574907907+3477657156705594*2^64),(12805254401803837468+4328510719958390*2^64),(13292452945363995674+328656928871804*2^64),(9223373411244310530+12678745568520*2^64),(18049583015788545+17867068164096*2^64),(16498384730853706114+2580455760633725*2^64),(11401379330637185136+4357269674186078*2^64),(18050819832152065+158604556519424*2^64),(17651804872099862812+2006477453631359*2^64),(16027091788435604787+4040610465832830*2^64),(18050682394247169+17884248033280*2^64),(11561153149276538947+4357132156853580*2^64),(11957188415268882947+346249030197068*2^64)]
def label : Array Nat := #[26,38,25,24,27,35,12,11,34,18,17,23,14,21,37,13,31,22,28,32,36,19,3,15,39,0,1,30,2,4,16,6,7,8,9,10,20,33,29,5,30,39,28,34,39,39,39,35,37,39,39,32,39,39,23,39,21,39,39,39,39,39,39,39,39,35,39,39,39,24,39,20,39,39,39,39,39,29,26,39,39,39,39,39,39,18,39,25,17,39,39,25,15,39,28,39,27,16,36,38,39,32,39,39,29,38,19,38,26,31,39,33,31,37,37,22]
def sample (v : Nat) (i : Fin 40) := v.testBit i.val
def X (i : R) := run pre (List.ofFn (sample lo[i.val]!))
def Y (i : R) := run pre (List.ofFn (sample hi[i.val]!))
def decode (v : Nat) := List.ofFn fun w : Fin 116 => v.testBit w.val
theorem outputs : ∀ i : R,target (sample lo[i.val]!)≠target (sample hi[i.val]!) := by decide +kernel
theorem replay : ∀ i : R,X i=decode lower[i.val]! ∧ Y i=decode upper[i.val]! := by decide +kernel
theorem classify : ∀ (i : R) (w : Fin 116),lower[i.val]!.testBit w.val ≠ upper[i.val]!.testBit w.val →
    label[w.val]! = i.val := by decide +kernel
theorem lengths (i : R) : (X i).length=116 ∧ (Y i).length=116 := by
  rw [(replay i).1,(replay i).2];simp [decode]
theorem uniqueColumn (w : Nat) (i j : R) (h : (X i).getD w false≠(Y i).getD w false)
    (h' : (X j).getD w false≠(Y j).getD w false) : i=j := by
  by_cases wr : w<116
  · have diff (t : R) (d : (X t).getD w false≠(Y t).getD w false) :
        lower[t.val]!.testBit w ≠ upper[t.val]!.testBit w := by
      rw [(replay t).1,(replay t).2] at d
      simpa only [decode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos wr,Option.getD_some] using d
    exact Fin.ext ((classify i ⟨w,wr⟩ (diff i h)).symm.trans (classify j ⟨w,wr⟩ (diff j h')))
  · exfalso; apply h
    rw [List.getD_eq_default _ _ (by have := (lengths i).1; omega),
      List.getD_eq_default _ _ (by have := (lengths i).2; omega)]
theorem signed_prefix_price (tail : List Gate) (out : Nat)
    (fan : FanInTwo (⟨pre++tail,out⟩ : Circuit))
    (works : ∀ x : Fin 40→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=target x) :
    114+inverters tail≤(⟨pre++tail,out⟩ : Circuit).size := by
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
  have plen : pre.length=76 := by decide
  have total := mass_split tail
  change 114+inverters tail≤(pre++tail).length
  rw [List.length_append,plen]; omega
end Prefix9838

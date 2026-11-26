import PEqualNP.Defs
namespace Sides9766
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
abbrev Raw := Fin 26
def edgeF (x : Raw → Bool) := (x 0 && x 17) || (x 0 && x 23) || (x 0 && x 25) || (x 1 && x 13) || (x 1 && x 14) || (x 1 && x 18) || (x 1 && x 24) || (x 2 && x 14) || (x 2 && x 15) || (x 2 && x 19) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 16) || (x 3 && x 20) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 17) || (x 4 && x 21) || (x 5 && x 15) || (x 5 && x 17) || (x 5 && x 18) || (x 5 && x 22) || (x 6 && x 16) || (x 6 && x 18) || (x 6 && x 19) || (x 6 && x 23) || (x 7 && x 17) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 24) || (x 8 && x 18) || (x 8 && x 20) || (x 8 && x 21) || (x 8 && x 25) || (x 9 && x 13) || (x 9 && x 19) || (x 9 && x 21) || (x 9 && x 22) || (x 10 && x 14) || (x 10 && x 20) || (x 10 && x 22) || (x 10 && x 23) || (x 11 && x 15) || (x 11 && x 21) || (x 11 && x 23) || (x 11 && x 24) || (x 12 && x 16) || (x 12 && x 22) || (x 12 && x 24) || (x 12 && x 25)
def lo : Array Nat := #[33558266,15861,23529,38867,69543,139086,269981,531771,1055351,2102511,4196831,8393662,16779133,50036738,32972804,65945608,64790544,62480416,57860160,48619648,30138624,60277248,53453824,39806976,12513280,25026561]
def hi : Array Nat := #[33558267,15863,23533,38875,69559,139118,270045,531899,1055607,2103023,4197855,8395710,16783229,50044930,32989188,65978376,64856080,62611488,58122304,49143936,31187200,62374400,57648128,48195584,29290496,58580993]
def A (i k : Raw) := lo[i.val]!.testBit k.val
def B (i k : Raw) := hi[i.val]!.testBit k.val
def side (i : Raw) := decide (i.val<13)
theorem raised : ∀ i k : Raw, B i k = true ↔ k=i ∨ A i k=true := by decide +kernel
theorem cross : ∀ i j : Raw, i≠j → side i=side j → A i j=true ∨ A j i=true := by decide +kernel
theorem changes : ∀ i : Raw, edgeF (A i)≠edgeF (B i) := by decide +kernel
def disj (s : Finset Raw) (x : Raw→Bool) := decide (∃ k∈s, x k=true)
def phase (b v : Bool) := if b then !v else v
def homogeneous (s : Finset Raw) := ∀ i∈s, ∀ j∈s,side i=side j

def value (pre : List Gate) (w : Nat) (x : Raw→Bool) := (run pre (List.ofFn x)).getD w false
abbrev Support := Finset Raw
def W (j : Nat) := 26+j
theorem run_old (gs : List Gate) (w : List Bool) (u : Nat) (hu : u<w.length) :
    (run gs w).getD u false=w.getD u false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD u false=_
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hu

theorem raw_wire (pre : List Gate) (u : Nat) (hu : u<26) (x : Raw→Bool) :
    value pre u x=x ⟨u,hu⟩ := by
  unfold value
  rw [run_old _ _ _ (by simpa using hu)]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hu,Option.getD_some]

theorem prior_value (pre : List Gate) (j u : Nat) (hj : j≤pre.length) (hu : u<26+j) (x : Raw→Bool) :
    value (pre.take j) u x=value pre u x := by
  have cut : pre=pre.take j++pre.drop j := by simp
  have len : (run (pre.take j) (List.ofFn x)).length=26+j := by simp [length_run,Nat.min_eq_left hj]
  unfold value
  conv_rhs => rw [cut]; simp only [run,List.foldl_append]
  exact (run_old (pre.drop j) (run (pre.take j) (List.ofFn x)) u (len.symm ▸ hu)).symm

theorem gate_value (pre : List Gate) (j : Nat) (hj : j<pre.length) (x : Raw→Bool) :
    value pre (W j) x = pre[j].op.eval (pre[j].inputs.map fun u => value (pre.take j) u x) := by
  let w := run (pre.take j) (List.ofFn x)
  have len : w.length=W j := by simp [w,length_run,W,Nat.min_eq_left (Nat.le_of_lt hj)]
  have cut : pre=pre.take j++pre[j]::pre.drop (j+1) := by simp
  unfold value
  conv_lhs => rw [cut]; simp only [run,List.foldl_append,List.foldl_cons]
  change (run (pre.drop (j+1)) (step w pre[j])).getD (W j) false=_
  rw [run_old _ _ _ (by simp [step,len])]
  change (w++[_]).getD (W j) false=_
  rw [←len,snoc_last]

/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<26, (S w).card≤1)
    (step : ∀ j < m, cold (W j) → ∃ K : Finset Nat,
      (∀ i∈K, i<W j ∧ cold i) ∧ S (W j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0)) :
    ∀ q ≤ m, ∀ F : Finset Nat, (∀ i∈F, i<W q ∧ cold i) →
      (F.biUnion S).card≤ F.card + ((Finset.range q).filter charged).card := by
  classical
  intro q
  induction q with
  | zero =>
    intro _ F good
    apply Finset.card_biUnion_le.trans
    have bound := Finset.sum_le_sum (fun w (h : w∈F) => raw w (good w h).1)
    simpa using bound
  | succ q ih =>
    intro lim F good
    have lt := Nat.lt_of_succ_le lim
    have lim' := Nat.le_of_lt lt
    have cf : ((Finset.range (q+1)).filter charged).card =
        ((Finset.range q).filter charged).card + (if charged q then 1 else 0) := by
      have re : Finset.range (q+1)=insert q (Finset.range q) := by ext n; simp; omega
      rw [re,Finset.filter_insert]
      split_ifs with h <;> simp [h]
    rw [cf]
    by_cases h : W q∈F
    · obtain ⟨K,prior,sub,kc⟩ := step q lt (good _ h).2
      let P := F.erase (W q) ∪ K
      have hp : ∀ i∈P, i<W q ∧ cold i := by
        intro i hi
        rcases Finset.mem_union.mp hi with he|hk
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp he
          have g := good i mem
          exact ⟨by dsimp [W] at g ne ⊢; omega,g.2⟩
        · exact prior i hk
      have hs : F.biUnion S ⊆ P.biUnion S := by
        intro u hu
        obtain ⟨i,hi,ui⟩ := Finset.mem_biUnion.mp hu
        by_cases e : i=W q
        · subst i
          obtain ⟨k,hk,uk⟩ := Finset.mem_biUnion.mp (sub ui)
          exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,uk⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩),ui⟩
      have e := Finset.card_erase_add_one h
      have upper : P.card≤(F.erase (W q)).card+K.card := Finset.card_union_le _ _
      have bd := (Finset.card_le_card hs).trans (ih lim' P hp)
      omega
    · have bd := ih lim' F (fun i hi => ⟨by
          have ne : i≠W q := fun e => h (e ▸ hi)
          have g := (good i hi).1
          dsimp [W] at g ne ⊢
          omega,(good i hi).2⟩)
      omega

theorem shrink_cut {S : Nat→Support} {t : Support} {K : Finset Nat} (kc : K.card≤2)
    (cover : t⊆K.biUnion S) :
    ∃ H⊆K, t⊆H.biUnion S ∧ H.card≤1+(if 2≤t.card then 1 else 0) := by
  classical
  by_cases big : 2≤t.card
  · exact ⟨K,Finset.Subset.rfl,cover,by simpa [big] using kc⟩
  · by_cases has : t.Nonempty
    · obtain ⟨v,hv⟩ := has
      obtain ⟨u,hu,member⟩ := Finset.mem_biUnion.mp (cover hv)
      refine ⟨{u},by simpa using hu,?_,by simp [big]⟩
      intro z hz
      have eq := Finset.card_le_one.mp (by omega : t.card≤1) z hz v hv
      simpa [eq] using member
    · exact ⟨∅,by simp,by simp [Finset.not_nonempty_iff_eq_empty.mp has],by simp⟩

def families : Array Nat := #[522,1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357,67108863]
def starBases : Array Nat := #[15861,23529,38867,69543,139086,269981,531771,1055351,2102511,4196831,8393662,16779133,33558266]
abbrev Reg := Fin 14
def eligible (r : Reg) : Support := Finset.univ.filter (fun i => families[r.val]!.testBit i.val)
def LX (r : Reg) (i k : Raw) := if r.val<13 then starBases[r.val]!.testBit k.val else A i k
def HX (r : Reg) (i k : Raw) := decide (k=i) || LX r i k
theorem sameOff : ∀ (r : Reg) (i k : Raw), i≠k → LX r i k=HX r i k := by
  intro r i k ne
  simp [HX,Ne.symm ne]
theorem answers : ∀ (r : Reg) (i : Raw), i∈eligible r → edgeF (LX r i)≠edgeF (HX r i) := by decide +kernel
theorem prices : ∑ r : Reg,(eligible r).card=77 := by decide +kernel
def R (r : Reg) (pre : List Gate) (w : Nat) : Support :=
  (eligible r).filter (fun i => value pre w (LX r i) ≠ value pre w (HX r i))
def G (pre : List Gate) (j : Nat) := pre.getD j ⟨.or,[]⟩
def singleSource (r : Reg) (pre : List Gate) (j : Nat) :=
  ∃ u∈(useful (G pre j)).toFinset,u<W j ∧ R r pre (W j)⊆R r pre u
def pays (r : Reg) (pre : List Gate) (j : Nat) :=
    2≤(R r pre (W j)).card ∧ charge (G pre j).op=1 ∧ ¬singleSource r pre j
theorem rawBound (r : Reg) (pre : List Gate) (u : Nat) (hu : u<26) : (R r pre u).card≤1 := by
  have sub : R r pre u⊆{(⟨u,hu⟩ : Raw)} := by
    intro i hi
    have diff := (Finset.mem_filter.mp hi).2
    rw [raw_wire pre u hu,raw_wire pre u hu] at diff
    by_contra h
    exact diff (sameOff r i ⟨u,hu⟩ (by simpa using h))
  exact (Finset.card_le_card sub).trans (by simp)
theorem family_cover (r : Reg) (pre : List Gate) (j : Nat) (hj : j<pre.length) :
    ∃ K : Finset Nat, (∀ u∈K,u<W j) ∧ R r pre (W j)⊆K.biUnion (R r pre) ∧
    K.card≤(useful pre[j]).length := by
  classical
  let K := (useful pre[j]).toFinset.filter (fun u => u<W j)
  refine ⟨K,fun _ h => (Finset.mem_filter.mp h).2,?_,
    (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)⟩
  intro i hi
  have diff := (Finset.mem_filter.mp hi).2
  rw [gate_value pre j hj (LX r i),gate_value pre j hj (HX r i),use_sound pre[j] (fun u => value (pre.take j) u (LX r i)),use_sound pre[j] (fun u => value (pre.take j) u (HX r i))] at diff
  have changed : ∃ u∈useful pre[j],value (pre.take j) u (LX r i)≠value (pre.take j) u (HX r i) := by
    by_contra! none
    exact diff (congrArg pre[j].op.eval (List.map_congr_left none))
  obtain ⟨u,mem,delta⟩ := changed
  have lt : u<W j := by
    by_contra! high
    have L (z : Raw→Bool) : (run (pre.take j) (List.ofFn z)).length≤u := by
      simpa [length_run,Nat.min_eq_left (Nat.le_of_lt hj),W] using high
    exact delta ((List.getD_eq_default _ _ (L (LX r i))).trans (List.getD_eq_default _ _ (L (HX r i))).symm)
  rw [prior_value pre j u (Nat.le_of_lt hj) lt (LX r i),prior_value pre j u (Nat.le_of_lt hj) lt (HX r i)] at delta
  exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr mem,lt⟩,
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,delta⟩⟩

open Classical in
theorem family_bound (r : Reg) (C : Circuit) (fan : FanInTwo C)
    (works : ∀ x : Raw→Bool,C.eval (List.ofFn x)=edgeF x) :
    (eligible r).card≤1+((Finset.range C.gates.length).filter (pays r C.gates)).card := by
  classical
  let gs := C.gates
  have st (j : Nat) (hj : j<gs.length) (_ok : True) :
      ∃ H : Finset Nat, (∀ u∈H,u<W j ∧ True) ∧ R r gs (W j)⊆H.biUnion (R r gs) ∧
        H.card≤1+(if pays r gs j then 1 else 0) := by
    obtain ⟨K,old,cov,kc⟩ := family_cover r gs j hj
    have usage := use_count gs[j] (fan _ (List.getElem_mem hj)).2
    have cap : charge gs[j].op≤1 := by cases gs[j].op <;> simp [charge]
    have op : G gs j=gs[j] := List.getD_eq_getElem gs _ hj
    by_cases copy : singleSource r gs j
    · obtain ⟨v,_,prior,cover⟩ := copy
      refine ⟨{v},by simpa using prior,by simpa using cover,by simp⟩
    · by_cases binary : charge gs[j].op=1
      · obtain ⟨H,sub,cv,small⟩ := shrink_cut (by omega : K.card≤2) cov
        refine ⟨H,fun u hu => ⟨old u (sub hu),True.intro⟩,cv,?_⟩
        simpa only [pays,op,binary,copy,not_false_eq_true,and_true] using small
      · refine ⟨K,fun u hu => ⟨old u hu,True.intro⟩,cov,?_⟩
        have np : ¬pays r gs j := by
          intro h
          have bz := h.2.1
          rw [op] at bz
          exact binary bz
        simp [np]
        omega
  have eq : R r gs C.output=eligible r := by
    ext i
    simp only [R,Finset.mem_filter]
    refine ⟨And.left,fun hi => ⟨hi,?_⟩⟩
    change C.eval (List.ofFn (LX r i))≠C.eval (List.ofFn (HX r i))
    rw [works,works]
    exact answers r i hi
  have valid : C.output<W gs.length := by
    by_contra! bad
    have zero (x : Raw→Bool) : value gs C.output x=false := by
      apply List.getD_eq_default
      simpa [length_run,W] using bad
    have d := changes (0 : Raw)
    exact d ((works (A 0)).symm.trans ((zero (A 0)).trans ((zero (B 0)).symm.trans (works (B 0)))))
  have bound := frontier gs.length (R r gs) (fun _ => True) (pays r gs) (rawBound r gs)
    st gs.length le_rfl {C.output} (by simpa using valid)
  simpa [eq,gs] using bound

theorem shared_branch_required (C : Circuit) (fan : FanInTwo C) (cap : C.size≤62)
    (works : ∀ x : Raw→Bool,C.eval (List.ofFn x)=edgeF x) :
    ∃ j<C.gates.length,∃ r s : Reg,r≠s ∧ pays r C.gates j ∧ pays s C.gates j := by
  classical
  by_contra none
  let F (r : Reg) := (Finset.range C.gates.length).filter (pays r C.gates)
  have dis : (↑(Finset.univ : Finset Reg) : Set Reg).PairwiseDisjoint F := by
    intro r _ s _ ne
    apply Finset.disjoint_left.mpr
    intro j hr hs
    have jr := Finset.mem_filter.mp hr
    have js := Finset.mem_filter.mp hs
    exact none ⟨j,Finset.mem_range.mp jr.1,r,s,ne,jr.2,js.2⟩
  have sum := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset Reg)) => family_bound r C fan works)
  rw [prices,Finset.sum_add_distrib] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at sum
  have union : (Finset.univ.biUnion F).card=∑ r,(F r).card := Finset.card_biUnion dis
  have sub : Finset.univ.biUnion F⊆Finset.range C.gates.length := by
    intro j hj
    obtain ⟨t,_,m⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp m).1
  have count := Finset.card_le_card sub
  rw [union,Finset.card_range] at count
  change C.gates.length≤62 at cap
  change 77≤14+∑ r,(F r).card at sum
  omega
private theorem count_filter {α : Type} [DecidableEq α] (s : Finset α) (P : α→Prop) [DecidablePred P] :
    (s.filter P).card=∑ i∈s, if P i then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s h ih => by_cases pa : P a <;> simp [Finset.filter_insert,h,pa,ih,Nat.add_comm]

open Classical in
noncomputable def multiplicity (pre : List Gate) (j : Nat) :=
  ((Finset.univ : Finset Reg).filter (fun r => pays r pre j)).card

theorem repeated_demand (C : Circuit) (fan : FanInTwo C)
    (works : ∀ x : Raw→Bool,C.eval (List.ofFn x)=edgeF x) :
    63+((Finset.range C.gates.length).filter (fun j => multiplicity C.gates j=0)).card ≤
      C.size+ ∑ j∈Finset.range C.gates.length,(multiplicity C.gates j-1) := by
  classical
  let f := multiplicity C.gates
  let J := Finset.range C.gates.length
  have need := Finset.sum_le_sum (fun r (_ : r∈(Finset.univ : Finset Reg)) => family_bound r C fan works)
  rw [prices,Finset.sum_add_distrib] at need
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at need
  have exch : (∑ r : Reg,(J.filter (pays r C.gates)).card)=∑ j∈J,f j := by
    simp only [f,multiplicity,count_filter]
    rw [Finset.sum_comm]
  change 77≤14+∑ r : Reg,(J.filter (pays r C.gates)).card at need
  rw [exch] at need
  have eq (j : Nat) : f j+(if f j=0 then 1 else 0)=1+(f j-1) := by split <;> omega
  have balance := Finset.sum_congr (rfl : J=J) (fun j (_ : j∈J) => eq j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] at balance
  have cs : J.card=C.size := by change (Finset.range _).card=_; simp [Circuit.size]
  change 63+(J.filter (fun j=>f j=0)).card≤C.size+∑ j∈J,(f j-1)
  rw [count_filter]
  omega

theorem inverter_idle (C : Circuit) (j : Nat) (inv : (G C.gates j).op=GateOp.not) :
    multiplicity C.gates j=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have yes : pays r C.gates j := (Finset.mem_filter.mp hr).2
  have h := yes.2.1
  simp [inv,charge] at h
end Sides9766

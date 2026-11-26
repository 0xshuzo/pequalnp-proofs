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

theorem disj_change (s : Finset Raw) (i : Raw) (d : disj s (A i) ≠ disj s (B i)) :
    i∈s ∧ ∀ j∈s,A i j≠true := by
  have off : ¬∃ j∈s,A i j=true := by
    rintro ⟨j,js,v⟩
    have hA : disj s (A i)=true := decide_eq_true ⟨j,js,v⟩
    have hB : disj s (B i)=true := decide_eq_true ⟨j,js,(raised i j).2 (.inr v)⟩
    exact d (hA.trans hB.symm)
  have vA : disj s (A i)=false := by simp [disj,off]
  have vB : disj s (B i)=true := Bool.eq_true_of_not_eq_false (fun h => d (vA.trans h.symm))
  obtain ⟨j,js,jv⟩ := of_decide_eq_true vB
  have ji := ((raised i j).1 jv).resolve_right (fun v => off ⟨j,js,v⟩)
  exact ⟨ji ▸ js,fun k hk v => off ⟨k,hk,v⟩⟩

theorem column (s : Finset Raw) (hs : homogeneous s) (b : Bool) (i j : Raw)
    (h : phase b (disj s (A i))≠phase b (disj s (B i)))
    (h' : phase b (disj s (A j))≠phase b (disj s (B j))) : i=j := by
  have a := disj_change s i (fun eq => h (congrArg (phase b) eq))
  have c := disj_change s j (fun eq => h' (congrArg (phase b) eq))
  by_contra d
  rcases cross i j d (hs i a.1 j c.1) with p|p
  · exact a.2 j c.1 p
  · exact c.2 i a.1 p

def value (pre : List Gate) (w : Nat) (x : Raw→Bool) := (run pre (List.ofFn x)).getD w false
def sideBank (pre : List Gate) := ∀ w : Nat, ∃ (s : Finset Raw) (b : Bool),
    homogeneous s ∧ ∀ x : Raw→Bool, value pre w x = phase b (disj s x)
theorem suffix_bound (pre tail : List Gate) (out : Nat) (bank : sideBank pre)
    (fan : FanInTwo (⟨pre++tail,out⟩ : Circuit))
    (works : ∀ x : Raw→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=edgeF x) :
    25+inverters tail≤tail.length := by
  let X := fun i : Raw => run pre (List.ofFn (A i))
  let Y := fun i : Raw => run pre (List.ofFn (B i))
  have lens (i : Raw) : (X i).length=26+pre.length ∧ (Y i).length=26+pre.length := by
    simp [X,Y,length_run]
  have uniq (w : Nat) (i j : Raw) (h : (X i).getD w false≠(Y i).getD w false)
      (h' : (X j).getD w false≠(Y j).getD w false) : i=j := by
    obtain ⟨s,b,hs,ev⟩ := bank w
    apply column s hs b i j
    · rw [←ev (A i),←ev (B i)]
      exact h
    · rw [←ev (A j),←ev (B j)]
      exact h'
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (x : Raw→Bool) : (run tail (run pre (List.ofFn x))).getD out false=edgeF x := by
    have h := works x
    change ((pre++tail).foldl step (List.ofFn x)).getD out false=_ at h
    simpa only [run,List.foldl_append] using h
  have required := price X Y lens uniq tail ft out (fun i => by
    change (run tail (run pre _)).getD out false≠(run tail (run pre _)).getD out false
    rw [sim,sim]
    exact changes i)
  have sum := mass_split tail
  omega
abbrev Support := Finset Raw
def W (j : Nat) := 26+j
def outsider (s : Support) (k : Raw) := decide (k∉s)
def spike (s : Support) (i k : Raw) := decide (k=i ∨ k∉s)

theorem facet (s t : Support) (i : Raw)
    (d : disj t (outsider s) ≠ disj t (spike s i)) : i∈t ∧ t⊆s := by
  have sub : t⊆s := by
    intro k hk
    by_contra bad
    have y : disj t (outsider s)=true := decide_eq_true ⟨k,hk,decide_eq_true bad⟩
    have z : disj t (spike s i)=true := decide_eq_true ⟨k,hk,decide_eq_true (.inr bad)⟩
    exact d (y.trans z.symm)
  have zero : disj t (outsider s)=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨k,hk,no⟩ := of_decide_eq_true h
    exact (of_decide_eq_true no) (sub hk)
  have one : disj t (spike s i)=true := Bool.eq_true_of_not_eq_false (fun h => d (zero.trans h.symm))
  obtain ⟨k,hk,on⟩ := of_decide_eq_true one
  have eq := (of_decide_eq_true on).resolve_right (fun no => no (sub hk))
  exact ⟨eq ▸ hk,sub⟩

theorem own_facet (s : Support) (i : Raw) (hi : i∈s) :
    disj s (outsider s)≠disj s (spike s i) := by
  have z : disj s (outsider s)=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨k,hk,hk'⟩ := of_decide_eq_true h
    exact (of_decide_eq_true hk') hk
  have o : disj s (spike s i)=true := decide_eq_true ⟨i,hi,decide_eq_true (.inl rfl)⟩
  simp [z,o]

theorem phase_inj (b : Bool) : Function.Injective (phase b) := by
  intro x y eq
  cases b <;> cases x <;> cases y <;> simp_all [phase]

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
  simp [List.getD_eq_getElem?_getD,hu]

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
  rfl

def represents (pre : List Gate) (S : Nat→Support) (b : Nat→Bool) :=
  ∀ w x, value pre w x=phase (b w) (disj (S w) x)

theorem raw_card (pre : List Gate) (S : Nat→Support) (b : Nat→Bool) (rep : represents pre S b)
    (u : Nat) (hu : u<26) : (S u).card≤1 := by
  let z : Raw := ⟨u,hu⟩
  have sub : S u⊆{z} := by
    intro i hi
    by_contra h
    have ne : z≠i := by simpa [eq_comm] using h
    have eq : outsider (S u) z=spike (S u) i z := by simp [outsider,spike,ne]
    have rawEq : value pre u (outsider (S u))=value pre u (spike (S u) i) := by
      simpa only [raw_wire pre u hu] using eq
    rw [rep,rep] at rawEq
    exact own_facet _ i hi (phase_inj _ rawEq)
  exact (Finset.card_le_card sub).trans (by simp)

theorem local_cover (pre : List Gate) (S : Nat→Support) (b : Nat→Bool) (rep : represents pre S b)
    (j : Nat) (hj : j<pre.length) (fan : pre[j].inputs.length≤2) :
    ∃ K : Finset Nat, (∀ u∈K, u<W j ∧ S u⊆S (W j)) ∧
      S (W j)⊆K.biUnion S ∧ K.card≤2 := by
  classical
  let t := S (W j)
  let K := pre[j].inputs.toFinset.filter fun u => u<W j ∧ S u⊆t
  refine ⟨K,fun u h => (Finset.mem_filter.mp h).2,?_,?_⟩
  · intro i hi
    let x := outsider t
    let y := spike t i
    have diff : value pre (W j) x≠value pre (W j) y := by
      rw [rep,rep]
      exact fun e => own_facet t i hi (phase_inj _ e)
    rw [gate_value pre j hj x,gate_value pre j hj y] at diff
    have changed : ∃ u∈pre[j].inputs,value (pre.take j) u x≠value (pre.take j) u y := by
      by_contra! none
      exact diff (congrArg pre[j].op.eval (List.map_congr_left none))
    obtain ⟨u,mem,delta⟩ := changed
    have lt : u<W j := by
      by_contra! high
      have L (z : Raw→Bool) : (run (pre.take j) (List.ofFn z)).length≤u := by
        simp [length_run,Nat.min_eq_left (Nat.le_of_lt hj)]
        exact high
      exact delta ((List.getD_eq_default _ _ (L x)).trans (List.getD_eq_default _ _ (L y)).symm)
    rw [prior_value pre j u (Nat.le_of_lt hj) lt x,prior_value pre j u (Nat.le_of_lt hj) lt y,rep,rep] at delta
    obtain ⟨inc,sub⟩ := facet t (S u) i (fun e => delta (congrArg (phase (b u)) e))
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr mem,lt,sub⟩,inc⟩
  · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans fan)
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

def outputs : List (List Nat) := [[1,3,9],[1,2,4,10],[2,3,5,11],[3,4,6,12],
  [0,4,5,7],[1,5,6,8],[2,6,7,9],[3,7,8,10],[4,8,9,11],[5,9,10,12],
  [0,6,10,11],[1,7,11,12],[0,2,8,12]]
def target (t : Fin 13) : Support := Finset.univ.filter (fun i => i.val∈outputs.getD t.val [])
lemma separation : ∀ a b : Fin 13, a≠b → (target a∩target b).card≤1 := by decide +kernel
lemma totalStars : ∑ t : Fin 13, (target t).card = 51 := by decide +kernel
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

theorem prefix_price (pre : List Gate) (S : Nat→Support) (b : Nat→Bool) (rep : represents pre S b)
    (fan : ∀ g∈pre,g.inputs.length≤2) (out : Fin 13→Nat) (bounded : ∀ t,out t<W pre.length)
    (contains : ∀ t,S (out t)=target t) : 38≤pre.length := by
  classical
  let Q (t : Fin 13) := (Finset.range pre.length).filter fun j => S (W j)⊆target t ∧ 2≤(S (W j)).card
  have one (t : Fin 13) : (target t).card≤1+(Q t).card := by
    let cold (u : Nat) := S u⊆target t
    let charge (j : Nat) := S (W j)⊆target t ∧ 2≤(S (W j)).card
    have st (j : Nat) (hj : j<pre.length) (off : cold (W j)) :
        ∃ H : Finset Nat, (∀ u∈H,u<W j ∧ cold u) ∧ S (W j)⊆H.biUnion S ∧
          H.card≤1+(if charge j then 1 else 0) := by
      obtain ⟨K,prior,cov,kc⟩ := local_cover pre S b rep j hj (fan _ (List.getElem_mem hj))
      obtain ⟨H,sub,cover,small⟩ := shrink_cut kc cov
      refine ⟨H,fun u hu => ⟨(prior u (sub hu)).1,(prior u (sub hu)).2.trans off⟩,cover,?_⟩
      simpa only [charge,show S (W j)⊆target t from off,true_and] using small
    have bound := frontier pre.length S cold charge (raw_card pre S b rep) st pre.length le_rfl {out t} (by
      simpa [cold,contains] using bounded t)
    simpa [Q,charge,contains] using bound
  have dis : (↑(Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Q := by
    intro t _ s _ neq
    apply Finset.disjoint_left.mpr
    intro j ht hs
    obtain ⟨sub,large⟩ := (Finset.mem_filter.mp ht).2
    have inc := (Finset.mem_filter.mp hs).2.1
    have lo := Finset.card_le_card (Finset.subset_inter sub inc)
    have cap := separation t s neq
    omega
  have sum := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset (Fin 13))) => one t)
  rw [totalStars,Finset.sum_add_distrib] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at sum
  have union : (Finset.univ.biUnion Q).card=∑ t,(Q t).card := Finset.card_biUnion dis
  have sub : Finset.univ.biUnion Q⊆Finset.range pre.length := by
    intro j hj
    obtain ⟨t,_,m⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp m).1
  have cap := Finset.card_le_card sub
  rw [union,Finset.card_range] at cap
  omega

theorem signed_star_cut (pre tail : List Gate) (root : Nat) (S : Nat→Support) (b : Nat→Bool)
    (rep : represents pre S b) (sides : ∀ w, homogeneous (S w))
    (out : Fin 13→Nat) (bounded : ∀ t,out t<W pre.length) (contains : ∀ t,S (out t)=target t)
    (fan : FanInTwo (⟨pre++tail,root⟩ : Circuit))
    (works : ∀ x : Raw→Bool,(⟨pre++tail,root⟩ : Circuit).eval (List.ofFn x)=edgeF x) :
    63+inverters tail≤(⟨pre++tail,root⟩ : Circuit).size := by
  have pp := prefix_price pre S b rep (fun g hg => (fan g (by
    change g∈pre++tail; exact List.mem_append_left _ hg)).2) out bounded contains
  have sp := suffix_bound pre tail root (fun w => ⟨S w,b w,sides w,rep w⟩) fan works
  change 63+inverters tail≤(pre++tail).length
  rw [List.length_append]
  omega
end Sides9766

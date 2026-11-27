import PEqualNP.Defs
namespace DoubleReach
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
def target (x : Fin 25 → Bool) := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)


abbrev J := Fin 4
abbrev V := Fin 25 → Bool
def input (m : Nat) (a : Fin 25) : Bool := m.testBit a.val
def view (c : Nat × Nat) (w : Fin 81) : Bool :=
  if w.val<44 then c.1.testBit w.val else c.2.testBit (w.val-44)
def sample (c : Nat × Nat) : List Bool := List.ofFn (view c)
def pre : List Gate := [⟨.or, [3,5]⟩,⟨.or, [11,25]⟩,⟨.or, [2,26]⟩,⟨.and, [14,27]⟩,⟨.or, [9,11]⟩,⟨.or, [4,29]⟩,⟨.or, [8,30]⟩,⟨.and, [20,31]⟩,⟨.or, [7,10]⟩,⟨.or, [3,33]⟩,⟨.or, [8,34]⟩,⟨.and, [19,35]⟩,⟨.or, [10,11]⟩,⟨.or, [6,37]⟩,⟨.or, [0,38]⟩,⟨.and, [22,39]⟩,⟨.and, [13,1]⟩,⟨.or, [41,12]⟩,⟨.or, [7,42]⟩,⟨.or, [11,43]⟩,⟨.and, [23,44]⟩,⟨.or, [5,6]⟩,⟨.or, [1,46]⟩,⟨.or, [8,47]⟩,⟨.and, [17,48]⟩,⟨.or, [10,12]⟩,⟨.or, [5,50]⟩,⟨.or, [9,51]⟩,⟨.and, [21,52]⟩,⟨.or, [4,12]⟩,⟨.or, [6,54]⟩,⟨.or, [3,55]⟩,⟨.and, [15,56]⟩,⟨.or, [0,2]⟩,⟨.or, [8,12]⟩,⟨.or, [58,59]⟩,⟨.and, [24,60]⟩,⟨.or, [5,7]⟩,⟨.or, [0,62]⟩,⟨.or, [4,63]⟩,⟨.and, [16,64]⟩,⟨.or, [2,7]⟩,⟨.or, [9,66]⟩,⟨.or, [6,67]⟩,⟨.and, [18,68]⟩,⟨.or, [57,61]⟩,⟨.or, [28,45]⟩,⟨.or, [41,69]⟩,⟨.or, [72,71]⟩,⟨.or, [49,73]⟩,⟨.or, [53,74]⟩,⟨.or, [40,65]⟩,⟨.or, [32,75]⟩,⟨.or, [36,70]⟩,⟨.or, [76,77]⟩,⟨.or, [78,79]⟩]
def lo : J → Nat := ![15337,15337,15337,1]
def hi : J → Nat := ![15341,15353,16361,65537]
def left : J → Nat × Nat := ![(14220334742505,31317469),(14220334742505,31317469),(14220334742505,31317469),(549755813889,1654784)]
def right : J → Nat × Nat := ![(14220334742509,31317469),(14220334742521,31317469),(14220334743529,31317469),(549755879425,107377934336)]
theorem lowRun : ∀i,run pre (List.ofFn (input (lo i)))=sample (left i) := by decide +kernel
theorem highRun : ∀i,run pre (List.ofFn (input (hi i)))=sample (right i) := by decide +kernel
theorem pivotal : ∀ i,target (input (lo i)) ≠ target (input (hi i)) := by decide +kernel
theorem separate : ∀(w : Fin 81)(i j : J), view (left i) w ≠ view (right i) w →
  view (left j) w ≠ view (right j) w → i=j := by decide +kernel
theorem suffixPrice (tail : List Gate) (root : Nat)
    (fan : FanInTwo (⟨pre++tail,root⟩ : Circuit))
    (works : ∀ x : V,(⟨pre++tail,root⟩ : Circuit).eval (List.ofFn x)=target x) :
    3 + inverters tail ≤ tail.length := by
  let X := fun i : J => sample (left i)
  let Y := fun i : J => sample (right i)
  have lens (i : J) : (X i).length=81 ∧ (Y i).length=81 := by simp [X,Y,sample]
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail
    exact List.mem_append_right _ hg)).2
  have unique (w : Nat) (i j : J) (hi : (X i).getD w false ≠ (Y i).getD w false)
      (hj : (X j).getD w false ≠ (Y j).getD w false) : i=j := by
    by_cases hw : w<81
    · have entry (c : Nat × Nat) : (sample c).getD w false=view c ⟨w,hw⟩ := by simp [sample,hw]
      exact separate ⟨w,hw⟩ i j (by simpa only [X,Y,entry] using hi)
        (by simpa only [X,Y,entry] using hj)
    · have lx := (lens i).1
      have ly := (lens i).2
      rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)] at hi
      exact (hi rfl).elim
  have sim (m : Nat) : (run tail (run pre (List.ofFn (input m)))).getD root false=target (input m) := by
    have h := works (input m)
    change ((pre++tail).foldl step (List.ofFn (input m))).getD root false=_ at h
    simpa only [run,List.foldl_append] using h
  have different (i : J) : (run tail (X i)).getD root false≠(run tail (Y i)).getD root false := by
    have a := sim (lo i)
    have b := sim (hi i)
    rw [lowRun] at a
    rw [highRun] at b
    exact fun eq => pivotal i (a.symm.trans (eq.trans b))
  have charge := price X Y lens unique tail ft root different
  have tally := mass_split tail
  omega
end DoubleReach

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

def tapped {t : Nat} (gs : List Gate) (port : Fin t → Nat) (bank : List Bool) :
    Fin t → Bool := fun j => (run gs bank).getD (port j) false

theorem feedbackFive {A : Type} {m t : Nat} (gs : List Gate)
    (fan : ∀ g∈gs,g.inputs.length≤2) (port : Fin t → Nat)
    (bank : A → (Fin t → Bool) → List Bool) (len : ∀ a z,(bank a z).length=m)
    (out : A → (Fin t → Bool) → Bool) (target : A → Bool → Bool)
    (blank : A) (point : Fin 4 → A)
    (single : ∀ (w : Nat) (i j : Fin 4),
      (bank blank (fun _ => false)).getD w false≠(bank (point i) (fun _ => false)).getD w false →
      (bank blank (fun _ => false)).getD w false≠(bank (point j) (fun _ => false)).getD w false → i=j)
    (quiet : tapped gs port (true :: bank blank (fun _ => false))=fun _ => false)
    (before : ∀ i,out (point i) (fun _ => false)=false)
    (newEdges : ∀ i,target (point i) true=true) (noEdge : target (point 0) false=false)
    (realize : ∃ z, tapped gs port (false :: bank (point 0) z)=z)
    (works : ∀ a b z, tapped gs port (b :: bank a z)=z → out a z=target a b) :
    5≤gs.length+t := by
  classical
  let zero : Fin t → Bool := fun _ => false
  obtain ⟨z,fixed⟩ := realize
  have flip : tapped gs port (false :: bank (point 0) z) ≠ tapped gs port (true :: bank (point 0) z) := by
    intro eq
    have bad0 := works _ _ _ fixed
    have bad1 := works _ _ _ (eq.symm.trans fixed)
    rw [noEdge] at bad0
    rw [newEdges] at bad1
    exact Bool.noConfusion (bad0.symm.trans bad1)
  have miss (i : Fin 4) : tapped gs port (true :: bank blank zero) ≠ tapped gs port (true :: bank (point i) zero) := by
    intro eq
    have act := works _ _ _ (eq.symm.trans quiet)
    rw [newEdges] at act
    exact Bool.noConfusion ((before i).symm.trans act)
  let X : Fin 5 → List Bool := Fin.cases (false::bank (point 0) z) (fun _ => true::bank blank zero)
  let Y : Fin 5 → List Bool := Fin.cases (true::bank (point 0) z) (fun i => true::bank (point i) zero)
  apply manyPrice (m:=m+1) X Y ?_ ?_ gs fan port ?_
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [X,Y,len]
  · intro w i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    · exact fun _ _ => rfl
    · cases w with
      | zero => simp [X,Y]
      | succ w => simp [X,Y]
    · cases w with
      | zero => simp [X,Y]
      | succ w => simp [X,Y]
    · cases w with
      | zero => simp [X,Y]
      | succ w =>
        simp only [X,Y,Fin.cases_succ,List.getD_cons_succ]
        intro ha hb
        exact congrArg Fin.succ (single w a b ha hb)
  · intro i
    have sep : tapped gs port (X i)≠tapped gs port (Y i) :=
      Fin.cases (by simpa [X,Y] using flip) (fun j => by simpa [X,Y] using miss j) i
    by_contra! all
    exact sep (funext all)

end PEqualNP.Outside.L_meta_9743.Guarded

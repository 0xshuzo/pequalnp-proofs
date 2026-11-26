import PEqualNP.Defs
namespace Exterior9737
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

abbrev Raw := Fin 16
abbrev Core := Fin 13
abbrev Source := Fin 48
def label : Raw → Fin 25 := ![13,15,16,14,22,4,2,3,5,10,6,0,11,1,7,12]
def edges : List (Nat × Nat) := [(0,5),(1,5),(2,5),(0,6),(3,6),(1,7),(3,7),(2,8),(3,8),(0,9),(4,9),(1,10),(4,10),(2,11),(4,11),(3,12),(4,12),(0,13),(2,14),(1,15)]
def fullEdges : List (Nat × Nat) := [(1,13),(2,13),(4,13),(10,13),(2,14),(3,14),(5,14),(11,14),(3,15),(4,15),(6,15),(12,15),(0,16),(4,16),(5,16),(7,16),(1,17),(5,17),(6,17),(8,17),(2,18),(6,18),(7,18),(9,18),(3,19),(7,19),(8,19),(10,19),(4,20),(8,20),(9,20),(11,20),(5,21),(9,21),(10,21),(12,21),(0,22),(6,22),(10,22),(11,22),(1,23),(7,23),(11,23),(12,23),(0,24),(2,24),(8,24),(12,24)]
def streets : Fin 7 → Nat := ![17,18,19,20,21,23,24]
def starMasks : Fin 7 → Nat := ![9472,17472,17024,4128,33536,61440,34880]
def nonlinear : List Nat := [640, 768, 1088, 1280, 2112, 4128, 8448, 9216, 9472, 12288, 16448, 16512, 16896, 17024, 17408, 17472, 20480, 24576, 28672, 32832, 33024, 33280, 33536, 34816, 34880, 36864, 40960, 45056, 49152, 53248, 57344, 61440]
def six : List Nat := [640, 768, 1088, 1280, 2112, 4128]
def localTarget (m : Nat) := edges.any fun e => m.testBit e.1 && m.testBit e.2
def sourceMask (w : Source) : Nat := if w.val<16 then 2^w.val else nonlinear.getD (w.val-16) 0
def visible (m : Nat) (w : Source) : Bool := decide (m &&& sourceMask w ≠ 0)
def bank (m : Nat) := List.ofFn (visible m)
def lo : Raw → Nat := ![512,1024,256,256,512,56705,56705,31554,46788,56705,31554,46788,60968,56705,46788,31554]
def hi : Raw → Nat := ![513,1026,260,264,528,56737,56769,31682,47044,57217,32578,48836,65064,64897,63172,64322]

theorem local_incidence : ∀ i j : Raw,
    ((i.val,j.val) ∈ edges ↔
     i.val<5 ∧ 5≤j.val ∧ ((label j).val,(label i).val)∈fullEdges) := by decide +kernel

theorem outside_incidence : ∀ (s : Fin 7) (i : Raw),
    ((starMasks s).testBit i.val = true ↔ ((label i).val,streets s)∈fullEdges) := by decide +kernel

-- Every nontrivial sub-OR of an exterior neighborhood is among the listed masks.
def genuine (m : Nat) := (List.range 16).filter (fun i => m.testBit i)
def pieces (s : Nat) := ((List.range 16).filter (fun i => s.testBit i)).sublists.map
  (fun sub => (sub.map (fun i => 2^i)).sum)
theorem exterior_bank : ∀ s : Fin 7, (pieces (starMasks s)).all (fun m =>
    decide ((genuine m).length ≤ 1 ∨ m ∈ nonlinear)) = true := by decide +kernel

theorem projected_bank : nonlinear.all (fun m =>
    let v := m % 8192
    decide ((genuine v).length ≤ 1 ∨ v ∈ six)) = true := by decide +kernel

theorem source_certificate : ∀ (i : Raw) (w : Source),
    (visible (lo i) w ≠ visible (hi i) w ↔ w.val=i.val) := by decide +kernel
theorem target_certificate : ∀ i : Raw, localTarget (lo i)=false ∧ localTarget (hi i)=true :=
  by decide +kernel

theorem raw_required (T : Finset Source)
    (hits : ∀ i : Raw, ∃ w ∈ T, visible (lo i) w ≠ visible (hi i) w) (i : Raw) :
    (⟨i.val,by omega⟩ : Source) ∈ T := by
  obtain ⟨w,hw,d⟩ := hits i
  have eq : w = (⟨i.val,by omega⟩ : Source) := Fin.ext ((source_certificate i w).mp d)
  simpa [eq] using hw

theorem physical (gs : List Gate) (root : Nat) (fan : ∀ g∈gs,g.inputs.length≤2)
    (ok : ∀ m : Nat,(run gs (bank m)).getD root false=localTarget m) :
    15 + inverters gs ≤ gs.length := by
  have atWire (m w : Nat) (h : w<48) :
      (bank m).getD w false=visible m ⟨w,h⟩ := by
    simp only [bank,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    simp [h]
  have same (m w : Nat) (h : 48≤w) : (bank m).getD w false=false := by
    apply List.getD_eq_default
    simpa [bank] using h
  have uniq (w : Nat) (i j : Raw)
      (a : (bank (lo i)).getD w false ≠ (bank (hi i)).getD w false)
      (b : (bank (lo j)).getD w false ≠ (bank (hi j)).getD w false) : i=j := by
    by_cases h : w<48
    · rw [atWire _ _ h,atWire _ _ h] at a b
      apply Fin.ext
      exact ((source_certificate i ⟨w,h⟩).mp a).symm.trans ((source_certificate j ⟨w,h⟩).mp b)
    · exact False.elim (a ((same _ _ (by omega)).trans (same _ _ (by omega)).symm))
  have hp := price (k:=16) (m:=48) (fun i=>bank (lo i)) (fun i=>bank (hi i))
    (fun i=>by simp [bank]) uniq gs fan root (fun i=>by
      rw [ok,ok,(target_certificate i).1,(target_certificate i).2]
      decide)
  have hm := mass_split gs
  omega
end Exterior9737

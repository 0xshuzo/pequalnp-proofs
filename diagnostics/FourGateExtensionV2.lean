import PEqualNP.Defs
namespace Extension9768
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

theorem trace (k m : Nat) (X Y : Fin k→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (S : Finset Nat) (sep : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+gs.length := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,sep,by simp⟩
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
    · let R := S.erase last ∪ g.inputs.toFinset
      have rsep : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := sep i
        by_cases eq : w=last
        · subst w
          by_contra! blocked
          have same : g.inputs.map (fun t => (V i).getD t false)=g.inputs.map (fun t => (W i).getD t false) := by
            apply List.map_congr_left
            intro t ht
            exact blocked t (Finset.mem_union_right _ (List.mem_toFinset.mpr ht))
          change (run (gs++[g]) (X i)).getD last false≠(run (gs++[g]) (Y i)).getD last false at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false≠(W i++[g.op.eval _]).getD last false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          exact diff (congrArg g.op.eval same)
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,st,card⟩ := ih old R rsep
      have maxfan := fan g (by simp)
      have len := List.toFinset_card_le g.inputs
      have union : R.card≤(S.erase last).card+g.inputs.toFinset.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_add_one mem
      exact ⟨T,st,by simp only [List.length_append,List.length_singleton]; omega⟩
    · have oldSep : separates V W S := by
        intro i
        obtain ⟨w,ws,h⟩ := sep i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) h⟩
      obtain ⟨T,st,card⟩ := ih old S oldSep
      exact ⟨T,st,by simp only [List.length_append,List.length_singleton]; omega⟩

theorem price {k m : Nat} (X Y : Fin k→List Bool) (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (unique : ∀ (w : Nat) (i j : Fin k),(X i).getD w false≠(Y i).getD w false →
       (X j).getD w false≠(Y j).getD w false → i=j)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (root : Nat) (correct : ∀ i,(run gs (X i)).getD root false≠(run gs (Y i)).getD root false) :
    k≤gs.length+1 := by
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
def flagF (x : Fin 42 → Bool) := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)
abbrev R := Fin 6
def lowMask : R→Nat := ![2,2097152,2097152,2097152,2097152,1]
def hiMask : R→Nat := ![2097154,2097154,2097168,2113536,2162688,67108865]
def input (m : Nat) (i : Fin 42) := m.testBit i.val
def pre : List Gate := [⟨.or,[3,10]⟩,⟨.or,[10,13]⟩,⟨.or,[0,10]⟩,⟨.or,[9,20]⟩,⟨.or,[11,42]⟩,⟨.or,[1,10]⟩,⟨.or,[1,3]⟩,⟨.or,[8,18]⟩,⟨.or,[8,48]⟩,⟨.or,[5,20]⟩,⟨.or,[17,19]⟩,⟨.or,[5,6]⟩,⟨.or,[7,12]⟩,⟨.or,[9,19]⟩,⟨.or,[3,4]⟩,⟨.or,[0,15]⟩,⟨.or,[14,20]⟩,⟨.or,[7,20]⟩,⟨.or,[49,51]⟩,⟨.or,[7,56]⟩,⟨.or,[15,18]⟩,⟨.or,[6,47]⟩,⟨.or,[12,19]⟩,⟨.or,[12,17]⟩,⟨.or,[6,14]⟩,⟨.or,[2,4]⟩,⟨.or,[11,13]⟩,⟨.or,[0,8]⟩,⟨.or,[7,11]⟩,⟨.or,[16,18]⟩,⟨.or,[52,61]⟩,⟨.and,[24,72]⟩,⟨.or,[0,53]⟩,⟨.or,[13,16]⟩,⟨.or,[54,75]⟩,⟨.or,[5,76]⟩,⟨.or,[69,70]⟩,⟨.or,[8,66]⟩,⟨.or,[43,67]⟩,⟨.or,[2,78]⟩,⟨.or,[55,74]⟩,⟨.and,[33,77]⟩,⟨.or,[18,65]⟩,⟨.or,[17,79]⟩,⟨.or,[4,60]⟩,⟨.or,[9,62]⟩,⟨.or,[2,3]⟩,⟨.or,[3,57]⟩,⟨.or,[2,64]⟩,⟨.or,[14,87]⟩,⟨.or,[59,63]⟩,⟨.or,[9,12]⟩,⟨.or,[8,19]⟩,⟨.or,[7,91]⟩,⟨.or,[9,80]⟩,⟨.or,[44,84]⟩,⟨.and,[38,97]⟩,⟨.and,[35,95]⟩,⟨.or,[50,93]⟩,⟨.or,[13,85]⟩,⟨.and,[25,86]⟩,⟨.or,[15,16]⟩,⟨.or,[58,90]⟩,⟨.and,[26,82]⟩,⟨.and,[30,96]⟩,⟨.and,[34,101]⟩,⟨.and,[27,92]⟩,⟨.or,[71,88]⟩,⟨.or,[1,68]⟩,⟨.or,[94,103]⟩,⟨.and,[29,100]⟩,⟨.and,[40,104]⟩,⟨.or,[5,14]⟩,⟨.or,[4,12]⟩,⟨.and,[28,81]⟩,⟨.or,[15,115]⟩,⟨.or,[6,117]⟩,⟨.or,[1,2]⟩,⟨.or,[11,16]⟩,⟨.or,[107,113]⟩,⟨.or,[5,119]⟩,⟨.or,[6,109]⟩,⟨.or,[10,111]⟩,⟨.or,[17,120]⟩,⟨.or,[13,89]⟩,⟨.or,[15,122]⟩,⟨.and,[23,123]⟩,⟨.or,[20,126]⟩,⟨.or,[19,110]⟩,⟨.or,[17,127]⟩,⟨.or,[11,118]⟩,⟨.or,[99,106]⟩,⟨.and,[32,132]⟩,⟨.or,[105,128]⟩,⟨.or,[45,125]⟩,⟨.or,[46,114]⟩,⟨.or,[98,112]⟩,⟨.and,[22,131]⟩,⟨.and,[36,124]⟩,⟨.or,[18,130]⟩,⟨.or,[138,140]⟩,⟨.and,[39,141]⟩,⟨.or,[121,133]⟩,⟨.and,[31,137]⟩,⟨.or,[135,144]⟩,⟨.and,[37,136]⟩,⟨.or,[83,143]⟩,⟨.or,[102,145]⟩,⟨.and,[41,129]⟩,⟨.or,[146,149]⟩,⟨.or,[147,148]⟩,⟨.or,[116,150]⟩,⟨.or,[73,139]⟩,⟨.or,[134,154]⟩,⟨.or,[153,155]⟩,⟨.or,[151,152]⟩,⟨.or,[142,157]⟩,⟨.or,[156,158]⟩,⟨.or,[108,159]⟩]

def X (i : R) := run pre (List.ofFn (input (lowMask i)))
def Y (i : R) := run pre (List.ofFn (input (hiMask i)))
theorem lengths : ∀ i,(X i).length=161 ∧ (Y i).length=161 := by decide +kernel
theorem outputs : ∀ i,flagF (input (lowMask i))≠flagF (input (hiMask i)) := by decide +kernel
theorem bankTable : ∀ (w : Fin 161) (i j : R),(X i).getD w.val false≠(Y i).getD w.val false →
    (X j).getD w.val false≠(Y j).getD w.val false → i=j := by decide +kernel
theorem augmented_price (tail : List Gate) (out : Nat)
    (fan : FanInTwo (⟨pre++tail,out⟩ : Circuit))
    (works : ∀ x : Fin 42→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=flagF x) :
    124≤(⟨pre++tail,out⟩ : Circuit).size := by
  have uniq (w : Nat) (i j : R) (h1 : (X i).getD w false≠(Y i).getD w false)
      (h2 : (X j).getD w false≠(Y j).getD w false) : i=j := by
    by_cases h : w<161
    · exact bankTable ⟨w,h⟩ i j h1 h2
    · exfalso; apply h1
      rw [List.getD_eq_default _ _ (by have := (lengths i).1; omega),
        List.getD_eq_default _ _ (by have := (lengths i).2; omega)]
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (x : Fin 42→Bool) : (run tail (run pre (List.ofFn x))).getD out false=flagF x := by
    have h := works x
    change ((pre++tail).foldl step (List.ofFn x)).getD out false=_ at h
    simpa only [run,List.foldl_append] using h
  have required := price X Y lengths uniq tail ft out (fun i => by
    change (run tail (run pre _)).getD out false≠(run tail (run pre _)).getD out false
    rw [sim,sim]
    exact outputs i)
  have plen : pre.length=119 := by decide
  change 124≤(pre++tail).length
  rw [List.length_append,plen]; omega
end Extension9768

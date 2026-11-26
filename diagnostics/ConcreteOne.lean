import PEqualNP.Defs
namespace Puncture9760
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
def target (x : Fin 42 → Bool) := (x 0 && x 21) || (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)

abbrev V := Fin 42 → Bool
abbrev J := Fin 7
def input (m : Nat) (w : Fin 42) := m.testBit w.val
def wire (u v z : Nat) (w : Fin 161) : Bool :=
  if w.val < 55 then u.testBit w.val else if w.val < 110 then v.testBit (w.val-55)
  else z.testBit (w.val-110)
def row (t : Nat × Nat × Nat) := List.ofFn (wire t.1 t.2.1 t.2.2)
def separated (X Y : J → Nat × Nat × Nat) : Prop :=
  ∀ (w : Fin 161) (i j : J),
    wire (X i).1 (X i).2.1 (X i).2.2 w ≠ wire (Y i).1 (Y i).2.1 (Y i).2.2 w →
    wire (X j).1 (X j).2.1 (X j).2.2 w ≠ wire (Y j).1 (Y j).2.1 (Y j).2.2 w → i=j

theorem result (pre : List Gate) (lo hi : J → Nat) (X Y : J → Nat × Nat × Nat)
    (xOK : ∀ i,run pre (List.ofFn (input (lo i))) = row (X i))
    (yOK : ∀ i,run pre (List.ofFn (input (hi i))) = row (Y i))
    (diff : ∀ i,target (input (lo i)) ≠ target (input (hi i))) (sep : separated X Y)
    (tail : List Gate) (root : Nat)
    (fan : FanInTwo (⟨pre++tail,root⟩ : Circuit))
    (works : ∀ x : V,(⟨pre++tail,root⟩ : Circuit).eval (List.ofFn x)=target x) :
    6+inverters tail≤tail.length := by
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (m : Nat) : (run tail (run pre (List.ofFn (input m)))).getD root false=target (input m) := by
    have h := works (input m)
    change ((pre++tail).foldl step (List.ofFn (input m))).getD root false=_ at h
    simpa only [run,List.foldl_append] using h
  have uniq (w : Nat) (i j : J)
      (a : (row (X i)).getD w false ≠ (row (Y i)).getD w false)
      (b : (row (X j)).getD w false ≠ (row (Y j)).getD w false) : i=j := by
    by_cases h : w<161
    · apply sep ⟨w,h⟩ i j
      · simpa [row,List.getD,h] using a
      · simpa [row,List.getD,h] using b
    · have z (t : Nat × Nat × Nat) : (row t).getD w false=false :=
        List.getD_eq_default _ _ (by simp [row]; omega)
      exact False.elim (a ((z _).trans (z _).symm))
  have bound := price (k:=7) (m:=161) (fun i=>row (X i)) (fun i=>row (Y i))
    (fun i=>by simp [row]) uniq tail ft root (fun i=>by
      change (run tail (row (X i))).getD root false ≠ (run tail (row (Y i))).getD root false
      rw [← xOK,← yOK,sim,sim]; exact diff i)
  have account := mass_split tail
  omega
namespace p0
def pre : List Gate := [⟨.or, [12,17]⟩,⟨.or, [7,20]⟩,⟨.or, [4,10]⟩,⟨.or, [0,9]⟩,⟨.or, [2,9]⟩,⟨.or, [3,7]⟩,⟨.or, [10,11]⟩,⟨.or, [3,8]⟩,⟨.or, [5,48]⟩,⟨.or, [17,19]⟩,⟨.or, [44,46]⟩,⟨.or, [11,19]⟩,⟨.or, [6,19]⟩,⟨.or, [5,16]⟩,⟨.or, [10,19]⟩,⟨.or, [6,43]⟩,⟨.or, [1,5]⟩,⟨.or, [6,16]⟩,⟨.or, [45,54]⟩,⟨.or, [19,20]⟩,⟨.or, [2,61]⟩,⟨.or, [9,14]⟩,⟨.or, [12,14]⟩,⟨.or, [15,56]⟩,⟨.or, [7,18]⟩,⟨.or, [8,17]⟩,⟨.or, [8,20]⟩,⟨.or, [5,18]⟩,⟨.or, [47,51]⟩,⟨.or, [13,18]⟩,⟨.or, [1,9]⟩,⟨.or, [0,8]⟩,⟨.or, [6,11]⟩,⟨.or, [14,50]⟩,⟨.or, [15,17]⟩,⟨.or, [12,49]⟩,⟨.or, [1,10]⟩,⟨.or, [9,20]⟩,⟨.or, [7,11]⟩,⟨.or, [4,69]⟩,⟨.or, [15,74]⟩,⟨.or, [57,78]⟩,⟨.or, [15,66]⟩,⟨.or, [72,77]⟩,⟨.or, [4,70]⟩,⟨.or, [2,80]⟩,⟨.and, [27,83]⟩,⟨.or, [0,3]⟩,⟨.or, [63,84]⟩,⟨.or, [68,81]⟩,⟨.or, [1,71]⟩,⟨.or, [3,59]⟩,⟨.or, [53,92]⟩,⟨.or, [16,17]⟩,⟨.and, [29,85]⟩,⟨.or, [0,18]⟩,⟨.or, [79,95]⟩,⟨.or, [10,97]⟩,⟨.or, [7,13]⟩,⟨.or, [13,52]⟩,⟨.or, [73,87]⟩,⟨.and, [25,91]⟩,⟨.or, [5,60]⟩,⟨.or, [42,99]⟩,⟨.and, [38,105]⟩,⟨.or, [6,14]⟩,⟨.and, [28,102]⟩,⟨.or, [12,55]⟩,⟨.or, [16,65]⟩,⟨.and, [26,104]⟩,⟨.or, [12,82]⟩,⟨.or, [11,98]⟩,⟨.and, [39,94]⟩,⟨.and, [37,113]⟩,⟨.or, [8,110]⟩,⟨.or, [13,107]⟩,⟨.or, [67,117]⟩,⟨.and, [24,86]⟩,⟨.or, [100,109]⟩,⟨.and, [35,90]⟩,⟨.or, [96,114]⟩,⟨.or, [3,75]⟩,⟨.or, [88,119]⟩,⟨.and, [33,120]⟩,⟨.or, [4,112]⟩,⟨.and, [34,118]⟩,⟨.or, [18,93]⟩,⟨.or, [2,128]⟩,⟨.or, [2,76]⟩,⟨.and, [31,123]⟩,⟨.and, [36,116]⟩,⟨.and, [30,101]⟩,⟨.or, [122,127]⟩,⟨.and, [23,129]⟩,⟨.or, [108,135]⟩,⟨.or, [124,131]⟩,⟨.or, [106,133]⟩,⟨.and, [32,126]⟩,⟨.or, [115,139]⟩,⟨.or, [62,64]⟩,⟨.or, [58,130]⟩,⟨.and, [22,142]⟩,⟨.or, [136,137]⟩,⟨.or, [125,140]⟩,⟨.or, [13,20]⟩,⟨.or, [15,146]⟩,⟨.and, [40,141]⟩,⟨.or, [132,143]⟩,⟨.or, [138,149]⟩,⟨.or, [148,150]⟩,⟨.or, [103,151]⟩,⟨.or, [89,147]⟩,⟨.and, [41,153]⟩,⟨.or, [145,154]⟩,⟨.or, [111,155]⟩,⟨.or, [121,156]⟩,⟨.or, [144,157]⟩,⟨.or, [134,158]⟩,⟨.or, [152,159]⟩]
def lo : J → Nat := ![1,2199096925568,2199079886400,1099782596200,1443379552872,575528797708,16]
def X : J → Nat × Nat × Nat := ![(35184372088833,1851594761306144,8796093022208),(15654846629944704,19409378098413062,2148345165),(33062314703855168,24445207338157878,2148345293),(27009503407285864,24345373543488831,9006548329933),(24454581981291112,23196383345099069,9006547281292),(6747178876831244,1926747997251046,9008695812173),(4521191813414928,70439678246912,65536)]
def hi : J → Nat := ![2097153,2199096925584,2199079902784,1099782661736,1443379552874,575528797709,33554448]
def Y : J → Nat × Nat × Nat := ![(35184374185985,1851594761306144,8796093022208),(15654846629944720,19409378098413062,2148345165),(33062314703871552,24445207338157878,2148345293),(27009503407351400,24345373543488831,9006548329933),(24454581981291114,23196383353487677,9006547281292),(6747178876831245,1931146044024294,9008695812173),(4521191846969360,351914654957568,1130297953419264)]
theorem charge (tail : List Gate) (root : Nat) (fan : FanInTwo (⟨pre++tail,root⟩ : Circuit))
    (works : ∀ x : V,(⟨pre++tail,root⟩ : Circuit).eval (List.ofFn x)=target x) :
    6+inverters tail≤tail.length :=
  result pre lo hi X Y (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold separated; decide +kernel) tail root fan works
end p0
end Puncture9760

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
abbrev R := Fin 40
def pre : List Gate := [⟨.and,[0,21]⟩,⟨.not,[42]⟩,⟨.or,[26,40]⟩,⟨.or,[24,44]⟩,⟨.or,[28,29]⟩,⟨.or,[24,38]⟩,⟨.or,[34,36]⟩,⟨.or,[25,46]⟩,⟨.or,[25,27]⟩,⟨.or,[35,36]⟩,⟨.or,[23,27]⟩,⟨.or,[33,38]⟩,⟨.or,[28,35]⟩,⟨.or,[39,41]⟩,⟨.or,[26,35]⟩,⟨.or,[29,32]⟩,⟨.or,[48,49]⟩,⟨.or,[31,37]⟩,⟨.or,[41,50]⟩,⟨.or,[36,39]⟩,⟨.or,[33,34]⟩,⟨.or,[23,38]⟩,⟨.or,[24,30]⟩,⟨.or,[33,54]⟩,⟨.and,[29,43]⟩,⟨.or,[32,52]⟩,⟨.or,[27,31]⟩,⟨.or,[22,66]⟩,⟨.or,[45,61]⟩,⟨.or,[27,65]⟩,⟨.or,[39,63]⟩,⟨.or,[30,62]⟩,⟨.or,[31,34]⟩,⟨.or,[23,41]⟩,⟨.or,[34,47]⟩,⟨.or,[24,71]⟩,⟨.or,[55,73]⟩,⟨.or,[22,25]⟩,⟨.or,[26,34]⟩,⟨.and,[7,77]⟩,⟨.or,[21,40]⟩,⟨.or,[21,25]⟩,⟨.and,[8,58]⟩,⟨.or,[40,57]⟩,⟨.or,[30,40]⟩,⟨.or,[25,35]⟩,⟨.or,[64,83]⟩,⟨.or,[26,38]⟩,⟨.or,[22,28]⟩,⟨.and,[13,78]⟩,⟨.or,[31,33]⟩,⟨.or,[23,90]⟩,⟨.or,[30,37]⟩,⟨.or,[26,92]⟩,⟨.or,[37,60]⟩,⟨.or,[56,94]⟩,⟨.or,[72,87]⟩,⟨.or,[29,97]⟩,⟨.or,[39,59]⟩,⟨.or,[74,82]⟩,⟨.or,[32,88]⟩,⟨.or,[21,37]⟩,⟨.or,[28,100]⟩,⟨.or,[53,85]⟩,⟨.and,[9,99]⟩,⟨.or,[24,75]⟩,⟨.or,[21,69]⟩,⟨.or,[40,96]⟩,⟨.or,[30,36]⟩,⟨.and,[4,102]⟩,⟨.or,[41,89]⟩,⟨.and,[20,109]⟩,⟨.and,[18,98]⟩,⟨.and,[12,105]⟩,⟨.or,[43,115]⟩,⟨.or,[27,108]⟩,⟨.or,[35,101]⟩,⟨.or,[32,104]⟩,⟨.or,[32,41]⟩,⟨.or,[38,110]⟩,⟨.or,[36,103]⟩,⟨.or,[42,115]⟩,⟨.or,[22,51]⟩,⟨.or,[22,37]⟩,⟨.and,[11,119]⟩]
def lo : Array Nat := #[67108864,2097152,4194304,8388608,4194304,8388608,134217728,2097152,4194304,2097152,4194304,16777216,2685436706978,295145406480,268435456,16777216,2749601236064,1555851903306,2097152,33554432,8388608,1073741824,67108864,79481274945,524019564622,33554432,2255663727648,563219678209,1229493110787,146071405571,3243488854020,1928222310464,1202626635849,696665555984,1202626635849,1393431775232,18839242881,172192969730,2216616792608,598144581896]
def hi : Array Nat := #[67108865,2097154,4194308,8388616,4194336,8388672,134218752,2113536,4227072,2162688,4325376,17301504,3235192520866,303735341072,268437504,16777344,2753896203360,1555868680522,2097168,34603008,8650752,1073750016,67109376,96661144129,525093306446,33554688,2255667921952,563488113665,1229560219651,146205623299,3243497242628,1962582048832,1202626639945,2895688811536,1203163506761,1393433872384,1118350870657,240912446466,2218764276256,873022488840]
def lower : Array Nat := #[88269879110978595586607820599984128,5898791497281617927605777354775855104,64052498576581357459053034816762019840,83239335829599484860454941713498112,64052498576581357459053034816762019840,83239335829599484860454941713498112,249879365545305014678478562254651392,5898791497281617927605777354775855104,64052498576581357459053034816762019840,5898791497281617927605777354775855104,64052498576581357459053034816762019840,83244079925500250788557826876768256,73862610729121258372230548679297089698,3910838826651156631655100611289514000,747711041180232697858306193359896576,83244079925500250788557826876768256,2249468581621516299397831988179190880,72865530043128957606896135120047046986,5898791497281617927605777354775855104,83731254061590965390939685658820608,83239335829599484860454941713498112,2742836698599257335809604609915224064,88269879110978595586607820599984128,83577075005041981314282840428496814657,72865527507717140423244760889864224846,83731254061590965390939685658820608,23849424939079813474499975105363903520,2244276328255835250962958583920215041,29660558460568572326597675125133281283,48600788482130597901874745681832887299,74029088781899362908523060068834361348,3912304409563888585240779815726972992,40377631502788027503455508680910448713,48772453727835807800298583103140578320,40377631502788027503455508680910448713,3247668845519215296431367534609008640,82913089658132169256016951649440893057,70205895142580932264641572747593397250,7898657773895360730465836787420369440,31825291075498664004772742232206868744]
def upper : Array Nat := #[88269879110978595586607820599984129,5898791497281617927605777354775855106,64052498576581357459053034816762019844,83239335829599484860454941713498120,64052498576581357459053034816762019872,83239335829599484860454941713498176,249879365545305014678478562254652416,5898791497281617927605777354775871488,64052498576581357459053034816762052608,5898791497281617927605777354775920640,64052498576581357459053034816762150912,83244079925500250788557826877292544,73862610729121258372230549229052903586,3910838826651156631655100619879448592,85818302771414848563701958051301951488,83244079927918102427787085226180736,2249468581621516446971784582150571104,72865692302405786820259526698074112330,5901387645710885341420042602940465168,94115847778660620648000678318309376,104008523263738795374576927030640640,2742836701075137414380365159713480704,88351008749393202268303609605128704,83577075005043190240102455074851390017,72865527507794511694146841231828713550,83731254080933778504773752454119680,66384720804197725870331608348926477344,2244276329493775290266353257597256705,29665750758046077173868895758979172355,48766941981603712681135626743854973955,74029088791802883222806102268035743748,25179952342122542551776002208423837760,40502246627392863366540240592811735113,50101681723620723674355313867051025424,40377631502788027503599694238267353161,8564590969863680613881807749358127104,82913089658132170436608626242921957505,72865649208365397719662444045146272770,7898659086111802373545388934942954016,31825291075498739571859981195751325960]
def label : Array Nat := #[0,1,2,3,18,4,5,15,25,22,6,14,32,21,7,8,9,10,20,11,19,35,26,30,17,40,28,29,27,34,24,38,16,13,23,31,37,40,39,12,36,33,40,40,36,36,34,39,37,40,40,31,40,40,27,40,31,34,40,38,33,37,40,39,24,40,40,16,29,40,36,40,40,40,40,40,39,40,40,26,23,15,40,40,25,40,24,40,40,28,27,21,38,30,40,38,40,40,40,40,38,40,40,35,40,40,22,17,40,40,37,18,28,19,20,32,32,29,40,40,33,37,35,40,31,26,14]

def sample (v : Nat) (i : Fin 42) := v.testBit i.val
def X (i : R) := run pre (List.ofFn (sample lo[i.val]!))
def Y (i : R) := run pre (List.ofFn (sample hi[i.val]!))
def decode (v : Nat) := List.ofFn fun w : Fin 127 => v.testBit w.val
theorem outputs : ∀ i : R,flagF (sample lo[i.val]!)≠flagF (sample hi[i.val]!) := by decide +kernel
theorem replay : ∀ i : R,X i=decode lower[i.val]! ∧ Y i=decode upper[i.val]! := by decide +kernel
theorem classify : ∀ (i : R) (w : Fin 127),lower[i.val]!.testBit w.val ≠ upper[i.val]!.testBit w.val →
    label[w.val]! = i.val := by decide +kernel
theorem lengths (i : R) : (X i).length=127 ∧ (Y i).length=127 := by
  rw [(replay i).1,(replay i).2];simp [decode]
theorem uniqueColumn (w : Nat) (i j : R) (h : (X i).getD w false≠(Y i).getD w false)
    (h' : (X j).getD w false≠(Y j).getD w false) : i=j := by
  by_cases wr : w<127
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
    (works : ∀ x : Fin 42→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=flagF x) :
    124≤(⟨pre++tail,out⟩ : Circuit).size := by
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (x : Fin 42→Bool) : (run tail (run pre (List.ofFn x))).getD out false=flagF x := by
    have h := works x
    change ((pre++tail).foldl step (List.ofFn x)).getD out false=_ at h
    simpa only [run,List.foldl_append] using h
  have required := price X Y lengths uniqueColumn tail ft out (fun i => by
    change (run tail (run pre _)).getD out false≠(run tail (run pre _)).getD out false
    rw [sim,sim]
    exact outputs i)
  have plen : pre.length=85 := by decide
  change 124≤(pre++tail).length
  rw [List.length_append,plen]; omega
end Extension9768

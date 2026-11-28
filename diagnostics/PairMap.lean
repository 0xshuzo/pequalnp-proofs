import PEqualNP.Defs
namespace Restore17601
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
abbrev I := Fin 13
def heads : List (List Nat) := [[],[0],[13],[0,1],[13,14],[0,13],[0,14]]
def rail (s : List Nat) (x : List Bool) := x ++ [s.any fun i => x.getD i false]
def test (s : List Nat) (C : Circuit) (P L : Finset I) (b : Bool) :=
  C.eval (rail s (incidenceInput P L) ++ [b])
def hit (p l u v : I) := decide (u=p ∧ v=l)
def Yes (C : Circuit) (s : List Nat) (p l : I) :=
  ∀ u v : I, u ∈ singerLines3 v → test s C {u} {v} (hit p l u v) = true
def No (C : Circuit) (s : List Nat) :=
  ∀ Q : Finset I, IsQuadrangle singerLines3 Q → test s C Q (missLines singerLines3 Q) false = false
def hdr (C : Circuit) (s : List Nat) (p l : I) : Circuit :=
  ⟨⟨.or,s⟩ :: ⟨.and,[p.val,13+l.val]⟩ :: C.gates,C.output⟩
theorem hsLen {s : List Nat} (hs : s ∈ heads) : s.length≤2 ∧ ∀ i∈s,i<26 := by
  have h : ∀ t ∈ heads, t.length≤2 ∧ ∀ i∈t,i<26 := by decide
  exact h s hs
end Restore17601
namespace Swap17601

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def route (n m : Nat) (π : Nat → Nat) (wire : Nat) : Nat :=
  if wire<n then π wire else wire-n+m

def replace (n m : Nat) (π : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (route n m π)⟩

def Rel (n m : Nat) (π : Nat → Nat) (a b : List Bool) : Prop :=
  n ≤ a.length ∧ b.length+n=a.length+m ∧ ∀ t, b.getD (route n m π t) false=a.getD t false

theorem step_rel {n m S : Nat} {π : Nat → Nat} (valid : ∀ i<n, π i<m ∨ π i=S)
    {a b : List Bool} (rel : Rel n m π a b) (bound : b.length < S) (g : Gate) :
    Rel n m π (step a g) (step b (replace n m π g)) := by
  obtain ⟨ha,hb,hh⟩ := rel
  have hv : (replace n m π g).op.eval ((replace n m π g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [replace,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hh i
  refine ⟨by simp [step]; omega,by simp [step]; omega,?_⟩
  intro t
  simp only [step,hv]
  rcases Nat.lt_trichotomy t a.length with h|h|h
  · rw [List.getD_append _ _ _ _ h]
    have loc : route n m π t < b.length ∨ route n m π t = S := by
      by_cases small : t<n
      · rw [route,if_pos small]
        rcases valid t small with hv|hv
        · exact Or.inl (by omega)
        · exact Or.inr hv
      · exact Or.inl (by simp [route,small]; omega)
    rcases loc with l|l
    · rw [List.getD_append _ _ _ _ l]; exact hh t
    · have k := hh t
      rw [l,List.getD_eq_default _ _ (by omega)] at k
      rw [l,List.getD_eq_default _ _ (by simp; omega)]
      exact k
  · have loc : route n m π t = b.length := by
      rw [route,if_neg (by omega)]; omega
    rw [loc,h]
    simp
  · have loc : b.length+1 ≤ route n m π t := by
      rw [route,if_neg (by omega)]; omega
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem fold_rel {n m S : Nat} {π : Nat → Nat} (valid : ∀ i<n, π i<m ∨ π i=S) (gs : List Gate) :
    ∀ (a b : List Bool), Rel n m π a b → b.length+gs.length≤S →
      Rel n m π (gs.foldl step a) ((gs.map (replace n m π)).foldl step b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h bound
    simp only [List.length_cons] at bound
    apply ih
    · exact step_rel valid h (by omega) g
    · simp [step]; omega

def reduced (n m : Nat) (π : Nat → Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (replace n m π),route n m π C.output⟩

theorem cost (n m : Nat) (π : Nat → Nat) (C : Circuit) : (reduced n m π C).size = C.size := by
  simp [Circuit.size,reduced]

theorem mono (n m : Nat) (π : Nat → Nat) {C : Circuit} (hm : Monotone2 C) :
    Monotone2 (reduced n m π C) := by
  intro g hg
  change g ∈ C.gates.map (replace n m π) at hg
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hg
  simpa [replace] using hm old ho

theorem evaluation {n m S : Nat} (π : Nat → Nat) (valid : ∀ i<n, π i<m ∨ π i=S)
    (C : Circuit) (cover : m+C.gates.length ≤ S) (a b : List Bool)
    (la : a.length=n) (lb : b.length=m)
    (hr : ∀ i<n, a.getD i false = b.getD (π i) false) :
    (reduced n m π C).eval b = C.eval a := by
  have r : Rel n m π a b := by
    refine ⟨by omega,by omega,?_⟩
    intro t
    by_cases h : t<n
    · simpa [route,h] using (hr t h).symm
    · rw [route,if_neg h,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
  exact (fold_rel valid C.gates a b r (by omega)).2.2 C.output

end Swap17601
namespace Restore17601
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover
def flip (i : Nat) := if i=26 then 27 else if i=27 then 26 else i
def tailC (C : Circuit) := Swap17601.reduced 28 28 flip C
def block (C : Circuit) (s : List Nat) : Circuit :=
  ⟨⟨.or,s⟩ :: (tailC C).gates,(tailC C).output⟩
theorem flipSmall (i : Nat) (h : i<28) : flip i<28 := by
  unfold flip
  split <;> (try split) <;> omega
theorem swapSize (C : Circuit) (s : List Nat) : (block C s).size=C.size+1 := by
  simp [block,tailC,Swap17601.reduced,Circuit.size]
theorem swapLegal {C : Circuit} {s : List Nat} (hs : s∈heads) (hm : Monotone2 C) :
    Monotone2 (block C s) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|h
  · exact ⟨Or.inr rfl,(hsLen hs).1⟩
  · exact Swap17601.mono 28 28 flip hm g h
theorem swapReads {C : Circuit} {s : List Nat} (hs : s∈heads) (hr : ReadsBack 28 C) :
    ReadsBack 27 (block C s) := by
  intro i hi w hw
  cases i with
  | zero => have := (hsLen hs).2 w hw; omega
  | succ j =>
    have hj : j<C.gates.length := by simpa [block,tailC,Swap17601.reduced] using hi
    have mem : w ∈ (C.gates[j].inputs.map (Swap17601.route 28 28 flip)) := by
      simpa [gateAt,block,tailC,Swap17601.reduced,Swap17601.replace,hj,List.getElem?_eq_getElem hj] using hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp mem
    have hh : u ∈ (gateAt C j).inputs := by simpa [gateAt,List.getElem?_eq_getElem hj] using hu
    have lim := hr j hj u hh
    by_cases small : u<28
    · have := flipSmall u small; simp only [Swap17601.route,if_pos small]; omega
    · simp only [Swap17601.route,if_neg small]; omega
theorem swapEval (C : Circuit) (s : List Nat) (hs : s∈heads) (P L : Finset I) (b : Bool) :
    (block C s).eval (incidenceInput P L ++ [b]) = test s C P L b := by
  let x := incidenceInput P L
  have lx : x.length=26 := by simp [x,incidenceInput]
  let o := s.any fun i=>x.getD i false
  have mx : (s.map fun i=>(x++[b]).getD i false) = (s.map fun i=>x.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact List.getD_append _ _ _ _ (by have := (hsLen hs).2 i hi; omega)
  have ho : GateOp.or.eval (s.map fun i=>(x++[b]).getD i false)=o := by
    rw [mx]
    simp [o,GateOp.eval,List.any_map,Function.comp_def]
  change (tailC C).eval ((x++[b])++[GateOp.or.eval (s.map fun i=>(x++[b]).getD i false)]) =
    C.eval ((x++[o])++[b])
  rw [ho]
  apply Swap17601.evaluation (S:=28+C.gates.length) flip (fun i h=>Or.inl (flipSmall i h)) C (by omega)
  · simp [lx]
  · simp [lx]
  · intro i hi
    by_cases low : i<26
    · have f : flip i=i := by simp [flip,show i≠26 by omega,show i≠27 by omega]
      rw [f,List.getD_append _ _ _ _ (by simp [lx]; omega),List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by simp [lx]; omega),List.getD_append _ _ _ _ (by omega)]
    · have z : i=26 ∨ i=27 := by omega
      rcases z with rfl|rfl <;> simp [flip,List.getD_eq_getElem?_getD,List.getElem?_append,lx]
theorem swapFacts (C : Circuit) (s : List Nat) (hs : s∈heads) (p l : I)
    (y : Yes C s p l) (n : No C s) :
    (∀ u v : I, u∈singerLines3 v → (u≠p ∨ v≠l) →
      (block C s).eval (incidenceInput {u} {v} ++ [false])=true) ∧
    (∀ Q : Finset I, IsQuadrangle singerLines3 Q →
      (block C s).eval (incidenceInput Q (missLines singerLines3 Q) ++ [false])=false) := by
  constructor
  · intro u v inc ne
    rw [swapEval C s hs]
    have hh : hit p l u v=false := decide_eq_false (fun h=>ne.elim (fun a=>a h.1) (fun a=>a h.2))
    simpa [hh] using y u v inc
  · intro Q hQ
    rw [swapEval C s hs]
    exact n Q hQ
end Restore17601
namespace Restore17601
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma cones_length (n : ℕ) (C : Circuit) :
    (cones n C).length = C.gates.length := by
  unfold cones coneStep
  rw [foldl_append_length]
  simp

private lemma cones_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (cones n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [cones_length]; exact hj

private lemma cones_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones coneStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => (w - n) :: pre.getD (w - n) [])) = _
  rw [hprelen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma inCone_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (i j : ℕ) :
    InCone n C i j ↔
      j < C.gates.length ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  constructor
  · intro hmem
    have hj : j < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [cones_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨hj, ?_⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap] at hmem
    rcases hmem with ⟨w, hw, hiw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    rw [List.mem_cons] at hiw
    exact ⟨w, hw.1, hw.2.1, hiw⟩
  · rintro ⟨hj, w, hw, hnw, hiw⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap]
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hw, hnw, hRB j hj w hw⟩
    · rw [List.mem_cons]
      exact hiw

theorem mappedGate {C : Circuit} (s : List Nat) {j : Nat} (hj : j<C.gates.length) :
    gateAt (block C s) (j+1) = Swap17601.replace 28 28 flip (gateAt C j) := by
  simp [gateAt,block,tailC,Swap17601.reduced,List.getD_eq_getElem?_getD,hj]
theorem mappedAnc {C : Circuit} {s : List Nat} (hs : s∈heads) (hr : ReadsBack 28 C) :
    ∀j i : Nat, InCone 27 (block C s) (i+1) (j+1) → InCone 28 C i j := by
  have rb:=swapReads hs hr
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i h
    obtain ⟨hj,w,hw,old,chain⟩ := (inCone_iff rb (i+1) (j+1)).mp h
    have jlt : j<C.gates.length := by simpa [block,tailC,Swap17601.reduced] using hj
    rw [mappedGate s jlt] at hw
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hw
    by_cases small : u<28
    · have wu : Swap17601.route 28 28 flip u=27 := by
        have := flipSmall u small; simp only [Swap17601.route,if_pos small] at *; omega
      rw [wu] at chain
      rcases chain with a|a
      · omega
      · obtain ⟨_,t,ht,htn,_⟩:=(inCone_iff rb (i+1) 0).mp a
        have := (hsLen hs).2 t ht; omega
    · have wu : Swap17601.route 28 28 flip u = u := by simp [Swap17601.route,small]; omega
      rw [wu] at chain
      apply (inCone_iff hr i j).mpr
      refine ⟨jlt,u,hu,by omega,?_⟩
      rcases chain with a|a
      · exact Or.inl (by omega)
      · apply Or.inr
        apply ih (u-28) (by have := hr j jlt u hu; omega) i
        rwa [show u-28+1=u-27 by omega]
theorem pairPrice {C : Circuit} {s : List Nat} (hs : s∈heads) (hr : ReadsBack 28 C) :
    andPairs 27 (block C s) ≤ andPairs 28 C := by
  let K := block C s
  let source (n : Nat) (D : Circuit) :=
    ((Finset.range D.gates.length ×ˢ Finset.range D.gates.length).filter fun p =>
      (gateAt D p.1).op = GateOp.and ∧ (gateAt D p.2).op = GateOp.and ∧ InCone n D p.1 p.2)
  change (source 27 K).card≤(source 28 C).card
  let f (p : Nat×Nat) := (p.1-1,p.2-1)
  have data {p : Nat×Nat} (hp : p∈source 27 K) : 0<p.1 ∧ 0<p.2 := by
    obtain ⟨_,a,b,_⟩:=Finset.mem_filter.mp hp
    have z : (gateAt K 0).op=GateOp.or := rfl
    constructor
    · by_contra! zero
      rw [show p.1=0 by omega,z] at a
      contradiction
    · by_contra! zero
      rw [show p.2=0 by omega,z] at b
      contradiction
  apply Finset.card_le_card_of_injOn f
  · rintro ⟨i,j⟩ hp
    obtain ⟨zi,zj⟩:=data hp
    obtain ⟨ij,oi,oj,c⟩:=Finset.mem_filter.mp hp
    obtain ⟨li,lj⟩:=Finset.mem_product.mp ij
    replace li:=Finset.mem_range.mp li
    replace lj:=Finset.mem_range.mp lj
    change i<(block C s).gates.length at li
    change j<(block C s).gates.length at lj
    simp only [block,tailC,Swap17601.reduced,List.length_cons,List.length_map] at li lj
    change 0<i at zi
    change 0<j at zj
    have ai : i-1<C.gates.length := by omega
    have aj : j-1<C.gates.length := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ai,Finset.mem_range.mpr aj⟩,?_,?_,?_⟩
    · have g:=congrArg Gate.op (mappedGate s ai)
      rw [show i-1+1=i by omega] at g
      exact g.symm.trans oi
    · have g:=congrArg Gate.op (mappedGate s aj)
      rw [show j-1+1=j by omega] at g
      exact g.symm.trans oj
    · apply mappedAnc hs hr (j-1) (i-1)
      rwa [show i-1+1=i by omega,show j-1+1=j by omega]
  · intro u hu v hv h
    obtain ⟨a,b⟩:=data hu
    obtain ⟨c,d⟩:=data hv
    have h1:=congrArg Prod.fst h
    have h2:=congrArg Prod.snd h
    apply Prod.ext <;> dsimp [f] at h1 h2 <;> omega
end Restore17601

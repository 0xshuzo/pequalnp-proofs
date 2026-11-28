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

import PEqualNP.Defs

set_option maxRecDepth 12000
namespace PEqualNP.Outside.L_meta_9838.Corner

inductive Tree (I : Type)
  | leaf (i : I)
  | meet (a b : Tree I)
  | join (a b : Tree I)

def Tree.uses {I : Type} (t : Tree I) (i : I) : Prop :=
  match t with
  | .leaf j => i = j
  | .meet a b | .join a b => a.uses i ∨ b.uses i

def Tree.uniqueAt {I : Type} (t : Tree I) (i : I) : Prop :=
  match t with
  | .leaf _ => True
  | .meet a b | .join a b =>
    a.uniqueAt i ∧ b.uniqueAt i ∧ (a.uses i → b.uses i → False)

def Tree.eval {I : Type} (t : Tree I) (v : I → Bool) : Bool :=
  match t with
  | .leaf i => v i
  | .meet a b => a.eval v && b.eval v
  | .join a b => a.eval v || b.eval v

def Tree.pick {I : Type} (t : Tree I) (p n : I → Bool) : I :=
  match t with
  | .leaf i => i
  | .meet a b => if a.eval n = false then a.pick p n else b.pick p n
  | .join a b => if a.eval p = true then a.pick p n else b.pick p n

theorem Tree.pick_uses {I : Type} (t : Tree I) (p n : I → Bool) :
    t.uses (t.pick p n) := by
  induction t with
  | leaf i => rfl
  | meet a b ha hb =>
    simp only [Tree.uses, Tree.pick]
    split
    · exact Or.inl ha
    · exact Or.inr hb
  | join a b ha hb =>
    simp only [Tree.uses, Tree.pick]
    split
    · exact Or.inl ha
    · exact Or.inr hb

theorem Tree.pick_sep {I : Type} (t : Tree I) (p n : I → Bool)
    (hp : t.eval p = true) (hn : t.eval n = false) :
    p (t.pick p n) = true ∧ n (t.pick p n) = false := by
  induction t with
  | leaf i => exact ⟨hp,hn⟩
  | meet a b ha hb =>
    cases ap : a.eval p <;> cases bp : b.eval p <;>
      cases an : a.eval n <;> cases bn : b.eval n <;>
      simp_all [Tree.eval, Tree.pick]
  | join a b ha hb =>
    cases ap : a.eval p <;> cases bp : b.eval p <;>
      cases an : a.eval n <;> cases bn : b.eval n <;>
      simp_all [Tree.eval, Tree.pick]

theorem Tree.rectangle {I : Type} (t : Tree I) (i : I) (h : t.uniqueAt i)
    (p q n m : I → Bool) (hp : t.pick p n = i) (hq : t.pick q m = i) :
    t.pick p m = i := by
  induction t with
  | leaf j => exact hp
  | meet a b ha hb =>
    obtain ⟨ua,ub,dis⟩ := h
    by_cases h1 : a.eval n = false <;> by_cases h2 : a.eval m = false
    · simp only [Tree.pick, if_pos h1, if_pos h2] at hp hq ⊢
      exact ha ua hp hq
    · simp only [Tree.pick, if_pos h1, if_neg h2] at hp hq ⊢
      exact (dis (hp ▸ a.pick_uses p n) (hq ▸ b.pick_uses q m)).elim
    · simp only [Tree.pick, if_neg h1, if_pos h2] at hp hq ⊢
      exact (dis (hq ▸ a.pick_uses q m) (hp ▸ b.pick_uses p n)).elim
    · simp only [Tree.pick, if_neg h1, if_neg h2] at hp hq ⊢
      exact hb ub hp hq
  | join a b ha hb =>
    obtain ⟨ua,ub,dis⟩ := h
    by_cases h1 : a.eval p = true <;> by_cases h2 : a.eval q = true
    · simp only [Tree.pick, if_pos h1, if_pos h2] at hp hq ⊢
      exact ha ua hp hq
    · simp only [Tree.pick, if_pos h1, if_neg h2] at hp hq ⊢
      exact (dis (hp ▸ a.pick_uses p n) (hq ▸ b.pick_uses q m)).elim
    · simp only [Tree.pick, if_neg h1, if_pos h2] at hp hq ⊢
      exact (dis (hq ▸ a.pick_uses q m) (hp ▸ b.pick_uses p n)).elim
    · simp only [Tree.pick, if_neg h1, if_neg h2] at hp hq ⊢
      exact hb ub hp hq

def forced {I : Type} (p n : I → Bool) (i : I) : Prop :=
  ∀ j, p j = true → n j = false → j = i

theorem Tree.private_pick {I : Type} (t : Tree I) {p n : I → Bool} {i : I}
    (hp : t.eval p = true) (hn : t.eval n = false) (h : forced p n i) :
    t.pick p n = i := by
  obtain ⟨a,b⟩ := t.pick_sep p n hp hn
  exact h _ a b

theorem Tree.private_overlap {I : Type} (t : Tree I) {i j : I} (hi : t.uniqueAt i) (hj : t.uniqueAt j)
    {a b c x y z : I → Bool}
    (ha : t.eval a = true) (hb : t.eval b = true) (hc : t.eval c = true)
    (hx : t.eval x = false) (hy : t.eval y = false) (hz : t.eval z = false)
    (ax : forced a x i) (byi : forced b y i)
    (az : forced a z j) (cy : forced c y j) :
    i = j := by
  have first := t.rectangle i hi a b x y (t.private_pick ha hx ax) (t.private_pick hb hy byi)
  have second := t.rectangle j hj a c z y (t.private_pick ha hz az) (t.private_pick hc hy cy)
  exact first.symm.trans second


abbrev Wire := Fin 154
def ops : List (Nat×Nat×Nat) := [(1,20,34),(1,21,40),(1,20,27),(1,35,31),(1,22,37),(1,24,38),(1,25,34),(1,33,26),(1,29,27),(1,28,37),(1,29,46),(1,23,31),(1,22,36),(1,24,29),(1,24,35),(1,36,28),(1,50,55),(1,23,33),(1,22,25),(1,23,38),(1,25,42),(1,36,57),(1,22,21),(1,35,26),(1,37,63),(1,21,26),(1,38,65),(1,39,62),(1,28,66),(1,21,61),(1,34,26),(1,37,60),(1,41,43),(1,34,45),(1,28,27),(1,32,52),(0,0,71),(1,32,21),(1,27,70),(1,38,27),(1,54,74),(1,37,69),(1,32,23),(1,39,59),(1,29,33),(1,25,35),(1,44,73),(1,36,79),(1,39,34),(1,39,31),(1,22,28),(0,17,81),(1,78,82),(0,15,72),(1,48,67),(1,29,30),(1,33,80),(1,20,90),(0,2,94),(1,64,95),(1,47,58),(1,23,97),(0,10,99),(1,32,89),(1,33,88),(0,7,92),(1,32,84),(1,30,101),(0,3,107),(1,93,108),(1,49,103),(0,9,56),(1,83,85),(0,19,112),(1,31,100),(1,51,53),(0,1,68),(1,91,113),(1,20,106),(0,8,96),(0,4,115),(0,18,86),(0,6,114),(1,102,116),(1,38,118),(0,13,124),(1,24,30),(1,119,120),(0,12,110),(1,121,128),(1,109,123),(1,30,104),(1,35,75),(0,16,132),(0,14,131),(1,30,87),(1,77,126),(1,76,98),(1,25,136),(1,125,130),(1,122,139),(1,31,135),(0,11,141),(0,5,138),(1,133,142),(1,111,143),(1,137,144),(1,117,146),(1,105,145),(1,127,147),(1,140,148),(1,129,150),(1,149,151),(1,134,152)]
def edges : List (Nat×Nat) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]
def rows : Fin 6 → Nat := ![1081344,34359771136,1048584,1048576,34359738376,32768]
def codes : Wire → Nat := ![0,0,0,20,0,0,0,0,0,0,0,0,0,0,0,35,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,13,13,13,18,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,13,0,0,18,18,0,0,0,0,0,0,13,31,0,0,0,0,0,0,0,18,0,0,0,0,18,0,0,0,0,0,0,0,3,0,0,18,13,0,18,0,13,0,0,0,0,0,13,4,7,0,0,18,0,0,0,0,0,13,0,0,0,0,0,13,0,0,0,0,0,7,0,18,0,0,0,0,0,0,7,7,0,0,0,0,0,0,0,0,0,7,7,7,7]
def sig (i : Fin 6) (w : Wire) : Bool := (codes w).testBit i.val
def run (i : Fin 6) (cut : Option Bool) : List Bool :=
  ops.foldl (fun v g =>
    let a := v.getD g.2.1 false
    let b := v.getD g.2.2 false
    let x := if g.1=0 then a && b else if g.1=1 then a || b else !a
    v++[if v.length=109 then cut.getD x else x])
    (List.ofFn (fun j : Fin 40 => (rows i).testBit j.val))
def target (i : Fin 6) := edges.any (fun e => (rows i).testBit e.1 && (rows i).testBit e.2)
def bank (i : Fin 6) (w : Wire) := (run i none).getD w.val false
def need (i : Fin 6) := decide (i.val<3)
theorem recorded : ∀i,run i none=List.ofFn (sig i) := by decide +kernel
theorem bankSig (i : Fin 6) : bank i=sig i := by
  funext w
  have get {n : Nat} (F : Fin n → Bool) (j : Fin n) : (List.ofFn F).getD j.val false=F j := by simp
  exact (congrArg (fun L : List Bool => L.getD w.val false) (recorded i)).trans (get (sig i) w)
theorem cares : ∀ (i : Fin 6) (b : Bool),
  (run i (some b)).getD 153 false=target i → b=need i := by decide +kernel
def offered : Finset Wire := Finset.univ.filter (fun w : Wire => !([109,130,139,140,150,151,152,153] : List Nat).contains w.val)
def escapes : Finset Wire := {40,41,42,60,71,72,93,97,101,107,108,118,124}
theorem thirteen : escapes.card=13 := by decide +kernel
theorem privateRows : ∀w∈offered,w∉escapes →
   (sig 0 w=true → sig 3 w=false → w=15) ∧ (sig 1 w=true → sig 4 w=false → w=15) ∧
   (sig 0 w=true → sig 5 w=false → w=20) ∧ (sig 2 w=true → sig 4 w=false → w=20) := by decide +kernel

theorem cutNeedsAlternate (t : Tree Wire) (up : t.uniqueAt 15) (uq : t.uniqueAt 20)
    (menu : ∀w,t.uses w → w∈offered)
    (repair : ∀i,(run i (some (t.eval (bank i)))).getD 153 false=target i) :
    ∃w,t.uses w ∧ w∈escapes := by
  by_contra fail
  have formal (i : Fin 6) : t.eval (sig i)=need i := by
    rw [←bankSig i]
    exact cares i _ (repair i)
  have recordedRows (p n : Fin 6) (hp : need p=true) (hn : need n=false) :
      sig p (t.pick (sig p) (sig n))=true ∧ sig n (t.pick (sig p) (sig n))=false :=
    t.pick_sep _ _ ((formal p).trans hp) ((formal n).trans hn)
  let privateAt := fun (p n : Fin 6) => privateRows (t.pick (sig p) (sig n))
    (menu _ (t.pick_uses _ _)) (fun h=>fail ⟨_,t.pick_uses _ _,h⟩)
  have ax := (privateAt 0 3).1 (recordedRows 0 3 (by decide) (by decide)).1 (recordedRows 0 3 (by decide) (by decide)).2
  have byp := (privateAt 1 4).2.1 (recordedRows 1 4 (by decide) (by decide)).1 (recordedRows 1 4 (by decide) (by decide)).2
  have az := (privateAt 0 5).2.2.1 (recordedRows 0 5 (by decide) (by decide)).1 (recordedRows 0 5 (by decide) (by decide)).2
  have cy := (privateAt 2 4).2.2.2 (recordedRows 2 4 (by decide) (by decide)).1 (recordedRows 2 4 (by decide) (by decide)).2
  have a := t.rectangle 15 up (sig 0) (sig 1) (sig 3) (sig 4) ax byp
  have b := t.rectangle 20 uq (sig 0) (sig 2) (sig 5) (sig 4) az cy
  exact (by decide : (15 : Wire)≠20) (a.symm.trans b)
end PEqualNP.Outside.L_meta_9838.Corner

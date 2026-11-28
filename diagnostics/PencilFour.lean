import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10009.Pencil
abbrev V := Fin 31
abbrev Box := Finset V × Finset V
def rows : Array Nat := #[1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736]
def picks : Array Nat := #[1,5,11,24,2,6,12,25,3,7,13,26,4,8,14,27,0,5,9,15,1,6,10,16,0,2,7,11,0,1,3,8,1,2,4,9,2,3,5,10,3,4,6,11,4,5,7,12,5,6,8,13,6,7,9,14,7,8,10,15,8,9,11,16,9,10,12,17,10,11,13,18,11,12,14,19,12,13,15,20,0,13,14,16,1,14,15,17,2,15,16,18,3,16,17,19,4,17,18,20,5,18,19,21,0,6,19,20,1,7,20,21,2,8,21,22,3,9,22,23,0,4,10,23]
def joins : Array Nat := #[4,7,6,7,30,4,26,6,7,4,30,6,7,20,20,4,20,6,7,26,26,20,26,30,30,20,30,26,4,4,6,7,0,8,7,8,0,5,27,7,8,5,0,7,8,21,21,5,21,7,8,27,27,21,27,0,0,21,0,27,5,5,6,8,1,9,8,9,1,6,28,8,9,6,1,8,9,22,22,6,22,8,9,28,28,22,28,1,1,22,1,28,6,7,7,9,2,10,9,10,2,7,29,9,10,7,2,9,10,23,23,7,23,9,10,29,29,23,29,2,2,23,2,29,30,8,8,10,3,11,10,11,3,8,30,10,11,8,3,10,11,24,24,8,24,10,11,30,30,24,30,3,3,24,3,4,0,9,9,11,0,12,11,12,4,9,0,11,12,9,4,11,12,25,25,9,25,11,12,0,0,25,0,4,4,25,26,5,1,10,10,12,1,13,12,13,5,10,1,12,13,10,5,12,13,26,26,10,26,12,13,1,1,26,1,5,5,6,27,6,2,11,11,13,2,14,13,14,6,11,2,13,14,11,6,13,14,27,27,11,27,13,14,2,2,27,2,6,7,7,28,7,3,12,12,14,3,15,14,15,7,12,3,14,15,12,7,14,15,28,28,12,28,14,15,3,3,28,3,4,8,8,29,8,4,13,13,15,4,16,15,16,8,13,4,15,16,13,8,15,16,29,29,13,29,15,16,4,4,29,30,5,9,9,30,9,5,14,14,16,5,17,16,17,9,14,5,16,17,14,9,16,17,30,30,14,30,16,17,5,5,6,0,6,10,10,0,10,6,15,15,17,0,18,17,18,10,15,6,17,18,15,10,17,18,0,0,15,0,17,18,6,7,7,1,7,11,11,1,11,7,16,16,18,1,19,18,19,11,16,7,18,19,16,11,18,19,1,1,16,1,18,19,20,8,8,2,8,12,12,2,12,8,17,17,19,2,20,19,20,12,17,8,19,20,17,12,19,20,2,2,17,2,19,20,21,9,9,3,9,13,13,3,13,9,18,18,20,3,21,20,21,13,18,9,20,21,18,13,20,21,3,3,18,3,4,21,22,10,10,4,10,14,14,4,14,10,19,19,21,4,22,21,22,14,19,10,21,22,19,14,21,22,4,4,19,20,5,22,23,11,11,5,11,15,15,5,15,11,20,20,22,5,23,22,23,15,20,11,22,23,20,15,22,23,5,5,6,21,6,23,24,12,12,6,12,16,16,6,16,12,21,21,23,6,24,23,24,16,21,12,23,24,21,16,23,24,6,7,7,22,7,24,25,13,13,7,13,17,17,7,17,13,22,22,24,7,25,24,25,17,22,13,24,25,22,17,24,25,26,8,8,23,8,25,26,14,14,8,14,18,18,8,18,14,23,23,25,8,26,25,26,18,23,14,25,26,23,18,25,26,27,9,9,24,9,26,27,15,15,9,15,19,19,9,19,15,24,24,26,9,27,26,27,19,24,15,26,27,24,19,20,27,28,10,10,25,10,27,28,16,16,10,16,20,20,10,20,16,25,25,27,10,28,27,28,20,25,16,27,28,25,26,21,28,29,11,11,26,11,28,29,17,17,11,17,21,21,11,21,17,26,26,28,11,29,28,29,21,26,17,28,29,30,27,22,29,30,12,12,27,12,29,30,18,18,12,18,22,22,12,22,18,27,27,29,12,30,29,30,22,27,18,29,30,0,28,23,30,0,13,13,28,13,30,0,19,19,13,19,23,23,13,23,19,28,28,30,0,0,30,0,23,28,19,20,0,1,29,24,0,1,14,14,29,14,0,1,20,20,14,20,24,24,14,24,20,29,29,0,0,1,0,1,24,29,30,21,1,2,30,25,1,2,15,15,30,15,1,2,21,21,15,21,25,25,15,25,21,30,30,1,1,2,1,2,25,26,0,22,2,3,0,26,2,3,16,16,0,16,2,3,22,22,16,22,26,26,16,26,22,0,0,2,0,3,2,3,4,27,1,23,3,4,1,27,3,4,17,17,1,17,3,4,23,23,17,23,27,27,17,27,23,1,1,3,1,4,3,4,5,28,2,24,4,5,2,28,4,5,18,18,2,18,4,5,24,24,18,24,28,28,18,28,24,2,2,4,2,5,6,5,6,29,3,25,5,6,3,29,5,6,19,19,3,19,5,6,25,25,19,25,29,29,19,29,25,3,3,5,3]
def asV (n : Nat) : V := ⟨n % 31,Nat.mod_lt _ (by decide)⟩
def incidence (p h : V) := (rows[p.val]!).testBit h.val
def onLine (h : V) (i : Fin 4) := asV (picks[4*h.val+i.val]!)
def through (p x : V) := asV (joins[31*p.val+x.val]!)
def legal (B : Box) := ∀ x ∈ B.1, ∀ l ∈ B.2, incidence x l = false
def full {k : Nat} (c : Fin k → Box) := ∀ x l, incidence x l = false →
  ∃ t, x ∈ (c t).1 ∧ l ∈ (c t).2
def meets (B : Box) (h : V) := ∃ x ∈ B.1, incidence x h = true

theorem rowFact : ∀ h : V, ∀ i : Fin 4, incidence (onLine h i) h = true := by decide +kernel
set_option maxRecDepth 5000 in
theorem lineFact : ∀ p h : V, incidence p h = false → ∀ i : Fin 4,
    incidence p (through p (onLine h i)) = true := by decide +kernel
set_option maxRecDepth 5000 in
theorem crown : ∀ p h : V, incidence p h = false → ∀ i j : Fin 4,
    incidence (onLine h i) (through p (onLine h j)) = decide (i=j) := by decide +kernel

def bothWays (x y : Fin 8) : Bool :=
  (List.finRange 3).any (fun b => x.val.testBit b.val && !y.val.testBit b.val)
theorem antichain (a b c d : Fin 8) :
    ¬ (bothWays a b && bothWays b a && bothWays a c && bothWays c a &&
       bothWays a d && bothWays d a && bothWays b c && bothWays c b &&
       bothWays b d && bothWays d b && bothWays c d && bothWays d c) = true := by
  revert a b c d
  decide +kernel
def code (g : Fin 3 → Bool) : Fin 8 :=
  ⟨(if g 0 then 1 else 0) + (if g 1 then 2 else 0) + (if g 2 then 4 else 0), by
    split <;> split <;> split <;> decide⟩
private theorem evalCode (g : Fin 3 → Bool) (t : Fin 3) :
    (code g).val.testBit t.val = g t := by
  fin_cases t <;> cases h0 : g 0 <;> cases h1 : g 1 <;> cases h2 : g 2 <;>
    simp [code,h0,h1,h2] <;> decide
private theorem impossible (g : Fin 4 → Fin 3 → Bool)
    (sep : ∀ a b, a ≠ b → ∃ t, g a t = true ∧ g b t = false) : False := by
  have facts (a b : Fin 4) (h : a ≠ b) : bothWays (code (g a)) (code (g b)) = true := by
    obtain ⟨t,ht,hs⟩ := sep a b h
    apply List.any_eq_true.mpr
    exact ⟨t,by simp, by simp [evalCode,ht,hs]⟩
  exact (antichain (code (g 0)) (code (g 1)) (code (g 2)) (code (g 3))) (by
    simp [facts _ _ (by decide : (0:Fin 4) ≠ 1), facts _ _ (by decide : (1:Fin 4) ≠ 0),
      facts _ _ (by decide : (0:Fin 4) ≠ 2), facts _ _ (by decide : (2:Fin 4) ≠ 0),
      facts _ _ (by decide : (0:Fin 4) ≠ 3), facts _ _ (by decide : (3:Fin 4) ≠ 0),
      facts _ _ (by decide : (1:Fin 4) ≠ 2), facts _ _ (by decide : (2:Fin 4) ≠ 1),
      facts _ _ (by decide : (1:Fin 4) ≠ 3), facts _ _ (by decide : (3:Fin 4) ≠ 1),
      facts _ _ (by decide : (2:Fin 4) ≠ 3), facts _ _ (by decide : (3:Fin 4) ≠ 2)])

theorem fourth {k : Nat} (c : Fin k → Box) (law : ∀ t, legal (c t)) (cover : full c)
    (p h : V) (off : incidence p h = false) (three : Fin 3 → Fin k) :
    ∃ t, (∀ b, t ≠ three b) ∧ meets (c t) h ∧ p ∉ (c t).1 ∧
        ∃ l ∈ (c t).2, incidence p l = true := by
  classical
  by_contra avoid
  let g (i : Fin 4) (b : Fin 3) := decide (onLine h i ∈ (c (three b)).1)
  apply impossible g
  intro i j diff
  have zero := crown p h off i j
  simp only [diff, decide_false] at zero
  obtain ⟨t,pt,lt⟩ := cover _ _ zero
  have id : ∃ b, t = three b := by
    by_contra no
    apply avoid
    refine ⟨t, fun b eq => no ⟨b,eq⟩, ⟨_,pt,rowFact h i⟩, ?_, _,lt,lineFact p h off j⟩
    intro bad
    have u := law t p bad _ lt
    rw [lineFact p h off j] at u
    contradiction
  obtain ⟨b,rfl⟩ := id
  refine ⟨b, by simpa [g] using pt, ?_⟩
  have no : onLine h j ∉ (c (three b)).1 := by
    intro a
    have u := law _ _ a _ lt
    rw [crown p h off j j] at u
    contradiction
  simpa [g] using no

theorem pureFourth {k : Nat} (c : Fin k → Box) (law : ∀ t, legal (c t)) (cover : full c)
    (h : V) (t : Fin k) (other : Fin 3 → Fin k)
    (exhaust : ∀ s, meets (c s) h → s=t ∨ ∃ b, s=other b) :
    ∀ p ∈ (c t).1, incidence p h = true := by
  intro p member
  cases e : incidence p h with
  | true => rfl
  | false =>
    obtain ⟨s,aside,touch,out,_⟩ := fourth c law cover p h e other
    rcases exhaust s touch with eq | ⟨b,eq⟩
    · exact False.elim (out (eq.symm ▸ member))
    · exact False.elim (aside b eq)
end PEqualNP.Outside.L_meta_10009.Pencil

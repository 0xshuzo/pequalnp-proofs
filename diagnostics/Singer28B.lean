import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.Singer
open Finset
abbrev V := Fin 31
abbrev H := Fin 6
def mat : Array Nat := #[1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736]
def leftBox : Array Nat := #[151055113,201373989,17416549,197201,427073,3309825]
def rightBox : Array Nat := #[184551458,696262688,688062468,437142021,939821325,537274663]
def forbidden : Array Nat := #[2134752510,973078428,1995437934,1995437934,2134752510,973078428]
def rootWitness : Array Nat := #[0,490,430,461,5,404,290,1,0,0,104,346,842,303,0,259,771,0,848,489,25,745,0,0,273,98,275,280,365,366,458,0,0,494,182,399,0,0,67,261,346,488,365,842,408,833,354,401,385,23,489,13,168,89,5,835,0,0,271,86,430,0,0,513,277,182,0,773,250,0,272,467,492,0,29,215,605,17,498,157,760,79,0,172,210,16,0,89,613,0,86,213,481,0,545,205,279,0,293,186,0,529,306,515,0,496,536,28,17,498,541,151,126,0,195,18,304,0,25,133,0,214,141,513,0,586,527,558,312,468,194,530,0,0,328,535,585,15,0,483,3,0,560,201,186,8,0,0,321,2,339,197,493,494,554,0,0,527,628,656,0,0,483,261,538,8,13,649,651,1,466,2,545,248,265,622,680,250,5,259,0,0,528,532,494,0]
def part : Array Nat := #[17152,33554466,1048720,1048720,17152,33554466]

def gap (a b : V) : ℕ := (b.val + 31 - a.val) % 31
def ban (h : H) (a b : V) := forbidden[h.val]!.testBit (gap a b)
def tint (h : H) (a b : V) : Fin 3 :=
  if a=b then 0 else if part[h.val]!.testBit (gap a b) then 1 else 2
def incident (p l : V) := mat[p.val]!.testBit l.val
def hits (h : H) (a p l : V) :=
  leftBox[h.val]!.testBit (gap a p) && rightBox[h.val]!.testBit (gap a l)
def wr (h : H) (a b : V) : V := ⟨((rootWitness[31*h.val+gap a b]! / 31) + a.val) % 31, by omega⟩
def wc (h : H) (a b : V) : V := ⟨(rootWitness[31*h.val+gap a b]! % 31 + a.val) % 31, by omega⟩

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem pairs : ∀ h a b, ban h a b = true →
    incident (wr h a b) (wc h a b) = false ∧
      ∀ t, hits h t (wr h a b) (wc h a b) = true → t=a ∨ t=b := by
  intro h
  fin_cases h <;> decide +kernel

theorem coloring : ∀ h a b c, ban h a b = false → ban h a c = false →
    ban h b c = false → tint h a b=tint h a c → b=c := by
  intro h
  fin_cases h <;> decide +kernel

theorem minimum (h : H) (S : Finset V)
    (cover : ∀ p l, incident p l = false → ∃ t ∈ S, hits h t p l = true) : 28 ≤ S.card := by
  classical
  let missing : Finset V := univ \ S
  have safe {a b : V} (ha : a ∈ missing) (hb : b ∈ missing) : ban h a b = false := by
    cases e : ban h a b with
    | false => rfl
    | true =>
      obtain ⟨z, who⟩ := pairs h a b e
      obtain ⟨t,ht,hitsT⟩ := cover _ _ z
      rcases who t hitsT with rfl | rfl
      · exact False.elim ((mem_sdiff.mp ha).2 ht)
      · exact False.elim ((mem_sdiff.mp hb).2 ht)
  have ub : missing.card ≤ 3 := by
    by_cases ne : missing.Nonempty
    · obtain ⟨a,ha⟩ := ne
      have inj : Set.InjOn (tint h a) (missing : Set V) := fun b hb c hc eq =>
        coloring h a b c (safe ha hb) (safe ha hc) (safe hb hc) eq
      calc
        _ = (missing.image (tint h a)).card := (card_image_of_injOn inj).symm
        _ ≤ (univ : Finset (Fin 3)).card := card_le_card (subset_univ _)
        _ = 3 := by decide
    · simp [Finset.not_nonempty_iff_eq_empty.mp ne]
  change (univ \ S).card ≤ 3 at ub
  rw [card_sdiff, inter_univ] at ub
  simp only [card_univ, Fintype.card_fin] at ub
  omega

end PEqualNP.Outside.L_meta_10007.Singer

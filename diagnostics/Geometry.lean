import PEqualNP.Defs

namespace Board5278
open PEqualNP.HeptadCover
abbrev V := Fin 13
abbrev Row := Fin 18 × V
def pTab : Array Nat := #[29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549]
def lTab : Array Nat := #[2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184]
def pt (r : Row) (p : V) : Bool := (pTab[r.1.val]!).testBit (p-r.2).val
def ln (r : Row) (l : V) : Bool := (lTab[r.1.val]!).testBit (l-r.2).val
def P (p : V) : Finset Row := Finset.univ.filter fun r => pt r p
def L (p : V) : Finset Row := Finset.univ.filter fun r => ln r p
def points (r : Row) : Finset V := Finset.univ.filter fun p => pt r p
def move (s : V) (r : Row) : Row := (r.1,r.2+s)
lemma ptMove (r : Row) (s i : V) : pt (move s r) (i+s) = pt r i := by
  simp [pt,move]
lemma lnMove (r : Row) (s i : V) : ln (move s r) (i+s) = ln r i := by
  simp [ln,move]
theorem allQuads : ∀ r : Row, IsQuadrangle singerLines3 (points r) := by decide +kernel
theorem miss : ∀ (r : Row) (l : V), (ln r l=true) ↔ l∈missLines singerLines3 (points r) := by decide +kernel
theorem outside : ∀ (r : Row) (p : V), pt r p=false →
    ∃ l : V, ln r l=true ∧ p∈singerLines3 l := by decide +kernel
theorem apartBase : ∀ (i j : Fin 18) (s : V), (i,(0:V)) ≠ (j,s) →
    ∃ p : V, pt (i,0) p=true ∧ pt (j,s) p=false := by decide +kernel
theorem apart (a b : Row) (hne : a ≠ b) : ∃ p : V, pt a p=true ∧ pt b p=false := by
  obtain ⟨i,t⟩ := a
  obtain ⟨j,u⟩ := b
  have diff : (i,(0:V)) ≠ (j,u-t) := by
    intro h
    have f := congrArg (move t) h
    exact hne (by simpa only [move,zero_add,sub_add_cancel] using f)
  obtain ⟨p,hp,hn⟩ := apartBase i j (u-t) diff
  refine ⟨p+t,?_,?_⟩
  · simpa only [move,zero_add] using (ptMove (i,0) t p).trans hp
  · simpa only [move,sub_add_cancel] using (ptMove (j,u-t) t p).trans hn

def shifted (s : V) (X : Finset Row) : Finset Row := X.image (move s)
lemma injMove (s : V) : Function.Injective (move s) := by
  rintro ⟨i,t⟩ ⟨j,u⟩ h
  have eq := congrArg (move (-s)) h
  simpa [move] using eq
lemma shiftP (s i : V) : shifted s (P i) = P (i+s) := by
  ext r
  constructor
  · intro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,ptMove] at ht ⊢
    exact ht
  · intro h
    refine Finset.mem_image.mpr ⟨move (-s) r,?_,by rcases r with ⟨a,b⟩; simp [move]⟩
    have e := ptMove r (-s) (i+s)
    simpa [P] using (e.trans (Finset.mem_filter.mp h).2)
lemma shiftL (s i : V) : shifted s (L i) = L (i+s) := by
  ext r
  constructor
  · intro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,lnMove] at ht ⊢
    exact ht
  · intro h
    refine Finset.mem_image.mpr ⟨move (-s) r,?_,by rcases r with ⟨a,b⟩; simp [move]⟩
    have e := lnMove r (-s) (i+s)
    simpa [L] using (e.trans (Finset.mem_filter.mp h).2)
lemma shiftUnion (s : V) (X Y : Finset Row) : shifted s (X∪Y)=shifted s X∪shifted s Y :=
  by simp [shifted,Finset.image_union]
lemma shiftInter (s : V) (X Y : Finset Row) : shifted s (X∩Y)=shifted s X∩shifted s Y := by
  exact Finset.image_inter _ _ (injMove s)
lemma shiftCard (s : V) (X : Finset Row) : (shifted s X).card=X.card :=
  Finset.card_image_of_injective _ (injMove s)

theorem point0 : (P 0).card ≤ 99 := by decide +kernel
theorem lines0 : ∀ l : V, (L 0 ∪ L l).card ≤ 99 := by decide +kernel
theorem pp0 : ∀ p : V, 18 ≤ (P 0 ∩ P p).card := by decide +kernel
theorem ll0 : ∀ l : V, 9 ≤ (L 0 ∩ L l).card := by decide +kernel
theorem mixed0 : ∀ l : V, (0 : V) ∉ singerLines3 l → 24 ≤ (P 0 ∩ L l).card := by decide +kernel
theorem incident0 : ∀ l : V, (0 : V) ∈ singerLines3 l → P 0 ∩ L l = ∅ := by decide +kernel
theorem twoPts0 : ∀ a b : V, a≠b → 24 ≤ (P 0 ∩ (P a ∪ P b)).card := by decide +kernel
theorem thin : ∀ a b i j : V, a≠b → i≠j → a∈singerLines3 i → a∈singerLines3 j →
    b∈singerLines3 i → b∉singerLines3 j := by decide +kernel

set_option maxHeartbeats 2000000 in
private theorem threes0 : ∀ b c : V, (0:V)≠b → (0:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 0 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes1 : ∀ b c : V, (1:V)≠b → (1:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 1 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes2 : ∀ b c : V, (2:V)≠b → (2:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 2 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes3 : ∀ b c : V, (3:V)≠b → (3:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 3 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes4 : ∀ b c : V, (4:V)≠b → (4:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 4 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes5 : ∀ b c : V, (5:V)≠b → (5:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 5 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes6 : ∀ b c : V, (6:V)≠b → (6:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 6 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes7 : ∀ b c : V, (7:V)≠b → (7:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 7 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes8 : ∀ b c : V, (8:V)≠b → (8:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 8 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes9 : ∀ b c : V, (9:V)≠b → (9:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 9 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes10 : ∀ b c : V, (10:V)≠b → (10:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 10 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes11 : ∀ b c : V, (11:V)≠b → (11:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 11 ∪ L b) ∪ L c)).card := by decide +kernel
set_option maxHeartbeats 2000000 in
private theorem threes12 : ∀ b c : V, (12:V)≠b → (12:V)≠c → b≠c → 24 ≤ (L 0 ∩ ((L 12 ∪ L b) ∪ L c)).card := by decide +kernel
theorem threeLs0 : ∀ a b c : V, a≠b → a≠c → b≠c → 24 ≤ (L 0 ∩ ((L a∪L b)∪L c)).card := by
  intro a
  fin_cases a <;> first
  | exact threes0
  | exact threes1
  | exact threes2
  | exact threes3
  | exact threes4
  | exact threes5
  | exact threes6
  | exact threes7
  | exact threes8
  | exact threes9
  | exact threes10
  | exact threes11
  | exact threes12
end Board5278

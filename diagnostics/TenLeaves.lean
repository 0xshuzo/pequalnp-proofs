import PEqualNP.Defs

namespace Split9755

def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def pins (l r : Nat) : Fin 10 → Bool := ![l.testBit 0,r.testBit 0,l.testBit 1,l.testBit 2,r.testBit 1,r.testBit 2,l.testBit 3,l.testBit 4,r.testBit 3,r.testBit 4]
def board (l r : Nat) := graph (pins l r)
def yes : Fin 7 → Nat × Nat := ![(6,0),(24,8),(17,17),(4,2),(3,1),(1,5),(0,12)]
theorem yesDiag : ∀ i, board (yes i).1 (yes i).2 = true := by decide +kernel
theorem yesCross : ∀ i j, i≠j → board (yes i).1 (yes j).2 ≠ true ∨ board (yes j).1 (yes i).2 ≠ true := by decide +kernel
def no : Fin 13 → Nat × Nat := ![(9,0),(20,1),(24,2),(12,4),(8,6),(17,9),(16,3),(5,17),(4,5),(3,24),(2,20),(1,25),(0,7)]
theorem noDiag : ∀ i, board (no i).1 (no i).2 = false := by decide +kernel
theorem noCross : ∀ i j, i≠j → board (no i).1 (no j).2 ≠ false ∨ board (no j).1 (no i).2 ≠ false := by decide +kernel

theorem price {k b : Nat} {t : Bool} {p : Fin k → Nat × Nat}
    (diag : ∀ i,board (p i).1 (p i).2=t)
    (cross : ∀ i j,i≠j → board (p i).1 (p j).2≠t ∨ board (p j).1 (p i).2≠t)
    (L R : Fin b → Nat → Prop)
    (safe : ∀ c l r,L c l → R c r → board l r=t)
    (cover : ∀ l r,board l r=t → ∃ c,L c l ∧ R c r) : k≤b := by
  classical
  have each (i : Fin k) := cover (p i).1 (p i).2 (diag i)
  let tag (i : Fin k) := (each i).choose
  have hit (i : Fin k) : L (tag i) (p i).1 ∧ R (tag i) (p i).2 := (each i).choose_spec
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have a := hit i
    have d := hit j
    rw [←eq] at d
    rcases cross i j ne with h|h
    · exact h (safe _ _ _ a.1 d.2)
    · exact h (safe _ _ _ d.1 a.2)
  simpa using Fintype.card_le_of_injective tag inj

theorem both {k m : Nat} (L R : Fin k → Nat → Prop) (P Q : Fin m → Nat → Prop)
    (one : ∀ l r,board l r=true ↔ ∃ i,L i l ∧ R i r)
    (zero : ∀ l r,board l r=false ↔ ∃ j,P j l ∧ Q j r) : 7≤k ∧ 13≤m := by
  exact ⟨price yesDiag yesCross L R (fun i l r a b => (one l r).2 ⟨i,a,b⟩)
      (fun l r => (one l r).1),
    price noDiag noCross P Q (fun i l r a b => (zero l r).2 ⟨i,a,b⟩)
      (fun l r => (zero l r).1)⟩

end Split9755
namespace Split9755

inductive Tree where
  | left (f : Nat → Bool) | right (f : Nat → Bool)
  | meet (a b : Tree) | join (a b : Tree) | neg (a : Tree)

def Tree.value : Tree → Nat → Nat → Bool
  | .left f,x,_ => f x
  | .right f,_,y => f y
  | .meet a b,x,y => a.value x y && b.value x y
  | .join a b,x,y => a.value x y || b.value x y
  | .neg a,x,y => !(a.value x y)

abbrev Rct := (Nat → Prop) × (Nat → Prop)
def Hit (P : List Rct) (x y : Nat) := ∃ p∈P,p.1 x ∧ p.2 y
def prodTable (P Q : List Rct) : List Rct := P.flatMap (fun p=>Q.map (fun q=>
  (fun x=>p.1 x ∧ q.1 x,fun y=>p.2 y ∧ q.2 y)))
theorem hitProduct (P Q : List Rct) (x y : Nat) :
    Hit (prodTable P Q) x y ↔ Hit P x y ∧ Hit Q x y := by
  constructor
  · rintro ⟨t,ht,hl,hr⟩
    obtain ⟨a,ha,bm⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp bm
    exact ⟨⟨a,ha,hl.1,hr.1⟩,⟨b,hb,hl.2,hr.2⟩⟩
  · rintro ⟨⟨a,ha,la,ra⟩,⟨b,hb,lb,rb⟩⟩
    exact ⟨_,List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩,
      ⟨la,lb⟩,⟨ra,rb⟩⟩

theorem hitUnion (P Q : List Rct) (x y : Nat) :
    Hit (P++Q) x y ↔ Hit P x y ∨ Hit Q x y := by
  constructor
  · rintro ⟨t,ht,yes⟩
    rcases List.mem_append.mp ht with h|h
    · exact Or.inl ⟨t,h,yes⟩
    · exact Or.inr ⟨t,h,yes⟩
  · rintro (⟨t,ht,yes⟩|⟨t,ht,yes⟩)
    · exact ⟨t,List.mem_append_left _ ht,yes⟩
    · exact ⟨t,List.mem_append_right _ ht,yes⟩

def Tree.rects : Tree → Bool → List Rct
  | .left f,t => [(fun x=>f x=t,fun _=>True)]
  | .right f,t => [(fun _=>True,fun y=>f y=t)]
  | .meet a b,true => prodTable (a.rects true) (b.rects true)
  | .meet a b,false => a.rects false ++ b.rects false
  | .join a b,true => a.rects true ++ b.rects true
  | .join a b,false => prodTable (a.rects false) (b.rects false)
  | .neg a,t => a.rects (!t)

theorem Tree.correct (g : Tree) (x y : Nat) (t : Bool) :
    Hit (g.rects t) x y ↔ g.value x y=t := by
  induction g generalizing t with
  | left f => simp [Tree.rects,Tree.value,Hit]
  | right f => simp [Tree.rects,Tree.value,Hit]
  | meet a b ia ib =>
    cases t <;> simp only [Tree.rects,Tree.value,hitProduct,hitUnion,ia,ib]
    all_goals cases a.value x y <;> cases b.value x y <;> decide
  | join a b ia ib =>
    cases t <;> simp only [Tree.rects,Tree.value,hitProduct,hitUnion,ia,ib]
    all_goals cases a.value x y <;> cases b.value x y <;> decide
  | neg a ih =>
    rw [Tree.rects,ih]
    cases a.value x y <;> cases t <;> decide

theorem Tree.budget (g : Tree) (ok : ∀x y,g.value x y=board x y) :
    7≤(g.rects true).length ∧ 13≤(g.rects false).length := by
  have lift (t : Bool) (x y : Nat) : board x y=t ↔ ∃ i : Fin (g.rects t).length,
      ((g.rects t).get i).1 x ∧ ((g.rects t).get i).2 y := by
    rw [←ok,(g.correct x y t).symm]
    constructor
    · rintro ⟨p,hp,k⟩
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨i,k⟩
    · rintro ⟨i,k⟩
      exact ⟨_,List.get_mem _ _,k⟩
  exact both _ _ _ _ (lift true) (lift false)

def Tree.leaves : Tree → Nat
  | .left _ | .right _ => 1
  | .meet a b | .join a b => a.leaves+b.leaves
  | .neg a => a.leaves

def capJoin (p q : Nat × Nat) := (p.1+q.1,p.2*q.2)
def capMeet (p q : Nat × Nat) := (p.1*q.1,p.2+q.2)
def port (g : Tree) := ((g.rects true).length,(g.rects false).length)

theorem prodLength (P Q : List Rct) : (prodTable P Q).length = P.length*Q.length := by
  induction P with
  | nil => simp [prodTable]
  | cons p P ih =>
    change (Q.map _ ++ prodTable P Q).length = (p::P).length*Q.length
    simp [ih,Nat.succ_mul,Nat.add_comm]

theorem port_left (x : Nat→Bool) : port (.left x) = (1,1) := rfl
theorem port_right (x : Nat→Bool) : port (.right x) = (1,1) := rfl
theorem port_meet (a b : Tree) : port (.meet a b) = capMeet (port a) (port b) := by
  simp [port,capMeet,Tree.rects,prodLength]
theorem port_join (a b : Tree) : port (.join a b) = capJoin (port a) (port b) := by
  simp [port,capJoin,Tree.rects,prodLength]
theorem port_neg (a : Tree) : port (.neg a) = (port a).swap := rfl
def s0 : List (Nat × Nat) := []
def s1 : List (Nat × Nat) := [(1,1)]
def s2 : List (Nat × Nat) := [(1,2),(2,1)]
def s3 : List (Nat × Nat) := [(1,3),(2,2),(3,1)]
def s4 : List (Nat × Nat) := [(1,4),(2,3),(2,4),(3,2),(4,1),(4,2)]
def s5 : List (Nat × Nat) := [(1,5),(2,4),(2,5),(2,6),(3,3),(3,4),(4,2),(4,3),(5,1),(5,2),(6,2)]
def s6 : List (Nat × Nat) := [(1,6),(2,5),(2,6),(2,7),(2,8),(2,9),(3,4),(3,5),(3,6),(3,8),(4,3),(4,4),(4,5),(5,2),(5,3),(5,4),(6,1),(6,2),(6,3),(7,2),(8,2),(8,3),(9,2)]
def s7 : List (Nat × Nat) := [(1,7),(2,6),(2,7),(2,8),(2,9),(2,10),(2,12),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,12),(4,4),(4,5),(4,6),(4,7),(4,8),(5,3),(5,4),(5,5),(5,6),(6,2),(6,3),(6,4),(6,5),(7,1),(7,2),(7,3),(7,4),(8,2),(8,3),(8,4),(9,2),(9,3),(10,2),(10,3),(12,2),(12,3)]
def s8 : List (Nat × Nat) := [(1,8),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,15),(2,16),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(3,18),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(4,12),(4,16),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(7,2),(7,3),(7,4),(7,5),(7,6),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(9,2),(9,3),(9,4),(9,5),(9,6),(10,2),(10,3),(10,4),(10,5),(11,2),(11,3),(12,2),(12,3),(12,4),(13,2),(13,3),(14,3),(15,2),(15,3),(16,2),(16,3),(16,4),(18,3)]
def s9 : List (Nat × Nat) := [(1,9),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,16),(2,17),(2,18),(2,20),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(3,17),(3,18),(3,19),(3,20),(3,21),(3,24),(3,27),(4,6),(4,7),(4,8),(4,9),(4,10),(4,11),(4,12),(4,13),(4,14),(4,15),(4,16),(4,17),(4,18),(4,20),(4,24),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(5,11),(5,12),(5,14),(5,15),(5,16),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(6,11),(6,12),(6,13),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(11,2),(11,3),(11,4),(11,5),(11,6),(12,2),(12,3),(12,4),(12,5),(12,6),(13,2),(13,3),(13,4),(13,6),(14,2),(14,3),(14,4),(14,5),(15,3),(15,4),(15,5),(16,2),(16,3),(16,4),(16,5),(17,2),(17,3),(17,4),(18,2),(18,3),(18,4),(19,3),(20,2),(20,3),(20,4),(21,3),(24,3),(24,4),(27,3)]
def small : Nat → List (Nat × Nat)
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => s7
  | 8 => s8
  | 9 => s9
  | _ => []

def paid (i j : Nat) := (small i).all (fun a => (small j).all (fun b =>
  decide (capMeet a b∈small (i+j)) && decide (capJoin a b∈small (i+j))))
def symmetric (i : Nat) := (small i).all (fun a=>decide (a.swap∈small i))
def tooSmall (i : Nat) := (small i).all (fun a=>decide (a.1<7 ∨ a.2<13))
theorem flip0 : symmetric 0=true := by decide +kernel
theorem bad0 : tooSmall 0=true := by decide +kernel
theorem mix0_0 : paid 0 0=true := by decide +kernel
theorem mix0_1 : paid 0 1=true := by decide +kernel
theorem mix0_2 : paid 0 2=true := by decide +kernel
theorem mix0_3 : paid 0 3=true := by decide +kernel
theorem mix0_4 : paid 0 4=true := by decide +kernel
theorem mix0_5 : paid 0 5=true := by decide +kernel
theorem mix0_6 : paid 0 6=true := by decide +kernel
theorem mix0_7 : paid 0 7=true := by decide +kernel
theorem mix0_8 : paid 0 8=true := by decide +kernel
theorem mix0_9 : paid 0 9=true := by decide +kernel
theorem flip1 : symmetric 1=true := by decide +kernel
theorem bad1 : tooSmall 1=true := by decide +kernel
theorem mix1_0 : paid 1 0=true := by decide +kernel
theorem mix1_1 : paid 1 1=true := by decide +kernel
theorem mix1_2 : paid 1 2=true := by decide +kernel
theorem mix1_3 : paid 1 3=true := by decide +kernel
theorem mix1_4 : paid 1 4=true := by decide +kernel
theorem mix1_5 : paid 1 5=true := by decide +kernel
theorem mix1_6 : paid 1 6=true := by decide +kernel
theorem mix1_7 : paid 1 7=true := by decide +kernel
theorem mix1_8 : paid 1 8=true := by decide +kernel
theorem flip2 : symmetric 2=true := by decide +kernel
theorem bad2 : tooSmall 2=true := by decide +kernel
theorem mix2_0 : paid 2 0=true := by decide +kernel
theorem mix2_1 : paid 2 1=true := by decide +kernel
theorem mix2_2 : paid 2 2=true := by decide +kernel
theorem mix2_3 : paid 2 3=true := by decide +kernel
theorem mix2_4 : paid 2 4=true := by decide +kernel
theorem mix2_5 : paid 2 5=true := by decide +kernel
theorem mix2_6 : paid 2 6=true := by decide +kernel
theorem mix2_7 : paid 2 7=true := by decide +kernel
theorem flip3 : symmetric 3=true := by decide +kernel
theorem bad3 : tooSmall 3=true := by decide +kernel
theorem mix3_0 : paid 3 0=true := by decide +kernel
theorem mix3_1 : paid 3 1=true := by decide +kernel
theorem mix3_2 : paid 3 2=true := by decide +kernel
theorem mix3_3 : paid 3 3=true := by decide +kernel
theorem mix3_4 : paid 3 4=true := by decide +kernel
theorem mix3_5 : paid 3 5=true := by decide +kernel
theorem mix3_6 : paid 3 6=true := by decide +kernel
theorem flip4 : symmetric 4=true := by decide +kernel
theorem bad4 : tooSmall 4=true := by decide +kernel
theorem mix4_0 : paid 4 0=true := by decide +kernel
theorem mix4_1 : paid 4 1=true := by decide +kernel
theorem mix4_2 : paid 4 2=true := by decide +kernel
theorem mix4_3 : paid 4 3=true := by decide +kernel
theorem mix4_4 : paid 4 4=true := by decide +kernel
theorem mix4_5 : paid 4 5=true := by decide +kernel
theorem flip5 : symmetric 5=true := by decide +kernel
theorem bad5 : tooSmall 5=true := by decide +kernel
theorem mix5_0 : paid 5 0=true := by decide +kernel
theorem mix5_1 : paid 5 1=true := by decide +kernel
theorem mix5_2 : paid 5 2=true := by decide +kernel
theorem mix5_3 : paid 5 3=true := by decide +kernel
theorem mix5_4 : paid 5 4=true := by decide +kernel
theorem flip6 : symmetric 6=true := by decide +kernel
theorem bad6 : tooSmall 6=true := by decide +kernel
theorem mix6_0 : paid 6 0=true := by decide +kernel
theorem mix6_1 : paid 6 1=true := by decide +kernel
theorem mix6_2 : paid 6 2=true := by decide +kernel
theorem mix6_3 : paid 6 3=true := by decide +kernel
theorem flip7 : symmetric 7=true := by decide +kernel
theorem bad7 : tooSmall 7=true := by decide +kernel
theorem mix7_0 : paid 7 0=true := by decide +kernel
theorem mix7_1 : paid 7 1=true := by decide +kernel
theorem mix7_2 : paid 7 2=true := by decide +kernel
theorem flip8 : symmetric 8=true := by decide +kernel
theorem bad8 : tooSmall 8=true := by decide +kernel
theorem mix8_0 : paid 8 0=true := by decide +kernel
theorem mix8_1 : paid 8 1=true := by decide +kernel
theorem flip9 : symmetric 9=true := by decide +kernel
theorem bad9 : tooSmall 9=true := by decide +kernel
theorem mix9_0 : paid 9 0=true := by decide +kernel

theorem mixCheck (i j : Nat) (sz : i+j≤9) : paid i j=true := by
  have hi : i≤9 := by omega
  have hj : j≤9 := by omega
  interval_cases i <;> interval_cases j <;> first | omega | exact mix0_0 | exact mix0_1 | exact mix0_2 | exact mix0_3 | exact mix0_4 | exact mix0_5 | exact mix0_6 | exact mix0_7 | exact mix0_8 | exact mix0_9 | exact mix1_0 | exact mix1_1 | exact mix1_2 | exact mix1_3 | exact mix1_4 | exact mix1_5 | exact mix1_6 | exact mix1_7 | exact mix1_8 | exact mix2_0 | exact mix2_1 | exact mix2_2 | exact mix2_3 | exact mix2_4 | exact mix2_5 | exact mix2_6 | exact mix2_7 | exact mix3_0 | exact mix3_1 | exact mix3_2 | exact mix3_3 | exact mix3_4 | exact mix3_5 | exact mix3_6 | exact mix4_0 | exact mix4_1 | exact mix4_2 | exact mix4_3 | exact mix4_4 | exact mix4_5 | exact mix5_0 | exact mix5_1 | exact mix5_2 | exact mix5_3 | exact mix5_4 | exact mix6_0 | exact mix6_1 | exact mix6_2 | exact mix6_3 | exact mix7_0 | exact mix7_1 | exact mix7_2 | exact mix8_0 | exact mix8_1 | exact mix9_0 
theorem flipCheck (i : Nat) (hi : i≤9) : symmetric i=true := by
  interval_cases i <;> first  | exact flip0 | exact flip1 | exact flip2 | exact flip3 | exact flip4 | exact flip5 | exact flip6 | exact flip7 | exact flip8 | exact flip9
theorem badCheck (i : Nat) (hi : i≤9) : tooSmall i=true := by
  interval_cases i <;> first  | exact bad0 | exact bad1 | exact bad2 | exact bad3 | exact bad4 | exact bad5 | exact bad6 | exact bad7 | exact bad8 | exact bad9
theorem portSmall (g : Tree) (h : g.leaves≤9) : port g ∈ small g.leaves := by
  induction g with
  | left f => change (1,1) ∈ s1; decide
  | right f => change (1,1) ∈ s1; decide
  | meet a b ia ib =>
    change a.leaves+b.leaves≤9 at h
    rw [port_meet]
    have o := List.all_eq_true.mp (mixCheck _ _ h) _ (ia (by omega))
    have p := List.all_eq_true.mp o _ (ib (by omega))
    exact of_decide_eq_true (by simp only [Bool.and_eq_true] at p; exact p.1)
  | join a b ia ib =>
    change a.leaves+b.leaves≤9 at h
    rw [port_join]
    have o := List.all_eq_true.mp (mixCheck _ _ h) _ (ia (by omega))
    have p := List.all_eq_true.mp o _ (ib (by omega))
    exact of_decide_eq_true (by simp only [Bool.and_eq_true] at p; exact p.2)
  | neg a ia =>
    rw [port_neg]
    exact of_decide_eq_true (List.all_eq_true.mp (flipCheck a.leaves h) _ (ia h))
theorem tenLeaves (g : Tree) (ok : ∀x y,g.value x y=board x y) : 10≤g.leaves := by
  by_contra! smallLeaf
  have h : g.leaves≤9 := by omega
  have bad := of_decide_eq_true (List.all_eq_true.mp (badCheck _ h) _ (portSmall _ h))
  have pr := g.budget ok
  change (port g).1<7 ∨ (port g).2<13 at bad
  change 7≤(port g).1 ∧ 13≤(port g).2 at pr
  omega
end Split9755

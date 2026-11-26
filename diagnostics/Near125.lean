import Mathlib
import PEqualNP.Defs

namespace Rectangle8193
abbrev V := Fin 21
abbrev Cell := (V × V) × (V → Bool)

def incident (p l : V) := p-l∈([0,1,4,14,16] : List V)
def avoid (m : V→Bool) (l : V) := !(m l || m (l+1) || m (l+4) || m (l+14) || m (l+16))

private theorem hit {m : V→Bool} {p l : V} (e : incident p l) (on_ : m p=true) : avoid m l=false := by
  have rel : ∀ p l : V, incident p l → p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16 := by decide
  rcases rel p l e with h|h|h|h|h <;> rw [h] at on_ <;> simp [avoid,on_]

inductive Kind
  | p (i : V) | l (i : V) | partialRow (p : V) (ls : List V) | star (p : V) | firstRows (k : Nat)
deriving DecidableEq

def rows : Kind → V × V → Prop
  | .p p, e => e.1=p
  | .l l, e => e.2=l
  | .partialRow p ls, e => e.1=p ∧ e.2∈ls
  | .star p, e => e.1=p ∧ incident e.1 e.2
  | .firstRows k, e => e.1.val≤k ∧ incident e.1 e.2

def cols : Kind → (V→Bool) → Prop
  | .p p, m => m p=false
  | .l l, m => avoid m l=false
  | .partialRow p _, m => m p=true
  | .star _, _ | .firstRows _, _ => True

def box (k : Kind) : Set Cell := {z | rows k z.1 ∧ cols k z.2}

private theorem rect (k : Kind) : ∀ x∈box k, ∀ y∈box k,(x.1,y.2)∈box k :=
  fun _ x _ y => ⟨x.1,y.2⟩

private theorem start (p a b : V) (ha : incident p a) (hb : incident p b) :
    box (.partialRow p [a,b]) ⊆ box (.l a) ∪ box (.l b) := by
  rintro ⟨⟨q,l⟩,m⟩ ⟨⟨eq,ls⟩,on_⟩
  have ab : l=a ∨ l=b := by simpa using ls
  rcases ab with rfl|rfl
  · exact Or.inl ⟨rfl,hit ha on_⟩
  · exact Or.inr ⟨rfl,hit hb on_⟩

private theorem grow (p a : V) (ls : List V) (ha : incident p a) :
    box (.partialRow p (a::ls)) ⊆ box (.partialRow p ls) ∪ box (.l a) := by
  rintro ⟨⟨q,l⟩,m⟩ ⟨⟨eq,h⟩,on_⟩
  rcases List.mem_cons.mp h with rfl|mem
  · exact Or.inr ⟨rfl,hit ha on_⟩
  · exact Or.inl ⟨⟨eq,mem⟩,on_⟩

private theorem closeRow (p : V) (ls : List V) (complete : ∀ l,incident p l → l∈ls) :
    box (.star p) ⊆ box (.p p) ∪ box (.partialRow p ls) := by
  rintro ⟨⟨q,l⟩,m⟩ ⟨⟨eq,h⟩,_⟩
  change q=p at eq
  subst q
  cases m0 : m p with
  | false => exact Or.inl ⟨rfl,m0⟩
  | true => exact Or.inr ⟨⟨rfl,complete l h⟩,m0⟩

private theorem firstPair : box (.firstRows 1) ⊆ box (.star 0) ∪ box (.star 1) := by
  rintro ⟨⟨q,l⟩,m⟩ ⟨⟨le,h⟩,_⟩
  have either : q=0 ∨ q=1 := (by decide : ∀ q : V,q.val≤1 → q=0 ∨ q=1) q le
  rcases either with rfl|rfl
  · exact Or.inl ⟨⟨rfl,h⟩,trivial⟩
  · exact Or.inr ⟨⟨rfl,h⟩,trivial⟩

private theorem nextRow (p : V) (hp : 0<p.val) : box (.firstRows p.val) ⊆ box (.firstRows (p.val-1)) ∪ box (.star p) := by
  rintro ⟨⟨q,l⟩,m⟩ ⟨⟨le,h⟩,_⟩
  change q.val≤p.val at le
  by_cases eq : q=p
  · exact Or.inr ⟨⟨eq,h⟩,trivial⟩
  · have ne : q.val ≠ p.val := fun e => eq (Fin.ext e)
    exact Or.inl ⟨⟨by change q.val≤p.val-1; omega,h⟩,trivial⟩

private def catalog : List Kind := [
  .p 0,
  .p 1,
  .p 2,
  .p 3,
  .p 4,
  .p 5,
  .p 6,
  .p 7,
  .p 8,
  .p 9,
  .p 10,
  .p 11,
  .p 12,
  .p 13,
  .p 14,
  .p 15,
  .p 16,
  .p 17,
  .p 18,
  .p 19,
  .p 20,
  .l 0,
  .l 1,
  .l 2,
  .l 3,
  .l 4,
  .l 5,
  .l 6,
  .l 7,
  .l 8,
  .l 9,
  .l 10,
  .l 11,
  .l 12,
  .l 13,
  .l 14,
  .l 15,
  .l 16,
  .l 17,
  .l 18,
  .l 19,
  .l 20,
  .partialRow 0 [0,20],
  .partialRow 0 [17,0,20],
  .partialRow 0 [7,17,0,20],
  .partialRow 0 [5,7,17,0,20],
  .star 0,
  .partialRow 1 [1,0],
  .partialRow 1 [18,1,0],
  .partialRow 1 [8,18,1,0],
  .partialRow 1 [6,8,18,1,0],
  .star 1,
  .partialRow 2 [2,1],
  .partialRow 2 [19,2,1],
  .partialRow 2 [9,19,2,1],
  .partialRow 2 [7,9,19,2,1],
  .star 2,
  .partialRow 3 [3,2],
  .partialRow 3 [20,3,2],
  .partialRow 3 [10,20,3,2],
  .partialRow 3 [8,10,20,3,2],
  .star 3,
  .partialRow 4 [4,3],
  .partialRow 4 [0,4,3],
  .partialRow 4 [11,0,4,3],
  .partialRow 4 [9,11,0,4,3],
  .star 4,
  .partialRow 5 [5,4],
  .partialRow 5 [1,5,4],
  .partialRow 5 [12,1,5,4],
  .partialRow 5 [10,12,1,5,4],
  .star 5,
  .partialRow 6 [6,5],
  .partialRow 6 [2,6,5],
  .partialRow 6 [13,2,6,5],
  .partialRow 6 [11,13,2,6,5],
  .star 6,
  .partialRow 7 [7,6],
  .partialRow 7 [3,7,6],
  .partialRow 7 [14,3,7,6],
  .partialRow 7 [12,14,3,7,6],
  .star 7,
  .partialRow 8 [8,7],
  .partialRow 8 [4,8,7],
  .partialRow 8 [15,4,8,7],
  .partialRow 8 [13,15,4,8,7],
  .star 8,
  .partialRow 9 [9,8],
  .partialRow 9 [5,9,8],
  .partialRow 9 [16,5,9,8],
  .partialRow 9 [14,16,5,9,8],
  .star 9,
  .partialRow 10 [10,9],
  .partialRow 10 [6,10,9],
  .partialRow 10 [17,6,10,9],
  .partialRow 10 [15,17,6,10,9],
  .star 10,
  .partialRow 11 [11,10],
  .partialRow 11 [7,11,10],
  .partialRow 11 [18,7,11,10],
  .partialRow 11 [16,18,7,11,10],
  .star 11,
  .partialRow 12 [12,11],
  .partialRow 12 [8,12,11],
  .partialRow 12 [19,8,12,11],
  .partialRow 12 [17,19,8,12,11],
  .star 12,
  .partialRow 13 [13,12],
  .partialRow 13 [9,13,12],
  .partialRow 13 [20,9,13,12],
  .partialRow 13 [18,20,9,13,12],
  .star 13,
  .partialRow 14 [14,13],
  .partialRow 14 [10,14,13],
  .partialRow 14 [0,10,14,13],
  .partialRow 14 [19,0,10,14,13],
  .star 14,
  .partialRow 15 [15,14],
  .partialRow 15 [11,15,14],
  .partialRow 15 [1,11,15,14],
  .partialRow 15 [20,1,11,15,14],
  .star 15,
  .partialRow 16 [16,15],
  .partialRow 16 [12,16,15],
  .partialRow 16 [2,12,16,15],
  .partialRow 16 [0,2,12,16,15],
  .star 16,
  .partialRow 17 [17,16],
  .partialRow 17 [13,17,16],
  .partialRow 17 [3,13,17,16],
  .partialRow 17 [1,3,13,17,16],
  .star 17,
  .partialRow 18 [18,17],
  .partialRow 18 [14,18,17],
  .partialRow 18 [4,14,18,17],
  .partialRow 18 [2,4,14,18,17],
  .star 18,
  .partialRow 19 [19,18],
  .partialRow 19 [15,19,18],
  .partialRow 19 [5,15,19,18],
  .partialRow 19 [3,5,15,19,18],
  .star 19,
  .partialRow 20 [20,19],
  .partialRow 20 [16,20,19],
  .partialRow 20 [6,16,20,19],
  .partialRow 20 [4,6,16,20,19],
  .star 20,
  .firstRows 1,
  .firstRows 2,
  .firstRows 3,
  .firstRows 4,
  .firstRows 5,
  .firstRows 6,
  .firstRows 7,
  .firstRows 8,
  .firstRows 9,
  .firstRows 10,
  .firstRows 11,
  .firstRows 12,
  .firstRows 13,
  .firstRows 14,
  .firstRows 15,
  .firstRows 16,
  .firstRows 17,
  .firstRows 18,
  .firstRows 19,
  .firstRows 20]

private def R (i : Nat) : Set Cell := box (catalog.getD i (.p 0))

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem inputsP (p : V) : R p.val = box (.p p) := by fin_cases p <;> rfl
private theorem inputsL (l : V) : R (21+l.val) = box (.l l) := by fin_cases l <;> rfl

private theorem steps (i : Fin 125) :
    ∃ a<42+i.val, ∃ b<42+i.val, R (42+i.val) ⊆ R a ∪ R b := by
  fin_cases i
  · exact ⟨21,by decide,41,by decide,start 0 0 20 (by decide) (by decide)⟩
  · exact ⟨42,by decide,38,by decide,grow 0 17 [0,20] (by decide)⟩
  · exact ⟨43,by decide,28,by decide,grow 0 7 [17,0,20] (by decide)⟩
  · exact ⟨44,by decide,26,by decide,grow 0 5 [7,17,0,20] (by decide)⟩
  · exact ⟨0,by decide,45,by decide,closeRow 0 [5,7,17,0,20] (by decide)⟩
  · exact ⟨22,by decide,21,by decide,start 1 1 0 (by decide) (by decide)⟩
  · exact ⟨47,by decide,39,by decide,grow 1 18 [1,0] (by decide)⟩
  · exact ⟨48,by decide,29,by decide,grow 1 8 [18,1,0] (by decide)⟩
  · exact ⟨49,by decide,27,by decide,grow 1 6 [8,18,1,0] (by decide)⟩
  · exact ⟨1,by decide,50,by decide,closeRow 1 [6,8,18,1,0] (by decide)⟩
  · exact ⟨23,by decide,22,by decide,start 2 2 1 (by decide) (by decide)⟩
  · exact ⟨52,by decide,40,by decide,grow 2 19 [2,1] (by decide)⟩
  · exact ⟨53,by decide,30,by decide,grow 2 9 [19,2,1] (by decide)⟩
  · exact ⟨54,by decide,28,by decide,grow 2 7 [9,19,2,1] (by decide)⟩
  · exact ⟨2,by decide,55,by decide,closeRow 2 [7,9,19,2,1] (by decide)⟩
  · exact ⟨24,by decide,23,by decide,start 3 3 2 (by decide) (by decide)⟩
  · exact ⟨57,by decide,41,by decide,grow 3 20 [3,2] (by decide)⟩
  · exact ⟨58,by decide,31,by decide,grow 3 10 [20,3,2] (by decide)⟩
  · exact ⟨59,by decide,29,by decide,grow 3 8 [10,20,3,2] (by decide)⟩
  · exact ⟨3,by decide,60,by decide,closeRow 3 [8,10,20,3,2] (by decide)⟩
  · exact ⟨25,by decide,24,by decide,start 4 4 3 (by decide) (by decide)⟩
  · exact ⟨62,by decide,21,by decide,grow 4 0 [4,3] (by decide)⟩
  · exact ⟨63,by decide,32,by decide,grow 4 11 [0,4,3] (by decide)⟩
  · exact ⟨64,by decide,30,by decide,grow 4 9 [11,0,4,3] (by decide)⟩
  · exact ⟨4,by decide,65,by decide,closeRow 4 [9,11,0,4,3] (by decide)⟩
  · exact ⟨26,by decide,25,by decide,start 5 5 4 (by decide) (by decide)⟩
  · exact ⟨67,by decide,22,by decide,grow 5 1 [5,4] (by decide)⟩
  · exact ⟨68,by decide,33,by decide,grow 5 12 [1,5,4] (by decide)⟩
  · exact ⟨69,by decide,31,by decide,grow 5 10 [12,1,5,4] (by decide)⟩
  · exact ⟨5,by decide,70,by decide,closeRow 5 [10,12,1,5,4] (by decide)⟩
  · exact ⟨27,by decide,26,by decide,start 6 6 5 (by decide) (by decide)⟩
  · exact ⟨72,by decide,23,by decide,grow 6 2 [6,5] (by decide)⟩
  · exact ⟨73,by decide,34,by decide,grow 6 13 [2,6,5] (by decide)⟩
  · exact ⟨74,by decide,32,by decide,grow 6 11 [13,2,6,5] (by decide)⟩
  · exact ⟨6,by decide,75,by decide,closeRow 6 [11,13,2,6,5] (by decide)⟩
  · exact ⟨28,by decide,27,by decide,start 7 7 6 (by decide) (by decide)⟩
  · exact ⟨77,by decide,24,by decide,grow 7 3 [7,6] (by decide)⟩
  · exact ⟨78,by decide,35,by decide,grow 7 14 [3,7,6] (by decide)⟩
  · exact ⟨79,by decide,33,by decide,grow 7 12 [14,3,7,6] (by decide)⟩
  · exact ⟨7,by decide,80,by decide,closeRow 7 [12,14,3,7,6] (by decide)⟩
  · exact ⟨29,by decide,28,by decide,start 8 8 7 (by decide) (by decide)⟩
  · exact ⟨82,by decide,25,by decide,grow 8 4 [8,7] (by decide)⟩
  · exact ⟨83,by decide,36,by decide,grow 8 15 [4,8,7] (by decide)⟩
  · exact ⟨84,by decide,34,by decide,grow 8 13 [15,4,8,7] (by decide)⟩
  · exact ⟨8,by decide,85,by decide,closeRow 8 [13,15,4,8,7] (by decide)⟩
  · exact ⟨30,by decide,29,by decide,start 9 9 8 (by decide) (by decide)⟩
  · exact ⟨87,by decide,26,by decide,grow 9 5 [9,8] (by decide)⟩
  · exact ⟨88,by decide,37,by decide,grow 9 16 [5,9,8] (by decide)⟩
  · exact ⟨89,by decide,35,by decide,grow 9 14 [16,5,9,8] (by decide)⟩
  · exact ⟨9,by decide,90,by decide,closeRow 9 [14,16,5,9,8] (by decide)⟩
  · exact ⟨31,by decide,30,by decide,start 10 10 9 (by decide) (by decide)⟩
  · exact ⟨92,by decide,27,by decide,grow 10 6 [10,9] (by decide)⟩
  · exact ⟨93,by decide,38,by decide,grow 10 17 [6,10,9] (by decide)⟩
  · exact ⟨94,by decide,36,by decide,grow 10 15 [17,6,10,9] (by decide)⟩
  · exact ⟨10,by decide,95,by decide,closeRow 10 [15,17,6,10,9] (by decide)⟩
  · exact ⟨32,by decide,31,by decide,start 11 11 10 (by decide) (by decide)⟩
  · exact ⟨97,by decide,28,by decide,grow 11 7 [11,10] (by decide)⟩
  · exact ⟨98,by decide,39,by decide,grow 11 18 [7,11,10] (by decide)⟩
  · exact ⟨99,by decide,37,by decide,grow 11 16 [18,7,11,10] (by decide)⟩
  · exact ⟨11,by decide,100,by decide,closeRow 11 [16,18,7,11,10] (by decide)⟩
  · exact ⟨33,by decide,32,by decide,start 12 12 11 (by decide) (by decide)⟩
  · exact ⟨102,by decide,29,by decide,grow 12 8 [12,11] (by decide)⟩
  · exact ⟨103,by decide,40,by decide,grow 12 19 [8,12,11] (by decide)⟩
  · exact ⟨104,by decide,38,by decide,grow 12 17 [19,8,12,11] (by decide)⟩
  · exact ⟨12,by decide,105,by decide,closeRow 12 [17,19,8,12,11] (by decide)⟩
  · exact ⟨34,by decide,33,by decide,start 13 13 12 (by decide) (by decide)⟩
  · exact ⟨107,by decide,30,by decide,grow 13 9 [13,12] (by decide)⟩
  · exact ⟨108,by decide,41,by decide,grow 13 20 [9,13,12] (by decide)⟩
  · exact ⟨109,by decide,39,by decide,grow 13 18 [20,9,13,12] (by decide)⟩
  · exact ⟨13,by decide,110,by decide,closeRow 13 [18,20,9,13,12] (by decide)⟩
  · exact ⟨35,by decide,34,by decide,start 14 14 13 (by decide) (by decide)⟩
  · exact ⟨112,by decide,31,by decide,grow 14 10 [14,13] (by decide)⟩
  · exact ⟨113,by decide,21,by decide,grow 14 0 [10,14,13] (by decide)⟩
  · exact ⟨114,by decide,40,by decide,grow 14 19 [0,10,14,13] (by decide)⟩
  · exact ⟨14,by decide,115,by decide,closeRow 14 [19,0,10,14,13] (by decide)⟩
  · exact ⟨36,by decide,35,by decide,start 15 15 14 (by decide) (by decide)⟩
  · exact ⟨117,by decide,32,by decide,grow 15 11 [15,14] (by decide)⟩
  · exact ⟨118,by decide,22,by decide,grow 15 1 [11,15,14] (by decide)⟩
  · exact ⟨119,by decide,41,by decide,grow 15 20 [1,11,15,14] (by decide)⟩
  · exact ⟨15,by decide,120,by decide,closeRow 15 [20,1,11,15,14] (by decide)⟩
  · exact ⟨37,by decide,36,by decide,start 16 16 15 (by decide) (by decide)⟩
  · exact ⟨122,by decide,33,by decide,grow 16 12 [16,15] (by decide)⟩
  · exact ⟨123,by decide,23,by decide,grow 16 2 [12,16,15] (by decide)⟩
  · exact ⟨124,by decide,21,by decide,grow 16 0 [2,12,16,15] (by decide)⟩
  · exact ⟨16,by decide,125,by decide,closeRow 16 [0,2,12,16,15] (by decide)⟩
  · exact ⟨38,by decide,37,by decide,start 17 17 16 (by decide) (by decide)⟩
  · exact ⟨127,by decide,34,by decide,grow 17 13 [17,16] (by decide)⟩
  · exact ⟨128,by decide,24,by decide,grow 17 3 [13,17,16] (by decide)⟩
  · exact ⟨129,by decide,22,by decide,grow 17 1 [3,13,17,16] (by decide)⟩
  · exact ⟨17,by decide,130,by decide,closeRow 17 [1,3,13,17,16] (by decide)⟩
  · exact ⟨39,by decide,38,by decide,start 18 18 17 (by decide) (by decide)⟩
  · exact ⟨132,by decide,35,by decide,grow 18 14 [18,17] (by decide)⟩
  · exact ⟨133,by decide,25,by decide,grow 18 4 [14,18,17] (by decide)⟩
  · exact ⟨134,by decide,23,by decide,grow 18 2 [4,14,18,17] (by decide)⟩
  · exact ⟨18,by decide,135,by decide,closeRow 18 [2,4,14,18,17] (by decide)⟩
  · exact ⟨40,by decide,39,by decide,start 19 19 18 (by decide) (by decide)⟩
  · exact ⟨137,by decide,36,by decide,grow 19 15 [19,18] (by decide)⟩
  · exact ⟨138,by decide,26,by decide,grow 19 5 [15,19,18] (by decide)⟩
  · exact ⟨139,by decide,24,by decide,grow 19 3 [5,15,19,18] (by decide)⟩
  · exact ⟨19,by decide,140,by decide,closeRow 19 [3,5,15,19,18] (by decide)⟩
  · exact ⟨41,by decide,40,by decide,start 20 20 19 (by decide) (by decide)⟩
  · exact ⟨142,by decide,37,by decide,grow 20 16 [20,19] (by decide)⟩
  · exact ⟨143,by decide,27,by decide,grow 20 6 [16,20,19] (by decide)⟩
  · exact ⟨144,by decide,25,by decide,grow 20 4 [6,16,20,19] (by decide)⟩
  · exact ⟨20,by decide,145,by decide,closeRow 20 [4,6,16,20,19] (by decide)⟩
  · exact ⟨46,by decide,51,by decide,firstPair⟩
  · exact ⟨147,by decide,56,by decide,nextRow 2 (by decide)⟩
  · exact ⟨148,by decide,61,by decide,nextRow 3 (by decide)⟩
  · exact ⟨149,by decide,66,by decide,nextRow 4 (by decide)⟩
  · exact ⟨150,by decide,71,by decide,nextRow 5 (by decide)⟩
  · exact ⟨151,by decide,76,by decide,nextRow 6 (by decide)⟩
  · exact ⟨152,by decide,81,by decide,nextRow 7 (by decide)⟩
  · exact ⟨153,by decide,86,by decide,nextRow 8 (by decide)⟩
  · exact ⟨154,by decide,91,by decide,nextRow 9 (by decide)⟩
  · exact ⟨155,by decide,96,by decide,nextRow 10 (by decide)⟩
  · exact ⟨156,by decide,101,by decide,nextRow 11 (by decide)⟩
  · exact ⟨157,by decide,106,by decide,nextRow 12 (by decide)⟩
  · exact ⟨158,by decide,111,by decide,nextRow 13 (by decide)⟩
  · exact ⟨159,by decide,116,by decide,nextRow 14 (by decide)⟩
  · exact ⟨160,by decide,121,by decide,nextRow 15 (by decide)⟩
  · exact ⟨161,by decide,126,by decide,nextRow 16 (by decide)⟩
  · exact ⟨162,by decide,131,by decide,nextRow 17 (by decide)⟩
  · exact ⟨163,by decide,136,by decide,nextRow 18 (by decide)⟩
  · exact ⟨164,by decide,141,by decide,nextRow 19 (by decide)⟩
  · exact ⟨165,by decide,146,by decide,nextRow 20 (by decide)⟩

theorem near : have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 - x2 ∈ [(0 : Fin (21 : ℕ)), (1 : Fin (21 : ℕ)), (4 : Fin (21 : ℕ)), (14 : Fin (21 : ℕ)), (16 : Fin (21 : ℕ))]; have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ x3 ≤ (125 : ℕ), ∃ (x4 : ℕ → Set ((Fin (21 : ℕ) × Fin (21 : ℕ)) × (Fin (21 : ℕ) → Bool))), (∀ (x5 : Fin (21 : ℕ)), ∀ x6 ∈ x4 ↑x5, x6.1.1 = x5 ∧ x6.2 x5 = Bool.false) ∧ (∀ (x5 : Fin (21 : ℕ)), ∀ x6 ∈ x4 ((21 : ℕ) + ↑x5), x6.1.2 = x5 ∧ x2 x6.2 x5 = Bool.false) ∧ (∀ x5 < x3, (∀ x7 ∈ x4 ((42 : ℕ) + x5), ∀ x9 ∈ x4 ((42 : ℕ) + x5), (x7.1, x9.2) ∈ x4 ((42 : ℕ) + x5)) ∧ ∃ x7 < (42 : ℕ) + x5, ∃ x8 < (42 : ℕ) + x5, x4 ((42 : ℕ) + x5) ⊆ x4 x7 ∪ x4 x8) ∧ ∃ x5 < (42 : ℕ) + x3, ∀ (x6 x7 : Fin (21 : ℕ)), x1 x6 x7 → ∀ (x9 : Fin (21 : ℕ) → Bool), (∀ (x10 : Fin (21 : ℕ)), x9 x10 = Bool.false → ∃ (x12 : Fin (21 : ℕ)), x1 x10 x12 ∧ x2 x9 x12 = Bool.true) → ((x6, x7), x9) ∈ x4 x5 := by
  intro _ _
  refine ⟨125,by decide,R,?_,?_,?_,?_⟩
  · intro p c h; rw [inputsP] at h; exact h
  · intro l c h; rw [inputsL] at h; exact h
  · intro i hi
    exact ⟨rect _,steps ⟨i,hi⟩⟩
  · refine ⟨166,by decide,?_⟩
    intro p l e m _
    change (p.val≤20 ∧ incident p l) ∧ True
    exact ⟨⟨by omega,e⟩,trivial⟩

end Rectangle8193

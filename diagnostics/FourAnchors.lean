import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
abbrev Big := Fin 5 × Fin 4
abbrev Small := Fin 4 × Fin 3
def pigeon (m n : Nat) (i : Fin m) : Clause (Fin m × Fin n) := univ.image (fun j => ((i,j),true))
def collision (m n : Nat) (i k : Fin m) (j : Fin n) : Clause (Fin m × Fin n) :=
  {((i,j),false),((k,j),false)}
def raw (m n : Nat) : Finset (Clause (Fin m × Fin n)) :=
  (univ.image (pigeon m n)) ∪
    ((univ.filter (fun v : Fin m × Fin m × Fin n => v.1≠v.2.1)).image
       (fun v => collision m n v.1 v.2.1 v.2.2))
theorem raw_spec {m n : Nat} {C : Clause (Fin m×Fin n)} : C∈raw m n ↔ C∈PHP m n := by
  simp only [raw,mem_union,mem_image,mem_univ,mem_filter,true_and]
  constructor
  · rintro (⟨i,rfl⟩|⟨⟨i,k,j⟩,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨i,k,j,ne,rfl⟩
  · rintro (⟨i,rfl⟩|⟨i,k,j,ne,rfl⟩)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr ⟨⟨i,k,j⟩,ne,rfl⟩

def emb (p : Fin 5) (h : Fin 4) (u : Small) : Big := (p.succAbove u.1,h.succAbove u.2)
def lower (p : Fin 5) (h : Fin 4) (z : Big) : Small :=
  (⟨(z.1.val - (if p<z.1 then 1 else 0))%4, Nat.mod_lt _ (by decide)⟩,
   ⟨(z.2.val - (if h<z.2 then 1 else 0))%3, Nat.mod_lt _ (by decide)⟩)
def switch (p : Fin 5) (h : Fin 4) (u : Small) (z : Big) : Option (Small × Bool) :=
  if z=(p,h) then some (u,false)
  else if z=(p,(emb p h u).2) ∨ z=((emb p h u).1,h) then some (u,true)
  else if z=emb p h u ∨ z.1=p ∨ z.2=h then none
  else some (lower p h z,true)

def translate {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (z : A×Bool) :
    Finset (B×Bool) :=
  match f z.1 with
  | none => ∅
  | some (w,s) => {(w,if z.2 then s else !s)}
def body {A B : Type} [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) :=
  c.biUnion (translate f)
def paid {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool)) (c : Clause A) : Bool :=
  decide (∀ z∈c, f z.1=none → z.2=true) &&
    decide (∀ z∈body f c, (z.1,!z.2)∉body f c)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem oneSwitch : let f := switch 4 3 (0,0)
    (((raw 5 4).filter (fun c=> paid f c)).image (body f))=raw 4 3 ∧
    ((raw 5 4).filter (fun c=> paid f c)).card=22 := by decide +kernel

end PEqualNP.Outside.L_pcx_166.Switch
namespace PEqualNP.Outside.L_pcx_166.Switch
open PEqualNP.ProofComplexity Finset
def extend {A B : Type} (f : A→Option (B×Bool)) (fixed : A→Bool) (a : B→Bool) (z : A) : Bool :=
  match f z with
  | none => fixed z
  | some (b,s) => decide (a b=s)
def nontrivial {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool)) (fixed : A→Bool) (c : Clause A) : Prop :=
  (∀z∈c, f z.1=none → fixed z.1≠z.2) ∧ (∀z∈body f c, (z.1,!z.2)∉body f c)
theorem projectedLit {A B : Type} [DecidableEq B] (f : A→Option (B×Bool))
    (fixed : A→Bool) (a : B→Bool) (z : A×Bool) (y : B×Bool) (mem : y∈translate f z) :
    a y.1=y.2 → extend f fixed a z.1=z.2 := by
  rcases z with ⟨x,s⟩
  cases h : f x with
  | none => simp [translate,h] at mem
  | some b =>
    rcases b with ⟨t,k⟩
    cases s <;> cases k <;> simp [translate,h] at mem <;> subst y <;>
      cases ha : a t <;> simp [extend,h,ha]
theorem badImage {A B : Type} [DecidableEq A] [DecidableEq B] {f : A→Option (B×Bool)}
    {fixed : A→Bool} {a : B→Bool} {c : Clause A} (bad : ¬ClauseSat (extend f fixed a) c) :
    nontrivial f fixed c ∧ ¬ClauseSat a (body f c) := by
  have no : ¬ClauseSat a (body f c) := by
    rintro ⟨y,mem,on⟩
    obtain ⟨z,m,hm⟩:=mem_biUnion.mp mem
    exact bad ⟨z,m,projectedLit f fixed a z y hm on⟩
  refine ⟨?_,no⟩
  constructor
  · intro z hm off on
    exact bad ⟨z,hm,by simpa [extend,off] using on⟩
  · intro z hm opp
    by_cases on : a z.1=z.2
    · exact no ⟨z,hm,on⟩
    · have flipOn : a z.1= !z.2 := by cases hx : a z.1 <;> cases hy : z.2 <;> simp_all
      exact no ⟨(z.1,!z.2),opp,flipOn⟩
theorem sizeBody {A B : Type} [DecidableEq A] [DecidableEq B] (f : A→Option (B×Bool))
    (c : Clause A) : (body f c).card≤c.card := by
  classical
  induction c using Finset.induction_on with
  | empty => simp [body]
  | @insert x s fresh ih =>
    have single : (translate f x).card≤1 := by
      cases hx : f x.1 with
      | none => simp [translate,hx]
      | some z => rcases z with ⟨u,k⟩; simp [translate,hx]
    have eq : body f (insert x s)=translate f x ∪ body f s := by simp [body]
    rw [eq,card_insert_of_notMem fresh]
    have bound:=card_union_le (translate f x) (body f s)
    omega
def wall (r : Fin 4) (v : Small) : Bool :=
  decide (v.1≠r ∧ v.2.val=v.1.val-(if r<v.1 then 1 else 0))
theorem wallRows : ∀ r s : Fin 4,
    ¬(∃z∈pigeon 4 3 s, wall r z.1=z.2) → s=r := by decide +kernel
theorem wallColumns : ∀ r a b : Fin 4, ∀h : Fin 3, a≠b →
    ∃z∈collision 4 3 a b h, wall r z.1=z.2 := by decide +kernel
theorem distinctRows : ∀ i j : Fin 4, i≠j → (pigeon 4 3 i ∪ pigeon 4 3 j).card=6 := by
  decide +kernel
theorem cardRows : ∀ i : Fin 4, (pigeon 4 3 i).card=3 := by decide +kernel
theorem cardBigRows : ∀ i : Fin 5, (pigeon 5 4 i).card=4 := by decide +kernel
theorem contradictionBoard (a : Big→Bool) : ∃c∈PHP 5 4, ¬ClauseSat a c := by
  classical
  by_contra! all
  have rows (i : Fin 5) : ∃j : Fin 4, a (i,j)=true := by
    obtain ⟨z,mem,on⟩:=all (pigeon 5 4 i) (Or.inl ⟨i,rfl⟩)
    obtain ⟨j,_,rfl⟩:=mem_image.mp mem
    exact ⟨j,on⟩
  choose sel tr using rows
  have inj : Function.Injective sel := by
    intro i k eq
    by_contra ne
    obtain ⟨z,mem,on⟩:=all (collision 5 4 i k (sel i)) (Or.inr ⟨i,k,sel i,ne,rfl⟩)
    rcases mem_insert.mp mem with h|h
    · subst z; have hh:=tr i; change a (i,sel i)=false at on; simp_all
    · have e:=mem_singleton.mp h
      subst z; change a (k,sel i)=false at on
      rw [eq,tr] at on
      contradiction
  have hn:=Fintype.card_le_of_injective sel inj
  simp at hn
theorem anchoredRows (f : Big→Option (Small×Bool)) (fixed : Big→Bool)
    (zeroCost : ∀c∈PHP 5 4, nontrivial f fixed c → ∃d∈PHP 4 3,d⊆body f c) :
    ∃sel : Fin 4→Fin 5, Function.Injective sel ∧ ∀r, pigeon 4 3 r ⊆ body f (pigeon 5 4 (sel r)) := by
  classical
  have hit (r : Fin 4) : ∃j, pigeon 4 3 r ⊆ body f (pigeon 5 4 j) := by
    obtain ⟨c,mc,bad⟩:=contradictionBoard (extend f fixed (wall r))
    obtain ⟨paid',off⟩:=badImage bad
    obtain ⟨d,md,sub⟩:=zeroCost c mc paid'
    have dd : ¬ClauseSat (wall r) d := fun ⟨z,mem,on⟩=>off ⟨z,sub mem,on⟩
    have eq : d=pigeon 4 3 r := by
      rcases md with ⟨j,rfl⟩|⟨a,b,h,ne,rfl⟩
      · have same:=wallRows r j dd
        subst j; rfl
      · exact (dd (wallColumns r a b h ne)).elim
    rw [eq] at sub
    rcases mc with ⟨j,rfl⟩|⟨a,b,h,ne,rfl⟩
    · exact ⟨j,sub⟩
    · have small := sizeBody f (collision 5 4 a b h)
      have lower := card_le_card sub
      rw [cardRows] at lower
      have cap : (collision 5 4 a b h).card≤2 := by
        exact (card_insert_le _ _).trans (by simp)
      omega
  choose sel inc using hit
  refine ⟨sel,?_,inc⟩
  intro i j eq
  by_contra ne
  have sub : pigeon 4 3 i ∪ pigeon 4 3 j ⊆ body f (pigeon 5 4 (sel j)) :=
    union_subset (eq ▸ inc i) (inc j)
  have lower:=card_le_card sub
  rw [distinctRows i j ne] at lower
  have cap:=sizeBody f (pigeon 5 4 (sel j))
  rw [cardBigRows] at cap
  omega
end PEqualNP.Outside.L_pcx_166.Switch

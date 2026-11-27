import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18180
open Finset PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
abbrev Edges (n m : Nat) := Finset (Fin n × Fin m)
def Linear {n m} (E : Edges n m) := ∀ a b i j, a ≠ b → i ≠ j →
  ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)
def Flags {n m} (E : Edges n m) (x : Fin (n+m) → Bool) :=
  decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
def Budget {n m} (E : Edges n m) (s : Nat) := ∃ A : Finset (Fin n), ∃ B : Finset (Fin m),
  (∀ e∈E, e.1∈A ∨ e.2∈B) ∧ E.card+A.card+B.card ≤ s+1
def Ends {n m} (E : Edges n m) : Finset (Fin (n+m)) := E.biUnion fun e =>
  {Fin.castAdd m e.1,Fin.natAdd n e.2}
def NoStar {n m} (E : Edges n m) := ¬∃ A B : Edges n m, ∃ v : Fin (n+m),
  A.Nonempty ∧ A∪B=E ∧ Disjoint (Ends A) (Ends B) ∧
  ∀ e∈A, Fin.castAdd m e.1=v ∨ Fin.natAdd n e.2=v
def PathCover {n m} (E : Edges n m) := ∀ e∈E, ∃ a b i j, a≠b ∧ i≠j ∧
  (a,i)∈E ∧ (a,j)∈E ∧ (b,j)∈E ∧ (e=(a,i) ∨ e=(a,j) ∨ e=(b,j))
theorem sep {n m} (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro eq
  have z := congrArg Fin.val eq
  simp only [Fin.val_castAdd, Fin.val_natAdd] at z
  have := a.isLt
  omega
theorem path_noStar {n m} {E : Edges n m} (h : PathCover E) : NoStar E := by
  rintro ⟨A,B,v,⟨e,he⟩,hu,hd,center⟩
  have propagate (r : Fin n × Fin m) (hr : r∈A) (s : Fin n × Fin m) (hs : s∈E) (close : r.1=s.1 ∨ r.2=s.2) : s∈A := by
    rw [←hu, mem_union] at hs
    rcases hs with hs|hs
    · exact hs
    · exfalso
      rcases close with f|f
      · apply Finset.disjoint_left.mp hd (a := Fin.castAdd m r.1)
        · exact mem_biUnion.mpr ⟨r,hr,by simp⟩
        · exact mem_biUnion.mpr ⟨s,hs,by simp [f]⟩
      · apply Finset.disjoint_left.mp hd (a := Fin.natAdd n r.2)
        · exact mem_biUnion.mpr ⟨r,hr,by simp⟩
        · exact mem_biUnion.mpr ⟨s,hs,by simp [f]⟩
  have hE : e∈E := hu ▸ mem_union_left _ he
  obtain ⟨a,b,i,j,ab,ij,ai,aj,bj,loc⟩ := h e hE
  have middle : (a,j)∈A := by
    rcases loc with rfl|rfl|rfl
    · exact propagate _ he _ aj (.inl rfl)
    · exact he
    · exact propagate _ he _ aj (.inr rfl)
  have one := center _ (propagate _ middle _ ai (.inl rfl))
  have two := center _ (propagate _ middle _ bj (.inr rfl))
  rcases one with h1|h1 <;> rcases two with h2|h2
  · exact ab (Fin.castAdd_inj.mp (h1.trans h2.symm))
  · exact sep a j (h1.trans h2.symm)
  · exact sep b i (h2.trans h1.symm)
  · have z := congrArg Fin.val (h1.trans h2.symm)
    change n+i.val=n+j.val at z
    exact ij (Fin.ext (by omega))

structure Layout (n m N M : Nat) where
  row : Fin n ↪ Fin N
  tip : Fin n ↪ Fin N
  col : Fin m ↪ Fin M
  mid : Fin n ↪ Fin M
  rt : ∀ p q, row p ≠ tip q
  cm : ∀ l q, col l ≠ mid q
variable {n m N M : Nat}
def old (b : Layout n m N M) : (Fin n × Fin m) ↪ (Fin N × Fin M) where
  toFun e := (b.row e.1,b.col e.2)
  inj' := by
    intro x y eq
    exact Prod.ext (b.row.injective (congrArg Prod.fst eq)) (b.col.injective (congrArg Prod.snd eq))
def near (b : Layout n m N M) : Fin n ↪ (Fin N × Fin M) where
  toFun p := (b.row p,b.mid p)
  inj' := by intro p q eq; exact b.row.injective (congrArg Prod.fst eq)
def far (b : Layout n m N M) : Fin n ↪ (Fin N × Fin M) where
  toFun p := (b.tip p,b.mid p)
  inj' := by intro p q eq; exact b.tip.injective (congrArg Prod.fst eq)
def active (E : Edges n m) := E.image Prod.fst
def board (b : Layout n m N M) (E : Edges n m) : Edges N M :=
  (E.map (old b) ∪ (active E).map (near b)) ∪ (active E).map (far b)
theorem on_board (b : Layout n m N M) (E : Edges n m) (e : Fin N × Fin M) :
    e∈board b E ↔ (∃ f∈E, e=(b.row f.1,b.col f.2)) ∨
    (∃ p∈active E, e=(b.row p,b.mid p)) ∨ (∃ p∈active E, e=(b.tip p,b.mid p)) := by
  simp only [board,mem_union,mem_map,old,near,far,Function.Embedding.coeFn_mk]
  grind
theorem board_paths (b : Layout n m N M) (E : Edges n m) : PathCover (board b E) := by
  intro e he
  have path (p : Fin n) (l : Fin m) (h : (p,l)∈E)
      (eq : e=(b.row p,b.col l) ∨ e=(b.row p,b.mid p) ∨ e=(b.tip p,b.mid p)) :
      ∃ a c i j, a≠c ∧ i≠j ∧ (a,i)∈board b E ∧ (a,j)∈board b E ∧
        (c,j)∈board b E ∧ (e=(a,i) ∨ e=(a,j) ∨ e=(c,j)) := by
    have act : p∈active E := mem_image.mpr ⟨(p,l),h,rfl⟩
    exact ⟨_,_,_,_,b.rt p p,b.cm l p,(on_board _ _ _).2 (.inl ⟨(p,l),h,rfl⟩),
      (on_board _ _ _).2 (.inr (.inl ⟨p,act,rfl⟩)),
      (on_board _ _ _).2 (.inr (.inr ⟨p,act,rfl⟩)),eq⟩
  rcases (on_board _ _ _).1 he with ⟨⟨p,l⟩,h,rfl⟩|⟨p,h,rfl⟩|⟨p,h,rfl⟩
  · exact path p l h (.inl rfl)
  · obtain ⟨⟨p',l⟩,hp,rfl⟩ := mem_image.mp h
    exact path p' l hp (.inr (.inl rfl))
  · obtain ⟨⟨p',l⟩,hp,rfl⟩ := mem_image.mp h
    exact path p' l hp (.inr (.inr rfl))

theorem board_card (b : Layout n m N M) (E : Edges n m) :
    (board b E).card = E.card + 2*(active E).card := by
  have dn : Disjoint (E.map (old b)) ((active E).map (near b)) := by
    rw [Finset.disjoint_left]
    rintro _ hx hy
    obtain ⟨e,_,rfl⟩ := mem_map.mp hx
    obtain ⟨p,_,eq⟩ := mem_map.mp hy
    exact b.cm e.2 p (congrArg Prod.snd eq.symm)
  have df : Disjoint (E.map (old b) ∪ (active E).map (near b)) ((active E).map (far b)) := by
    rw [Finset.disjoint_left]
    rintro _ hu hf
    obtain ⟨p,_,rfl⟩ := mem_map.mp hf
    rcases mem_union.mp hu with ho|hn
    · obtain ⟨e,_,eq⟩ := mem_map.mp ho
      exact b.rt e.1 p (congrArg Prod.fst eq)
    · obtain ⟨q,_,eq⟩ := mem_map.mp hn
      exact b.rt q p (congrArg Prod.fst eq)
  rw [board,Finset.card_union_of_disjoint df,Finset.card_union_of_disjoint dn]
  simp
  <;> omega

end PEqualNP.Outside.L_meta_18180

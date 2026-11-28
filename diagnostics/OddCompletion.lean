import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.OddCompletion

def vote (a b c d e : Bool) : Bool :=
  decide (3 ≤ a.toNat + b.toNat + c.toNat + d.toNat + e.toNat)

private theorem cyclic (a b c d e : Bool) : vote b c d e a = vote a b c d e := by
  decide +revert

private theorem complement (a b c d e : Bool) :
    vote (!a) (!b) (!c) (!d) (!e) = !(vote a b c d e) := by decide +revert

def avg {X : Type} (T : X→X) (c : X→Bool) (x : X) :=
  vote (c x) (c (T x)) (c (T (T x))) (c (T (T (T x)))) (c (T (T (T (T x)))))

theorem invariant {X : Type} {T : X→X} (ord : ∀ x,T (T (T (T (T x))))=x)
    (c : X→Bool) (x : X) : avg T c (T x)=avg T c x := by
  unfold avg
  rw [ord]
  exact cyclic _ _ _ _ _

private theorem flip_of_ne {a b : Bool} (ne : a≠b) : b=(!a) := by
  cases a <;> cases b <;> simp_all

theorem proper {X : Type} {E : X→X→Prop} {T : X→X} (pres : ∀ {x y},E x y → E (T x) (T y))
    {c : X→Bool} (ok : ∀ {x y}, E x y → c x≠c y) {x y : X} (edge : E x y) :
    avg T c x≠avg T c y := by
  have e₀ := flip_of_ne (ok edge)
  have e₁ := flip_of_ne (ok (pres edge))
  have e₂ := flip_of_ne (ok (pres (pres edge)))
  have e₃ := flip_of_ne (ok (pres (pres (pres edge))))
  have e₄ := flip_of_ne (ok (pres (pres (pres (pres edge)))))
  unfold avg
  rw [e₀,e₁,e₂,e₃,e₄,complement]
  cases vote (c x) (c (T x)) (c (T (T x))) (c (T (T (T x)))) (c (T (T (T (T x))))) <;> decide

/-- X indexes the outstanding cells.  A class with no conflict has legal Cartesian closure. -/
def crossed {X P L : Type} (row : X→P) (col : X→L) (legal : P→L→Prop) (x y : X) :=
  ¬legal (row x) (col y) ∨ ¬legal (row y) (col x)

theorem physical {X P L : Type} [Fintype X] [DecidableEq P] [DecidableEq L]
    (row : X→P) (col : X→L) (legal : P→L→Prop) (T : X→X)
    (point : P→P) (line : L→L) (ord : ∀ x,T (T (T (T (T x))))=x)
    (actions : ∀ x,row (T x)=point (row x) ∧ col (T x)=line (col x))
    (pres : ∀ {x y}, crossed row col legal x y → crossed row col legal (T x) (T y))
    (S : Bool → Finset P × Finset L)
    (empty : ∀ b,∀ i∈(S b).1,∀ j∈(S b).2,legal i j)
    (cover : ∀ x,∃ b : Bool,row x∈(S b).1 ∧ col x∈(S b).2) :
    ∃ B : Bool → Finset P × Finset L,
      (∀ b,∀ i∈(B b).1,∀ j∈(B b).2,legal i j) ∧
      (∀ x,∃ b : Bool,row x∈(B b).1 ∧ col x∈(B b).2) ∧
      (∀ b,∀ i∈(B b).1,point i∈(B b).1) ∧ (∀ b,∀ j∈(B b).2,line j∈(B b).2) := by
  classical
  choose color hit using cover
  have ok {x y : X} (bad : crossed row col legal x y) : color x≠color y := by
    intro same
    have hx := hit x
    rw [same] at hx
    rcases bad with left|right
    · exact left (empty _ _ hx.1 _ (hit y).2)
    · exact right (empty _ _ (hit y).1 _ hx.2)
  let c := avg T color
  let B (b : Bool) := (((Finset.univ.filter (fun x : X => c x=b)).image row),
                        ((Finset.univ.filter (fun x : X => c x=b)).image col))
  have rowmem (b : Bool) (i : P) : i ∈ (B b).1 ↔ ∃ x,c x=b ∧ row x=i := by simp [B]
  have colmem (b : Bool) (j : L) : j ∈ (B b).2 ↔ ∃ x,c x=b ∧ col x=j := by simp [B]
  refine ⟨B,?_,?_,?_,?_⟩
  · intro b i hi j hj
    obtain ⟨x,hx,rfl⟩ := (rowmem _ _).mp hi
    obtain ⟨y,hy,rfl⟩ := (colmem _ _).mp hj
    by_contra no
    exact proper pres ok (Or.inl no : crossed row col legal x y) (hx.trans hy.symm)
  · intro x
    exact ⟨c x,(rowmem _ _).mpr ⟨x,rfl,rfl⟩,(colmem _ _).mpr ⟨x,rfl,rfl⟩⟩
  · intro b i hi
    obtain ⟨x,hx,rfl⟩ := (rowmem _ _).mp hi
    exact (rowmem _ _).mpr ⟨T x,(invariant ord color x).trans hx,(actions x).1⟩
  · intro b j hj
    obtain ⟨x,hx,rfl⟩ := (colmem _ _).mp hj
    exact (colmem _ _).mpr ⟨T x,(invariant ord color x).trans hx,(actions x).2⟩
end PEqualNP.Outside.L_meta_10007.OddCompletion

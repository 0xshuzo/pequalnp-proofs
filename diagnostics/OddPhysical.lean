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
    have ne : avg T color x ≠ avg T color y :=
      proper (T:=T) (E:=crossed row col legal) (c:=color) (x:=x) (y:=y)
        (fun {u v} h => pres (x:=u) (y:=v) h) (fun {u v} h => ok (x:=u) (y:=v) h) (Or.inl no)
    exact ne (hx.trans hy.symm)
  · intro x
    exact ⟨c x,(rowmem _ _).mpr ⟨x,rfl,rfl⟩,(colmem _ _).mpr ⟨x,rfl,rfl⟩⟩
  · intro b i hi
    obtain ⟨x,hx,rfl⟩ := (rowmem _ _).mp hi
    exact (rowmem _ _).mpr ⟨T x,(invariant ord color x).trans hx,(actions x).1⟩
  · intro b j hj
    obtain ⟨x,hx,rfl⟩ := (colmem _ _).mp hj
    exact (colmem _ _).mpr ⟨T x,(invariant ord color x).trans hx,(actions x).2⟩
end PEqualNP.Outside.L_meta_10007.OddCompletion

namespace PEqualNP.Outside.L_meta_10007.OddPhysical
open OddCompletion
abbrev V := Fin 31
abbrev Box := Finset V × Finset V
def matrix (x y : V) := (([1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736] : List Nat).getD x.val 0).testBit y.val
def hit (A : List Box) (x y : V) := ∃ r∈A,x∈r.1 ∧ y∈r.2
abbrev legal (x y : V) := matrix x y=false
def pU : V → V := ![0,9,2,5,1,20,25,7,29,19,3,11,28,4,10,27,23,17,15,13,14,24,21,18,8,26,12,16,6,22,30]
def lU : V → V := ![15,1,11,5,26,29,6,4,8,9,0,27,24,14,2,18,23,10,17,3,30,16,22,12,21,19,20,13,28,25,7]
set_option maxHeartbeats 1000000 in
theorem boardU : ∀ x y : V,matrix (pU x) (lU y)=matrix x y := by decide +kernel
theorem orderU : (∀ x : V,pU (pU (pU (pU (pU x))))=x) ∧ (∀ y : V,lU (lU (lU (lU (lU y))))=y) := by decide +kernel
def pV : V → V := ![3,9,2,25,1,28,27,20,30,19,12,5,23,4,6,24,21,14,22,13,26,11,7,8,0,15,18,29,16,17,10]
def lV : V → V := ![4,22,24,5,23,16,9,29,8,1,0,27,3,26,19,25,18,11,12,30,10,13,28,20,21,17,2,15,6,14,7]
set_option maxHeartbeats 1000000 in
theorem boardV : ∀ x y : V,matrix (pV x) (lV y)=matrix x y := by decide +kernel
theorem orderV : (∀ x : V,pV (pV (pV (pV (pV x))))=x) ∧ (∀ y : V,lV (lV (lV (lV (lV y))))=y) := by decide +kernel

theorem normalize (p l : V→V) (pres : ∀ x y,matrix (p x) (l y)=matrix x y)
    (ordp : ∀ x,p (p (p (p (p x))))=x) (ordl : ∀ y,l (l (l (l (l y))))=y)
    (A : List Box) (stable : ∀ x y,hit A (p x) (l y) ↔ hit A x y)
    (S : Bool→Box) (empty : ∀ b,∀ i∈(S b).1,∀ j∈(S b).2,legal i j)
    (covers : ∀ x y,legal x y → hit A x y ∨ ∃ b : Bool, x∈(S b).1 ∧ y∈(S b).2) :
    ∃ B : Bool→Box, (∀ b,∀ i∈(B b).1,∀ j∈(B b).2,legal i j) ∧
      (∀ x y,legal x y → hit A x y ∨ ∃ b : Bool,x∈(B b).1 ∧ y∈(B b).2) ∧
      (∀ b,∀ x∈(B b).1,p x∈(B b).1) ∧ (∀ b,∀ y∈(B b).2,l y∈(B b).2) := by
  classical
  let X := {z : V×V // legal z.1 z.2 ∧ ¬hit A z.1 z.2}
  let rt (x : X) : V := x.val.1
  let ct (x : X) : V := x.val.2
  let T (x : X) : X := ⟨(p (rt x),l (ct x)),
    (pres (rt x) (ct x)).trans x.property.1,
    fun h => x.property.2 ((stable _ _).mp h)⟩
  have acts (x : X) : rt (T x)=p (rt x) ∧ ct (T x)=l (ct x) := ⟨rfl,rfl⟩
  have cycle (x : X) : T (T (T (T (T x))))=x := by
    apply Subtype.ext
    apply Prod.ext
    · exact ordp (rt x)
    · exact ordl (ct x)
  have respects {x y : X} (bad : crossed rt ct legal x y) : crossed rt ct legal (T x) (T y) := by
    rcases bad with h | h
    · exact Or.inl (fun k => h ((pres (rt x) (ct y)).symm.trans k))
    · exact Or.inr (fun k => h ((pres (rt y) (ct x)).symm.trans k))
  have eligible (x : X) : ∃ b : Bool,rt x∈(S b).1 ∧ ct x∈(S b).2 :=
    (covers _ _ x.property.1).resolve_left x.property.2
  obtain ⟨B,clean,fill,pr,lr⟩ := physical rt ct legal T p l cycle acts
    (fun {x y} h => respects (x:=x) (y:=y) h) S empty eligible
  refine ⟨B,clean,?_,pr,lr⟩
  intro x y good
  by_cases h : hit A x y
  · exact Or.inl h
  · exact Or.inr (fill (⟨(x,y),good,h⟩ : X))
end PEqualNP.Outside.L_meta_10007.OddPhysical

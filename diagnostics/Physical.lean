import PEqualNP.Outside.L_meta_2264

namespace MixedClosure6796
variable {E : Type} [Fintype E] [DecidableEq E]
abbrev Bank (E : Type) := Finset (Finset E)

/-- Arbitrarily many conjunctions between successive ORs. Allowing the empty
conjunction keeps intersections of zero previous generators uniform. -/
inductive Made (B : Bank E) : Finset E → Prop
  | raw {w} : w∈B → Made B w
  | top : Made B .univ
  | and {a b} : Made B a → Made B b → Made B (a∩b)

theorem mono {B D : Bank E} (sub : B⊆D) {w : Finset E} (h : Made B w) : Made D w := by
  induction h with
  | raw e => exact .raw (sub e)
  | top => exact .top
  | and _ _ a b => exact .and a b

theorem inserted {B : Bank E} {z w : Finset E} (h : Made (insert z B) w) :
    Made B w ∨ ∃ c, Made B c ∧ w=c∩z := by
  induction h with
  | raw memb =>
    rcases Finset.mem_insert.mp memb with eq | mem
    · exact Or.inr ⟨Finset.univ,.top,by simpa using eq⟩
    · exact Or.inl (.raw mem)
  | top => exact Or.inl .top
  | and x y ix iy =>
    rcases ix with ax | ⟨a,ax,rfl⟩ <;> rcases iy with by' | ⟨b,by',rfl⟩
    · exact Or.inl (.and ax by')
    · exact Or.inr ⟨_,.and ax by',by ext i; simp [and_assoc]⟩
    · exact Or.inr ⟨_,.and ax by',by ext i; simp [and_assoc,and_comm,and_left_comm]⟩
    · exact Or.inr ⟨_,.and ax by',by ext i; simp [and_assoc,and_comm,and_left_comm]⟩

def Usable (B : Bank E) (P Q t : Finset E) : Prop :=
  ∃ w, Made B w ∧ Disjoint w Q ∧ t⊆w∩P

noncomputable def Guarded (B : Bank E) (P Q z : Finset E) : Finset E := by
  classical
  exact P.filter (fun e => ∃ c, Made B c ∧ ¬Disjoint c Q ∧ Disjoint (c∩z) Q ∧ e∈c)

theorem splitOr {B : Bank E} {P Q a b t : Finset E} (ha : Made B a) (hb : Made B b)
    (new : Usable (insert (a∪b) B) P Q t) :
    Usable B P Q t ∨
      Usable B P Q (t∩a) ∧ Usable B P Q (t∩b) ∧ t⊆a∪b ∧ t⊆Guarded B P Q (a∪b) := by
  classical
  obtain ⟨w,hw,clean,sub⟩ := new
  rcases inserted hw with old | ⟨c,hc,rfl⟩
  · exact Or.inl ⟨w,old,clean,sub⟩
  · by_cases cc : Disjoint c Q
    · left
      refine ⟨c,hc,cc,?_⟩
      intro e et
      obtain ⟨es,ep⟩ := Finset.mem_inter.mp (sub et)
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp es).1,ep⟩
    right
    have narrow (x : Finset E) (hx : Made B x) (xz : x⊆a∪b) : Usable B P Q (t∩x) := by
      refine ⟨c∩x,.and hc hx,?_,?_⟩
      · apply Finset.disjoint_left.mpr
        intro e ecx eq
        obtain ⟨ec,ex⟩ := Finset.mem_inter.mp ecx
        exact Finset.disjoint_left.mp clean (Finset.mem_inter.mpr ⟨ec,xz ex⟩) eq
      · intro e ex
        obtain ⟨et,ew⟩ := Finset.mem_inter.mp ex
        obtain ⟨es,ep⟩ := Finset.mem_inter.mp (sub et)
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp es).1,ew⟩,ep⟩
    refine ⟨narrow a ha (Finset.subset_union_left),narrow b hb (Finset.subset_union_right),?_,?_⟩
    · intro e et
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp (sub et)).1).2
    · intro e et
      have both := Finset.mem_inter.mp (sub et)
      exact Finset.mem_filter.mpr ⟨both.2,c,hc,cc,clean,(Finset.mem_inter.mp both.1).1⟩

end MixedClosure6796

namespace MixedClosure6796
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2264 PEqualNP.Outside.L_meta_2264.Local1490

variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

def wire (C : Circuit) (rows : E → Fin n → Bool) (w : ℕ) : Finset E :=
  Finset.univ.filter (fun i => BlindGate.wireValue C n (rows i) w)
def roots (rows : E → Fin n → Bool) : Bank E :=
  Finset.univ.image (fun v : Fin n => Finset.univ.filter (fun i => rows i v))
theorem wireMem {C : Circuit} {rows : E → Fin n → Bool} {w i} :
    i∈wire C rows w ↔ val C (List.ofFn (rows i)) w=true := by
  simp [wire,BlindGate.wireValue,val]
theorem inputMem {C : Circuit} {rows : E → Fin n → Bool} {w} (lt : w<n) :
    wire C rows w∈roots rows := by
  refine Finset.mem_image.mpr ⟨⟨w,lt⟩,Finset.mem_univ _,?_⟩
  ext i
  rw [wireMem,val_ofFn C (rows i) ⟨w,lt⟩]
  simp

theorem wireAnd {C : Circuit} (rows : E → Fin n → Bool) (ao : IsAO2 n C)
    {j} (lt : j<C.gates.length) (op : (gateAt C j).op=.and) :
    wire C rows (n+j)=wire C rows (opnd C j 0) ∩ wire C rows (opnd C j 1) := by
  ext i
  rw [wireMem,Finset.mem_inter,wireMem,wireMem]
  exact andValBoth ao lt op (rows i)
theorem wireOr {C : Circuit} (rows : E → Fin n → Bool) (ao : IsAO2 n C)
    {j} (lt : j<C.gates.length) (op : (gateAt C j).op=.or) :
    wire C rows (n+j)=wire C rows (opnd C j 0) ∪ wire C rows (opnd C j 1) := by
  ext i
  obtain ⟨a,b,eq⟩ := binaryInputs ao lt
  rw [wireMem,Finset.mem_union,wireMem,wireMem,val_or (n:=n) (by simp) lt op]
  have bound (v) (hv : v∈(gateAt C j).inputs) := ao.2.1 j lt v hv
  have ha := bound a (by simp [eq])
  have hb := bound b (by simp [eq])
  simp [eq,opnd,ha,hb]

inductive OrRun (good : Finset E → Prop) (B : Bank E) : ℕ → Bank E → Prop
  | start : OrRun good B 0 B
  | emit {r D a b} : OrRun good B r D → Made D a → Made D b →
      good a → good b → good (a∪b) → OrRun good B (r+1) (insert (a∪b) D)

def orCount (C : Circuit) : ℕ → ℕ
  | 0 => 0
  | j+1 => if (gateAt C j).op=.or then orCount C j+1 else orCount C j

theorem circuitBank {C : Circuit} {rows : E → Fin n → Bool} (good : Finset E → Prop)
    (ao : IsAO2 n C) (mixed : ∀ w<n+C.gates.length, good (wire C rows w))
    (j : ℕ) (bound : j≤C.gates.length) :
    ∃ B, OrRun good (roots rows) (orCount C j) B ∧
      ∀ w<n+j, Made B (wire C rows w) := by
  induction j with
  | zero =>
    refine ⟨_,.start,?_⟩
    intro w hw
    exact .raw (inputMem (by simpa using hw))
  | succ j ih =>
    obtain ⟨D,run,earlier⟩ := ih (by omega)
    have hj : j<C.gates.length := by omega
    have ha := opndBound ao hj 0
    have hb := opndBound ao hj 1
    rcases ao.1 _ (gateAt_mem hj) with op | op
    · refine ⟨D,?_,?_⟩
      · simpa [orCount,op] using run
      · intro w hw
        by_cases prev : w<n+j
        · exact earlier w prev
        · have eq : w=n+j := by omega
          rw [eq,wireAnd rows ao hj op]
          exact .and (earlier _ ha) (earlier _ hb)
    · let z := wire C rows (opnd C j 0) ∪ wire C rows (opnd C j 1)
      have wz : wire C rows (n+j)=z := wireOr rows ao hj op
      have ga := mixed (opnd C j 0) (by omega)
      have gb := mixed (opnd C j 1) (by omega)
      have gz := mixed (n+j) (by omega)
      rw [wz] at gz
      refine ⟨insert z D,?_,?_⟩
      · simpa [orCount,op] using OrRun.emit run (earlier _ ha) (earlier _ hb) ga gb gz
      · intro w hw
        by_cases prev : w<n+j
        · exact mono (Finset.subset_insert _ _) (earlier w prev)
        · have eq : w=n+j := by omega
          rw [eq,wz]
          exact .raw (Finset.mem_insert_self _ _)

end MixedClosure6796

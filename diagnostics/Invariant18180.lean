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
      · exact (Finset.disjoint_left.mp hd)
          (show Fin.castAdd m r.1∈Ends A from mem_biUnion.mpr ⟨r,hr,by simp⟩)
          (show Fin.castAdd m r.1∈Ends B from mem_biUnion.mpr ⟨s,hs,by simp [f]⟩)
      · exact (Finset.disjoint_left.mp hd)
          (show Fin.natAdd n r.2∈Ends A from mem_biUnion.mpr ⟨r,hr,by simp⟩)
          (show Fin.natAdd n r.2∈Ends B from mem_biUnion.mpr ⟨s,hs,by simp [f]⟩)
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
  simp only [board,mem_union,mem_map,or_assoc]
  constructor <;> rintro (⟨p,h,eq⟩|⟨p,h,eq⟩|⟨p,h,eq⟩)
  · exact .inl ⟨p,h,eq.symm⟩
  · exact .inr (.inl ⟨p,h,eq.symm⟩)
  · exact .inr (.inr ⟨p,h,eq.symm⟩)
  · exact .inl ⟨p,h,eq.symm⟩
  · exact .inr (.inl ⟨p,h,eq.symm⟩)
  · exact .inr (.inr ⟨p,h,eq.symm⟩)
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
theorem star_row (b : Layout n m N M) {E : Edges n m} {p : Fin n} {z : Fin M}
    (h : (b.tip p,z) ∈ board b E) : z=b.mid p := by
  rcases (on_board _ _ _).1 h with ⟨f,_,eq⟩|⟨q,_,eq⟩|⟨q,_,eq⟩
  · exact False.elim (b.rt _ _ (congrArg Prod.fst eq.symm))
  · exact False.elim (b.rt _ _ (congrArg Prod.fst eq.symm))
  · have hh : p=q := b.tip.injective (congrArg Prod.fst eq)
    subst q
    exact congrArg Prod.snd eq
theorem old_row (b : Layout n m N M) {E : Edges n m} {p : Fin n} {z : Fin M}
    (h : (b.row p,z)∈board b E) :
    (∃ l, (p,l)∈E ∧ z=b.col l) ∨ z=b.mid p := by
  rcases (on_board _ _ _).1 h with ⟨⟨q,l⟩,he,eq⟩|⟨q,_,eq⟩|⟨q,_,eq⟩
  · have hh : p=q := b.row.injective (congrArg Prod.fst eq)
    subst q
    exact Or.inl ⟨l,he,congrArg Prod.snd eq⟩
  · have hh : p=q := b.row.injective (congrArg Prod.fst eq)
    subst q
    exact Or.inr (congrArg Prod.snd eq)
  · exact False.elim (b.rt _ _ (congrArg Prod.fst eq))
theorem board_linear (b : Layout n m N M) {E : Edges n m} (hE : Linear E) : Linear (board b E) := by
  rintro r s i j rs ij ⟨ri,rj,si,sj⟩
  have raw {v x y} (vx : (v,x)∈board b E) (vy : (v,y)∈board b E) (xy : x≠y) :
      ∃ p, v=b.row p := by
    rcases (on_board _ _ _).1 vx with ⟨f,_,eq⟩|⟨p,_,eq⟩|⟨p,_,eq⟩
    · exact ⟨_,congrArg Prod.fst eq⟩
    · exact ⟨_,congrArg Prod.fst eq⟩
    · have ev : v=b.tip p := congrArg Prod.fst eq
      subst v
      exact False.elim (xy ((star_row b vx).trans (star_row b vy).symm))
  obtain ⟨p,rfl⟩ := raw ri rj ij
  obtain ⟨q,rfl⟩ := raw si sj ij
  have pq : p≠q := fun eq => rs (congrArg _ eq)
  have col {z} (pZ : (b.row p,z)∈board b E) (qZ : (b.row q,z)∈board b E) :
      ∃ l, (p,l)∈E ∧ (q,l)∈E ∧ z=b.col l := by
    rcases old_row b pZ with ⟨l,pl,eq⟩|eq <;> rcases old_row b qZ with ⟨k,qk,ev⟩|ev
    · have h : l=k := b.col.injective (eq.symm.trans ev)
      exact ⟨l,pl,h ▸ qk,eq⟩
    · exact False.elim (b.cm _ _ (eq.symm.trans ev))
    · exact False.elim (b.cm _ _ (ev.symm.trans eq))
    · exact False.elim (pq (b.mid.injective (eq.symm.trans ev)))
  obtain ⟨l,pl,ql,rfl⟩ := col ri si
  obtain ⟨k,pk,qk,rfl⟩ := col rj sj
  exact hE p q l k pq (fun eq => ij (congrArg _ eq)) ⟨pl,pk,ql,qk⟩

theorem pull_cover (b : Layout n m N M) (E : Edges n m)
    (U : Finset (Fin N)) (V : Finset (Fin M))
    (cov : ∀ e∈board b E, e.1∈U ∨ e.2∈V) :
    ∃ A : Finset (Fin n), ∃ B : Finset (Fin m),
    (∀ e∈E, e.1∈A ∨ e.2∈B) ∧ A.card+B.card+(active E).card≤U.card+V.card := by
  classical
  let A := univ.filter fun p => b.row p∈U
  let B := univ.filter fun l => b.col l∈V
  let X := (active E).filter fun p => b.tip p∈U
  let Y := active E \ X
  have subX : X⊆active E := filter_subset _ _
  have ca := Finset.card_sdiff_add_card_eq_card subX
  change Y.card+X.card=(active E).card at ca
  have bound {α β γ : Type} [DecidableEq γ] (f : α ↪ γ) (g : β ↪ γ)
      (sep : ∀ i j, f i ≠ g j) {I : Finset α} {J : Finset β} {T : Finset γ}
      (hI : ∀ i∈I,f i∈T) (hJ : ∀ j∈J,g j∈T) : I.card+J.card≤T.card := by
    have dis : Disjoint (I.map f) (J.map g) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i,_,rfl⟩ := mem_map.mp hz
      obtain ⟨j,_,eq⟩ := mem_map.mp hz'
      exact sep i j eq.symm
    have sub : I.map f ∪ J.map g ⊆ T := by
      intro z hz
      rcases mem_union.mp hz with h|h
      · obtain ⟨i,hi,rfl⟩ := mem_map.mp h
        exact hI i hi
      · obtain ⟨j,hj,rfl⟩ := mem_map.mp h
        exact hJ j hj
    simpa [card_union_of_disjoint dis] using card_le_card sub
  have left : A.card+X.card≤U.card := bound b.row b.tip b.rt
    (fun _ h => (mem_filter.mp h).2) (fun _ h => (mem_filter.mp h).2)
  have right : B.card+Y.card≤V.card := by
    apply bound b.col b.mid b.cm (fun _ h => (mem_filter.mp h).2)
    intro p hp
    have hp' := mem_sdiff.mp hp
    rcases cov _ ((on_board b E _).2 (.inr (.inr ⟨p,hp'.1,rfl⟩))) with h|h
    · exact False.elim (hp'.2 (mem_filter.mpr ⟨hp'.1,h⟩))
    · exact h
  refine ⟨A,B,?_,by omega⟩
  intro e he
  rcases cov _ ((on_board b E _).2 (.inl ⟨e,he,rfl⟩)) with h|h
  · exact .inl (mem_filter.mpr ⟨mem_univ _,h⟩)
  · exact .inr (mem_filter.mpr ⟨mem_univ _,h⟩)

theorem lift_budget (b : Layout n m N M) (E : Edges n m) (s t : Nat)
    (h : Budget (board b E) t) (small : t≤s+3*(active E).card) : Budget E s := by
  obtain ⟨U,V,cov,price⟩ := h
  obtain ⟨A,B,hit,charge⟩ := pull_cover b E U V cov
  rw [board_card] at price
  exact ⟨A,B,hit,by omega⟩
namespace GridCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
def Good (base : ℕ) (gs : List Gate) := ∀ j (hj : j<gs.length),
  (gs[j].op = .and ∨ gs[j].op = .or) ∧ gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < base+j
theorem good_iff (n) (C : Circuit) : Good n C.gates ↔ IsAO2 n C := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg; exact (h j hj).1
    · intro j hj k hk
      have eq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
      exact (h j hj).2.2 k (eq ▸ hk)
    · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg; exact (h j hj).2.1
  · rintro ⟨hm,hb,ha⟩ j hj
    have eq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
    exact ⟨hm _ (List.getElem_mem hj),ha _ (List.getElem_mem hj),fun k hk => hb j hj k (eq ▸ hk)⟩

theorem good_append {n} {a b : List Gate} (ha : Good n a) (hb : Good (n+a.length) b) : Good n (a++b) := by
  intro j hj
  by_cases h : j<a.length
  · simpa only [List.getElem_append_left h] using ha j h
  · have hy : j-a.length < b.length := by simp at hj; omega
    have h1 := hb (j-a.length) hy
    rw [show n+a.length+(j-a.length)=n+j by omega] at h1
    simpa only [List.getElem_append_right (by omega : a.length≤j)] using h1

def name {n m} (f : Fin n → Fin m) (base i : ℕ) :=
  if hi : i<n then (f ⟨i,hi⟩).val else base+(i-n)
def renameG {n m} (f : Fin n → Fin m) (base : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (name f base)⟩
theorem name_lt {n m} (f : Fin n → Fin m) {base j i : ℕ} (hb : m≤base) (hi : i<n+j) :
    name f base i < base+j := by
  unfold name
  split
  next h => have := (f ⟨i,h⟩).isLt; omega
  next => omega

theorem good_rename {n m base gs} (f : Fin n → Fin m) (hb : m≤base) (h : Good n gs) :
    Good base (gs.map (renameG f base)) := by
  intro j hj
  have hj' : j<gs.length := by simpa using hj
  simp only [List.getElem_map,renameG,List.length_map]
  obtain ⟨ho,hl,hi⟩ := h j hj'
  refine ⟨ho,hl,?_⟩
  intro k hk
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hk
  exact name_lt f hb (hi i hi')

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]; simp [step]; omega
theorem old (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k<w.length) : (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem lookup {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m ≤ W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (z : List Bool) (i : Nat) :
    (W++z).getD (name f W.length i) false = (List.ofFn x++z).getD i false := by
  unfold name
  split
  next hi =>
    rw [List.getD_append _ _ _ _ (by have := (f ⟨i,hi⟩).isLt; omega),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD,hi] using ag ⟨i,hi⟩
  next hi =>
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : W.length ≤ W.length+(i-n)),
      List.getElem?_append_right (by simp;omega : (List.ofFn x).length ≤ i),List.length_ofFn,Nat.add_sub_cancel_left]

theorem sim {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (gs : List Gate) (z : List Bool) :
    ∃ endBits, run gs (List.ofFn x ++ z) = List.ofFn x ++ endBits ∧
      run (gs.map (renameG f W.length)) (W++z) = W++endBits := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (List.ofFn x ++ z).getD i false)
    obtain ⟨t,h1,h2⟩ := ih (z++[bit])
    refine ⟨t,?_,?_⟩
    · simpa [run,step,bit,List.append_assoc] using h1
    · have hstep : step (W++z) (renameG f W.length g) = W++(z++[bit]) := by
        simp only [step,renameG,List.map_map,Function.comp_def,lookup f W hw x ag,List.append_assoc,bit]
      change run _ (step (W++z) (renameG f W.length g)) = _
      rw [hstep];exact h2

theorem copy_val {n m} (f : Fin n → Fin m) (W : List Bool) (hw : m≤W.length)
    (x : Fin n → Bool) (ag : ∀ p, W.getD (f p).val false = x p) (C : Circuit) :
    (run (C.gates.map (renameG f W.length)) W).getD (name f W.length C.output) false = circuitFun n C x := by
  obtain ⟨z,h1,h2⟩ := sim f W hw x ag C.gates []
  simp only [List.append_nil] at h1 h2
  change _ = (run C.gates (List.ofFn x)).getD C.output false
  rw [h1,h2,lookup _ _ hw x ag]

def Gadget {n} (f : (Fin n → Bool) → Bool) (k : ℕ) := ∃ C : Circuit, IsAO2 n C ∧
  C.output < n + C.gates.length ∧ C.size = k ∧ circuitFun n C = f

theorem output_valid {n} (C : Circuit) (yes : ∃ x, circuitFun n C x = true) :
    C.output<n+C.gates.length := by
  by_contra! h
  obtain ⟨x,hx⟩ := yes
  change (run C.gates (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by simpa [len] using h)] at hx;contradiction

theorem relabel {n m} (C : Circuit) (ok : IsAO2 n C) (valid : C.output<n+C.gates.length)
    (f : Fin n → Fin m) :
    Gadget (fun x => circuitFun n C (x ∘ f)) C.size := by
  let D : Circuit := ⟨C.gates.map (renameG f m),name f m C.output⟩
  refine ⟨D,(good_iff m D).mp (good_rename f le_rfl ((good_iff n C).mpr ok)),?_,?_,?_⟩
  · simpa only [D,List.length_map] using name_lt f le_rfl valid
  · simp [Circuit.size,D]
  · funext x
    have h := copy_val f (List.ofFn x) (by simp) (x ∘ f) (fun i => by simp [List.getD]) C
    change (run (C.gates.map (renameG f m)) (List.ofFn x)).getD (name f m C.output) false = _
    simpa only [List.length_ofFn] using h

def op (b : Bool) : GateOp := if b then .and else .or
def bop (b p q : Bool) : Bool := if b then p && q else p || q

theorem last_ok (base i j) (b : Bool) (hi : i<base) (hj : j<base) :
    Good base [⟨op b,[i,j]⟩] := by
  intro k hk
  have eq : k=0 := by simp at hk;omega
  subst k; cases b <;> simp [op,hi,hj]

theorem last_eval (g : Gate) (W : List Bool) : (run [g] W).getD W.length false =
    g.op.eval (g.inputs.map fun i => W.getD i false) := by simp [run,step,List.getD]

theorem append_run (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := List.foldl_append

theorem join {n k l} {f g : (Fin n → Bool) → Bool} (b : Bool)
    (hA : Gadget f k) (hB : Gadget g l) : Gadget (fun x => bop b (f x) (g x)) (k+l+1) := by
  obtain ⟨A,ao,ab,asz,ae⟩ := hA
  obtain ⟨B,bo,bb,bsz,be⟩ := hB
  let base := n+A.gates.length
  let bs := B.gates.map (renameG (id : Fin n → Fin n) base)
  let bi := name (id : Fin n → Fin n) base B.output
  let ov := base+bs.length
  let newGate : Gate := ⟨op b,[A.output,bi]⟩
  let D : Circuit := ⟨A.gates ++ bs ++ [newGate],ov⟩
  have bl : bs.length = B.gates.length := by simp [bs]
  have bn : n≤base := by simp [base]
  have blo : bi<ov := by unfold ov; rw [bl]; exact name_lt id bn bb
  have alo : A.output<ov := Nat.lt_of_lt_of_le ab (Nat.le_add_right _ _)
  have og : Good base bs := good_rename id bn ((good_iff n B).mpr bo)
  have wa : n+(A.gates++bs).length=ov := by simp [ov,base,Nat.add_assoc]
  refine ⟨D,(good_iff n D).mp (good_append (good_append ((good_iff _ _).mpr ao) og)
    (wa ▸ last_ok ov A.output bi b alo blo)),?_,?_,?_⟩
  · simp [D,ov,base,List.length_append]; omega
  · change A.gates.length=k at asz
    change B.gates.length=l at bsz
    simp [Circuit.size,D,bl,asz,bsz,Nat.add_assoc]
  · funext x
    let W := run A.gates (List.ofFn x)
    let Y := run bs W
    have wl : W.length=base := by simp [W,len,base]
    have yl : Y.length=ov := by simp [Y,len,wl,ov]
    have ah : Y.getD A.output false = f x := by
      rw [show Y.getD A.output false = W.getD A.output false from old bs W A.output (wl ▸ ab)]
      exact congrFun ae x
    have inh (p : Fin n) : W.getD ((id : Fin n → Fin n) p).val false = x p := by
      change (run A.gates (List.ofFn x)).getD p.val false = x p
      rw [old A.gates _ _ (by simp)]
      simp [List.getD]
    have bv := copy_val (id : Fin n → Fin n) W (wl ▸ bn) x inh B
    have bh : Y.getD bi false = g x := by
      change (run (B.gates.map (renameG id base)) W).getD (name id base B.output) false = _
      rw [←wl]
      exact bv.trans (congrFun be x)
    change (run (A.gates++bs++[newGate]) (List.ofFn x)).getD ov false = _
    rw [append_run,append_run]
    change (run [newGate] Y).getD ov false = _
    rw [←yl,last_eval]
    simp only [newGate,List.map_cons,List.map_nil,ah,bh]
    cases b <;> simp [op,bop,GateOp.eval]

theorem atom {n} (u : Fin n) : Gadget (fun x => x u) 0 := by
  let C : Circuit := ⟨[],u.val⟩
  refine ⟨C,(good_iff _ _).mp (by intro j hj; simp [C] at hj),by simpa [C] using u.isLt,rfl,?_⟩
  funext x
  simp [circuitFun,Circuit.eval,Circuit.wires,C,List.getD]

theorem gather {n} {α : Type} (val : α → (Fin n → Bool) → Bool) (cost : α → ℕ) (l : List α)
    (exist : l≠[]) (ok : ∀ a∈l, Gadget (val a) (cost a)) :
    Gadget (fun x => l.any (fun a => val a x)) ((l.map cost).sum+(l.length-1)) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    have head := ok a List.mem_cons_self
    by_cases hz : l=[]
    · subst l; simpa using head
    have tail := ih hz (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    have both := join false head tail
    have hl : 0<l.length := List.length_pos_iff.mpr hz
    have cnt : cost a+((l.map cost).sum+(l.length-1))+1 =
        ((a::l).map cost).sum+((a::l).length-1) := by simp;omega
    rw [←cnt]
    simpa [bop] using both

def star {n} (st : Fin n × List (Fin n)) (x : Fin n → Bool) := x st.1 && st.2.any x
theorem star_ok {n} (st : Fin n × List (Fin n)) (nonempty : st.2≠[]) : Gadget (star st) st.2.length := by
  have hl : 0<st.2.length := List.length_pos_iff.mpr nonempty
  have g := gather (fun (i : Fin n) (x : Fin n → Bool) => x i) (fun _ => 0)
    st.2 nonempty (fun i _ => atom i)
  have gz : (st.2.map fun _ => (0 : ℕ)).sum=0 := by simp
  rw [gz,Nat.zero_add] at g
  have h := join true (atom st.1) g
  have cnt : 0 + (st.2.length - 1) + 1 = st.2.length := by omega
  rw [cnt] at h
  exact h

theorem sum_constant {α} (l : List α) (k : Nat) : (l.map fun _ => k).sum = l.length*k := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,ih];omega

theorem assemble {n m : ℕ} (C : Circuit) (ok : IsAO2 n C) (valid : C.output < n+C.gates.length)
    (copies : List (Fin n → Fin m)) (hc : copies ≠ []) (stars : List (Fin m × List (Fin m)))
    (hs : ∀ st ∈ stars, st.2 ≠ []) :
    ∃ D : Circuit, IsAO2 m D ∧ D.output < m+D.gates.length ∧
      D.size ≤ copies.length*C.size+(copies.length-1)+(stars.map (fun st => st.2.length)).sum+stars.length ∧
      ∀ x, circuitFun m D x = true ↔
        (∃ f ∈ copies, circuitFun n C (x ∘ f) = true) ∨
        ∃ st ∈ stars, x st.1=true ∧ ∃ leaf ∈ st.2, x leaf=true := by
  let A : List (((Fin m → Bool) → Bool) × ℕ) :=
    copies.map (fun f => (fun x => circuitFun n C (x ∘ f),C.size))
  let B : List (((Fin m → Bool) → Bool) × ℕ) := stars.map (fun st => (star st,st.2.length))
  have nne : A++B ≠ [] := by simpa [A,B] using (show ¬(copies=[] ∧ stars=[]) from fun h => hc h.1)
  have hg (q) (hq : q ∈ A++B) : Gadget q.1 q.2 := by
    rcases List.mem_append.mp hq with hh|hh
    · obtain ⟨f,_,rfl⟩ := List.mem_map.mp hh
      exact relabel C ok valid f
    · obtain ⟨st,hst,rfl⟩ := List.mem_map.mp hh
      exact star_ok st (hs st hst)
  obtain ⟨D,hd,hb,sz,eval⟩ := gather (fun q => q.1) (fun q => q.2) (A++B) nne hg
  refine ⟨D,hd,hb,?_,?_⟩
  · rw [sz]
    have hl := List.length_pos_iff.mpr hc
    simp only [A,B,List.map_append,List.map_map,Function.comp_def,List.sum_append,
      List.length_append,List.length_map,sum_constant]
    omega
  · intro x
    rw [eval]
    simp [A,B,star,List.any_eq_true]

end GridCircuit
def sideMap (b : Layout n m N M) : Fin (n+m) → Fin (N+M) :=
  Fin.addCases (fun p => Fin.castAdd M (b.row p)) (fun l => Fin.natAdd N (b.col l))
def pathStar (b : Layout n m N M) (p : Fin n) : Fin (N+M) × List (Fin (N+M)) :=
  (Fin.natAdd N (b.mid p),[Fin.castAdd M (b.row p),Fin.castAdd M (b.tip p)])

theorem board_circuit (b : Layout n m N M) {E : Edges n m} (ne : E.Nonempty)
    (C : Circuit) (ao : IsAO2 (n+m) C) (spec : ∀ x, circuitFun (n+m) C x=Flags E x) :
    ∃ D : Circuit, IsAO2 (N+M) D ∧ D.size≤C.size+3*(active E).card ∧
      ∀ x, circuitFun (N+M) D x=Flags (board b E) x := by
  classical
  have valid : C.output < n+m+C.gates.length := by
    apply GridCircuit.output_valid
    refine ⟨fun _ => true,?_⟩
    rw [spec,Flags,decide_eq_true_eq]
    obtain ⟨e,he⟩ := ne
    exact ⟨e,he,rfl,rfl⟩
  let ps := (active E).toList
  let stars := ps.map (pathStar b)
  have non (st) (h : st∈stars) : st.2≠[] := by
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp h
    simp [pathStar]
  obtain ⟨D,good,_,cost,correct⟩ := GridCircuit.assemble C ao valid [sideMap b] (by simp) stars non
  have cnt : (stars.map (fun st => st.2.length)).sum = ps.length*2 := by
    simpa [stars,List.map_map,Function.comp_def,pathStar] using GridCircuit.sum_constant ps 2
  have sz : ps.length=(active E).card := by simp [ps]
  refine ⟨D,good,?_,?_⟩
  · rw [cnt] at cost
    simp [stars,sz] at cost
    omega
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [correct,Flags,decide_eq_true_eq]
    have copied : (∃ f∈[sideMap b], circuitFun (n+m) C (x ∘ f)=true) ↔
        ∃ e∈E, x (Fin.castAdd M (b.row e.1))=true ∧ x (Fin.natAdd N (b.col e.2))=true := by
      simp [spec,Flags,sideMap,Function.comp_def]
    rw [copied]
    constructor
    · rintro (⟨e,he,hp,hl⟩|⟨st,hst,hl,i,hi,hp⟩)
      · exact ⟨_,(on_board b E _).2 (.inl ⟨e,he,rfl⟩),hp,hl⟩
      · obtain ⟨p,hs,rfl⟩ := List.mem_map.mp hst
        have act : p∈active E := by simpa [ps] using hs
        change i∈[Fin.castAdd M (b.row p),Fin.castAdd M (b.tip p)] at hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl
        · exact ⟨_,(on_board b E _).2 (.inr (.inl ⟨p,act,rfl⟩)),hp,hl⟩
        · exact ⟨_,(on_board b E _).2 (.inr (.inr ⟨p,act,rfl⟩)),hp,hl⟩
    · rintro ⟨e,he,hp,hl⟩
      rcases (on_board _ _ _).1 he with ⟨f,hf,rfl⟩|⟨p,hm,rfl⟩|⟨p,hm,rfl⟩
      · exact .inl ⟨f,hf,hp,hl⟩
      · refine .inr ⟨pathStar b p,List.mem_map.mpr ⟨p,by simpa [ps] using hm,rfl⟩,hl,_,?_,hp⟩
        simp [pathStar]
      · refine .inr ⟨pathStar b p,List.mem_map.mpr ⟨p,by simpa [ps] using hm,rfl⟩,hl,_,?_,hp⟩
        simp [pathStar]
namespace Cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit simplifier is adapted from L_meta_7328 and L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma op_cases {g : Gate} (h : Good g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa using h.1

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Good g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Good]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Good]
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Good g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op (op_cases hgok) w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

-- Every gate with a constant input can be omitted. An absorbing input
-- additionally marks the gate output as a constant for the next gate.
def absorb : GateOp → Bool
  | .or => true
  | _ => false

lemma simplify_drop (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : ∃ b, Sum.inl b ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨b, hb⟩
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hb hl
  all_goals cases s <;> (try cases t) <;> simp_all [simplify, simpAnd, simpOr]

lemma simplify_absorb (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : Sum.inl (absorb op) ∈ ins) :
    (simplify op m ins).2 = Sum.inl (absorb op) := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hc hl
  all_goals cases s <;> (try cases t) <;> simp_all [absorb, simplify, simpAnd, simpOr]
  grind

abbrev State := List Stat × List Gate

def stat (s : State) (i : ℕ) : Stat := s.1.getD i (Sum.inl false)

def plan (n : ℕ) (s : State) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + s.2.length) (g.inputs.map (stat s))

lemma elim_append (n : ℕ) (pre post : List Gate) (s : State) :
    elim n (pre ++ post) s = elim n post (elim n pre s) := by
  simp [elim, List.foldl_append]

lemma elim_extends (n : ℕ) (gs : List Gate) (s : State) :
    ∃ t, (elim n gs s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (elimStep n s g)
    refine ⟨(plan n s g).2 :: t, ?_, by simp [hlen]⟩
    change (elim n gs (elimStep n s g)).1 = _
    rw [ht]
    change (s.1 ++ [(plan n s g).2]) ++ t = _
    simp

lemma elim_stat (n : ℕ) (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    stat (elim n gs s) i = stat s i := by
  obtain ⟨t, ht, _⟩ := elim_extends n gs s
  unfold stat
  rw [ht, List.getD_append _ _ _ _ hi]

lemma elim_good (n : ℕ) (gs : List Gate) (s : State)
    (h : ∀ g ∈ gs, Good g) (hs : ∀ g ∈ s.2, Good g) :
    ∀ g ∈ (elim n gs s).2, Good g := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    change ∀ g' ∈ (elim n gs (elimStep n s g)).2, Good g'
    apply ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro a ha
    change a ∈ s.2 ++ (plan n s g).1.toList at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hs a ha
    · exact simplify_ok _ _ _ a (by simpa [plan] using ha)

def fix {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = p then b else x i

def initial {n : ℕ} (p : Fin n) (b : Bool) : State :=
  (List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val, [])

lemma initial_length {n : ℕ} (p : Fin n) (b : Bool) :
    (initial p b).1.length = n := by simp [initial]

lemma initial_stat {n : ℕ} (p : Fin n) (b : Bool) : stat (initial p b) p.val = Sum.inl b := by
  simp [stat, initial]

lemma initial_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p b x)) (initial p b) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (initial p b) j.val).Valid _ ∧ (stat (initial p b) j.val).val _ = _
    by_cases hj : j = p <;>
      simp [stat, initial, fix, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma drop_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} {b : Bool} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl b) :
    (plan n s g).1 = none := by
  apply simplify_drop _ (op_cases hg) _ _ (by simpa using hg.2)
  exact ⟨b, hb ▸ List.mem_map_of_mem hi⟩

lemma absorb_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl (absorb g.op)) :
    (plan n s g).2 = Sum.inl (absorb g.op) := by
  apply simplify_absorb _ (op_cases hg) _ _ (by simpa using hg.2)
  exact hb ▸ List.mem_map_of_mem hi

lemma restriction (C : Circuit) (hm : Monotone2 C) {n : ℕ} (p : Fin n) (b : Bool)
    (hnc : ∃ x y, circuitFun n C (fix p b x) ≠ circuitFun n C (fix p b y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧
      D.size = (elim n C.gates (initial p b)).2.length := by
  let s := elim n C.gates (initial p b)
  have hval (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) =
        circuitFun n C (fix p b x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (initial_inv p b x)).2 C.output).2
  cases hz : stat s C.output with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [hz] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ hm (by simp [initial]), ?_, rfl⟩
    intro x
    change (wiresFrom s.2 (List.ofFn x)).getD j false = _
    simpa only [hz, Stat.val] using hval x

lemma single_drop {n : ℕ} (p : Fin n) (b : Bool) (pre post : List Gate) (g : Gate)
    (hg : Good g) (hp : p.val ∈ g.inputs) :
    (elim n (pre ++ g :: post) (initial p b)).2.length + 1 ≤
      (pre ++ g :: post).length := by
  let s := elim n pre (initial p b)
  have hs : stat s p.val = Sum.inl b :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p b)
  have hd := drop_at_reader n s g hg hp hs
  have hpre := elim_len n pre (initial p b)
  have hpost := elim_len n post (elimStep n s g)
  rw [elim_append]
  change (elim n post (elimStep n s g)).2.length + 1 ≤ _
  have hstep : (elimStep n s g).2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  rw [hstep] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  simp only [List.length_append, List.length_cons]
  omega

lemma double_drop {n : ℕ} (p : Fin n) (pre mid post : List Gate) (g h : Gate)
    (hg : Good g) (hh : Good h) (hp : p.val ∈ g.inputs) (hr : n + pre.length ∈ h.inputs) :
    (elim n (pre ++ g :: (mid ++ h :: post)) (initial p (absorb g.op))).2.length + 2 ≤
      (pre ++ g :: (mid ++ h :: post)).length := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  let u := elim n mid t
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hd := drop_at_reader n s g hg hp hs
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hu := (elim_stat n mid t _ hlt).trans ht
  have hd' := drop_at_reader n u h hh hr hu
  have hpre := elim_len n pre (initial p (absorb g.op))
  have hmid := elim_len n mid t
  have hpost := elim_len n post (elimStep n u h)
  have hstep : t.2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  have hstep' : (elimStep n u h).2.length = u.2.length := by
    change (u.2 ++ (plan n u h).1.toList).length = _
    simp [hd']
  rw [hstep] at hmid
  rw [hstep'] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  change u.2.length ≤ _ at hmid
  rw [elim_append]
  change (elim n (mid ++ h :: post) t).2.length + 2 ≤ _
  rw [elim_append]
  change (elim n post (elimStep n u h)).2.length + 2 ≤ _
  simp only [List.length_append, List.length_cons]
  omega

-- A dependency trace either reaches a direct reader or contains two successive gates.
def Direct (n p w : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre post : List Gate) (g : Gate),
    gs = pre ++ g :: post ∧ p ∈ g.inputs ∧ w = n + pre.length

def Chain (n p : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre mid post : List Gate) (g h : Gate),
    gs = pre ++ g :: (mid ++ h :: post) ∧ p ∈ g.inputs ∧ n + pre.length ∈ h.inputs

lemma wire_trace {n p : ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ w, w ≠ p → x.getD w false = y.getD w false)
    (gs : List Gate) (w : ℕ)
    (hne : (wiresFrom gs x).getD w false ≠ (wiresFrom gs y).getD w false) :
    w = p ∨ Direct n p w gs ∨ Chain n p gs := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    exact Or.inl (by by_contra h; exact hne (hxy w h))
  | append_singleton gs g ih =>
    have hxlen : (wiresFrom gs x).length = n + gs.length := by rw [length_wiresFrom, hx]
    have hylen : (wiresFrom gs y).length = n + gs.length := by rw [length_wiresFrom, hy]
    rw [wiresFrom_append, wiresFrom_append] at hne
    change ((wiresFrom gs x) ++ [_]).getD w false ≠
      ((wiresFrom gs y) ++ [_]).getD w false at hne
    by_cases hw : w = n + gs.length
    · rw [getD_snoc_len _ _ _ _ (hxlen.trans hw.symm),
          getD_snoc_len _ _ _ _ (hylen.trans hw.symm)] at hne
      obtain ⟨i, hi, hdiff⟩ : ∃ i ∈ g.inputs,
          (wiresFrom gs x).getD i false ≠ (wiresFrom gs y).getD i false := by
        by_contra! hsame
        apply hne
        apply congrArg (GateOp.eval g.op)
        exact List.map_congr_left hsame
      rcases ih i hdiff with rfl | ⟨pre, post, h, he, hr, rfl⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inr (Or.inl ⟨gs, [], g, rfl, hi, hw⟩)
      · exact Or.inr (Or.inr ⟨pre, post, [], h, g, by simp [he, List.append_assoc], hr, hi⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)
    · rw [getD_snoc_ne _ _ _ _ (by rwa [hxlen]), getD_snoc_ne _ _ _ _ (by rwa [hylen])] at hne
      rcases ih w hne with hp | ⟨pre, post, h, he, hr, hval⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨pre, post ++ [g], h, by simp [he, List.append_assoc], hr, hval⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)

lemma fix_agree {n : ℕ} (p : Fin n) (x : Fin n → Bool) (w : ℕ) (hw : w ≠ p.val) :
    (List.ofFn (fix p false x)).getD w false =
      (List.ofFn (fix p true x)).getD w false := by
  by_cases hi : w < n
  · let i : Fin n := ⟨w, hi⟩
    have hn : i ≠ p := fun h => hw (congrArg Fin.val h)
    change (List.ofFn (fix p false x)).getD i.val false =
      (List.ofFn (fix p true x)).getD i.val false
    simp [fix, hn]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

def Essential {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x, f (fix p false x) ≠ f (fix p true x)

lemma trace_of_essential {n : ℕ} (C : Circuit) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    Direct n p.val C.output C.gates ∨ Chain n p.val C.gates := by
  obtain ⟨x, hx⟩ := he
  rcases wire_trace (n := n) (x := List.ofFn (fix p false x)) (y := List.ofFn (fix p true x))
      (by simp) (by simp) (fix_agree p x) C.gates C.output hx with hp | h
  · exfalso
    obtain ⟨v, w, hne⟩ := hnc
    apply hne
    have heval (z : Fin n → Bool) : circuitFun n C (fix p false z) = false := by
      change (wiresFrom C.gates (List.ofFn (fix p false z))).getD C.output false = false
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn (fix p false z))
      rw [hp, ht, List.getD_append _ _ _ _ (by simp)]
      simp [fix]
    change circuitFun n C (fix p false v) = circuitFun n C (fix p false w)
    rw [heval v, heval w]
  · exact h

lemma direct_const {n : ℕ} (p : Fin n) (pre post : List Gate) (g : Gate)
    (hm : ∀ h ∈ pre ++ g :: post, Good h) (hp : p.val ∈ g.inputs) (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ g :: post, n + pre.length⟩ (fix p (absorb g.op) x) = absorb g.op := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  have hg : Good g := hm g (by simp)
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hstat : stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length) =
      Sum.inl (absorb g.op) := by
    rw [elim_append]
    exact (elim_stat n post t _ hlt).trans ht
  have hval := ((inv_elim n _ (by simp) _ _ _ hm (initial_inv p (absorb g.op) x)).2
    (n + pre.length)).2
  change (stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length)).val _ = _ at hval
  rw [hstat] at hval
  exact hval.symm

lemma leaf_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : ∀ b, Nonconstant (fun x => circuitFun n C (fix p b x))) :
    ∃ (b : Bool) (D : Circuit), Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧ D.size + 2 ≤ C.size := by
  rcases trace_of_essential C p he (hnc false) with hd | ⟨pre, mid, post, g, h, hgs, hp, hr⟩
  · rcases C with ⟨gs, out⟩
    obtain ⟨pre, post, g, rfl, hp, rfl⟩ := hd
    obtain ⟨x, y, hxy⟩ := hnc (absorb g.op)
    exact False.elim (hxy ((direct_const p pre post g hm hp x).trans
      (direct_const p pre post g hm hp y).symm))
  · obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p (absorb g.op) (hnc _)
    refine ⟨absorb g.op, D, hD, hval, ?_⟩
    have hg : Good g := hm g (by simp [hgs])
    have hh : Good h := hm h (by simp [hgs])
    rw [hsz, Circuit.size, hgs]
    exact double_drop p pre mid post g h hg hh hp hr

lemma center_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) ∧
      D.size ≤ C.size ∧ (Essential (circuitFun n C) p → D.size + 1 ≤ C.size) := by
  obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p false hnc
  refine ⟨D, hD, hval, ?_, ?_⟩
  · rw [hsz, Circuit.size]
    simpa [initial] using elim_len n C.gates (initial p false)
  · intro he
    rw [hsz, Circuit.size]
    have hr : ∃ pre post g, C.gates = pre ++ g :: post ∧ p.val ∈ g.inputs := by
      rcases trace_of_essential C p he hnc with ⟨pre, post, g, hh, hg, _⟩ |
        ⟨pre, mid, post, g, h, hh, hg, _⟩
      · exact ⟨pre, post, g, hh, hg⟩
      · exact ⟨pre, mid ++ h :: post, g, hh, hg⟩
    obtain ⟨pre, post, g, hh, hg⟩ := hr
    have hg' := hm g (by simp [hh])
    rw [hh]
    exact single_drop p false pre post g hg' hg

abbrev left {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.castAdd b e.1

abbrev right {a b : ℕ} (e : Fin a × Fin b) : Fin (a + b) := Fin.natAdd a e.2

abbrev incident {a b : ℕ} (i : Fin (a + b)) (e : Fin a × Fin b) : Prop :=
  left e = i ∨ right e = i

def edgeFun {a b : ℕ} (E : Finset (Fin a × Fin b)) (x : Fin (a + b) → Bool) : Bool :=
  decide (∃ e ∈ E, x (left e) = true ∧ x (right e) = true)

lemma edge_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {x : Fin (a + b) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, x (left e) = true ∧ x (right e) = true := by
  simp [edgeFun]

lemma endpoints_ne {a b : ℕ} (e : Fin a × Fin b) : left e ≠ right e := by
  intro h
  have hv := congrArg Fin.val h
  change e.1.val = a + e.2.val at hv
  omega

lemma both_endpoints {a b : ℕ} {e : Fin a × Fin b} {p q : Fin (a + b)}
    (hn : p ≠ q) (hp : incident p e) (hq : incident q e) :
    (left e = p ∧ right e = q) ∨ (left e = q ∧ right e = p) := by
  rcases hp with hl | hr <;> rcases hq with hl' | hr'
  · exact (hn (hl.symm.trans hl')).elim
  · exact Or.inl ⟨hl, hr'⟩
  · exact Or.inr ⟨hl', hr⟩
  · exact (hn (hr.symm.trans hr')).elim

lemma single_support_false {a b : ℕ} (E : Finset (Fin a × Fin b))
    (x : Fin (a + b) → Bool) (r : Fin (a + b))
    (h : ∀ i, x i = true → i = r) : edgeFun E x = false := by
  cases he : edgeFun E x with
  | false => rfl
  | true =>
    obtain ⟨e, _, hl, hr⟩ := edge_true.mp he
    exact (endpoints_ne e ((h _ hl).trans (h _ hr).symm)).elim

def one {n : ℕ} (r i : Fin n) : Bool := decide (i = r)

lemma one_false {a b : ℕ} (E : Finset (Fin a × Fin b)) (r : Fin (a + b)) :
    edgeFun E (one r) = false := by
  apply single_support_false E _ r
  simp [one]

lemma pair_true {a b : ℕ} {E : Finset (Fin a × Fin b)} {e : Fin a × Fin b}
    {p q : Fin (a + b)} (he : e ∈ E) (hn : p ≠ q)
    (hp : incident p e) (hq : incident q e) :
    edgeFun E (fix p true (one q)) = true := by
  apply edge_true.mpr
  refine ⟨e, he, ?_⟩
  rcases both_endpoints hn hp hq with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp [hl, hr, fix, one, hn.symm]

lemma fix_one_false {n : ℕ} {p q : Fin n} (h : p ≠ q) :
    fix p false (one q) = one q := by
  funext i
  by_cases hi : i = p <;> simp [fix, one, hi, h]

lemma graph_nonconstant {a b : ℕ} {E : Finset (Fin a × Fin b)}
    (h : E.Nonempty) (p : Fin (a + b)) : Nonconstant (edgeFun E) := by
  obtain ⟨e, he⟩ := h
  refine ⟨one p, fun _ => true, ?_⟩
  rw [one_false, edge_true.mpr ⟨e, he, rfl, rfl⟩]
  decide

lemma delete_center {a b : ℕ} (E : Finset (Fin a × Fin b))
    (p q : Fin (a + b)) (hpq : ∀ e ∈ E, incident p e → incident q e)
    (hn : p ≠ q) (bval : Bool) (x : Fin (a + b) → Bool) :
    edgeFun E (fix p bval (fix q false x)) = edgeFun (E.filter fun e => ¬incident q e) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [edge_true, Finset.mem_filter]
  constructor
  · rintro ⟨e, he, hl, hr⟩
    have hq : ¬incident q e := by
      rintro (hq | hq)
      · simp [fix, hq, hn.symm] at hl
      · simp [fix, hq, hn.symm] at hr
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, ⟨he, not_or.mpr hq⟩, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩
  · rintro ⟨e, ⟨he, hq⟩, hl, hr⟩
    have hp : ¬incident p e := fun h => hq (hpq e he h)
    simp only [incident, not_or] at hq hp
    exact ⟨e, he, by simpa [fix, hp.1, hq.1] using hl,
      by simpa [fix, hp.2, hq.2] using hr⟩

lemma center_essential {a b : ℕ} (E : Finset (Fin a × Fin b))
    (p q : Fin (a + b)) (hn : p ≠ q) (e : Fin a × Fin b) (he : e ∈ E)
    (hp : incident p e) (hq : incident q e)
    (huniq : ∀ e' ∈ E, incident p e' → e' = e)
    (hdeg : 2 ≤ (E.filter (incident q)).card) (bval : Bool) :
    Essential (fun x => edgeFun E (fix p bval x)) q := by
  cases bval
  · let S := E.filter (incident q)
    change 2 ≤ S.card at hdeg
    have hmore : ∃ d ∈ S, d ≠ e := by
      by_contra! h
      have hsub : S ⊆ {e} := by
        intro d hd
        simpa using h d hd
      have hlt := Finset.card_le_card hsub
      simp at hlt
      omega
    obtain ⟨d, hd, hde⟩ := hmore
    have hd' := Finset.mem_filter.mp hd
    have hnp : ¬incident p d := fun h => hde (huniq d hd'.1 h)
    obtain ⟨r, hqr, hpr, hor⟩ : ∃ r, q ≠ r ∧ p ≠ r ∧ incident r d := by
      rcases hd'.2 with hl | hr
      · refine ⟨right d, ?_, ?_, Or.inr rfl⟩
        · intro h
          exact endpoints_ne d (hl.trans h)
        · exact fun h => hnp (Or.inr h.symm)
      · refine ⟨left d, ?_, ?_, Or.inl rfl⟩
        · intro h
          exact endpoints_ne d (hr.trans h).symm
        · exact fun h => hnp (Or.inl h.symm)
    refine ⟨one r, ?_⟩
    change edgeFun E (fix p false (fix q false (one r))) ≠
      edgeFun E (fix p false (fix q true (one r)))
    have hyes : edgeFun E (fix p false (fix q true (one r))) = true := by
      apply edge_true.mpr
      refine ⟨d, hd'.1, ?_⟩
      rcases both_endpoints hqr hd'.2 hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [fix, h1, h2, one, hqr.symm, hn.symm, hpr.symm]
      · simp [fix, h1, h2, one, hqr.symm, hn.symm, hpr.symm]
    rw [fix_one_false hqr, fix_one_false hpr, one_false, hyes]
    decide
  · refine ⟨fun _ => false, ?_⟩
    change edgeFun E (fix p true (fix q false (fun _ => false))) ≠
      edgeFun E (fix p true (fix q true (fun _ => false)))
    have hz : fix q false (fun _ => false) = (fun _ => false) := by
      funext i
      simp [fix]
    have hsingle : fix p true (fun _ => false) = one p := by
      funext i
      by_cases h : i = p <;> simp [fix, one, h]
    have hother : fix q true (fun _ => false) = one q := by
      funext i
      by_cases h : i = q <;> simp [fix, one, h]
    rw [hz, hsingle, hother, one_false, pair_true he hn hp hq]
    decide

lemma solve {a b : ℕ} (E : Finset (Fin a × Fin b)) (C : Circuit) (hm : Monotone2 C)
    (hc : circuitFun (a + b) C = edgeFun E) (p q : Fin (a + b)) (hn : p ≠ q)
    (hcard : (E.filter (incident p)).card = 1)
    (hedge : ∃ e ∈ E, incident p e ∧ incident q e)
    (hne : (E.filter fun e => ¬incident q e).Nonempty) :
    ∃ D : Circuit, Monotone2 D ∧
      circuitFun (a + b) D = edgeFun (E.filter fun e => ¬incident q e) ∧
      D.size + min 3 ((E.filter (incident q)).card + 1) ≤ C.size := by
  classical
  obtain ⟨e, he, hp, hq⟩ := hedge
  have huniq (d) (hd : d ∈ E) (hi : incident p d) : d = e := by
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hcard
    have hmem (u) (hu : u ∈ E) (hui : incident p u) : u = s := by
      have hh : u ∈ E.filter (incident p) := Finset.mem_filter.mpr ⟨hu, hui⟩
      simpa [hs] using hh
    exact (hmem d hd hi).trans (hmem e he hp).symm
  have hdel (bval : Bool) (x : Fin (a + b) → Bool) :
      circuitFun (a + b) C (fix p bval (fix q false x)) = edgeFun (E.filter fun e => ¬incident q e) x := by
    rw [hc]
    apply delete_center E p q _ hn
    intro d hd hi
    rwa [huniq d hd hi]
  obtain ⟨x, y, hxy⟩ := graph_nonconstant hne p
  have hnc (bval : Bool) : Nonconstant (fun z => circuitFun (a + b) C (fix p bval z)) := by
    refine ⟨fix q false x, fix q false y, ?_⟩
    simpa only [hdel] using hxy
  have he' : Essential (circuitFun (a + b) C) p := by
    rw [hc]
    exact ⟨one q, by rw [fix_one_false hn, one_false, pair_true he hn hp hq]; decide⟩
  obtain ⟨bval, C', hm', hc', hs'⟩ := leaf_step C hm p he' hnc
  have hn' : Nonconstant (fun z => circuitFun (a + b) C' (fix q false z)) := by
    refine ⟨x, y, ?_⟩
    simpa only [hc', hdel] using hxy
  obtain ⟨D, hmD, hcD, hsD, hsMore⟩ := center_step C' hm' q hn'
  refine ⟨D, hmD, funext fun z => (hcD z).trans ((hc' _).trans (hdel bval z)), ?_⟩
  by_cases hd : 2 ≤ (E.filter (incident q)).card
  · have heq : Essential (circuitFun (a + b) C') q := by
      obtain ⟨z, hz⟩ := center_essential E p q hn e he hp hq huniq hd bval
      exact ⟨z, by simpa only [hc', hc] using hz⟩
    have hh := hsMore heq
    rw [min_eq_left (by omega)]
    omega
  · have hh : min 3 ((E.filter (incident q)).card + 1) ≤ 2 :=
      (min_le_right _ _).trans (by omega)
    omega

end Cut
abbrev touched (v : Fin (N+M)) (e : Fin N × Fin M) : Prop :=
  Fin.castAdd M e.1=v ∨ Fin.natAdd N e.2=v
def attached (b : Layout n m N M) (E : Edges n m) (S : Finset (Fin n)) : Edges N M :=
  ((E.map (old b)) ∪ S.map (near b)) ∪ S.map (far b)
theorem attached_mem (b : Layout n m N M) (E : Edges n m) (S : Finset (Fin n)) (e : Fin N × Fin M) :
    e∈attached b E S ↔ (∃ f∈E,e=old b f) ∨ (∃ p∈S,e=near b p) ∨ (∃ p∈S,e=far b p) := by
  simp only [attached,mem_union,mem_map,or_assoc]
  constructor <;> rintro (⟨p,h,eq⟩|⟨p,h,eq⟩|⟨p,h,eq⟩)
  · exact .inl ⟨p,h,eq.symm⟩
  · exact .inr (.inl ⟨p,h,eq.symm⟩)
  · exact .inr (.inr ⟨p,h,eq.symm⟩)
  · exact .inl ⟨p,h,eq.symm⟩
  · exact .inr (.inl ⟨p,h,eq.symm⟩)
  · exact .inr (.inr ⟨p,h,eq.symm⟩)
theorem touch_point (r : Fin N) (e : Fin N × Fin M) : touched (Fin.castAdd M r) e ↔ e.1=r := by
  change (Fin.castAdd M e.1=Fin.castAdd M r ∨ Fin.natAdd N e.2=Fin.castAdd M r) ↔ _
  simp only [Fin.castAdd_inj,Ne.symm (sep r e.2),or_false]
theorem touch_line (l : Fin M) (e : Fin N × Fin M) : touched (Fin.natAdd N l) e ↔ e.2=l := by
  change (Fin.castAdd M e.1=Fin.natAdd N l ∨ Fin.natAdd N e.2=Fin.natAdd N l) ↔ _
  simp only [sep e.1 l,false_or]
  constructor
  · intro eq
    have h := congrArg Fin.val eq
    change N+e.2.val=N+l.val at h
    exact Fin.ext (by omega)
  · exact congrArg (Fin.natAdd N)
theorem shift_shapes (b : Layout n m N M) (E : Edges n m) (S : Finset (Fin n)) (p : Fin n)
    (fresh : p∉S) :
    let B := attached b E (insert p S)
    let v := Fin.castAdd M (b.tip p)
    let u := Fin.natAdd N (b.mid p)
    (B.filter (touched v)) = {far b p} ∧
    (B.filter (touched u)) = {near b p,far b p} ∧
    (B.filter fun e => ¬touched u e) = attached b E S := by
  classical
  dsimp only
  have casesB (e) : e∈attached b E (insert p S) ↔
      e∈attached b E S ∨ e=near b p ∨ e=far b p := by
    simp only [attached_mem,mem_insert]
    grind
  have miss_tip {e} (he : e∈attached b E S) : e.1≠b.tip p := by
    rcases (attached_mem _ _ _ _).1 he with ⟨f,_,rfl⟩|⟨q,_,rfl⟩|⟨q,hq,rfl⟩
    · exact b.rt _ _
    · exact b.rt _ _
    · exact fun h => fresh (b.tip.injective h ▸ hq)
  have miss_mid {e} (he : e∈attached b E S) : e.2≠b.mid p := by
    rcases (attached_mem _ _ _ _).1 he with ⟨f,_,rfl⟩|⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
    · exact b.cm _ _
    · exact fun h => fresh (b.mid.injective h ▸ hq)
    · exact fun h => fresh (b.mid.injective h ▸ hq)
  have nr : (near b p).1≠b.tip p := b.rt _ _
  have fr : (far b p).1=b.tip p := rfl
  have nc : (near b p).2=b.mid p := rfl
  have fc : (far b p).2=b.mid p := rfl
  constructor
  · ext e
    simp only [mem_filter,casesB,touch_point,mem_singleton]
    grind
  constructor
  · ext e
    simp only [mem_filter,casesB,touch_line,mem_insert,mem_singleton]
    grind
  · ext e
    simp only [mem_filter,casesB,touch_line]
    grind

theorem unroll_paths (b : Layout n m N M) (E : Edges n m) (non : E.Nonempty) (S : Finset (Fin n))
    (C : Circuit) (hm : Monotone2 C) (rep : circuitFun (N+M) C=Flags (attached b E S)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun (N+M) D=Flags (E.map (old b)) ∧
      D.size+3*S.card≤C.size := by
  classical
  induction S using Finset.induction_on generalizing C with
  | empty =>
    exact ⟨C,hm,by simpa [attached] using rep,by simp⟩
  | @insert p S fresh ih =>
    let B := attached b E (insert p S)
    let v := Fin.castAdd M (b.tip p)
    let u := Fin.natAdd N (b.mid p)
    obtain ⟨hv,hu,off⟩ := shift_shapes b E S p fresh
    have hfv : (B.filter (touched v)).card=1 := by rw [hv]; simp
    have middle : (B.filter (touched u)).card=2 := by
      have ne : near b p ≠ far b p := fun eq => b.rt p p (congrArg Prod.fst eq)
      rw [hu]
      simp [ne]
    have edge : ∃ e∈B,touched v e ∧ touched u e := by
      have e : far b p∈B := (attached_mem _ _ _ _).2 (.inr (.inr ⟨p,mem_insert_self _ _,rfl⟩))
      exact ⟨far b p,e,.inl rfl,.inr rfl⟩
    have still : (B.filter fun e => ¬touched u e).Nonempty := by
      rw [off]
      obtain ⟨f,hf⟩ := non
      exact ⟨old b f,(attached_mem _ _ _ _).2 (.inl ⟨f,hf,rfl⟩)⟩
    obtain ⟨D,dm,de,sz⟩ := Cut.solve B C hm rep v u (sep _ _) hfv edge still
    change circuitFun (N+M) D = Flags (B.filter fun e => ¬touched u e) at de
    change D.size + min 3 ((B.filter (touched u)).card+1) ≤ C.size at sz
    rw [off] at de
    rw [middle] at sz
    obtain ⟨K,km,ke,ks⟩ := ih D dm de
    exact ⟨K,km,ke,by rw [card_insert_of_notMem fresh]; omega⟩
namespace Normalize

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def AO (n : ℕ) (ds : List Gate) : Prop :=
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < n + j

def Rep (n : ℕ) (ds : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c, ∀ y, f y = c) ∨
    ∃ k < n + ds.length, ∀ y, f y = (run ds (List.ofFn y)).getD k false

theorem rep_app (n : ℕ) (ds : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
    rw [h y, run_prefix _ _ _ _ (by simpa using hk)]

theorem rep_two (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (u v : (Fin n → Bool) → Bool)
    (hu : Rep n ds u) (hv : Rep n ds v) :
    ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
  have triv : ∀ w : (Fin n → Bool) → Bool, Rep n ds w → (∀ y, o.eval [u y, v y] = w y) →
      ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
    intro w hw e
    refine ⟨[], by simp, by simpa using hds, ?_⟩
    rw [List.append_nil, show (fun y => o.eval [u y, v y]) = w from funext e]
    exact hw
  have cst : ∀ c : Bool, Rep n ds fun _ => c := fun c => Or.inl ⟨c, fun _ => rfl⟩
  rcases hu with ⟨c, hc⟩ | ⟨a, ha, hua⟩
  · rcases ho with rfl | rfl <;> cases c
    · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
  · rcases hv with ⟨c, hc⟩ | ⟨b, hb, hvb⟩
    · have hu : Rep n ds u := Or.inr ⟨a, ha, hua⟩
      rcases ho with rfl | rfl <;> cases c
      · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
    · refine ⟨[⟨o, [a, b]⟩], by simp, ⟨?_, ?_⟩, Or.inr ⟨n + ds.length, by simp, fun y => ?_⟩⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact hds.1 g h
        · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
      · intro j hj i hi
        by_cases h : j < ds.length
        · rw [List.getElem_append_left h] at hi
          exact hds.2 j h i hi
        · have hj' : j = ds.length := by simp at hj; omega
          subst hj'
          simp at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [run_snoc, show n + ds.length = (run ds (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
        simp [hua, hvb]

theorem build (n : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ ds : List Gate, AO n ds ∧ ds.length ≤ gs.length ∧
      ∀ w, Rep n ds fun y => (run gs (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ⟨by simp, by simp⟩, le_rfl, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr ⟨w, by simpa using hw, fun y => rfl⟩
    · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by simp [run]; omega)⟩
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have main : ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧ Rep n (ds ++ hs)
        fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
      match hI : g.inputs, hlen with
      | [], _ =>
        exact ⟨[], by simp, by simpa using h1, Or.inl ⟨g.op.eval [], fun y => rfl⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, by simpa using h1, ?_⟩
        rw [List.append_nil]
        have e : (fun y : Fin n → Bool => g.op.eval ([a].map fun i =>
            (run gs (List.ofFn y)).getD i false)) =
            fun y => (run gs (List.ofFn y)).getD a false := by
          funext y
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
        rw [e]
        exact h3 a
      | [a, b], _ => exact rep_two n ds h1 g.op hop _ _ (h3 a) (h3 b)
    obtain ⟨hs, k1, k2, k3⟩ := main
    have k4 : ∀ f : (Fin n → Bool) → Bool, Rep n ds f → Rep n (ds ++ hs) f := by
      intro f hf
      match hs, k1 with
      | [], _ => simpa using hf
      | [g'], _ => exact rep_app n ds g' f hf
    refine ⟨ds ++ hs, k2, by simp; omega, fun w => ?_⟩
    by_cases hw : w = n + gs.length
    · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
          fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
        funext y
        rw [run_snoc, hw, show n + gs.length = (run gs (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
      rw [e]
      exact k3
    · by_cases hw' : w < n + gs.length
      · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
            fun y => (run gs (List.ofFn y)).getD w false := by
          funext y
          exact run_prefix _ _ _ _ (by simpa using hw')
        rw [e]
        exact k4 _ (h3 w)
      · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by
          rw [run_length]; simp; omega)⟩

end Normalize

open Normalize PEqualNP.CircuitLowerBounds in
theorem Normalize.result : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C hC h0
  obtain ⟨ds, h1, h2, h3⟩ := build n C.gates fun g hg => by
    obtain ⟨e1, e2⟩ := hC g hg
    exact ⟨by simpa using e1, e2⟩
  rcases h3 C.output with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
  · have hcf : c = false := (hc fun _ => false).symm.trans h0
    refine ⟨⟨[], n⟩, ⟨by intro g hg; simp at hg, by intro j hj; simp at hj,
      by intro g hg; simp at hg⟩, Nat.zero_le _, ?_⟩
    funext y
    refine Eq.trans ?_ ((hc y).trans hcf).symm
    exact List.getD_eq_default _ _ (by simp [Circuit.wires])
  · refine ⟨⟨ds, k⟩, ⟨fun g hg => (h1.1 g hg).1, fun j hj i hi => h1.2 j hj i ?_,
      fun g hg => (h1.1 g hg).2⟩, h2, funext fun y => (hk' y).symm⟩
    have hj' : j < ds.length := hj
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hj'] using hi
theorem side_injective (b : Layout n m N M) : Function.Injective (sideMap b) := by
  intro i j
  cases i using Fin.addCases <;> cases j using Fin.addCases
  · intro eq
    rename_i p q
    exact congrArg (Fin.castAdd m) (b.row.injective (Fin.castAdd_inj.mp (by simpa [sideMap] using eq)))
  · intro eq
    rename_i p l
    exact False.elim (sep (b.row p) (b.col l) (by simpa [sideMap] using eq))
  · intro eq
    rename_i l p
    exact False.elim (sep (b.row p) (b.col l) (by simpa [sideMap] using eq.symm))
  · intro eq
    rename_i l t
    have z := congrArg Fin.val eq
    simp [sideMap] at z
    apply congrArg (Fin.natAdd n)
    apply b.col.injective
    exact Fin.ext (by simpa using z)

theorem land_circuit (b : Layout n m N M) {E : Edges n m} (hn : E.Nonempty)
    (D : Circuit) (dm : Monotone2 D) (rep : circuitFun (N+M) D=Flags (E.map (old b))) :
    ∃ C : Circuit, IsAO2 (n+m) C ∧ C.size≤D.size ∧ circuitFun (n+m) C=Flags E := by
  classical
  obtain ⟨e,he⟩ := hn
  letI : Nonempty (Fin (n+m)) := ⟨Fin.castAdd m e.1⟩
  let back := Function.invFun (sideMap b)
  have left : Function.LeftInverse back (sideMap b) := Function.leftInverse_invFun (side_injective b)
  have L (p) : back (Fin.castAdd M (b.row p))=Fin.castAdd m p := by
    simpa [sideMap] using left (Fin.castAdd m p)
  have R (l) : back (Fin.natAdd N (b.col l))=Fin.natAdd n l := by
    simpa [sideMap] using left (Fin.natAdd n l)
  have zero : circuitFun (N+M) D (fun _ => false)=false := by rw [rep];simp [Flags]
  obtain ⟨X,ao,small,ex⟩ := Normalize.result (N+M) D dm zero
  have val : X.output<N+M+X.gates.length := by
    apply GridCircuit.output_valid
    refine ⟨fun _ => true,?_⟩
    rw [ex,rep,Flags,decide_eq_true_eq]
    exact ⟨old b e,mem_map.mpr ⟨e,he,rfl⟩,rfl,rfl⟩
  obtain ⟨C,co,_,size,eq⟩ := GridCircuit.relabel X ao val back
  refine ⟨C,co,size.le.trans small,?_⟩
  funext x
  rw [eq]
  change circuitFun (N+M) X (x ∘ back)=_
  rw [ex,rep]
  apply Bool.eq_iff_iff.mpr
  simp only [Flags,decide_eq_true_eq]
  constructor
  · rintro ⟨f,hf,l,r⟩
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    exact ⟨g,hg,by simpa [old,Function.comp_def,L] using l,by simpa [old,Function.comp_def,R] using r⟩
  · rintro ⟨g,hg,l,r⟩
    refine ⟨old b g,mem_map.mpr ⟨g,hg,rfl⟩,?_,?_⟩
    · change x (back (Fin.castAdd M (b.row g.1)))=true
      rwa [L]
    · change x (back (Fin.natAdd N (b.col g.2)))=true
      rwa [R]

theorem inverse_circuit (b : Layout n m N M) {E : Edges n m} (hn : E.Nonempty)
    (C : Circuit) (hm : Monotone2 C) (rep : circuitFun (N+M) C=Flags (board b E)) :
    ∃ K : Circuit, IsAO2 (n+m) K ∧ circuitFun (n+m) K=Flags E ∧
      K.size+3*(active E).card≤C.size := by
  obtain ⟨D,dm,de,ds⟩ := unroll_paths b E hn (active E) C hm rep
  obtain ⟨K,km,ks,ke⟩ := land_circuit b hn D dm de
  exact ⟨K,km,ke,by omega⟩

theorem push_cover (b : Layout n m N M) (E : Edges n m) {s t : Nat}
    (sharp : Budget E s) (sz : s+3*(active E).card≤t) : Budget (board b E) t := by
  obtain ⟨A,B,cover,price⟩ := sharp
  let U := A.map b.row
  let V := B.map b.col ∪ (active E).map b.mid
  have dis : Disjoint (B.map b.col) ((active E).map b.mid) := by
    rw [Finset.disjoint_left]
    intro z hz hy
    obtain ⟨i,_,rfl⟩ := mem_map.mp hz
    obtain ⟨j,_,eq⟩ := mem_map.mp hy
    exact b.cm i j eq.symm
  have vc : V.card=B.card+(active E).card := by simp [V,card_union_of_disjoint dis]
  refine ⟨U,V,?_,?_⟩
  · intro e he
    rcases (on_board b E e).1 he with ⟨f,hf,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
    · rcases cover f hf with ha|hb
      · exact .inl (mem_map.mpr ⟨_,ha,rfl⟩)
      · exact .inr (mem_union_left _ (mem_map.mpr ⟨_,hb,rfl⟩))
    · exact .inr (mem_union_right _ (mem_map.mpr ⟨_,hp,rfl⟩))
    · exact .inr (mem_union_right _ (mem_map.mpr ⟨_,hp,rfl⟩))
  · rw [board_card,vc]
    have uc : U.card=A.card := card_map _
    omega

def Sharp {n m} (E : Edges n m) := ∀ C : Circuit, IsAO2 (n+m) C →
  circuitFun (n+m) C=Flags E → Budget E C.size

theorem invariant (b : Layout n m N M) {E : Edges n m} (hne : E.Nonempty) :
    Sharp (board b E) ↔ Sharp E := by
  constructor
  · intro hard C ao eq
    obtain ⟨D,dd,sz,hd⟩ := board_circuit b hne C ao (congrFun eq)
    exact lift_budget b E _ _ (hard D dd (funext hd)) sz
  · intro hard C ao eq
    have hm : Monotone2 C := fun g hg => ⟨by simpa using ao.1 g hg,(ao.2.2 g hg).le⟩
    obtain ⟨D,dm,de,ds⟩ := inverse_circuit b hne C hm eq
    exact push_cover b E (hard D dm de) ds

end PEqualNP.Outside.L_meta_18180

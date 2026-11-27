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
abbrev Posted : Prop := ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (3 : ℕ) < x1 →     have x6 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x6 : Finset (Fin x1 × Fin x2)) => x6.biUnion fun (x7 : Fin x1 × Fin x2) => {Fin.castAdd x2 x7.1, Fin.natAdd x1 x7.2};     (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x9 = Decidable.decide (∃ x10 ∈ x3, x9 (Fin.castAdd x2 x10.1) = Bool.true ∧ x9 (Fin.natAdd x1 x10.2) = Bool.true)) → (¬∃ (x10 : Finset (Fin x1 × Fin x2)) (x11 : Finset (Fin x1 × Fin x2)) (x12 : Fin (x1 + x2)), x10.Nonempty ∧ x10 ∪ x11 = x3 ∧ Disjoint (x6 x10) (x6 x11) ∧ ∀ x13 ∈ x10, Fin.castAdd x2 x13.1 = x12 ∨ Fin.natAdd x1 x13.2 = x12) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ)
def longer (n m : Nat) : Layout n m (n+(n+4)) (m+n) where
  row := ⟨Fin.castAdd (n+4),fun _ _ h => Fin.castAdd_inj.mp h⟩
  tip := ⟨fun p => Fin.natAdd n (Fin.castAdd 4 p),by
    intro p q eq
    have z := congrArg Fin.val eq
    apply Fin.ext
    change n+p.val=n+q.val at z
    omega⟩
  col := ⟨Fin.castAdd n,fun _ _ h => Fin.castAdd_inj.mp h⟩
  mid := ⟨Fin.natAdd m,by
    intro p q eq
    have z := congrArg Fin.val eq
    apply Fin.ext
    change m+p.val=m+q.val at z
    omega⟩
  rt := fun p q => sep p (Fin.castAdd 4 q)
  cm := fun l p => sep l p

def Universal : Prop := ∀ n m (E : Edges n m) (C : Circuit), Linear E → IsAO2 (n+m) C →
  (∀ x, circuitFun (n+m) C x=Flags E x) → Budget E C.size

theorem exact_price_equivalence : Posted ↔ Universal := by
  constructor
  · intro posted n m E C free ao correct
    by_cases empty : E=∅
    · subst E
      exact ⟨∅,∅,by simp,by simp⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    let b := longer n m
    obtain ⟨D,ok,small,spec⟩ := board_circuit b non C ao correct
    have got := posted (n+(n+4)) (m+n) (board b E) D (by omega) (board_linear b free) ok
      spec (path_noStar (board_paths b E))
    exact lift_budget b E C.size D.size got small
  · intro h n m E C _ _ free ao spec _
    exact h n m E C free ao spec

def attach (F : Edges N M) (T : Finset (Fin N)) (h : Fin M) := F ∪ (T ×ˢ {h})
theorem attached {F : Edges N M} {T : Finset (Fin N)} {h l : Fin M} {v : Fin N} :
    (v,l)∈attach F T h ↔ (v,l)∈F ∨ v∈T ∧ l=h := by simp only [attach,mem_union,mem_product,mem_singleton]
theorem attach_linear {F : Edges N M} {T : Finset (Fin N)} {h : Fin M}
    (old : Linear F) (fresh : ∀ v, (v,h)∉F)
    (safe : ∀ a∈T, ∀ b∈T, ∀ l, (a,l)∈F → (b,l)∈F → a=b) : Linear (attach F T h) := by
  rintro a b i j ab ij ⟨ai,aj,bi,bj⟩
  have off {x : Fin N} {l : Fin M} (ne : l≠h) (he : (x,l)∈attach F T h) : (x,l)∈F :=
    (attached.mp he).elim id (fun hy => (ne hy.2).elim)
  have on {x : Fin N} (he : (x,h)∈attach F T h) : x∈T :=
    (attached.mp he).elim (fun he => (fresh x he).elim) And.left
  by_cases ih : i=h
  · subst i
    exact ab (safe a (on ai) b (on bi) j (off (Ne.symm ij) aj) (off (Ne.symm ij) bj))
  by_cases jh : j=h
  · subst j
    exact ab (safe a (on aj) b (on bj) i (off ih ai) (off ih bi))
  exact old a b i j ab ij ⟨off ih ai,off jh aj,off ih bi,off jh bj⟩
theorem attach_card {F : Edges N M} {T : Finset (Fin N)} {h : Fin M}
    (fresh : ∀ v, (v,h)∉F) : (attach F T h).card=F.card+T.card := by
  have dis : Disjoint F (T ×ˢ {h}) := by
    rw [Finset.disjoint_left]
    rintro ⟨a,l⟩ old mem
    obtain ⟨_,rfl⟩ : a∈T ∧ l=h := by simpa only [mem_product,mem_singleton] using mem
    exact fresh a old
  rw [attach,card_union_of_disjoint dis,card_product,card_singleton,Nat.mul_one]
theorem attach_pay {F : Edges N M} {T : Finset (Fin N)} {h : Fin M}
    (v : Fin N) (hv : v∈T) (hr : ∀ k, (v,k)∉F) (hc : ∀ u, (u,h)∉F)
    (s t : Nat) (budget : Budget (attach F T h) t) (cost : t≤s+T.card+1) : Budget F s := by
  obtain ⟨U,V,hit,ub⟩ := budget
  have hcvr : ∀ e∈F, e.1∈U.erase v ∨ e.2∈V.erase h := by
    rintro ⟨r,l⟩ he
    rcases hit (r,l) (attached.mpr (.inl he)) with u|w
    · exact .inl (mem_erase.mpr ⟨fun eq => hr l (eq ▸ he),u⟩)
    · exact .inr (mem_erase.mpr ⟨fun eq => hc r (eq ▸ he),w⟩)
  have vc := hit (v,h) (attached.mpr (.inr ⟨hv,rfl⟩))
  have x := card_le_card (erase_subset v U)
  have y := card_le_card (erase_subset h V)
  rw [attach_card hc] at ub
  refine ⟨_,_,hcvr,?_⟩
  change v∈U ∨ h∈V at vc
  rcases vc with va|hb
  · have eq : (U.erase v).card+1=U.card := card_erase_add_one va
    omega
  · have eq : (V.erase h).card+1=V.card := card_erase_add_one hb
    omega
theorem attach_circuit {F : Edges N M} {T : Finset (Fin N)} (h : Fin M)
    (non : F.Nonempty) (ne : T.Nonempty) (C : Circuit) (ao : IsAO2 (N+M) C)
    (spec : ∀ x, circuitFun (N+M) C x=Flags F x) : ∃ D : Circuit, IsAO2 (N+M) D ∧
    D.size≤C.size+T.card+1 ∧ ∀ x, circuitFun (N+M) D x=Flags (attach F T h) x := by
  have val : C.output<N+M+C.gates.length := by
    apply GridCircuit.output_valid
    refine ⟨fun _ => true,?_⟩
    rw [spec,Flags,decide_eq_true_eq]
    obtain ⟨e,he⟩ := non
    exact ⟨e,he,rfl,rfl⟩
  let st : Fin (N+M) × List (Fin (N+M)) := (Fin.natAdd N h,T.toList.map (Fin.castAdd M))
  have sn : ∀ u ∈ [st], u.2 ≠ [] := by
    intro u hu
    obtain rfl : u=st := by simpa using hu
    have hh : 0<st.2.length := by simpa [st] using card_pos.mpr ne
    intro eq
    simp [eq] at hh
  obtain ⟨D,dd,_,ds,de⟩ := GridCircuit.assemble C ao val [id] (by simp) [st] sn
  refine ⟨D,dd,by simpa [st] using ds,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [de]
  simp only [List.mem_singleton,exists_eq_left,Function.comp_id,spec,Flags,decide_eq_true_eq,
    st,List.mem_map,mem_toList]
  constructor
  · rintro (⟨⟨r,l⟩,old,rv,lv⟩|⟨hot,w,⟨r,hr,rfl⟩,rv⟩)
    · exact ⟨(r,l),attached.mpr (.inl old),rv,lv⟩
    · exact ⟨(r,h),attached.mpr (.inr ⟨hr,rfl⟩),rv,hot⟩
  · rintro ⟨⟨r,l⟩,he,rv,lv⟩
    rcases attached.mp he with old|⟨hr,rfl⟩
    · exact .inl ⟨(r,l),old,rv,lv⟩
    · exact .inr ⟨lv,Fin.castAdd M r,⟨r,hr,rfl⟩,rv⟩

structure Port (b : Layout n m N M) where
  leaf : Fin N
  hub : Fin M
  row_ne : ∀ p, b.row p ≠ leaf
  tip_ne : ∀ p, b.tip p ≠ leaf
  col_ne : ∀ l, b.col l ≠ hub
  mid_ne : ∀ p, b.mid p ≠ hub
def fan {b : Layout n m N M} (s : Port b) (E : Edges n m) :=
  insert s.leaf ((active E).map b.tip)
def cone {b : Layout n m N M} (s : Port b) (E : Edges n m) := attach (board b E) (fan s E) s.hub
theorem fresh_ends {b : Layout n m N M} (s : Port b) (E : Edges n m) :
    (∀ r, (r,s.hub)∉board b E) ∧ (∀ l, (s.leaf,l)∉board b E) := by
  constructor
  · intro r he
    rcases (on_board _ _ _).1 he with ⟨f,_,eq⟩|⟨p,_,eq⟩|⟨p,_,eq⟩
    · exact s.col_ne _ (congrArg Prod.snd eq.symm)
    · exact s.mid_ne _ (congrArg Prod.snd eq.symm)
    · exact s.mid_ne _ (congrArg Prod.snd eq.symm)
  · intro l he
    rcases (on_board _ _ _).1 he with ⟨f,_,eq⟩|⟨p,_,eq⟩|⟨p,_,eq⟩
    · exact s.row_ne _ (congrArg Prod.fst eq.symm)
    · exact s.row_ne _ (congrArg Prod.fst eq.symm)
    · exact s.tip_ne _ (congrArg Prod.fst eq.symm)
theorem cone_linear {b : Layout n m N M} (s : Port b) {E : Edges n m} (free : Linear E) :
    Linear (cone s E) := by
  apply attach_linear (board_linear b free) (fresh_ends s E).1
  intro a ha c hc l al cl
  have part {v} (hv : v∈fan s E) (hl : (v,l)∈board b E) : ∃ p, v=b.tip p ∧ l=b.mid p := by
    rcases mem_insert.mp hv with rfl|hy
    · exact False.elim ((fresh_ends s E).2 l hl)
    obtain ⟨p,_,rfl⟩ := mem_map.mp hy
    exact ⟨p,rfl,star_row b hl⟩
  obtain ⟨p,rfl,e⟩ := part ha al
  obtain ⟨q,rfl,f⟩ := part hc cl
  exact congrArg _ (b.mid.injective (e.symm.trans f))
def Centered {n m} (E : Edges n m) := ∃ h : Fin m, ∀ e∈E, (e.1,h)∈E ∨
  ∃ l r, (e.1,l)∈E ∧ (r,l)∈E ∧ (r,h)∈E
theorem cone_centered {b : Layout n m N M} (s : Port b) (E : Edges n m) : Centered (cone s E) := by
  refine ⟨s.hub,?_⟩
  rintro ⟨a,l⟩ hl
  have nearRoot (p) (hp : p∈active E) : (b.tip p,s.hub)∈cone s E :=
    attached.mpr (.inr ⟨mem_insert_of_mem (mem_map.mpr ⟨p,hp,rfl⟩),rfl⟩)
  have path (p) (hp : p∈active E) : ∃ k r, (b.row p,k)∈cone s E ∧ (r,k)∈cone s E ∧ (r,s.hub)∈cone s E :=
    ⟨_,_,attached.mpr (.inl ((on_board _ _ _).2 (.inr (.inl ⟨p,hp,rfl⟩)))),
      attached.mpr (.inl ((on_board _ _ _).2 (.inr (.inr ⟨p,hp,rfl⟩)))),nearRoot p hp⟩
  rcases attached.mp hl with old|⟨ha,rfl⟩
  · rcases (on_board _ _ _).1 old with ⟨⟨p,k⟩,hf,eq⟩|⟨p,hp,eq⟩|⟨p,hp,eq⟩
    · cases eq
      exact .inr (path p (mem_image.mpr ⟨(p,k),hf,rfl⟩))
    · cases eq
      exact .inr (path p hp)
    · cases eq
      exact .inl (nearRoot p hp)
  · exact .inl hl
theorem cone_paths {b : Layout n m N M} (s : Port b) {E : Edges n m} (hn : E.Nonempty) :
    PathCover (cone s E) := by
  rintro ⟨r,l⟩ hr
  have old {e} (he : e∈board b E) : e∈cone s E := mem_union_left _ he
  have leaf : (s.leaf,s.hub)∈cone s E := attached.mpr (.inr ⟨mem_insert_self _ _,rfl⟩)
  have localPath (p) (hp : p∈active E) (atE : (r,l)=(b.tip p,s.hub) ∨ (r,l)=(s.leaf,s.hub)) :
      ∃ a c i j, a≠c ∧ i≠j ∧ (a,i)∈cone s E ∧ (a,j)∈cone s E ∧ (c,j)∈cone s E ∧
          ((r,l)=(a,i) ∨ (r,l)=(a,j) ∨ (r,l)=(c,j)) := by
    refine ⟨b.tip p,s.leaf,b.mid p,s.hub,s.tip_ne _,s.mid_ne _,
      old ((on_board _ _ _).2 (.inr (.inr ⟨p,hp,rfl⟩))),?_,leaf,.inr atE⟩
    exact attached.mpr (.inr ⟨mem_insert_of_mem (mem_map.mpr ⟨p,hp,rfl⟩),rfl⟩)
  rcases attached.mp hr with he|⟨hp,eq⟩
  · obtain ⟨a,c,i,j,ac,ij,ai,aj,cj,loc⟩ := board_paths b E (r,l) he
    exact ⟨a,c,i,j,ac,ij,old ai,old aj,old cj,loc⟩
  · rcases mem_insert.mp hp with same|ht
    · obtain ⟨f,hf⟩ := hn
      exact localPath f.1 (mem_image.mpr ⟨f,hf,rfl⟩) (.inr (Prod.ext same eq))
    · obtain ⟨p,pp,pq⟩ := mem_map.mp ht
      exact localPath p pp (.inl (Prod.ext pq.symm eq))

def centerLayout (n m : Nat) : Layout n m (n+(n+4)) (m+(n+1)) where
  row := ⟨Fin.castAdd (n+4),fun _ _ h => Fin.castAdd_inj.mp h⟩
  tip := (longer n m).tip
  col := ⟨Fin.castAdd (n+1),fun _ _ h => Fin.castAdd_inj.mp h⟩
  mid := ⟨fun p => Fin.natAdd m (Fin.castAdd 1 p),by
    intro u v eq
    have hh := congrArg Fin.val eq
    change m+u.val=m+v.val at hh
    exact Fin.ext (by omega)⟩
  rt := (longer n m).rt
  cm := fun i p => sep i (Fin.castAdd 1 p)
def centerPort (n m : Nat) : Port (centerLayout n m) where
  leaf := Fin.natAdd n (Fin.last (n+3))
  hub := Fin.natAdd m (Fin.last n)
  row_ne := fun p => sep p (Fin.last (n+3))
  tip_ne := by
    intro p eq
    have e := congrArg Fin.val eq
    change n+p.val=n+(n+3) at e
    have := p.isLt
    omega
  col_ne := fun l => sep l (Fin.last n)
  mid_ne := by
    intro p eq
    have e := congrArg Fin.val eq
    change m+p.val=m+n at e
    have := p.isLt
    omega

def CenteredPrice := ∀ n m (E : Edges n m) (C : Circuit), 3<n → Linear E → Centered E → PathCover E →
    IsAO2 (n+m) C → (∀ x,circuitFun (n+m) C x=Flags E x) → Budget E C.size
theorem radius_four_equivalence : CenteredPrice ↔ Posted := by
  constructor
  · intro hard
    apply exact_price_equivalence.mpr
    intro n m E C lin ok corr
    by_cases empty : E=∅
    · subst E
      exact ⟨∅,∅,by simp,by simp⟩
    have ne := nonempty_iff_ne_empty.mpr empty
    let b := centerLayout n m
    let s : Port b := centerPort n m
    obtain ⟨D,dd,ds,de⟩ := board_circuit b ne C ok corr
    have hF : (board b E).Nonempty := by
      obtain ⟨f,hf⟩ := ne
      exact ⟨_,(on_board _ _ _).2 (.inl ⟨f,hf,rfl⟩)⟩
    have hT : s.leaf∈fan s E := mem_insert_self _ _
    obtain ⟨K,kk,ks,ke⟩ := attach_circuit s.hub hF ⟨_,hT⟩ D dd de
    have cv := hard _ _ (cone s E) K (by omega) (cone_linear s lin) (cone_centered s E)
      (cone_paths s ne) kk ke
    have got := attach_pay s.leaf hT (fresh_ends s E).2 (fresh_ends s E).1 _ _ cv ks
    exact lift_budget b E _ _ got ds
  · intro h n m E C w lin _ paths ao spec
    exact h n m E C w lin ao spec (path_noStar paths)

end PEqualNP.Outside.L_meta_18180

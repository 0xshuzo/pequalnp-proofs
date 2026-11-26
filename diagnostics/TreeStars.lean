import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743_Separated
variable {V : Type}

def boxFree (g : V → V → Prop) : Prop := ∀ a a' b b', a≠a' → b≠b' →
  g a b → g a b' → g a' b → g a' b' → False
def small (s : Set V) := ∀ i∈s, ∀ j∈s, i=j

theorem thin {g : V → V → Prop} (c4 : boxFree g) {a b : Set V}
    (all : ∀ i∈a, ∀ j∈b, g i j) : small a ∨ small b := by
  classical
  by_cases h : small a
  · exact Or.inl h
  · right
    unfold small at h
    push_neg at h
    obtain ⟨i,hi,i',hi',ne⟩ := h
    intro j hj j' hj'
    by_contra nj
    exact c4 i i' j j' ne nj (all i hi j hj) (all i hi j' hj')
      (all i' hi' j hj) (all i' hi' j' hj')

def depends (p : Set V → Prop) (a : Set V) := ∀ s t : Set V,
  (∀ v∈a, v∈s ↔ v∈t) → (p s ↔ p t)
def increasing (p : Set V → Prop) := ∀ s t : Set V, s⊆t → p s → p t

theorem project_one {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (out : j∉a) : p {i,j} ↔ p {i} := by
  apply h
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (rfl|rfl)
    · rfl
    · exact False.elim (out hx)
  · exact Or.inl

theorem project_two {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (out : i∉a) : p {i,j} ↔ p {j} := by
  rw [Set.pair_comm i j]
  exact project_one h out

theorem empty_pair {p : Set V → Prop} {a : Set V} (h : depends p a) {i j : V}
    (iout : i∉a) (jout : j∉a) : p {i,j} ↔ p ∅ := by
  apply h
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
  rintro (rfl|rfl)
  · exact iout hx
  · exact jout hx

-- Each input of a disjoint-support AND has access only to its own side.
-- The required pairs touch every input and the ambient allowed graph contains no C4.
theorem separated (a b : Set V) (p q : Set V → Prop) (d g : V → V → Prop)
    (sep : ∀ v, v∈a → v∉b) (pa : depends p a) (qb : depends q b)
    (up : increasing p) (uq : increasing q) (zp : ¬p ∅) (zq : ¬q ∅)
    (spanA : ∀ i∈a, ∃ j∈a ∪ b, d i j) (spanB : ∀ j∈b, ∃ i∈a ∪ b, d i j)
    (yes : ∀ i j, d i j → p {i,j} ∧ q {i,j})
    (safe : ∀ i∈a, ∀ j∈b, p {i,j} → q {i,j} → g i j) (c4 : boxFree g) :
    (small a ∨ small b) ∧
    (∀ i∈a, ∀ j∈b, d i j) ∧
    ∀ s, (p s ∧ q s) ↔ (∃ i∈a, i∈s) ∧ (∃ j∈b, j∈s) := by
  classical
  have otherA : ∀ i∈a, ∃ j∈b, d i j := by
    intro i hi
    obtain ⟨j,hj,h⟩ := spanA i hi
    rcases hj with ja | jb
    · exact False.elim (zq ((empty_pair qb (sep i hi) (sep j ja)).1 (yes i j h).2))
    · exact ⟨j,jb,h⟩
  have otherB : ∀ j∈b, ∃ i∈a, d i j := by
    intro j hj
    obtain ⟨i,hi,h⟩ := spanB j hj
    rcases hi with ia | ib
    · exact ⟨i,ia,h⟩
    · exact False.elim (zp ((empty_pair pa (fun h => sep i h ib) (fun h => sep j h hj)).1 (yes i j h).1))
  have p1 : ∀ i∈a, p {i} := by
    intro i hi
    obtain ⟨j,hj,h⟩ := otherA i hi
    exact (project_one pa (fun h => sep j h hj)).1 (yes i j h).1
  have q1 : ∀ j∈b, q {j} := by
    intro j hj
    obtain ⟨i,hi,h⟩ := otherB j hj
    exact (project_two qb (sep i hi)).1 (yes i j h).2
  have all : ∀ i∈a, ∀ j∈b, g i j := by
    intro i hi j hj
    exact safe i hi j hj ((project_one pa (fun h => sep j h hj)).2 (p1 i hi))
      ((project_two qb (sep i hi)).2 (q1 j hj))
  have half := thin c4 all
  refine ⟨half,?_,?_⟩
  · intro i hi j hj
    rcases half with ha | hb
    · obtain ⟨i',hi',h⟩ := otherB j hj
      exact (ha i' hi' i hi) ▸ h
    · obtain ⟨j',hj',h⟩ := otherA i hi
      exact (hb j' hj' j hj) ▸ h
  · intro s
    constructor
    · rintro ⟨ps,qs⟩
      constructor
      · by_contra miss
        push_neg at miss
        exact zp ((pa s ∅ (fun i hi => ⟨fun v => False.elim (miss i hi v),fun v => False.elim v⟩)).1 ps)
      · by_contra miss
        push_neg at miss
        exact zq ((qb s ∅ (fun j hj => ⟨fun v => False.elim (miss j hj v),fun v => False.elim v⟩)).1 qs)
    · rintro ⟨⟨i,hi,hs⟩,⟨j,hj,ht⟩⟩
      exact ⟨up _ _ (Set.singleton_subset_iff.mpr hs) (p1 i hi),
        uq _ _ (Set.singleton_subset_iff.mpr ht) (q1 j hj)⟩

inductive Tree (V : Type)
  | leaf (v : V)
  | both (x y : Tree V)
  | either (x y : Tree V)
def vars : Tree V → Set V
  | .leaf i => {i}
  | .both x y | .either x y => vars x ∪ vars y
def eval (s : Set V) : Tree V → Prop
  | .leaf i => i∈s
  | .both x y => eval s x ∧ eval s y
  | .either x y => eval s x ∨ eval s y
def separate : Tree V → Prop
  | .leaf _ => True
  | .both x y | .either x y =>
    (∀ i, i∈vars x → i∉vars y) ∧ separate x ∧ separate y

theorem eval_local (f : Tree V) : depends (fun s => eval s f) (vars f) := by
  induction f with
  | leaf j => intro s t h; exact h j (by simp [vars])
  | both x y ih jh =>
    intro s t h
    exact and_congr (ih s t (fun i hi => h i (Or.inl hi))) (jh s t (fun i hi => h i (Or.inr hi)))
  | either x y ih jh =>
    intro s t h
    exact or_congr (ih s t (fun i hi => h i (Or.inl hi))) (jh s t (fun i hi => h i (Or.inr hi)))

theorem eval_up (f : Tree V) : increasing (fun s => eval s f) := by
  induction f with
  | leaf j => intro s t h yes; exact h yes
  | both x y ih jh =>
    rintro s t h ⟨a,b⟩
    exact ⟨ih s t h a,jh s t h b⟩
  | either x y ih jh =>
    rintro s t h (a|b)
    · exact Or.inl (ih s t h a)
    · exact Or.inr (jh s t h b)

theorem eval_empty (f : Tree V) : ¬eval ∅ f := by
  induction f <;> simp_all [eval]

def meet (a s : Set V) := ∃ i∈a, i∈s
inductive StarSum {V : Type} : Set V → (Set V → Prop) → Prop where
  | star (a b : Set V) (sep : ∀ i, i∈a → i∉b) (thin : small a ∨ small b)
      (f : Set V → Prop) (eqv : ∀ s, f s ↔ meet a s ∧ meet b s) :
    StarSum (a∪b) f
  | join {a b : Set V} {f h : Set V → Prop} (sep : ∀ i, i∈a → i∉b)
      (x : StarSum a f) (y : StarSum b h) : StarSum (a∪b) (fun s => f s ∨ h s)

theorem private_tree (g d : V → V → Prop) (c4 : boxFree g)
    (dsym : ∀ i j, d i j → d j i) (f : Tree V) (tree : separate f)
    (zero1 : ∀ i, ¬eval {i} f)
    (safe : ∀ i j, eval {i,j} f → g i j)
    (span : ∀ i∈vars f, ∃ j∈vars f, d i j)
    (need : ∀ i∈vars f, ∀ j∈vars f, d i j → eval {i,j} f) :
    StarSum (vars f) (fun s => eval s f) := by
  induction f with
  | leaf i => exact False.elim (zero1 i (by simp [eval]))
  | both x y ix iy =>
    obtain ⟨dis,_,_⟩ := tree
    let a := vars x
    let b := vars y
    let d' : V → V → Prop := fun i j => i∈a ∪ b ∧ j∈a ∪ b ∧ d i j
    have ha : ∀ i∈a, ∃ j∈a ∪ b,d' i j := by
      intro i hi
      obtain ⟨j,hj,e⟩ := span i (Or.inl hi)
      exact ⟨j,hj,Or.inl hi,hj,e⟩
    have hb : ∀ j∈b, ∃ i∈a ∪ b,d' i j := by
      intro j hj
      obtain ⟨i,hi,e⟩ := span j (Or.inr hj)
      exact ⟨i,hi,hi,Or.inr hj,dsym j i e⟩
    obtain ⟨th,_,eqv⟩ := separated a b (fun s => eval s x) (fun s => eval s y) d' g dis
      (eval_local x) (eval_local y) (eval_up x) (eval_up y) (eval_empty x) (eval_empty y)
      ha hb (fun i j h => need i h.1 j h.2.1 h.2.2)
      (fun i _ j _ a' b' => safe i j ⟨a',b'⟩) c4
    exact StarSum.star a b dis th _ eqv
  | either x y ix iy =>
    obtain ⟨dis,sx,sy⟩ := tree
    have zx (i : V) : ¬eval {i} x := fun h => zero1 i (Or.inl h)
    have zy (i : V) : ¬eval {i} y := fun h => zero1 i (Or.inr h)
    have cross (i j : V) (hi : i∈vars x) (hj : j∈vars y) : ¬d i j := by
      intro e
      rcases need i (Or.inl hi) j (Or.inr hj) e with h | h
      · exact zx i ((project_one (eval_local x) (fun h0 => dis j h0 hj)).1 h)
      · exact zy j ((project_two (eval_local y) (dis i hi)).1 h)
    refine StarSum.join dis (ix sx zx (fun i j h => safe i j (Or.inl h)) ?_ ?_)
      (iy sy zy (fun i j h => safe i j (Or.inr h)) ?_ ?_)
    · intro i hi
      obtain ⟨j,hj,e⟩ := span i (Or.inl hi)
      rcases hj with hx | hy
      · exact ⟨j,hx,e⟩
      · exact False.elim (cross i j hi hy e)
    · intro i hi j hj e
      rcases need i (Or.inl hi) j (Or.inl hj) e with hx | hy
      · exact hx
      · exact False.elim (eval_empty y ((empty_pair (eval_local y) (dis i hi) (dis j hj)).1 hy))
    · intro i hi
      obtain ⟨j,hj,e⟩ := span i (Or.inr hi)
      rcases hj with hx | hy
      · exact False.elim (cross j i hx hi (dsym i j e))
      · exact ⟨j,hy,e⟩
    · intro i hi j hj e
      rcases need i (Or.inr hi) j (Or.inr hj) e with hx | hy
      · exact False.elim (eval_empty x ((empty_pair (eval_local x) (fun h => dis i h hi) (fun h => dis j h hj)).1 hx))
      · exact hy

end PEqualNP.Outside.L_meta_9743_Separated

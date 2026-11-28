import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18769.Rigid
open Finset
abbrev I := Fin 12
abbrev L := Fin 13
def idx (p : I) : L := ⟨p.val+1,by omega⟩
def nbr (p : I) : Finset L := univ.filter (fun l => idx p=l ∨ idx p=l+1 ∨ idx p=l+3 ∨ idx p=l+9)
theorem deg : ∀ p,(nbr p).card=4 := by decide +kernel
theorem loyal : ∀ p q : I,∀ l k : L, l≠k → l∈nbr p → l∈nbr q → k∈nbr p → k∈nbr q → p=q := by decide +kernel
def matching (l : L) (p : I) : L := (([[11, 12, 2, 1, 4, 10, 6, 5, 9, 7, 8, 3],[11, 2, 7, 4, 9, 5, 6, 12, 0, 10, 8, 3],[5, 12, 0, 1, 4, 6, 11, 8, 9, 7, 10, 3],[11, 12, 0, 1, 4, 10, 6, 5, 8, 7, 2, 9],[11, 2, 0, 8, 9, 5, 7, 12, 6, 1, 10, 3],[11, 12, 0, 1, 2, 6, 4, 7, 9, 10, 8, 3],[0, 12, 2, 4, 9, 5, 11, 7, 8, 1, 10, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 9, 8, 3],[0, 12, 7, 1, 2, 10, 4, 5, 6, 9, 11, 3],[11, 12, 0, 1, 2, 10, 4, 5, 6, 7, 8, 3],[11, 12, 0, 1, 2, 5, 4, 7, 6, 9, 8, 3],[5, 12, 0, 1, 2, 10, 4, 7, 6, 9, 8, 3],[0, 2, 7, 1, 4, 10, 11, 5, 6, 9, 8, 3]] : List (List L)).getD l.val []).getD p.val 0

theorem avoids : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧ Function.Injective (matching l) := by
  have facts : ∀ l : L,(∀ p : I,matching l p∈nbr p ∧ matching l p≠l) ∧
      (∀ p q : I,matching l p=matching l q → p=q) := by decide +kernel
  exact fun l => ⟨(facts l).1,fun _ _ => (facts l).2 _ _⟩
theorem cardinal12 {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a) :
    12≤Fintype.card α := by
  classical
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := by
    intro p q eq
    by_contra ne
    have d : matching 0 p ≠ matching 0 q := fun h=>ne ((avoids 0).2 h)
    have pq : p∈A (f q) := eq ▸ hp p
    have lp : matching 0 p∈B (f q) := eq ▸ hl p
    exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
        (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
  simpa using Fintype.card_le_of_injective f inj

theorem rigid {α : Type} [Fintype α] (A : α → Finset I) (B : α → Finset L)
    (valid : ∀a,∀p∈A a,∀l∈B a,l∈nbr p)
    (cover : ∀p,∀l∈nbr p,∃a,p∈A a ∧ l∈B a)
    (small : Fintype.card α≤12) :
    ∃ f : I → α,Function.Bijective f ∧ ∀p,A (f p)={p} ∧ B (f p)=nbr p := by
  classical
  have card : Fintype.card α=12 := le_antisymm small (cardinal12 A B valid cover)
  have hits (l : L) (a : α) : ∃ k∈B a,k≠l := by
    choose f hp hl using fun p => cover p (matching l p) ((avoids l).1 p).1
    have inj : Function.Injective f := by
      intro p q eq
      by_contra ne
      have d : matching l p ≠ matching l q := fun h=>ne ((avoids l).2 h)
      have pq : p∈A (f q) := eq ▸ hp p
      have lp : matching l p∈B (f q) := eq ▸ hl p
      exact ne (loyal p q _ _ d (valid _ p pq _ lp) (valid _ q (hp q) _ lp)
          (valid _ p pq _ (hl q)) (valid _ q (hp q) _ (hl q)))
    obtain ⟨p,rfl⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩).2 a
    exact ⟨_,hl p,((avoids l).1 p).2⟩
  have single (a : α) {p q : I} (hp : p∈A a) (hq : q∈A a) : p=q := by
    obtain ⟨u,hu,_⟩ := hits 0 a
    obtain ⟨v,hv,vu⟩ := hits u a
    exact loyal p q v u vu (valid _ _ hp _ hv) (valid _ _ hq _ hv) (valid _ _ hp _ hu) (valid _ _ hq _ hu)
  choose f hp hl using fun p => cover p (matching 0 p) ((avoids 0).1 p).1
  have inj : Function.Injective f := fun p q eq=>single (f q) (eq ▸ hp p) (hp q)
  have bij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [card]⟩
  refine ⟨f,bij,fun p=>⟨?_,?_⟩⟩
  · ext q
    exact ⟨fun h=>mem_singleton.mpr (single _ h (hp p)),fun h=>by rw [mem_singleton.mp h]; exact hp p⟩
  · apply Finset.Subset.antisymm
    · exact fun l h => valid _ _ (hp p) _ h
    · intro l hh
      obtain ⟨a,pa,la⟩ := cover p l hh
      obtain ⟨q,rfl⟩ := bij.2 a
      obtain rfl := single _ pa (hp q)
      exact la
end PEqualNP.Outside.L_meta_18769.Rigid
namespace PEqualNP.Outside.L_meta_18769.Multipliers
open Finset Rigid
abbrev Sig := I → L → Prop
def Raw (p : I) : Sig := fun q _=>q=p
def add (A B : Sig) : Sig := fun p l=>A p l ∨ B p l
def scale (A : Sig) (U : Finset L) : Sig := fun p l=>A p l ∧ l∈U
inductive Bank : Nat → Set Sig → Prop
  | inputs : Bank 0 (Set.range Raw)
  | join {n W} (h : Bank n W) {a b} (ha : a∈W) (hb : b∈W) : Bank n (insert (add a b) W)
  | mult {n W} (h : Bank n W) {a} (ha : a∈W) (u : Finset L) : Bank (n+1) (insert (scale a u) W)
def factors (bases : List (Finset I)) (signal : Sig) := ∃ U : Finset I,∃ coeff : Finset I→Finset L,
    ∀p l,signal p l ↔ p∈U ∨ ∃ A∈bases,p∈A ∧ l∈coeff A

theorem expand {n W} (h : Bank n W) :
    ∃ bases : List (Finset I),bases.length=n ∧ ∀ signal∈W,factors bases signal := by
  classical
  induction h with
  | inputs =>
    refine ⟨[],rfl,?_⟩
    rintro s ⟨p,rfl⟩
    exact ⟨{p},fun _=>∅,by simp [Raw]⟩
  | @join n W h a b ha hb ih =>
    obtain ⟨base,length,ok⟩ := ih
    refine ⟨base,length,?_⟩
    intro s hs
    rcases hs with rfl|old
    · obtain ⟨A,F,af⟩ := ok a ha
      obtain ⟨B,G,bg⟩ := ok b hb
      refine ⟨A∪B,fun c=>F c∪G c,?_⟩
      intro p l
      simp only [add,af,bg,mem_union]
      aesop
    · exact ok s old
  | @mult n W h a ha u ih =>
    obtain ⟨base,len,ok⟩ := ih
    obtain ⟨A,F,af⟩ := ok a ha
    refine ⟨A::base,by simp [len],?_⟩
    intro s hs
    rcases hs with rfl|old
    · let coeff (B : Finset I) := ((if B=A then u else ∅) ∪ (if B∈base then F B∩u else ∅))
      refine ⟨∅,coeff,?_⟩
      intro p l
      simp only [scale,af,mem_empty, false_or,List.mem_cons]
      constructor
      · rintro ⟨hp,hl⟩
        rcases hp with ap|⟨B,bb,pb,lf⟩
        · exact ⟨A,.inl rfl,ap,mem_union_left _ (by simpa using hl)⟩
        · exact ⟨B,.inr bb,pb,mem_union_right _ (by simpa [bb] using (mem_inter.mpr ⟨lf,hl⟩ : l∈F B∩u))⟩
      · rintro ⟨B,_,pb,lb⟩
        rcases mem_union.mp lb with la|le
        · by_cases eq : B=A
          · subst B;exact ⟨.inl pb,by simpa using la⟩
          · simp [eq] at la
        · by_cases hb : B∈base
          · have bu : l∈F B∩u := by simpa [hb] using le
            exact ⟨.inr ⟨B,hb,pb,(mem_inter.mp bu).1⟩,(mem_inter.mp bu).2⟩
          · simp [hb] at le
    · obtain ⟨B,G,eq⟩ := ok s old
      refine ⟨B,fun c=>if c∈base then G c else ∅,?_⟩
      intro p l
      rw [eq]
      constructor
      · rintro (hp|⟨q,hq,pq,lq⟩)
        · exact .inl hp
        · exact .inr ⟨q,List.mem_cons_of_mem _ hq,pq,by simpa [hq] using lq⟩
      · rintro (hp|⟨q,_,pq,lq⟩)
        · exact .inl hp
        · by_cases hq : q∈base
          · exact .inr ⟨q,hq,pq,by simpa [hq] using lq⟩
          · simp [hq] at lq

theorem twelve {n W} (h : Bank n W) (target : (fun p l=>l∈nbr p)∈W) : 12≤n := by
  classical
  obtain ⟨bases,len,hf⟩ := expand h
  obtain ⟨U,F,eq⟩ := hf _ target
  have empty : U=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have all : ∀l,l∈nbr p := fun l=>(eq p l).mpr (.inl hp)
    have full := eq_univ_of_forall all
    have z := deg p
    rw [full,card_univ,Fintype.card_fin] at z
    omega
  let A (i : Fin bases.length) := bases.get i
  let B (i : Fin bases.length) := F (A i)
  have valid (i : Fin bases.length) (p) (hp : p∈A i) (l) (hl : l∈B i) : l∈nbr p :=
    (eq p l).mpr (.inr ⟨_,List.get_mem _ _,hp,hl⟩)
  have covers (p) (l) (hl : l∈nbr p) : ∃i,p∈A i ∧ l∈B i := by
    obtain pin|⟨V,bb,pb,lb⟩ := (eq p l).mp hl
    · simp [empty] at pin
    · obtain ⟨i,ei⟩ := List.mem_iff_get.mp bb
      exact ⟨i,by simpa [A,ei] using pb,by simpa [B,A,ei] using lb⟩
  simpa only [Fintype.card_fin,len] using cardinal12 A B valid covers
end PEqualNP.Outside.L_meta_18769.Multipliers

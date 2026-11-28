import PEqualNP.Defs

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace PEqualNP.Outside.L_meta_17257

abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : Bank α) (n s : ℕ) := ∀ j<s,
  ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a∩W b

def UnionAt {α : Type*} (W : Bank α) (n j : ℕ) := ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b

theorem upward {α : Type*} {W : Bank α} {n s : ℕ} (hs : Steps W n s)
    {x y : α} (h : ∀ i<n, x∈W i → y∈W i) : ∀ w<n+s, x∈W w → y∈W w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hi : w<n
    · exact h w hi hx
    let j := w-n
    have eq : n+j=w := by dsimp [j]; omega
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := hs j (by dsimp [j]; omega) <;>
      rw [eq] at ha hb e <;> rw [e] at hx ⊢
    · exact hx.elim (fun t => Or.inl (ih a ha (ha.trans hw) t)) (fun t => Or.inr (ih b hb (hb.trans hw) t))
    · exact ih a ha (ha.trans hw) hx
    · exact hx
    · exact ⟨ih a ha (ha.trans hw) hx.1,ih b hb (hb.trans hw) hx.2⟩

def one {N : ℕ} (l : Fin N) : Vec N := fun k => decide (k=l)
def negRow {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (Y : Vec N) :
    Board N := (fun p => decide (¬∃ l, I p l ∧ Y l=true),Y)
def Inputs {N} (W : Bank (Board N)) := ∀ i : Fin N,
    W i.val = {z | z.1 i=true} ∧ W (N+i.val) = {z | z.2 i=true}


end PEqualNP.Outside.L_meta_17257

namespace PEqualNP.Outside.L_meta_17257.PoolBank
open Finset

variable {β : Type*} [Fintype β] [DecidableEq β]

noncomputable def sig (W : ℕ → Finset β → Prop) (w : ℕ) : Finset β :=
  univ.filter (fun l => (W w {l}))
theorem sig_spec (W : ℕ → Finset β → Prop) (w : ℕ) (l : β) : l∈sig W w ↔ W w {l} := by
  classical
  simp [sig]

def Rich (W : ℕ → Finset β → Prop) (L : Finset β) (w : ℕ) :=
  1<(sig W w).card ∧ sig W w⊆L


end PEqualNP.Outside.L_meta_17257.PoolBank
namespace PEqualNP.Outside.L_meta_17257.PoolBank
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]


end PEqualNP.Outside.L_meta_17257.PoolBank

namespace PEqualNP.Outside.L_meta_17257.Cut
open Finset
theorem boundary {n s : ℕ} (rich : ℕ → Prop) [DecidablePred rich]
    (parents : ℕ → Finset ℕ) (two : ∀ j<s,(parents j).card≤2)
    (back : ∀ j<s,∀ a∈parents j,a<n+j)
    (raw : ∀ w<n,¬rich w)
    {α : Type*} (W : ℕ → α → Prop)
    (forward : ∀ j<s,∀ x y,(∀ a∈parents j,W a x → W a y) → W (n+j) x → W (n+j) y) :
    ∀ k≤s,∀ Q : Finset ℕ,(∀ w∈Q,w<n+k) →
      ∃ F : Finset ℕ,(∀ w∈F,w<n+k ∧ ¬rich w) ∧
        F.card≤Q.card+((range k).filter (fun j => rich (n+j))).card ∧
        ∀ x y,(∀ w∈F,W w x → W w y) → ∀ w∈Q,W w x → W w y := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ Q lo
    exact ⟨Q,fun w hw => ⟨lo w hw,raw w (by simpa using lo w hw)⟩,by simp,fun _ _ h => h⟩
  | succ k ih =>
    intro cap Q lo
    let v := n+k
    let U := (range k).filter (fun j => rich (n+j))
    let T := (range (k+1)).filter (fun j => rich (n+j))
    have sub : U⊆T := by
      intro j hj
      have old := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp old.1)),old.2⟩
    have more := Finset.card_le_card sub
    have lower (w : ℕ) (hw : w∈Q) (ne : w≠v) : w<n+k := by
      have := lo w hw
      dsimp [v] at ne
      omega
    by_cases active : v∈Q
    · let E := Q.erase v
      have erase : E.card+1=Q.card := Finset.card_erase_add_one active
      have le (w : ℕ) (h : w∈E) : w<n+k := lower w (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1
      by_cases hit : rich v
      · let J := E∪parents k
        have low : ∀ a∈J,a<n+k := by
          intro a h
          exact (Finset.mem_union.mp h).elim (le a) (back k (by omega) a)
        obtain ⟨F,fr,fc,go⟩ := ih (by omega) J low
        refine ⟨F,fun w hw => ⟨by have z := (fr w hw).1; omega,(fr w hw).2⟩,?_,?_⟩
        · have jt := two k (by omega)
          have edge := Finset.card_union_le E (parents k)
          have mem : k∈T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hit⟩
          have miss : k∉U := by simp [U]
          have plus := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => miss (e.symm ▸ mem)⟩)
          change F.card≤J.card+U.card at fc
          change F.card≤Q.card+T.card
          dsimp [J] at fc
          omega
        · intro x y sim w hw
          by_cases eq : w=v
          · subst w
            exact forward k (by omega) x y (fun a ha => go x y sim a (Finset.mem_union_right _ ha))
          · exact go x y sim w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
      · obtain ⟨F,fr,fc,go⟩ := ih (by omega) E le
        refine ⟨insert v F,?_,?_,?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl|h
          · exact ⟨by dsimp [v]; omega,hit⟩
          · exact ⟨by have z := (fr w h).1; omega,(fr w h).2⟩
        · have plus := Finset.card_insert_le (a:=v) (s:=F)
          change F.card≤E.card+U.card at fc
          change _≤Q.card+T.card
          omega
        · intro x y sim w hw
          by_cases eq : w=v
          · exact eq.symm ▸ sim v (Finset.mem_insert_self _ _)
          · exact go x y (fun a ha => sim a (Finset.mem_insert_of_mem ha)) w (Finset.mem_erase.mpr ⟨eq,hw⟩)
    · obtain ⟨F,fr,fc,go⟩ := ih (by omega) Q (fun w hw => lower w hw (fun eq => active (eq ▸ hw)))
      refine ⟨F,fun w hw => ⟨by have z := (fr w hw).1; omega,(fr w hw).2⟩,?_,go⟩
      exact fc.trans (Nat.add_le_add_left more _)
end PEqualNP.Outside.L_meta_17257.Cut
namespace PEqualNP.Outside.L_meta_17257.PoolBank
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem necessary_cut (L : Finset β) (W : ℕ → Finset β → Prop) (o q : ℕ) (cap : L.card=q+1)
    (F : Finset ℕ) (coarse : ∀ w∈F, ¬Rich W L w)
    (up : ∀ w∈F,∀ X Y : Finset β,X⊆Y → W w X → W w Y)
    (forward : ∀ X Y : Finset β,(∀ w∈F,W w X → W w Y) → W o X → W o Y)
    (pos : ∀ l∈L,W o {l}) (neg : ∀ Y,Y.card≤q → Disjoint Y L → ¬W o Y) :
    q+1≤F.card := by
  classical
  by_contra! fail
  let C := F.filter (fun w => (sig W w).card≤1)
  have unseen : (C.biUnion (sig W)).card≤q := by
    have cu := Finset.card_biUnion_le (s:=C) (t:=sig W)
    have one : ∑ w∈C,(sig W w).card≤∑ _w∈C,1 :=
      Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp hw).2)
    have sub : C⊆F := Finset.filter_subset _ _
    have b := Finset.card_le_card sub
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at one
    omega
  obtain ⟨l,hl,miss⟩ : ∃ l∈L,l∉C.biUnion (sig W) := by
    by_contra! h
    have cl := Finset.card_le_card h
    omega
  let D := F.filter (fun w => l∈sig W w)
  have bad (w : ℕ) (hw : w∈D) : ∃ e∈sig W w,e∉L := by
    obtain ⟨wf,wl⟩ := Finset.mem_filter.mp hw
    by_contra! inside
    have tiny : (sig W w).card≤1 := by
      by_contra! h
      exact coarse w wf ⟨h,inside⟩
    exact miss (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨wf,tiny⟩,wl⟩)
  let pick (w : ℕ) := if h : w∈D then (bad w h).choose else l
  have chosen (w : ℕ) (h : w∈D) : pick w∈sig W w ∧ pick w∉L := by
    simpa [pick,h] using (bad w h).choose_spec
  let Y := D.image pick
  have ys : Y.card≤q := (Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))).trans (by omega : F.card≤q)
  have dis : Disjoint Y L := by
    apply Finset.disjoint_left.mpr
    intro a ha
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
    exact (chosen w hw).2
  apply neg Y ys dis
  apply forward {l} Y _ (pos l hl)
  intro w wf lit
  have wd : w∈D := Finset.mem_filter.mpr ⟨wf,(sig_spec W w l).mpr lit⟩
  exact up w wf {pick w} Y (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ wd))
    ((sig_spec W w (pick w)).mp (chosen w wd).1)

theorem sharp_row {n s o q : ℕ} (W : ℕ → Finset β → Prop) (L : Finset β) (cap : L.card=q+1)
    (oo : o<n+s) (up : ∀ w<n+s,∀ X Y : Finset β,X⊆Y → W w X → W w Y)
    (raw : ∀ w<n,¬Rich W L w) (T : ℕ → Finset ℕ) (two : ∀ j<s,(T j).card≤2)
    (back : ∀ j<s,∀ a∈T j,a<n+j) (forward : ∀ j<s,∀ X Y,
      (∀ w∈T j,W w X → W w Y) → W (n+j) X → W (n+j) Y)
    (pos : ∀ l∈L,W o {l}) (neg : ∀ Y,Y.card≤q → Disjoint Y L → ¬W o Y) :
    q≤((range s).filter (fun j => Rich W L (n+j))).card := by
  classical
  obtain ⟨F,lim,price,sim⟩ := Cut.boundary (Rich W L) T two back raw W forward s le_rfl {o}
    (by intro w hw; exact (Finset.mem_singleton.mp hw).symm ▸ oo)
  have cost := necessary_cut L W o q cap F (fun w hw => (lim w hw).2)
    (fun w hw => up w (lim w hw).1) (fun X Y h => sim X Y h o (by simp)) pos neg
  simp only [Finset.card_singleton] at price
  omega

end PEqualNP.Outside.L_meta_17257.PoolBank

end

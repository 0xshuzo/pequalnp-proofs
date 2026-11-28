import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17257.PoolBank
open Finset

variable {β : Type*} [Fintype β] [DecidableEq β]

noncomputable def sig (W : ℕ → Finset β → Prop) (w : ℕ) : Finset β :=
  univ.filter (fun l => by classical exact decide (W w {l}))
theorem sig_spec (W : ℕ → Finset β → Prop) (w : ℕ) (l : β) : l∈sig W w ↔ W w {l} := by
  classical
  simp [sig]

def Rich (W : ℕ → Finset β → Prop) (L : Finset β) (w : ℕ) :=
  1<(sig W w).card ∧ sig W w⊆L

theorem row_bound (W : ℕ → Finset β → Prop) (L : Finset β) (ports : Finset ℕ)
    (n s q : ℕ) (card : L.card=q+1)
    (up : ∀ w X Y,X⊆Y → W w X → W w Y)
    (raw : ∀ w<n,(sig W w).card≤1)
    (preds : ℕ → Finset ℕ) (two : ∀ j<s,(preds j).card≤2)
    (back : ∀ j<s,∀ w∈preds j,w<n+j)
    (compute : ∀ j<s,∀ X Y : Finset β,
      (∀ w∈preds j,W w X → W w Y) → W (n+j) X → W (n+j) Y)
    (live : ∀ w∈ports,w<n+s)
    (accept : Finset β → Prop)
    (query : ∀ X Y,(∀ w∈ports,W w X → W w Y) → accept X → accept Y)
    (pos : ∀ l∈L,accept {l}) (neg : ∀ Y,Y.card≤q → Disjoint Y L → ¬accept Y) :
    q+1≤ports.card+2*((range s).filter (fun j => by classical exact decide (Rich W L (n+j)))).card := by
  classical
  let R := (range s).filter (fun j => decide (Rich W L (n+j)))
  let F := ports∪R.biUnion preds
  have size : F.card≤ports.card+2*R.card := by
    have c := Finset.card_biUnion_le (s:=R) (t:=preds)
    have b : ∑ j∈R,(preds j).card≤∑ _j∈R,2 :=
      Finset.sum_le_sum (fun j hj => two j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
    have u := Finset.card_union_le ports (R.biUnion preds)
    simp only [Finset.sum_const,smul_eq_mul] at b
    dsimp [F]
    omega
  by_contra! fail
  change ports.card+2*R.card<q+1 at fail
  have small : F.card≤q := by omega
  let C := F.filter (fun w => (sig W w).card≤1)
  have csize : (C.biUnion (sig W)).card≤q := by
    have c := Finset.card_biUnion_le (s:=C) (t:=sig W)
    have b : ∑ j∈C,(sig W j).card≤∑ _j∈C,1 :=
      Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2)
    have sub : C⊆F := Finset.filter_subset _ _
    have one : ∑ _j∈C,1≤q := by simpa using (Finset.card_le_card sub).trans small
    exact c.trans (b.trans one)
  obtain ⟨l,hl,absent⟩ : ∃ l∈L,l∉C.biUnion (sig W) := by
    by_contra! bad
    have le := Finset.card_le_card bad
    omega
  let D := F.filter (fun w => ¬sig W w⊆L)
  have chooseBad (w : ℕ) (hw : w∈D) : ∃ e∈sig W w,e∉L := by
    have h := (Finset.mem_filter.mp hw).2
    by_contra! deny
    exact h deny
  let pick (w : ℕ) := if h : w∈D then (chooseBad w h).choose else l
  have chosen (w : ℕ) (h : w∈D) : pick w∈sig W w ∧ pick w∉L := by
    simpa [pick,dif_pos h] using (chooseBad w h).choose_spec
  let Y := D.image pick
  have ys : Y.card≤q := (Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))).trans small
  have dis : Disjoint Y L := by
    apply Finset.disjoint_left.mpr
    intro e he
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
    exact (chosen w hw).2
  have sim (w : ℕ) : w<n+s → w∈F → W w {l} → W w Y := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro lt wf lit
      have inSig := (sig_spec W w l).mpr lit
      by_cases tiny : (sig W w).card≤1
      · exact (absent (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨wf,tiny⟩,inSig⟩)).elim
      by_cases inside : sig W w⊆L
      · have nonraw : n≤w := by by_contra! h; exact tiny (raw w h)
        let j := w-n
        have eq : n+j=w := by dsimp [j]; omega
        have js : j<s := by omega
        have rich : Rich W L (n+j) := eq.symm ▸ ⟨by omega,inside⟩
        have jr : j∈R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr js,by simpa using rich⟩
        rw [←eq] at lit ⊢
        apply compute j js {l} Y _ lit
        intro a ha
        have aw := (back j js a ha)
        have af : a∈F := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,jr,ha⟩)
        exact ih a (by omega) (by omega) af
      · have wd : w∈D := Finset.mem_filter.mpr ⟨wf,inside⟩
        have hit := (sig_spec W w (pick w)).mp (chosen w wd).1
        exact up w {pick w} Y (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ wd)) hit
  exact neg Y ys dis (query {l} Y (fun w hw => sim w (live w hw) (Finset.mem_union_left _ hw)) (pos l hl))

theorem all_rows {N q n s} (W : ℕ → Finset (Fin N) → Prop)
    (L : Fin N → Finset (Fin N)) (ports : Fin N → Finset ℕ)
    (linear : ∀ p r : Fin N,p≠r → (L p∩L r).card≤1)
    (bound : ∀ p,q+1≤(ports p).card+
       2*((range s).filter (fun j => by classical exact decide (Rich W (L p) (n+j)))).card) :
    N*(q+1)≤2*s+∑ p,(ports p).card := by
  classical
  let U (p : Fin N) := (range s).filter (fun j => decide (Rich W (L p) (n+j)))
  have dis : (univ : Set (Fin N)).PairwiseDisjoint U := by
    intro p _ r _ ne
    apply Finset.disjoint_left.mpr
    intro j hp hr
    have pa : Rich W (L p) (n+j) := by simpa using (Finset.mem_filter.mp hp).2
    have ra : Rich W (L r) (n+j) := by simpa using (Finset.mem_filter.mp hr).2
    have sub : sig W (n+j)⊆L p∩L r := fun _ h => Finset.mem_inter.mpr ⟨pa.2 h,ra.2 h⟩
    exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (linear p r ne))) pa.1
  have cover : univ.biUnion U⊆range s := by
    intro j h
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp hp).1
  have spent := Finset.card_le_card cover
  rw [Finset.card_biUnion dis,Finset.card_range] at spent
  have localBound (p : Fin N) : q+1≤(ports p).card+2*(U p).card := bound p
  have sum := Finset.sum_le_sum (s:=univ) (fun (p : Fin N) _ => localBound p)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    Finset.sum_add_distrib,←Finset.mul_sum] at sum
  omega

end PEqualNP.Outside.L_meta_17257.PoolBank

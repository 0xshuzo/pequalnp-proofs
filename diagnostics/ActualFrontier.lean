import PEqualNP.Defs

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
  univ.filter (fun l => by classical exact decide (W w {l}))
theorem sig_spec (W : ℕ → Finset β → Prop) (w : ℕ) (l : β) : l∈sig W w ↔ W w {l} := by
  classical
  simp [sig]

def Rich (W : ℕ → Finset β → Prop) (L : Finset β) (w : ℕ) :=
  1<(sig W w).card ∧ sig W w⊆L


end PEqualNP.Outside.L_meta_17257.PoolBank
namespace PEqualNP.Outside.L_meta_17257.PoolBank
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem frontier_escape (W : ℕ → Finset β → Prop) (L : Finset β)
    (n s o q : ℕ) (oo : o<n+s)
    (up : ∀ w<n+s,∀ X Y : Finset β,X⊆Y → W w X → W w Y)
    (raw : ∀ w<n,¬Rich W L w)
    (preds : ℕ → Finset ℕ) (back : ∀ j<s,∀ w∈preds j,w<n+j)
    (compute : ∀ j<s,∀ X Y : Finset β,
      (∀ w∈preds j,W w X → W w Y) → W (n+j) X → W (n+j) Y)
    (l : β) (positive : W o {l})
    (negative : ∀ Y : Finset β,Y.card≤q → Disjoint Y L → ¬W o Y) :
    let R := (range s).filter (fun j => by classical exact decide (Rich W L (n+j)))
    let F := (insert o (R.biUnion preds)).filter (fun w => by classical exact decide (¬Rich W L w))
    (∃ w∈F,sig W w={l}) ∨
      (∀ Y : Finset β,Y.card≤q → Disjoint Y L →
        ∃ w∈F,l∈sig W w ∧ ¬sig W w⊆L ∧ Disjoint Y (sig W w)) := by
  classical
  dsimp only
  let R := (range s).filter (fun j => decide (Rich W L (n+j)))
  let H := insert o (R.biUnion preds)
  let F := H.filter (fun w => decide (¬Rich W L w))
  change (∃ w∈F,sig W w={l}) ∨ _
  by_cases found : ∃ w∈F,sig W w={l}
  · exact Or.inl found
  right
  intro Y small dis
  change ∃ w∈F,l∈sig W w ∧ ¬sig W w⊆L ∧ Disjoint Y (sig W w)
  by_contra failed
  have sim (w : ℕ) : w<n+s → w∈H → W w {l} → W w Y := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro lt wh lit
      have sigl := (sig_spec W w l).mpr lit
      by_cases rich : Rich W L w
      · have le : n≤w := by by_contra! h; exact raw w h rich
        let j := w-n
        have eq : n+j=w := by dsimp [j]; omega
        have js : j<s := by omega
        have jr : j∈R := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr js,by simpa only [decide_eq_true_eq,eq] using rich⟩
        rw [←eq] at lit ⊢
        apply compute j js {l} Y _ lit
        intro v hv
        have vl := back j js v hv
        exact ih v (by omega) (by omega)
          (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j,jr,hv⟩))
      · have wf : w∈F := Finset.mem_filter.mpr ⟨wh,by simpa using rich⟩
        have dirty : ¬sig W w⊆L := by
          intro inside
          have tiny : (sig W w).card≤1 := by
            by_contra! big
            exact rich ⟨big,inside⟩
          have same : sig W w={l} := by
            apply Finset.Subset.antisymm
            · intro y hy
              exact Finset.mem_singleton.mpr (Finset.card_le_one.mp tiny y hy l sigl)
            · exact Finset.singleton_subset_iff.mpr sigl
          exact found ⟨w,wf,same⟩
        have hit : ¬Disjoint Y (sig W w) := fun d => failed ⟨w,wf,sigl,dirty,d⟩
        obtain ⟨y,hy,hys⟩ := Finset.not_disjoint_iff.mp hit
        exact up w lt {y} Y (Finset.singleton_subset_iff.mpr hy) ((sig_spec W w y).mp hys)
  exact negative Y small dis (sim o oo (Finset.mem_insert_self o _) positive)

end PEqualNP.Outside.L_meta_17257.PoolBank
namespace PEqualNP.Outside.L_meta_17257
open Finset
open PoolBank

def bits {N} (Y : Finset (Fin N)) : Vec N := fun t => decide (t∈Y)
theorem bits_one {N} (l : Fin N) : bits {l}=one l := by
  funext r
  simp [bits,one]
def slice {N} (W : Bank (Board N)) (p : Fin N) (w : ℕ) (Y : Finset (Fin N)) : Prop :=
  (one p,bits Y)∈W w
theorem monoBoard {N s : ℕ} (W : Bank (Board N)) (raw : Inputs W) (hs : Steps W (N+N) s)
    {A B : Board N} (left : ∀ k,A.1 k=true → B.1 k=true) (right : ∀ k,A.2 k=true → B.2 k=true)
    (w : ℕ) (wl : w<N+N+s) : A∈W w → B∈W w := by
  apply upward hs _ w wl
  intro r hr
  by_cases h : r<N
  · let k : Fin N := ⟨r,h⟩
    change A∈W k.val → B∈W k.val
    rw [(raw k).1]
    exact left k
  · let k : Fin N := ⟨r-N,by omega⟩
    have e : N+k.val=r := by dsimp [k]; omega
    rw [←e,(raw k).2]
    exact right k

def ForkAt {N : ℕ} (W : Bank (Board N)) (j : ℕ) (T : Finset ℕ) :=
  T.card≤2 ∧ (∀ w∈T,w<N+N+j) ∧
    ∀ A B : Board N,(∀ w∈T,A∈W w → B∈W w) → A∈W (N+N+j) → B∈W (N+N+j)

theorem forks {N s} (W : Bank (Board N)) (hs : Steps W (N+N) s) :
    ∃ T : ℕ → Finset ℕ,∀ j<s,ForkAt W j (T j) := by
  classical
  have pick (j : ℕ) (hj : j<s) : ∃ t,ForkAt W j t := by
    obtain ⟨a,ha,b,hb,e⟩ := hs j hj
    refine ⟨{a,b},Finset.card_le_two,?_,?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl|h
      · exact ha
      · exact (Finset.mem_singleton.mp h).symm ▸ hb
    · intro x y sim
      have l := sim a (by simp)
      have r := sim b (by simp)
      rcases e with e|e|e|e <;> rw [e]
      · exact fun hit => hit.imp l r
      · exact l
      · exact id
      · exact fun h => ⟨l h.1,r h.2⟩
  exact ⟨fun j => if h : j<s then (pick j h).choose else ∅,
    fun j hj => by simpa only [dif_pos hj] using (pick j hj).choose_spec⟩

theorem flag_frontier {N q s o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (W : Bank (Board N)) (ho : o<N+N+s) (raw : Inputs W) (hs : Steps W (N+N) s)
    (pos : ∀ p l,I p l → (one p,one l)∈W o)
    (neg : ∀ Y : Vec N,Fintype.card {l : Fin N // Y l=true}≤q → negRow I Y∉W o)
    (outside : ∀ p,∃ l,¬I p l) :
    ∃ T : ℕ → Finset ℕ,(∀ j<s,ForkAt W j (T j)) ∧ ∀ (p l : Fin N), I p l →
      let V := slice W p
      let L := univ.filter (fun m => I p m)
      let R := (range s).filter (fun j => by classical exact decide (Rich V L (N+N+j)))
      let F := (insert o (R.biUnion T)).filter (fun w => by classical exact decide (¬Rich V L w))
      (∃ w∈F,sig V w={l}) ∨
        ∀ Y : Finset (Fin N), Y.card≤q → Disjoint Y L →
          ∃ w∈F,l∈sig V w ∧ ¬sig V w⊆L ∧ Disjoint Y (sig V w) := by
  classical
  obtain ⟨T,spec⟩ := forks W hs
  refine ⟨T,spec,?_⟩
  intro p l inc
  let V := slice W p
  let L := univ.filter (fun m => I p m)
  apply frontier_escape V L (N+N) s o q ho _ _ T (fun j hj => (spec j hj).2.1) _ l _ _
  · intro w hw X Y xy
    exact monoBoard W raw hs (fun _ h => h) (fun k h => by
      change decide (k∈X)=true at h
      change decide (k∈Y)=true
      exact decide_eq_true (xy (of_decide_eq_true h))) w hw
  · intro w hw h
    by_cases left : w<N
    · let r : Fin N := ⟨w,left⟩
      have eqv (t : Fin N) : V w {t} ↔ r=p := by
        change (one p,bits {t})∈W r.val ↔ _
        rw [(raw r).1]
        simp [one]
      have any := Finset.card_pos.mp (show 0<(sig V w).card by have := h.1; omega)
      obtain ⟨t,ht⟩ := any
      have rp := (eqv t).mp ((sig_spec V w t).mp ht)
      obtain ⟨v,hv⟩ := outside p
      exact hv (Finset.mem_filter.mp (h.2 ((sig_spec V w v).mpr ((eqv v).mpr rp)))).2
    · let r : Fin N := ⟨w-N,by omega⟩
      have eqw : N+r.val=w := by dsimp [r]; omega
      have sing : sig V w⊆{r} := by
        intro t ht
        have own := (sig_spec V w t).mp ht
        change (one p,bits {t})∈W w at own
        rw [←eqw,(raw r).2] at own
        have rt : r=t := by simpa [bits] using own
        exact Finset.mem_singleton.mpr rt.symm
      have cc := Finset.card_le_card sing
      simp only [Finset.card_singleton] at cc
      exact (Nat.not_lt_of_ge cc) h.1
  · intro j hj X Y sim
    exact (spec j hj).2.2 (one p,bits X) (one p,bits Y) sim
  · change (one p,bits {l})∈W o
    rw [bits_one]
    exact pos p l inc
  · intro Y sz clear hit
    have cy : Fintype.card {k : Fin N // bits Y k=true}≤q := by
      simpa [Fintype.card_subtype,bits] using sz
    apply neg (bits Y) cy
    apply monoBoard W raw hs _ (fun _ h => h) o ho hit
    intro k hk
    have kp : k=p := by simpa [one] using hk
    subst k
    change decide (¬∃ m,I p m ∧ bits Y m=true)=true
    apply decide_eq_true
    rintro ⟨m,mi,my⟩
    have ym : m∈Y := by simpa [bits] using my
    exact Finset.disjoint_left.mp clear ym (Finset.mem_filter.mpr ⟨Finset.mem_univ _,mi⟩)

end PEqualNP.Outside.L_meta_17257

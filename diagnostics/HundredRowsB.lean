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

theorem point_rich_count {N q s o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (W : Bank (Board N)) (ho : o<N+N+s) (raw : Inputs W) (hs : Steps W (N+N) s)
    (pos : ∀ p l,I p l → (one p,one l)∈W o)
    (neg : ∀ Y : Vec N,Fintype.card {l : Fin N // Y l=true}≤q → negRow I Y∉W o)
    (p : Fin N) (pencil : (univ.filter (fun l => I p l)).card=q+1) (outside : ∃ l,¬I p l) :
    q≤((range s).filter (fun j => Rich (slice W p) (univ.filter (fun l => I p l)) (N+N+j))).card := by
  classical
  let V := slice W p
  let L := univ.filter (fun m => I p m)
  obtain ⟨T,spec⟩ := forks W hs
  apply sharp_row V L pencil ho _ _ T (fun j hj => (spec j hj).1) (fun j hj => (spec j hj).2.1) _ _ _
  · intro w hw X Y xy
    exact monoBoard W raw hs (A:=(one p,bits X)) (B:=(one p,bits Y)) (fun _ h => h) (fun k h => by
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
      obtain ⟨v,hv⟩ := outside
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
  · intro l hl
    change (one p,bits {l})∈W o
    rw [bits_one]
    exact pos p l (Finset.mem_filter.mp hl).2
  · intro Y sz clear hit
    have cy : Fintype.card {k : Fin N // bits Y k=true}≤q := by
      simpa [Fintype.card_subtype,bits] using sz
    apply neg (bits Y) cy
    apply monoBoard W raw hs (A:=(one p,bits Y)) (B:=negRow I (bits Y)) _ (fun _ h => h) o ho hit
    intro k hk
    have kp : k=p := by simpa [one] using hk
    subst k
    change decide (¬∃ m,I p m ∧ bits Y m=true)=true
    apply decide_eq_true
    rintro ⟨m,mi,my⟩
    have ym : m∈Y := by simpa [bits] using my
    exact Finset.disjoint_left.mp clear ym (Finset.mem_filter.mpr ⟨Finset.mem_univ _,mi⟩)

end PEqualNP.Outside.L_meta_17257
namespace PEqualNP.Outside.L_meta_17257
open PoolBank Finset

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)



noncomputable def load {N} (W : Bank (Board N)) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (j : ℕ) :=
  (univ.filter (fun p : Fin N => Rich (slice W p) (univ.filter (fun l => I p l)) (N+N+j))).card

theorem dual_price {N q s o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (W : Bank (Board N)) (hq : 2≤q) (order : N=q^2+q+1)
    (col : ∀ l : Fin N,Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r : Fin N,p≠r → ∃! l,I p l ∧ I r l)
    (ho : o<N+N+s) (raw : Inputs W) (hs : Steps W (N+N) s)
    (pos : ∀ p l,I p l → (one p,one l)∈W o)
    (neg : ∀ Y : Vec N,Fintype.card {l : Fin N // Y l=true}≤q → negRow I Y∉W o) :
    N*q≤∑ j∈range s,load W I j := by
  classical
  have rows (p : Fin N) : (univ.filter (fun l => I p l)).card=q+1 := lines_through q N I hq order (fun l => by
    simpa only [Fintype.card_subtype] using col l) join p
  have outside (p : Fin N) : ∃ l,¬I p l := by
    by_contra! all
    have bad := rows p
    simp [all] at bad
    nlinarith
  have total := Finset.sum_le_sum (s:=univ) (fun (p : Fin N) _ =>
    point_rich_count I W ho raw hs pos neg p (rows p) (outside p))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  calc N*q ≤ _ := total
       _ = ∑ j∈range s,load W I j := by
          simp only [load,Finset.card_filter]
          rw [Finset.sum_comm]

theorem under99 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → x1 % (2 : ℕ) = (0 : ℕ) → (∀ j<x11,load x14 x3 j≤99) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11 := by
  intro q N I inst
  dsimp only
  intro hq order col join s o M W ho raw steps pos neg _ _ light
  have plain : Steps W (N+N) s := by
    intro j hj
    obtain ⟨a,ha,b,hb,e|e⟩ := steps j hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at e
      exact ⟨a,ha,b,hb,e.imp_right (Or.imp_right Or.inl)⟩
    · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr e.1))⟩
  have total := dual_price I W (by omega) order col join ho raw plain pos neg
  have lim := Finset.sum_le_sum (s:=range s) (fun j hj => light j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at lim
  have nq := Nat.mul_le_mul_left N (show 99≤q by omega)
  rw [Nat.mul_add,Nat.mul_one]
  omega

end PEqualNP.Outside.L_meta_17257
end

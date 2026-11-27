import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.Slices
open Finset
abbrev P := Fin 13
abbrev L := Fin 11
abbrev X := P → Bool
abbrev Y := L → Bool
def masks : L → Nat := ![2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]
def edge (q : P) (l : L) : Prop := (masks l).testBit q.val=true
instance (q : P) (l : L) : Decidable (edge q l) := by unfold edge; infer_instance
def neighbors (l : L) : Finset P := univ.filter fun q => edge q l
theorem degree : ∀l,(neighbors l).card=4 := by decide +kernel
theorem c4 : ∀ (l m : L) (p q : P),edge p l → edge q l → edge p m → edge q m → p≠q → l=m := by decide +kernel
theorem safePoint (p : P) (T : Finset L) (line : ∀l∈T,edge p l)
    (size : T.card≤3) {l : L} (away : l∉T) : ∃q : P,q≠p ∧ edge q l ∧ ∀m∈T,¬edge q m := by
  classical
  by_cases ep : edge p l
  · have ex : ∃ q∈neighbors l,q≠p := by
      by_contra! no
      have sub : neighbors l ⊆ {p} := by intro q h;simpa using no q h
      have le := card_le_card sub
      simp [degree] at le
    obtain ⟨q,hq,ne⟩ := ex
    have ql := (mem_filter.mp hq).2
    refine ⟨q,ne,ql,?_⟩
    intro m hm qm
    exact away ((c4 l m p q ep ql (line m hm) qm ne.symm).symm ▸ hm)
  · by_contra! fail
    have found (q : P) (hq : q∈neighbors l) : ∃m∈T,edge q m := by
      have ql := (mem_filter.mp hq).2
      have ne : q≠p := fun eq => ep (eq ▸ ql)
      exact fail q ne ql
    let pick (q : P) := if h : q∈neighbors l then Classical.choose (found q h) else 0
    have picked (q : P) (hq : q∈neighbors l) : pick q∈T ∧ edge q (pick q) := by
      simpa [pick,hq] using Classical.choose_spec (found q hq)
    have le : (neighbors l).card ≤ T.card := by
      apply card_le_card_of_injOn pick (fun q hq => (picked q hq).1)
      intro a ha b hb eq
      by_contra ne
      have ba : edge b (pick a) := eq.symm ▸ (picked b hb).2
      have same := c4 l (pick a) a b (mem_filter.mp ha).2 (mem_filter.mp hb).2 (picked a ha).2 ba ne
      exact away (same.symm ▸ (picked a ha).1)
    rw [degree] at le
    omega
def one (q : P) : X := fun r => decide (r=q)
def other (l : L) : X := fun r => !decide (edge r l)
def column (T : Finset L) : Y := fun l => decide (l∈T)
def hit (x : X) (y : Y) : Prop := ∃ q l, x q=true ∧ y l=true ∧ edge q l
def inc {A : Type} (a b : A→Bool) := ∀ i,a i=true → b i=true
def mono (a : X → Bool) := ∀ x y,inc x y → a x=true → a y=true
def mixMono (f : Y → Bool → Y → Bool) := ∀ z b y zz bb yy,
  inc z zz → (b=true → bb=true) → inc y yy → f z b y=true → f zz bb yy=true

structure Bank (p : P) (D : Finset L) where
  w : X → Bool
  h : L → X → Bool
  fn : Y → Bool → Y → Bool
  wm : mono w
  hm : ∀ l,mono (h l)
  up : mixMono fn
  plane : ∀ l∈D,edge p l
  pyes : w (one p)=true
  pno : ∀ q,q≠p → w (one q)=false
  absent : ∀ l∈D,h l (one p)=false
  single : ∀l q,edge q l → q≠p → h l (one q)=true
  decline : ∀ l,h l (other l)=false
  woff : ∀ l∈D,w (other l)=false
  exactFn : ∀ x y,fn (fun l => h l x) (w x) y=true ↔ hit x y

theorem one_mono {q : P} {x : X} (hq : x q=true) : inc (one q) x := by
  intro r h
  have e : r=q := by simpa [one] using h
  exact e ▸ hq

theorem Bank.outside {p D} (B : Bank p D) {q l} (h : ¬edge q l) :
    B.h l (one q)=false := by
  cases e : B.h l (one q)
  · rfl
  · have up := B.hm l _ _ (one_mono (by simp [other,h])) e
    rw [B.decline] at up
    contradiction

def background (T : Finset L) : X := fun q => decide (∀ m∈T,¬edge q m)
def code (D A : Finset L) : Y := fun l => decide (l∉D ∨ l∈A)

theorem Bank.low {p D} (B : Bank p D) {l : L} (hl : l∈D) :
    B.fn (code D ∅) true (column {l})=true ∧
      B.fn (code D {l}) false (column {l})=true := by
  have y : column {l} l=true := by simp [column]
  have fire (q : P) (eq : edge q l) : B.fn (fun j=>B.h j (one q)) (B.w (one q)) (column {l})=true :=
    (B.exactFn _ _).mpr ⟨q,l,by simp [one],y,eq⟩
  constructor
  · apply B.up _ _ _ _ _ _ ?_ (fun _=>rfl) (fun _ h=>h) (fire p (B.plane l hl))
    intro j h
    by_cases jd : j∈D
    · rw [B.absent j jd] at h; contradiction
    · simp [code,jd]
  · obtain ⟨q,ne,ql,_⟩ := safePoint p ∅ (by simp) (by simp) (l:=l) (by simp)
    apply B.up _ _ _ _ _ _ ?_ ?_ (fun _ h=>h) (fire q ql)
    · intro j yes
      by_cases jd : j∈D
      · by_cases eq : j=l
        · simp [code,eq]
        · have no : ¬edge q j := fun qj => eq ((c4 j l p q (B.plane j jd) qj (B.plane l hl) ql ne.symm))
          rw [B.outside no] at yes
          contradiction
      · simp [code,jd]
    · rw [B.pno q ne];simp

theorem Bank.high {p D} (B : Bank p D) (T : Finset L) (sub : T ⊆ D) (size : T.card≤3)
    (nonempty : T.Nonempty) : B.fn (code D (D \ T)) false (column T)=false := by
  let x := background T
  have below (l : L) (hl : l∈T) : inc x (other l) := by
    intro q e
    have all : ∀m∈T,¬edge q m := by simpa [x,background] using e
    simp [other,all l hl]
  have value (l : L) : B.h l x=code D (D \ T) l := by
    by_cases lt : l∈T
    · have no : B.h l x=false := by
        cases b : B.h l x
        · rfl
        · have v := B.hm l _ _ (below l lt) b
          rw [B.decline] at v
          contradiction
      simp [no,code,sub lt,lt]
    · obtain ⟨q,ne,ql,safe⟩ := safePoint p T (fun l h=>B.plane l (sub h)) size lt
      have on : x q=true := by simpa [x,background] using safe
      have b := B.hm l _ _ (one_mono on) (B.single l q ql ne)
      simp [b,code,lt]
  have w : B.w x=false := by
    obtain ⟨l,hl⟩ := nonempty
    cases b : B.w x
    · rfl
    · have z := B.wm _ _ (below l hl) b
      rw [B.woff _ (sub hl)] at z
      contradiction
  cases b : B.fn (code D (D \ T)) false (column T)
  · rfl
  · rw [←funext value,←w] at b
    obtain ⟨q,l,on,ys,e⟩ := (B.exactFn _ _).mp b
    have all : ∀m∈T,¬edge q m := by simpa [x,background] using on
    exact (all l (by simpa [column] using ys) e).elim

end PEqualNP.Outside.L_meta_9792.Slices

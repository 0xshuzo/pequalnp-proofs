import Mathlib
import PEqualNP.Defs

namespace Source2071

abbrev Gate (m : ℕ) := Fin m
def w {m : ℕ} (j : Gate m) := 26+j.val

inductive Feed {m : ℕ} (a b : Gate m → ℕ) (k : Gate m) : ℕ → Prop
  | here : Feed a b k (w k)
  | left (j : Gate m) (h : Feed a b k (a j)) : Feed a b k (w j)
  | right (j : Gate m) (h : Feed a b k (b j)) : Feed a b k (w j)

def SourceOnly {m : ℕ} (a b : Gate m → ℕ) (A : Gate m → Prop) (d : Gate m) :=
  ∀ k j, A k → A j → (Feed a b k (a j) ∨ Feed a b k (b j)) → k=d

def Live {m : ℕ} (a b : Gate m → ℕ) (o i : ℕ) :=
  ∀ H : ℕ → Prop, H o → (∀ j, H (w j) → H (a j) ∧ H (b j)) → H i

lemma reaches {m} {a b : Gate m → ℕ} {k : Gate m} {o : ℕ} (h : Live a b o (w k)) :
    Feed a b k o := by
  by_contra absent
  have h' := h (fun i => ¬Feed a b k i) absent (fun j hj =>
    ⟨fun ha => hj (.left j ha),fun hb => hj (.right j hb)⟩)
  exact h' .here

def Values {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (D : ℕ → Bool) :=
  ∀ j, (A j → D (w j) = (D (a j) && D (b j))) ∧
    (¬A j → D (w j) = (D (a j) || D (b j)))

lemma source_dirty {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o}
    (one : SourceOnly a b A d) (ak : A k) (hk : Live a b o (w k)) (Y : ℕ → Bool)
    (value : Values a b A Y) (yk : Y (w k)=true) (yo : Y o=false) : Y (w d)=true := by
  by_cases same : k=d
  · rwa [←same]
  have forward (i : ℕ) (h : Feed a b k i) : Y i=true := by
    induction h with
    | here => exact yk
    | left j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inl hj))
      simp [(value j).2 nj,ih]
    | right j hj ih =>
      have nj : ¬A j := fun aj => same (one k j ak aj (.inr hj))
      simp [(value j).2 nj,ih]
  exact Bool.noConfusion ((forward o (reaches hk)).symm.trans yo)

inductive Parse {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (x y : ℕ) :
    ℕ → ℕ → ℕ → Prop
  | xleaf : Parse a b A x y x 1 0
  | yleaf : Parse a b A x y y 0 1
  | join (j : Gate m) (op : A j) {u v s t : ℕ}
      (ha : Parse a b A x y (a j) u v) (hb : Parse a b A x y (b j) s t) :
      Parse a b A x y (w j) (u+s) (v+t)
  | left (j : Gate m) (op : ¬A j) {u v : ℕ} (ha : Parse a b A x y (a j) u v) :
      Parse a b A x y (w j) u v
  | right (j : Gate m) (op : ¬A j) {u v : ℕ} (hb : Parse a b A x y (b j) u v) :
      Parse a b A x y (w j) u v

lemma feed_le {m} {a b : Gate m → ℕ} (ha : ∀ j,a j < w j) (hb : ∀ j,b j < w j)
    {k : Gate m} {i : ℕ} (f : Feed a b k i) : w k ≤ i := by
  induction f with
  | here => exact le_rfl
  | left j _ h => exact h.trans (ha j).le
  | right j _ h => exact h.trans (hb j).le

def Above {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (w0 : ℕ) (S : Gate m → Prop) :=
  ∀ k, A k → Feed a b k w0 → S k

-- For any chosen proof, a wire with no AND ancestors contributes one leaf.
-- If its only possible AND ancestor is d, it contributes at most two;
-- if d is true on Y and the wire is false, it contributes just one.
lemma bound {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d : Gate m} {x y i u v}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    {Y : ℕ → Bool} (yd : Y (w d)=true) (val : Values a b A Y)
    (proof : Parse a b A x y i u v) :
    (Above a b A i (fun _ => False) → u+v=1) ∧
    (Above a b A i (fun k => k=d) → u+v ≤ 2 ∧ (Y i=false → u+v=1)) ∧
    (Y i=false → u+v ≤ 3) := by
  induction proof with
  | xleaf => simp
  | yleaf => simp
  | @join j op u v s t pr1 pr2 ih1 ih2 =>
    have oa : Above a b A (a j) (fun k => k=d) := fun k ak f => one k j ak op (.inl f)
    have ob : Above a b A (b j) (fun k => k=d) := fun k ak f => one k j ak op (.inr f)
    obtain ⟨small1,short1⟩ := ih1.2.1 oa
    obtain ⟨small2,short2⟩ := ih2.2.1 ob
    refine ⟨fun empty => (empty j op .here).elim,?_,?_⟩
    · intro only
      have eq : j=d := only j op .here
      have e1 : u+v=1 := ih1.1 (fun k ak f => by
        have same := (oa k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (ha j)) le)
      have e2 : s+t=1 := ih2.1 (fun k ak f => by
        have same := (ob k ak f).trans eq.symm
        have le := feed_le ha hb f
        rw [same] at le
        exact (Nat.not_le_of_lt (hb j)) le)
      refine ⟨by omega,?_⟩
      intro h
      rw [eq,yd] at h
      contradiction
    · intro no
      rw [(val j).1 op,Bool.and_eq_false_iff] at no
      rcases no with h | h
      · have := short1 h; omega
      · have := short2 h; omega
  | left j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (a j) S :=
      fun k ak f => all k ak (.left j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).1
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩
  | right j op pr ih =>
    have pull (S : Gate m → Prop) (all : Above a b A (w j) S) : Above a b A (b j) S :=
      fun k ak f => all k ak (.right j f)
    have back (no : Y (w j)=false) := (Bool.or_eq_false_iff.mp (((val j).2 op).symm.trans no)).2
    exact ⟨fun e => ih.1 (pull _ e), fun e => ⟨(ih.2.1 (pull _ e)).1,
      fun n => (ih.2.1 (pull _ e)).2 (back n)⟩,fun n => ih.2.2 (back n)⟩

lemma parse_of_value {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j)
    (D : ℕ → Bool) (ops : Values a b A D)
    (raw : ∀ i<26,D i=true → i=x ∨ i=y) :
    ∀ i, i<26+m → D i=true → ∃ u v, Parse a b A x y i u v := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi on
    by_cases small : i<26
    · rcases raw i small on with rfl | rfl
      · exact ⟨1,0,.xleaf⟩
      · exact ⟨0,1,.yleaf⟩
    let j : Gate m := ⟨i-26,by omega⟩
    have eq : i=w j := by dsimp [w,j]; omega
    have pa := ih (a j) ((ha j).trans_le eq.symm.le) (by have := ha j; omega)
    have pb := ih (b j) ((hb j).trans_le eq.symm.le) (by have := hb j; omega)
    rw [eq] at on ⊢
    by_cases op : A j
    · obtain ⟨va,vb⟩ := Bool.and_eq_true_iff.mp (((ops j).1 op).symm.trans on)
      obtain ⟨u,v,pu⟩ := pa va
      obtain ⟨s,t,pv⟩ := pb vb
      exact ⟨_,_,.join j op pu pv⟩
    · rcases Bool.or_eq_true_iff.mp (((ops j).2 op).symm.trans on) with va | vb
      · obtain ⟨u,v,pu⟩ := pa va
        exact ⟨_,_,.left j op pu⟩
      · obtain ⟨s,t,pv⟩ := pb vb
        exact ⟨_,_,.right j op pv⟩

def Trace {m} (a b : Gate m → ℕ) (A : Gate m → Prop) (X M : ℕ → Bool) :=
  ∀ j, (A j → M (w j) = (X (a j) && M (b j) || M (a j) && X (b j))) ∧
       (¬A j → M (w j) = (M (a j) || M (b j)))

lemma counts {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {x y i u v}
    {X Y L P : ℕ → Bool} (vx : Values a b A X) (vy : Values a b A Y)
    (tl : Trace a b A X L) (tp : Trace a b A Y P)
    (xx : X x=true) (yy : Y y=true) (lx : P x=true) (ly : L y=true)
    (proof : Parse a b A x y i u v) :
    (u=0 → Y i=true) ∧ (u=1 → P i=true) ∧ (v=0 → X i=true) ∧ (v=1 → L i=true) := by
  induction proof with
  | xleaf => simp [xx,lx]
  | yleaf => simp [yy,ly]
  | @join j op u v s t _ _ qa qb =>
    obtain ⟨py,pm,px,pn⟩ := qa
    obtain ⟨qy,qm,qx,qn⟩ := qb
    refine ⟨?_,?_,?_,?_⟩
    · intro e
      simp [(vy j).1 op,py (by omega),qy (by omega)]
    · intro e
      rw [(tp j).1 op]
      have alt : (u=0 ∧ s=1) ∨ (u=1 ∧ s=0) := by omega
      rcases alt with ⟨aa,bb⟩ | ⟨aa,bb⟩ <;> simp_all
    · intro e
      simp [(vx j).1 op,px (by omega),qx (by omega)]
    · intro e
      rw [(tl j).1 op]
      have alt : (v=0 ∧ t=1) ∨ (v=1 ∧ t=0) := by omega
      rcases alt with ⟨aa,bb⟩ | ⟨aa,bb⟩ <;> simp_all
  | left j op _ ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    exact ⟨fun e => by simp [(vy j).2 op,h0 e], fun e => by simp [(tp j).2 op,h1 e],
      fun e => by simp [(vx j).2 op,h2 e], fun e => by simp [(tl j).2 op,h3 e]⟩
  | right j op _ ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    exact ⟨fun e => by simp [(vy j).2 op,h0 e], fun e => by simp [(tp j).2 op,h1 e],
      fun e => by simp [(vx j).2 op,h2 e], fun e => by simp [(tl j).2 op,h3 e]⟩

theorem single_source {m} {a b : Gate m → ℕ} {A : Gate m → Prop} {d k : Gate m} {o x y : ℕ}
    (ha : ∀ j,a j<w j) (hb : ∀ j,b j<w j) (one : SourceOnly a b A d)
    (ak : A k) (live : Live a b o (w k)) {B X Y Z L P : ℕ → Bool}
    (vb : Values a b A B) (vx : Values a b A X) (vy : Values a b A Y)
    (vz : Values a b A Z) (tl : Trace a b A X L) (tp : Trace a b A Y P)
    (hout : o<26+m) (raw : ∀ i<26,B i=true → i=x ∨ i=y)
    (bp : B o=true) (nx : X o=false) (ny : Y o=false)
    (xx : X x=true) (yy : Y y=true) (lx : P x=true) (ly : L y=true)
    (zk : Z (w k)=true) (zo : Z o=false) : L o=true ∨ P o=true := by
  obtain ⟨u,v,pt⟩ := parse_of_value ha hb B vb raw o hout bp
  have small := (bound ha hb one (source_dirty one ak live Z vz zk zo) vz pt).2.2 zo
  obtain ⟨u0,u1,v0,v1⟩ := counts vx vy tl tp xx yy lx ly pt
  have hu : u≠0 := by intro h; have := u0 h; simp_all
  have hv : v≠0 := by intro h; have := v0 h; simp_all
  by_cases e : u=1
  · exact Or.inr (u1 e)
  · exact Or.inl (v1 (by omega))

end Source2071

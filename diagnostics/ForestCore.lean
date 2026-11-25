import Mathlib
import PEqualNP.Outside.L_meta_1003
import PEqualNP.Outside.L_meta_1485

namespace Forest3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1003_aux.H926
open PEqualNP.Outside.L_meta_1485 (gateAt_eq)

abbrev V (n : Nat) := Fin n → Bool

def raw (n : Nat) (w : List Bool) : V n := fun i => w.getD i.val false

def bit (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def Safe (F : Prop) (w : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2 ∧ (∀ u∈g.inputs, u<w.length) ∧
      (g.op=.and → bit g w=true → F)) ∧ Safe F (w++[bit g w]) gs

theorem append_safe (F : Prop) (w : List Bool) (s t : List Gate) (hs : Safe F w s)
    (ht : Safe F (wiresFrom s w) t) : Safe F w (s++t) := by
  induction s generalizing w with
  | nil => exact ht
  | cons g gs ih => exact ⟨hs.1, ih _ hs.2 ht⟩

theorem spec (F : Prop) (w : List Bool) (gs : List Gate) (safe : Safe F w gs)
    (j : Nat) (hj : j<gs.length) :
    (gs[j].op=.and ∨ gs[j].op=.or) ∧ gs[j].inputs.length≤2 ∧
    (∀ u∈gs[j].inputs, u<w.length+j) ∧
    (gs[j].op=.and → (wiresFrom gs w).getD (w.length+j) false=true → F) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have ⟨⟨op,len,back,hit⟩,_⟩ := safe
      refine ⟨op,len,by simpa using back,?_⟩
      intro hand h
      apply hit hand
      change (wiresFrom gs (w++[bit g w])).getD (w.length+0) false = true at h
      rw [Nat.add_zero,getD_wiresFrom _ _ _ (by simp),getD_snoc_eq] at h
      exact h
    | succ j =>
      have h := ih (w++[bit g w]) safe.2 j (by simpa using hj)
      have idx : (w++[bit g w]).length+j=w.length+(j+1) := by simp; omega
      rw [idx] at h
      exact h

def Build {n : Nat} (target : V n → Prop) (f : V n → Bool) (s : Nat) : Prop :=
  ∀ m, n≤m → ∃ (gs : List Gate) (o : Nat), gs.length ≤ s ∧ o<m+gs.length ∧
    ∀ w : List Bool, w.length=m →
      (wiresFrom gs w).getD o false=f (raw n w) ∧ Safe (target (raw n w)) w gs

variable {n : Nat} {T : V n → Prop}

theorem bld_mono {F : V n → Bool} {s t} (h : Build T F s) (leq : s≤t) : Build T F t := by
  intro m hm
  obtain ⟨gs,o,len,lt,ok⟩ := h m hm
  exact ⟨gs,o,len.trans leq,lt,ok⟩

theorem bld_congr {F H : V n → Bool} {s} (h : Build T F s) (eq : ∀ x, F x=H x) :
    Build T H s := by
  have : F=H := funext eq
  rwa [← this]

theorem bld_var (i : Fin n) : Build T (fun x => x i) 0 := by
  intro m hm
  exact ⟨[],i.val,le_rfl,by simp; omega,fun _ _ => ⟨rfl,True.intro⟩⟩

theorem bld_bin (op : GateOp) (hop : op=.and ∨ op=.or) (c : Bool → Bool → Bool)
    (hc : ∀ a b, op.eval [a,b]=c a b)
    {F H : V n → Bool} {s1 s2 : Nat} (h1 : Build T F s1) (h2 : Build T H s2)
    (safe : op=.and → ∀ x, c (F x) (H x)=true → T x) :
    Build T (fun x => c (F x) (H x)) (s1+s2+1) := by
  intro m hm
  obtain ⟨gs1,o1,len1,ho1,ev1⟩ := h1 m hm
  obtain ⟨gs2,o2,len2,ho2,ev2⟩ := h2 (m+gs1.length) (by omega)
  let g : Gate := ⟨op,[o1,o2]⟩
  refine ⟨gs1++gs2++[g],m+gs1.length+gs2.length,by simp; omega,by simp; omega,?_⟩
  intro w hw
  let v := wiresFrom gs1 w
  let u := wiresFrom gs2 v
  have lv : v.length=m+gs1.length := by simp [v,length_wiresFrom,hw]
  have lu : u.length=m+gs1.length+gs2.length := by simp [u,length_wiresFrom,lv]
  have rv : raw n v=raw n w := by
    funext i
    exact getD_wiresFrom _ _ _ (by omega)
  have e1 : u.getD o1 false=F (raw n w) :=
    (getD_wiresFrom _ _ _ (by omega)).trans (ev1 w hw).1
  have e2 : u.getD o2 false=H (raw n w) := (ev2 v lv).1.trans (congrArg H rv)
  have output : bit g u=c (F (raw n w)) (H (raw n w)) := by
    change op.eval [u.getD o1 false,u.getD o2 false]=_
    rw [hc,e1,e2]
  constructor
  · rw [wiresFrom_append,wiresFrom_append]
    change (u++[bit g u]).getD (m+gs1.length+gs2.length) false=_
    rw [←lu,getD_snoc_eq,output]
  · apply append_safe
    · exact append_safe _ _ _ _ (ev1 w hw).2 (rv ▸ (ev2 v lv).2)
    · rw [wiresFrom_append]
      change Safe (T (raw n w)) u [g]
      refine ⟨⟨hop,by decide,?_,?_⟩,True.intro⟩
      · intro y hy
        rcases (show y=o1 ∨ y=o2 by simpa [g] using hy) with rfl | rfl <;> omega
      · intro hand up
        exact safe hand _ (output ▸ up)

theorem bld_or {F H : V n → Bool} {s1 s2} (a : Build T F s1) (b : Build T H s2) :
    Build T (fun x => F x || H x) (s1+s2+1) :=
  bld_bin .or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) a b (by intro h; cases h)

theorem bld_and {F H : V n → Bool} {s1 s2} (a : Build T F s1) (b : Build T H s2)
    (safe : ∀ x, F x=true → H x=true → T x) : Build T (fun x => F x && H x) (s1+s2+1) :=
  bld_bin .and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) a b
    (fun _ x h => safe x (Bool.and_eq_true_iff.mp h).1 (Bool.and_eq_true_iff.mp h).2)

theorem realize {F : V n → Bool} {k : Nat} (h : Build T F k) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size≤k ∧ (∀ x, circuitFun n D x=F x) ∧
      ∀ j<D.gates.length, (gateAt D j).op=.and → ∀ x : V n,
        (D.wires (List.ofFn x)).getD (n+j) false=true → T x := by
  obtain ⟨gs,o,len,_,ok⟩ := h n le_rfl
  let D : Circuit := ⟨gs,o⟩
  have rr (x : V n) : raw n (List.ofFn x)=x := by
    funext i
    exact getD_ofFn x i
  have ss (x : V n) (j) (hj : j<gs.length) := spec _ _ _ (ok (List.ofFn x) (by simp)).2 j hj
  refine ⟨D,?_,?_,len,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    have p := ss (fun _ => false) j hj
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using p.1,p.2.1⟩
  · intro j hj u hu
    rw [gateAt_eq hj] at hu
    simpa using (ss (fun _ => false) j hj).2.2.1 u hu
  · intro x
    exact (ok (List.ofFn x) (by simp)).1.trans (congrArg F (rr x))
  · intro j hj hand x up
    rw [gateAt_eq hj] at hand
    have hh := (ss x j hj).2.2.2 hand (by simpa only [List.length_ofFn] using up)
    rwa [rr x] at hh

end Forest3321

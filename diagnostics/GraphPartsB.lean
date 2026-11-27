import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Pair7808
namespace Builder
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

theorem appendTerm {n s k : ℕ} {f t : (Fin n → Bool) → Bool} (c : HasCircuitSize n f s) (term : Bld n t k) :
    HasCircuitSize n (fun x => f x || t x) (s+k+1) := by
  obtain ⟨C,fan,cheap,correct⟩ := c
  let m := n+C.gates.length
  obtain ⟨gs,wout,ok,budget,range,computes⟩ := term m (by dsimp [m]; omega)
  let old := if C.output<m then C.output else m+gs.length+1
  let D : Circuit := ⟨C.gates++gs++[⟨.or,[old,wout]⟩],m+gs.length⟩
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    change g ∈ C.gates++gs++[_] at hg
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact fan _ h
      · exact ok _ h
    · obtain rfl := List.mem_singleton.mp h
      simp
  · change (C.gates++gs++[_]).length ≤ s+k+1
    change C.gates.length ≤ s at cheap
    simp
    omega
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    let finalW := wiresFrom gs w
    have lengthW : w.length=m := by simp [w,m,length_wiresFrom]
    have lengthFinal : finalW.length=m+gs.length := by simp [finalW,length_wiresFrom,lengthW]
    have first : finalW.getD old false = f x := by
      have eq : w.getD C.output false = f x := correct x
      rw [← eq]
      by_cases existsWire : C.output < m
      · change (wiresFrom gs w).getD old false = _
        rw [show old=C.output by simp [old,existsWire],getD_wiresFrom _ _ _ (by omega)]
      · rw [show old=m+gs.length+1 by simp [old,existsWire]]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
    have same : (fun i : Fin n => w.getD i.val false)=x := by
      funext i
      change (wiresFrom C.gates (List.ofFn x)).getD i.val false = _
      rw [getD_wiresFrom _ _ _ (by simp),getD_ofFn]
    have second : finalW.getD wout false = t x := (computes w lengthW).trans (congrArg t same)
    change (wiresFrom (C.gates++gs++[_]) (List.ofFn x)).getD (m+gs.length) false = _
    rw [wiresFrom_append,wiresFrom_append]
    change (finalW++[GateOp.or.eval [finalW.getD old false,finalW.getD wout false]]).getD (m+gs.length) false = _
    rw [← lengthFinal,getD_snoc_eq,first,second]
    simp [GateOp.eval]


open PEqualNP.MetaComplexity.NestedCover
variable {n : Nat}
def zeroPair (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

lemma true_zero (x:Fin n→Bool) (u v i:Fin n) :
    zeroPair u v x i=true ↔ i≠u ∧ i≠v ∧ x i=true := by
  by_cases h:i=v
  · subst i; simp [zeroPair]
  · by_cases q:i=u
    · subst i; simp [zeroPair,h]
    · simp [zeroPair,h,q]

def hit (S:Finset (Fin n)) (x:Fin n→Bool) := decide (∃i∈S,x i=true)
def term (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :=
  (x u && hit (G.neighborFinset u) x) || (x v && hit ((G.neighborFinset v).erase u) x)

lemma termCost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (edge:G.Adj u v)
    (uc:(G.neighborFinset u).card=3) (vc:(G.neighborFinset v).card=3) :
    Bld n (term G u v) 6 := by
  have mem : u∈G.neighborFinset v := (G.mem_neighborFinset _ _).mpr edge.symm
  have er : ((G.neighborFinset v).erase u).card=2 := by rw [Finset.card_erase_of_mem mem,vc]
  have a := bld_anyFinset (G.neighborFinset u) (Finset.card_pos.mp (by omega))
  have b := bld_anyFinset ((G.neighborFinset v).erase u) (Finset.card_pos.mp (by omega))
  have t := bld_or (bld_and (bld_var u) a) (bld_and (bld_var v) b)
  rwa [uc,er] at t

lemma termOff (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n) (x:Fin n→Bool) :
    term G u v (zeroPair u v x)=false := by
  have a := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v u).mp h).1 rfl)
  have b := Bool.eq_false_iff.mpr (fun h => ((true_zero x u v v).mp h).2.1 rfl)
  simp [term,a,b]

lemma splitGraph (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (u v:Fin n) (ha:u∉A) (hb:v∉A) (x:Fin n→Bool) :
    (graphFun G A (zeroPair u v x) || term G u v x) = graphFun G A x := by
  have spec (y:Fin n→Bool) : graphFun G A y=true ↔ (∃a∈A,y a=true) ∨ ∃a b,G.Adj a b ∧ y a=true ∧ y b=true := by
    simp [graphFun]
  have le (i:Fin n) (h:zeroPair u v x i=true) := ((true_zero x u v i).mp h).2.2
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,spec,term,hit,decide_eq_true_eq]
  constructor
  · rintro (h|h)
    · rcases h with ⟨a,aa,xa⟩ | ⟨a,b,ab,xa,xb⟩
      · exact Or.inl ⟨a,aa,le a xa⟩
      · exact Or.inr ⟨a,b,ab,le a xa,le b xb⟩
    · rcases h with ⟨xu,j,hj,xj⟩|⟨xv,j,hj,xj⟩
      · exact Or.inr ⟨u,j,(G.mem_neighborFinset _ _).mp hj,xu,xj⟩
      · exact Or.inr ⟨v,j,(G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hj).2,xv,xj⟩
  · rintro (⟨a,aa,xa⟩|⟨a,b,ab,xa,xb⟩)
    · exact Or.inl (Or.inl ⟨a,aa,(true_zero _ _ _ _).mpr ⟨fun e=>ha (e ▸ aa),fun e=>hb (e ▸ aa),xa⟩⟩)
    · by_cases au:a=u
      · subst a
        exact Or.inr (Or.inl ⟨xa,b,(G.mem_neighborFinset _ _).mpr ab,xb⟩)
      by_cases bu:b=u
      · subst b
        exact Or.inr (Or.inl ⟨xb,a,(G.mem_neighborFinset _ _).mpr ab.symm,xa⟩)
      by_cases av:a=v
      · subst a
        exact Or.inr (Or.inr ⟨xa,b,Finset.mem_erase.mpr ⟨bu,(G.mem_neighborFinset _ _).mpr ab⟩,xb⟩)
      by_cases bv:b=v
      · subst b
        exact Or.inr (Or.inr ⟨xb,a,Finset.mem_erase.mpr ⟨au,(G.mem_neighborFinset _ _).mpr ab.symm⟩,xa⟩)
      exact Or.inl (Or.inr ⟨a,b,ab,(true_zero _ _ _ _).mpr ⟨au,av,xa⟩,
        (true_zero _ _ _ _).mpr ⟨bu,bv,xb⟩⟩)

lemma neighbors_cost (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (A:Finset (Fin n))
    (rule:∀i,(G.neighborSet i).ncard=if i∈A then 0 else 3) (u v:Fin n) (edge:G.Adj u v) :
    u∉A ∧ (G.neighborFinset u).card=3 := by
  have h := rule u
  have eq : (G.neighborSet u).ncard=(G.neighborFinset u).card := by
    have he : G.neighborSet u=(↑(G.neighborFinset u):Set (Fin n)) := by
      ext i
      exact (G.mem_neighborFinset u i).symm
    rw [he, Set.ncard_coe_finset]
  rw [eq] at h
  have pos := Finset.card_pos.mpr (show (G.neighborFinset u).Nonempty from ⟨v,(G.mem_neighborFinset _ _).mpr edge⟩)
  by_cases hu:u∈A
  · rw [if_pos hu] at h
    omega
  · simpa [hu] using And.intro hu h

end Builder
end Pair7808

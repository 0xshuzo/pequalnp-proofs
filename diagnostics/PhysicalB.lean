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


def addr (B i : Nat) := if i<B then i else B+7
def sealGate (B : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (addr B)⟩
def sealed (n:Nat) (D:Circuit) : Circuit :=
  let B := n+D.size
  ⟨D.gates.map (sealGate B), addr B D.output⟩
lemma addr_get (B:Nat) (w:List Bool) (lim:w.length≤B) (i:Nat) :
    w.getD (addr B i) false = w.getD i false := by
  by_cases hi:i<B
  · simp [addr,hi]
  · rw [addr,if_neg hi,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
lemma seal_run (B:Nat) (gs:List Gate) (w:List Bool) (lim:w.length+gs.length≤B) :
    wiresFrom (gs.map (sealGate B)) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map (fun i => w.getD i false))
    have eq : (sealGate B g).op.eval ((sealGate B g).inputs.map (fun i => w.getD i false)) = val := by
      change g.op.eval ((g.inputs.map (addr B)).map _) = _
      rw [List.map_map]
      have e : (fun i => (fun j => w.getD j false) (addr B i)) = (fun i => w.getD i false) := by
        funext i; exact addr_get B w (by omega) i
      change g.op.eval (g.inputs.map (fun i => w.getD (addr B i) false)) = val
      rw [e]
    change wiresFrom (gs.map (sealGate B)) (w++[_]) = wiresFrom gs (w++[_])
    rw [eq]
    apply ih
    simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *
    omega
lemma seal_size (n:Nat) (D:Circuit) : (sealed n D).size = D.size := by simp [sealed,Circuit.size]
lemma seal_fan (n:Nat) (D:Circuit) (fan:FanInTwo D) : FanInTwo (sealed n D) := by
  intro g h
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
  simpa [sealGate] using fan z hz
lemma seal_eval (n:Nat) (D:Circuit) : circuitFun n (sealed n D) = circuitFun n D := by
  funext x
  change (wiresFrom (D.gates.map (sealGate (n+D.size))) (List.ofFn x)).getD (addr (n+D.size) D.output) false = _
  rw [seal_run _ _ _ (by simp [Circuit.size]),addr_get _ _ (by simp [length_wiresFrom,Circuit.size])]
  rfl
lemma seal_no (n:Nat) (D:Circuit) (g:Gate) (hg:g∈(sealed n D).gates) (w:Nat)
    (lo:n+D.size≤w) (hi:w<n+D.size+7) : w∉g.inputs := by
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hg
  intro h
  obtain ⟨i,_,e⟩ := List.mem_map.mp h
  change addr (n+D.size) i=w at e
  unfold addr at e
  split at e <;> omega

open PEqualNP.MetaComplexity.NestedCover
def zero₂ {n:Nat} (u v:Fin n) (x:Fin n→Bool) := Function.update (Function.update x u false) v false

def marked {n:Nat} (u v:Fin n) (F:Circuit) : Prop :=
  ∃H:Finset Nat, 7≤H.card ∧ ∀ k∈H, k<F.size ∧
    ((∃w:Nat, (w<n+k ∧ (w<n ∨ w-n∉H) ∨ n+F.size≤w) ∧
       ∀ x:Fin n→Bool, let W := F.wires (List.ofFn (zero₂ u v x))
                         W.getD (n+k) false=W.getD w false) ∨
     F.output≠n+k ∧ readsIn F (Finset.range F.size \ H) (n+k)=0)

lemma read_safe (gs : List Gate) (w : List Bool) (i:Nat)
    (hi:i<w.length ∨ w.length+gs.length≤i) : (wiresFrom gs w).getD i false=w.getD i false := by
  rcases hi with h|h
  · exact getD_wiresFrom _ _ _ h
  · rw [List.getD_eq_default _ _ (by rw [length_wiresFrom];omega),List.getD_eq_default _ _ (by omega)]

theorem appendMarked {n:Nat} (u v:Fin n) (t:(Fin n→Bool)→Bool) (D:Circuit) (fan:FanInTwo D)
    (term:Bld n t 6) (off:∀x,t (zero₂ u v x)=false) :
    ∃F:Circuit, FanInTwo F ∧ F.size=D.size+7 ∧
      circuitFun n F=(fun x=>circuitFun n D x || t x) ∧ marked u v F := by
  let m := n+D.size
  let E := sealed n D
  have Le : E.gates.length=D.size := seal_size n D
  have old : E.output<m ∨ E.output=m+7 := by
    change addr m D.output < m ∨ addr m D.output=m+7
    unfold addr; split <;> omega
  obtain ⟨gs,o,ok,len,range,run⟩ := term m (by dsimp [m];omega)
  let pad : List Gate := List.replicate (6-gs.length) ⟨.or,[]⟩
  let Q := gs++pad
  have qlen : Q.length=6 := by simp [Q,pad];omega
  let last : Gate := ⟨.or,[E.output,o]⟩
  let F : Circuit := ⟨E.gates++Q++[last],m+6⟩
  have sz : F.size=D.size+7 := by simp [F,Circuit.size,Le,qlen];omega
  have okF : FanInTwo F := by
    intro g hg
    change g∈E.gates++Q++[last] at hg
    rcases List.mem_append.mp hg with h|h
    · rcases List.mem_append.mp h with h|h
      · exact seal_fan n D fan g h
      · rcases List.mem_append.mp h with h|h
        · exact ok g h
        · obtain rfl := List.eq_of_mem_replicate h
          simp
    · obtain rfl := List.mem_singleton.mp h
      simp [last]
  have data (x:Fin n→Bool) :
      F.eval (List.ofFn x)=(circuitFun n D x || t x) ∧
      (F.wires (List.ofFn x)).getD E.output false=circuitFun n D x := by
    let w := wiresFrom E.gates (List.ofFn x)
    let z := wiresFrom Q w
    have lw:w.length=m := by simp [w,length_wiresFrom,Le,m]
    have lz:z.length=m+6 := by simp [z,length_wiresFrom,lw,qlen]
    have ed : w.getD E.output false = circuitFun n D x := congrFun (seal_eval n D) x
    have zo : z.getD E.output false=circuitFun n D x := by
      rw [←ed]
      apply read_safe
      rw [lw,qlen]
      omega
    have xeq : (fun i:Fin n=>w.getD i.val false) = x := by
      funext i
      exact (getD_wiresFrom E.gates (List.ofFn x) i.val (by simp)).trans (by simp)
    have loc : z.getD o false=t x := by
      change (wiresFrom (gs++pad) w).getD o false=_
      rw [wiresFrom_append,getD_wiresFrom _ _ _ (by rw [length_wiresFrom,lw];omega),run w lw,xeq]
    have final : F.wires (List.ofFn x)= z ++ [z.getD E.output false || z.getD o false] := by
      change wiresFrom (E.gates++Q++[last]) (List.ofFn x)=_
      rw [wiresFrom_append,wiresFrom_append]
      simp [last,wiresFrom,GateOp.eval,z,w]
    constructor
    · change (F.wires (List.ofFn x)).getD (m+6) false=_
      rw [final,←lz,getD_snoc_eq,zo,loc]
    · rw [final,←zo]
      rcases old with h|h
      · exact List.getD_append _ _ _ _ (by omega)
      · rw [List.getD_eq_default _ _ (by simp [lz];omega),List.getD_eq_default _ _ (by omega)]
  refine ⟨F,okF,sz,funext (fun x=>(data x).1),?_⟩
  let H := Finset.Ico D.size (D.size+7)
  have hcard : H.card=7 := by simp [H]
  have remain : Finset.range F.size \ H = Finset.range D.size := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_range,H,Finset.mem_Ico,sz]
    omega
  refine ⟨H,hcard.ge,?_⟩
  intro k hk
  obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hk
  refine ⟨by omega,?_⟩
  by_cases ke : k=D.size+6
  · left
    refine ⟨E.output,?_,?_⟩
    · rcases old with h|h
      · left
        refine ⟨by dsimp [m] at h;omega,?_⟩
        by_cases low : E.output<n
        · exact Or.inl low
        · right
          intro mem
          have := (Finset.mem_Ico.mp mem).1
          dsimp [m] at h
          omega
      · right
        dsimp [m] at h
        omega
    · intro x
      have val := data (zero₂ u v x)
      have eq : n+k=F.output := by change n+k=m+6;dsimp [m];omega
      change (F.wires _).getD (n+k) false = (F.wires _).getD E.output false
      rw [eq,val.2]
      change F.eval _=_
      rw [val.1,off,Bool.or_false]
  · right
    refine ⟨by change m+6≠n+k;dsimp [m];omega,?_⟩
    rw [remain]
    unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    have jlt : j<E.gates.length := by rw [Le];exact Finset.mem_range.mp hj
    have hget : gateAt F j=E.gates[j] := by
      unfold gateAt
      change (E.gates++Q++[last]).getD j _=_
      rw [List.getD_append _ _ _ _ (by simp;omega),List.getD_append _ _ _ _ jlt]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem jlt]
    rw [hget,List.count_eq_zero]
    apply seal_no n D E.gates[j] (List.getElem_mem _)
    all_goals omega

end Builder
end Pair7808

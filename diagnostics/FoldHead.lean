import PEqualNP.Outside.L_meta_2880

namespace Fold1739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2880

def wire {n m : ℕ} (σ : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w<n then (σ ⟨w,h⟩).val else m+(w-n)
def gate {n m : ℕ} (σ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (wire σ)⟩
def circ {n m : ℕ} (σ : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate σ),wire σ C.output⟩

theorem below {n m} (σ : Fin n → Fin m) (k i : ℕ) (hi : i<n+k) :
    wire σ i < m+k := by
  unfold wire
  split
  next hw => have := (σ ⟨i,hw⟩).isLt; omega
  next => omega

theorem keep {n m} (σ : Fin n → Fin m) (gs : List Gate) (W V : List Bool) (k : ℕ)
    (hw : W.length=m+k) (hv : V.length=n+k)
    (sync : ∀ i, W.getD (wire σ i) false=V.getD i false) :
    ∀ i, (wf (gs.map (gate σ)) W).getD (wire σ i) false=(wf gs V).getD i false := by
  induction gs generalizing W V k with
  | nil => exact sync
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => V.getD i false)
    have same : (gate σ g).op.eval ((gate σ g).inputs.map fun i => W.getD i false)=b := by
      change g.op.eval ((g.inputs.map (wire σ)).map _) = g.op.eval _
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun i _ => sync i
    intro w
    simp only [List.map_cons,wf,List.foldl_cons]
    rw [same]
    apply ih (W++[b]) (V++[b]) (k+1) (by simp;omega) (by simp;omega) _ w
    intro i
    rcases Nat.lt_trichotomy i V.length with lt|atEnd|gt
    · rw [getD_snoc_lt W b _ (by rw [hw]; apply below;omega),getD_snoc_lt V b _ lt]
      exact sync i
    · have he : wire σ i = W.length := by
        have hnot : ¬i<n := by omega
        rw [wire,dif_neg hnot];omega
      rw [he,atEnd,getD_snoc_eq,getD_snoc_eq]
    · have he : W.length < wire σ i := by
        have hnot : ¬i<n := by omega
        rw [wire,dif_neg hnot];omega
      rw [getD_snoc_gt W b _ he,getD_snoc_gt V b _ gt]

theorem eval {n m} (σ : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (circ σ C).eval (List.ofFn x)=C.eval (List.ofFn (x ∘ σ)) := by
  apply keep σ C.gates _ _ 0 (by simp) (by simp)
  intro i
  by_cases hi : i<n
  · simp [wire,hi,List.getD_eq_getElem?_getD,(σ ⟨i,hi⟩).isLt,Function.comp]
  · have he : m ≤ wire σ i := by rw [wire,dif_neg hi];omega
    rw [List.getD_eq_default _ _ (by simp;omega), List.getD_eq_default _ _ (by simp;omega)]

theorem legal {n m} (σ : Fin n → Fin m) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (circ σ C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [gate] using hm a ha

def Computes {n} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true

theorem transport {n m} (σ : Fin n → Fin m) {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (image : ∀ a b, H.Adj a b ↔ ∃ p q, G.Adj p q ∧ σ p=a ∧ σ q=b)
    {C : Circuit} (ok : Computes G C) : Computes H (circ σ C) := by
  intro x
  rw [eval, ok]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨σ a, σ b, (image _ _).mpr ⟨a,b,hab,rfl,rfl⟩, ha,hb⟩
  · rintro ⟨a,b,hab,ha,hb⟩
    obtain ⟨p,q,hpq,rfl,rfl⟩ := (image _ _).mp hab
    exact ⟨p,q,hpq,ha,hb⟩

theorem price {n m k} (σ : Fin n → Fin m) {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (image : ∀ a b, H.Adj a b ↔ ∃ p q, G.Adj p q ∧ σ p=a ∧ σ q=b)
    (lower : ∀ D : Circuit, Monotone2 D → Computes H D → k ≤ D.size + 1)
    (C : Circuit) (hm : Monotone2 C) (ok : Computes G C) : k ≤ C.size+1 := by
  simpa [circ,Circuit.size] using lower (circ σ C) (legal σ C hm) (transport σ image ok)


theorem paidHead {n m} (σ : Fin n → Fin m) (a b : Fin n) (eq : σ a=σ b)
    (op : GateOp) (hop : op=.and ∨ op=.or) (tail : List Gate) (out : ℕ)
    (hM : Monotone2 (⟨⟨op,[a.val,b.val]⟩ :: tail,out⟩ : Circuit)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size=tail.length ∧ ∀ x : Fin m → Bool,
      D.eval (List.ofFn x) = (⟨⟨op,[a.val,b.val]⟩ :: tail,out⟩ : Circuit).eval (List.ofFn (x∘σ)) := by
  let fp : Fin (n+1) → Fin m := Fin.lastCases (σ a) σ
  let T : Circuit := ⟨tail,out⟩
  have hmT : Monotone2 T := fun g hg => hM g (List.mem_cons_of_mem _ hg)
  refine ⟨circ fp T, legal fp T hmT, by simp [circ,T,Circuit.size], ?_⟩
  intro x
  rw [eval]
  have inputs : List.ofFn (x ∘ fp) = List.ofFn (x ∘ σ) ++ [x (σ a)] := by
    rw [List.ofFn_succ']
    simp [fp,Function.comp] <;> rfl
  rw [inputs]
  let ys := List.ofFn (x ∘ σ)
  have atA : ys.getD a.val false = x (σ a) := by simp [ys,List.getD_eq_getElem?_getD]
  have atB : ys.getD b.val false = x (σ a) := by simp [ys,List.getD_eq_getElem?_getD,eq]
  have pe : op.eval [ys.getD a.val false, ys.getD b.val false]=x (σ a) := by
    rw [atA,atB]
    rcases hop with rfl|rfl <;> cases x (σ a) <;> rfl
  change (wf tail (ys++[x (σ a)])).getD out false =
    (wf tail (ys++[op.eval [ys.getD a.val false, ys.getD b.val false]])).getD out false
  rw [pe]

end Fold1739

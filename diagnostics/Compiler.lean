import PEqualNP.Defs
namespace Compile18726
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, (by simp [Fan]), (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, (by simp [Fan]), (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

abbrev Input (n : Nat) := Fin n → Bool
abbrev Fun (n : Nat) := Input n → Bool
def Constant {n : Nat} (f : Fun n) := ∃c,∀x,f x=c

theorem rep_not {n : Nat} (new : List Gate) (f : Fun n) (h : Rep new f) :
    ∃new',Ext n new new' ∧ Rep new' (fun x => !(f x)) := by
  rcases h with ⟨c,h⟩|⟨j,hj,e⟩
  · exact ⟨new,Or.inl rfl,Or.inl ⟨!c,fun x => by rw [h x]⟩⟩
  · refine ⟨new++[⟨.not,[j]⟩],Or.inr ⟨_,rfl,by simp [Fan],by simpa using hj⟩,Or.inr ⟨n+new.length,by simp,?_⟩⟩
    intro x
    rw [W_val,if_pos rfl]
    simp [GateOp.eval,e x]

def semantic {n : Nat} (g : Gate) (src : Nat → Fun n) : Fun n :=
  fun x => g.op.eval (g.inputs.map fun w => src w x)
theorem applyGate {n : Nat} (new : List Gate) (g : Gate) (s : Nat → Fun n)
    (ok : Fan g) (nt : g.op=.not → g.inputs.length=1) (h : ∀w∈g.inputs, Rep new (s w)) :
    ∃new',Ext n new new' ∧ Rep new' (semantic g s) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨opok,small⟩ := ok
  change op=.and ∨ op=.or ∨ op=.not at opok
  change ins.length≤2 at small
  change ∀w∈ins,Rep new (s w) at h
  change op=.not → ins.length=1 at nt
  rcases ins with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩
  · rcases opok with rfl|rfl|rfl
    · exact ⟨new,Or.inl rfl,Or.inl ⟨true,by simp [semantic,GateOp.eval]⟩⟩
    · exact ⟨new,Or.inl rfl,Or.inl ⟨false,by simp [semantic,GateOp.eval]⟩⟩
    · simp at nt
  · rcases opok with rfl|rfl|rfl
    · exact ⟨new,Or.inl rfl,rep_congr (by simp [semantic,GateOp.eval]) (h a (by simp))⟩
    · exact ⟨new,Or.inl rfl,rep_congr (by simp [semantic,GateOp.eval]) (h a (by simp))⟩
    · simpa [semantic,GateOp.eval] using rep_not new _ (h a (by simp))
  · rcases opok with rfl|rfl|rfl
    · simpa [semantic,GateOp.eval] using rep_and new _ _ (h a (by simp)) (h b (by simp))
    · simpa [semantic,GateOp.eval] using rep_or new _ _ (h a (by simp)) (h b (by simp))
    · simp at nt
  · simp at small

def restrictSrc {n : Nat} (bound : Nat) (s : Nat → Fun n) (w : Nat) : Fun n :=
  fun x => if w<bound then s w x else false

theorem constOrEarlier {n : Nat} (bound : Nat) (s : Nat → Fun n) (g : Gate) (ok : Fan g)
    (nt : g.op=.not → g.inputs.length=1) (hc : ∃w∈g.inputs,Constant (s w)) :
    Constant (semantic g (restrictSrc bound s)) ∨
    ∃w∈g.inputs,w<bound ∧ ∀x,semantic g (restrictSrc bound s) x=s w x := by
  let R := restrictSrc bound s
  have forward (w : Nat) (hn : ¬w<bound) : ∀x,R w x=false := by simp [R,restrictSrc,hn]
  have earlier (w : Nat) (h : w<bound) : ∀x,R w x=s w x := by simp [R,restrictSrc,h]
  obtain ⟨a,bnd,ca⟩ := hc
  have con : Constant (R a) := by
    by_cases ha : a<bound
    · obtain ⟨c,hc⟩ := ca
      exact ⟨c,fun x => (earlier a ha x).trans (hc x)⟩
    · exact ⟨false,forward a ha⟩
  have lift (b : Nat) (m : b∈g.inputs) (eq : ∀x,semantic g R x=R b x) :
      Constant (semantic g R) ∨ ∃w∈g.inputs,w<bound ∧ ∀x,semantic g R x=s w x := by
    by_cases hb : b<bound
    · exact Or.inr ⟨b,m,hb,fun x => (eq x).trans (earlier b hb x)⟩
    · exact Or.inl ⟨false,fun x => (eq x).trans (forward b hb x)⟩
  change Constant (semantic g R) ∨ _
  obtain ⟨op,ins⟩ := g
  obtain ⟨opok,len⟩ := ok
  change op=.and ∨ op=.or ∨ op=.not at opok
  change ins.length≤2 at len
  change op=.not → ins.length=1 at nt
  change a∈ins at bnd
  obtain ⟨c,hc⟩ := con
  rcases ins with _|⟨b,_|⟨d,_|⟨z,rest⟩⟩⟩
  · simp at bnd
  · have eq : a=b := by simpa using bnd
    subst b
    rcases opok with rfl|rfl|rfl
    · exact Or.inl ⟨c,by simpa [semantic,GateOp.eval] using hc⟩
    · exact Or.inl ⟨c,by simpa [semantic,GateOp.eval] using hc⟩
    · exact Or.inl ⟨!c,by simp [semantic,GateOp.eval,hc]⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at bnd
    rcases bnd with rfl|rfl <;> rcases opok with rfl|rfl|rfl <;> cases c
    all_goals first
      | exact Or.inl ⟨false, by simp [semantic,GateOp.eval,hc]⟩
      | exact Or.inl ⟨true, by simp [semantic,GateOp.eval,hc]⟩
      | apply lift _ (by simp) (by simp [semantic,GateOp.eval,hc])
      | simp at nt
  · simp at len

def price (pay : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j+1 => price pay j + (if pay j then 1 else 0)
theorem build {n m : Nat} (F : Nat → Fun n) (dead : Nat → Prop) (pay : Nat → Bool)
    (base : ∀w<n,Rep [] (F w))
    (stepOnce : ∀j<m,∀new : List Gate,
      (∀w<n+j,¬dead w → Rep new (F w)) →
      ∃new',Ext n new new' ∧ (pay j=false → new'=new) ∧
        (¬dead (n+j) → Rep new' (F (n+j)))) :
    ∀k≤m,∃new : List Gate,(∀g∈new,Fan g) ∧ new.length≤price pay k ∧
      ∀w<n+k,¬dead w → Rep new (F w) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[],by simp,by simp [price],fun w hw _ => base w (by omega)⟩
  | succ j ih =>
    intro hj
    obtain ⟨new,good,len,prior⟩ := ih (by omega)
    obtain ⟨new',ex,nocost,represented⟩ := stepOnce j (by omega) new prior
    refine ⟨new',?_,?_,?_⟩
    · rcases ex with rfl|⟨g,rfl,gok,_⟩
      · exact good
      · intro z hz
        rcases List.mem_append.mp hz with old|last
        · exact good z old
        · exact (List.mem_singleton.mp last) ▸ gok
    · cases p : pay j
      · simpa [price,p,nocost p] using len
      · rcases ex with rfl|⟨g,rfl,_⟩ <;> simp [price,p] <;> omega
    · intro w hw live
      by_cases eq : w=n+j
      · subst w; exact represented live
      · exact rep_mono ex _ (prior w (by omega) live)
end Compile18726

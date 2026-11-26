import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18723
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp



def graphFn {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any fun e => x e.1 && x e.2

def zeroed {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ S then false else x i

theorem true_expand {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (x : Fin n → Bool) :
    graphFn E (Function.update x v true) = ((graphFn E (zeroed {v,u,w} x) || x u) || x w) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [graphFn, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, h, ha, hb⟩
    by_cases av : a = v
    · subst a
      rcases hn b (Or.inl h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using hb))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using hb)
    by_cases bv : b = v
    · subst b
      rcases hn a (Or.inr h) with rfl | rfl
      · exact Or.inl (Or.inr (by simpa [Function.update_of_ne vu.symm] using ha))
      · exact Or.inr (by simpa [Function.update_of_ne vw.symm] using ha)
    have xa : x a = true := by simpa [Function.update_of_ne av] using ha
    have xb : x b = true := by simpa [Function.update_of_ne bv] using hb
    by_cases au : a = u
    · exact Or.inl (Or.inr (au ▸ xa))
    by_cases bu : b = u
    · exact Or.inl (Or.inr (bu ▸ xb))
    by_cases aw : a = w
    · exact Or.inr (aw ▸ xa)
    by_cases bw : b = w
    · exact Or.inr (bw ▸ xb)
    exact Or.inl (Or.inl ⟨(a,b),h,by simpa [zeroed,av,au,aw] using xa, by simpa [zeroed,bv,bu,bw] using xb⟩)
  · rintro ((⟨⟨a,b⟩,h,ha,hb⟩ | hu') | hw')
    · have lift (i : Fin n) (hi : zeroed {v,u,w} x i = true) : Function.update x v true i = true := by
        by_cases mem : i ∈ ({v,u,w} : Finset (Fin n))
        · simp [zeroed,mem] at hi
        · have nv : i ≠ v := by intro eq; subst i; simp at mem
          simpa [zeroed,mem,Function.update_of_ne nv] using hi
      exact ⟨(a,b),h,lift a ha,lift b hb⟩
    · rcases hu with h | h
      · exact ⟨(v,u),h,by simp,by simpa [Function.update_of_ne vu.symm] using hu'⟩
      · exact ⟨(u,v),h,by simpa [Function.update_of_ne vu.symm] using hu',by simp⟩
    · rcases hw with h | h
      · exact ⟨(v,w),h,by simp,by simpa [Function.update_of_ne vw.symm] using hw'⟩
      · exact ⟨(w,v),h,by simpa [Function.update_of_ne vw.symm] using hw',by simp⟩

def addPin (n : ℕ) (D : Circuit) (i : Fin n) : Circuit :=
  ⟨D.gates ++ [⟨.or,[D.output,i.val]⟩], n+D.size⟩

theorem addPin_size (D : Circuit) (i : Fin n) : (addPin n D i).size = D.size+1 := by
  simp [addPin,Circuit.size]

theorem addPin_fan (D : Circuit) (i : Fin n) (h : FanInTwo D) : FanInTwo (addPin n D i) := by
  intro g hg
  simp only [addPin,List.mem_append,List.mem_singleton] at hg
  rcases hg with hv | rfl
  · exact h g hv
  · simp

theorem addPin_eval (D : Circuit) (i : Fin n) (x : Fin n → Bool) :
    (addPin n D i).eval (List.ofFn x) = (D.eval (List.ofFn x) || x i) := by
  let W := wiresFrom D.gates (List.ofFn x)
  have len : W.length = n+D.size := by simp [W,length_wiresFrom,Circuit.size]
  have input : W.getD i.val false = x i := by
    obtain ⟨t,h,_⟩ := wiresFrom_prefix D.gates (List.ofFn x)
    dsimp [W]
    rw [h,List.getD_append _ _ _ _ (by simpa using i.isLt)]
    simp
  change (wiresFrom (D.gates++[⟨.or,[D.output,i.val]⟩]) (List.ofFn x)).getD (n+D.size) false = _
  rw [wiresFrom_append]
  change (W ++ [_]).getD (n+D.size) false = _
  rw [← len, getD_snoc_eq]
  change GateOp.or.eval [W.getD D.output false,W.getD i.val false] = _
  have old : W.getD D.output false = D.eval (List.ofFn x) := rfl
  rw [input,old]
  simp [GateOp.eval]

theorem rebuild {n : ℕ} (E : List (Fin n × Fin n)) (v u w : Fin n) (C D : Circuit)
    (vu : v ≠ u) (vw : v ≠ w)
    (hu : (v,u) ∈ E ∨ (u,v) ∈ E) (hw : (v,w) ∈ E ∨ (w,v) ∈ E)
    (hn : ∀ z, (v,z) ∈ E ∨ (z,v) ∈ E → z = u ∨ z = w)
    (hd : FanInTwo D) (sz : D.size + 6 ≤ C.size)
    (mem : ∀ x, D.eval (List.ofFn x) = graphFn E (zeroed {v,u,w} x)) :
    ∃ T : Circuit, FanInTwo T ∧ T.size + 4 ≤ C.size ∧
      ∀ x, T.eval (List.ofFn x) = graphFn E (Function.update x v true) := by
  refine ⟨addPin n (addPin n D u) w, addPin_fan _ _ (addPin_fan _ _ hd), ?_, ?_⟩
  · simpa only [addPin_size, Nat.add_assoc] using sz
  · intro x
    rw [addPin_eval,addPin_eval,mem,true_expand E v u w vu vw hu hw hn]


def adj (E : List (Fin n × Fin n)) (a b : Fin n) : Prop :=
  (a,b) ∈ E ∨ (b,a) ∈ E

theorem adjSymm (E : List (Fin n × Fin n)) (a b : Fin n) : adj E a b ↔ adj E b a := or_comm

theorem freeNeighbor (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ t, (t=u ∨ t=w) ∧ adj E v t ∧ ¬ adj E z t := by
  classical
  by_cases zu : adj E z u
  · refine ⟨w,Or.inr rfl,vw,fun zw => ?_⟩
    exact noFour v u z w vz uw vu ((adjSymm E z u).mp zu) zw ((adjSymm E v w).mp vw)
  · exact ⟨u,Or.inl rfl,vu,zu⟩

def pairBits (z t : Fin n) (i : Fin n) : Bool := decide (i=z ∨ i=t)

theorem pairOff (E : List (Fin n × Fin n)) (z t : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2) (indep : ¬ adj E z t) :
    graphFn E (pairBits z t) = false := by
  classical
  cases h : graphFn E (pairBits z t) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨⟨a,b⟩,he,hbits⟩ := (List.any_eq_true.mp h)
    change (pairBits z t a && pairBits z t b) = true at hbits
    simp only [pairBits,Bool.and_eq_true,decide_eq_true_eq] at hbits
    rcases hbits with ⟨az | at',bz | bt⟩
    · exact loops _ he (az.trans bz.symm)
    · exact indep (Or.inl (by simpa [az,bt] using he))
    · exact indep (Or.inr (by simpa [at',bz] using he))
    · exact loops _ he (at'.trans bt.symm)

theorem togglesPair (E : List (Fin n × Fin n)) (v u w z : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (noFour : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u ≠ w) (vz : v ≠ z) (vu : adj E v u) (vw : adj E v w) :
    ∃ x : Fin n → Bool, x z = true ∧ x v = false ∧ graphFn E x = false ∧
      graphFn E (Function.update x v true) = true := by
  classical
  obtain ⟨t,_,vt,zt⟩ := freeNeighbor E v u w z noFour uw vz vu vw
  have tv : t ≠ v := by
    intro eq; subst t
    rcases vt with he|he <;> exact loops _ he rfl
  refine ⟨pairBits z t, by simp [pairBits], by simp [pairBits,vz,tv.symm], pairOff E z t loops zt, ?_⟩
  apply List.any_eq_true.mpr
  rcases vt with he|he
  · exact ⟨(v,t),he,by simp [Function.update_of_ne tv,pairBits]⟩
  · exact ⟨(t,v),he,by simp [Function.update_of_ne tv,pairBits]⟩

def Masks (E : List (Fin n × Fin n)) (v : Fin n) (H : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, x v = false → H x = true → graphFn E x = graphFn E (Function.update x v true)

theorem adjOn {E : List (Fin n × Fin n)} {a b : Fin n} {x : Fin n → Bool}
    (h : adj E a b) (ha : x a = true) (hb : x b = true) : graphFn E x = true := by
  apply List.any_eq_true.mpr
  rcases h with e|e
  · exact ⟨(a,b),e,by simp [ha,hb]⟩
  · exact ⟨(b,a),e,by simp [ha,hb]⟩

def triple (s t k i : Fin n) : Bool := decide (i=s ∨ i=t ∨ i=k)

theorem tripleOff (E : List (Fin n × Fin n)) (s t k : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2) (st : ¬ adj E s t) (sk : ¬ adj E s k) (tk : ¬ adj E t k) :
    graphFn E (triple s t k) = false := by
  cases h : graphFn E (triple s t k) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨⟨a,b⟩,he,hbits⟩ := List.any_eq_true.mp h
    change (triple s t k a && triple s t k b) = true at hbits
    simp only [triple,Bool.and_eq_true,decide_eq_true_eq] at hbits
    obtain ⟨ha,hb⟩ := hbits
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact loops _ he rfl | exact st (Or.inl he) | exact st (Or.inr he) |
        exact sk (Or.inl he) | exact sk (Or.inr he) | exact tk (Or.inl he) | exact tk (Or.inr he)

theorem andMasks (E : List (Fin n × Fin n)) (v u w s t : Fin n)
    (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (four : ∀ a b c d, a ≠ c → b ≠ d → adj E a b → adj E b c → adj E c d → adj E d a → False)
    (uw : u≠w) (vs : v≠s) (vt : v≠t)
    (vu : adj E v u) (vw : adj E v w)
    (only : ∀ j, adj E v j → j=u ∨ j=w) :
    Masks E v (fun x => x s && x t) ↔
      adj E s t ∨ (adj E s u ∧ adj E t w) ∨ (adj E s w ∧ adj E t u) := by
  classical
  have unloop {a : Fin n} : ¬ adj E a a := by rintro (h|h) <;> exact loops _ h rfl
  have vu' : v≠u := by intro e; subst u; exact unloop vu
  have vw' : v≠w := by intro e; subst w; exact unloop vw
  constructor
  · intro mask
    by_cases st : adj E s t
    · exact Or.inl st
    apply Or.inr
    have hit (j : Fin n) (vj : adj E v j) : adj E s j ∨ adj E t j := by
      by_contra hn
      have sj : ¬ adj E s j := fun h => hn (Or.inl h)
      have tj : ¬ adj E t j := fun h => hn (Or.inr h)
      have nvj : v ≠ j := by intro e; subst j; exact unloop vj
      let x := triple s t j
      have off := tripleOff E s t j loops st sj tj
      have same := mask x (by simp [x,triple,vs,vt,nvj]) (by simp [x,triple])
      have on : graphFn E (Function.update x v true) = true :=
        adjOn vj (by simp) (by simp [x,triple,Function.update_of_ne nvj.symm])
      exact Bool.noConfusion (off.symm.trans (same.trans on))
    have ns : ¬ (adj E s u ∧ adj E s w) := fun h =>
      four v u s w vs uw vu ((adjSymm E s u).mp h.1) h.2 ((adjSymm E v w).mp vw)
    have nt : ¬ (adj E t u ∧ adj E t w) := fun h =>
      four v u t w vt uw vu ((adjSymm E t u).mp h.1) h.2 ((adjSymm E v w).mp vw)
    rcases hit u vu with su|tu <;> rcases hit w vw with sw|tw
    · exact (ns ⟨su,sw⟩).elim
    · exact Or.inl ⟨su,tw⟩
    · exact Or.inr ⟨sw,tu⟩
    · exact (nt ⟨tu,tw⟩).elim
  · intro h x xv both
    have bs : x s=true ∧ x t=true := by simpa only [Bool.and_eq_true] using both
    have retain {a b : Fin n} (e : adj E a b) (av : a ≠ v) (bv : b ≠ v)
        (xa : x a=true) (xb : x b=true) : graphFn E x = graphFn E (Function.update x v true) := by
      have f := adjOn e xa xb
      have g : graphFn E (Function.update x v true) = true := adjOn e
        (by simpa [Function.update_of_ne av] using xa) (by simpa [Function.update_of_ne bv] using xb)
      exact f.trans g.symm
    rcases h with st|⟨su,tw⟩|⟨sw,tu⟩
    · exact retain st vs.symm vt.symm bs.1 bs.2
    all_goals
      by_cases xu : x u = true
      · first | exact retain su vs.symm vu'.symm bs.1 xu | exact retain tu vt.symm vu'.symm bs.2 xu
      by_cases xw : x w = true
      · first | exact retain tw vt.symm vw'.symm bs.2 xw | exact retain sw vs.symm vw'.symm bs.1 xw
      have buf : x u=false := by cases e : x u <;> simp_all
      have bwf : x w=false := by cases e : x w <;> simp_all
      have same : zeroed {v,u,w} x = x := by
        funext i; by_cases iv : i=v
        · subst i; simp [zeroed,xv]
        by_cases iu : i=u
        · subst i; simp [zeroed,buf]
        by_cases iw : i=w
        · subst i; simp [zeroed,bwf]
        simp [zeroed,iv,iu,iw]
      rw [true_expand E v u w vu' vw' vu vw only, same,buf,bwf]
      simp

end PEqualNP.Outside.L_meta_18723

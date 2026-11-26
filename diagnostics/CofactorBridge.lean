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
  change (W.getD D.output false || W.getD i.val false) = _
  rw [input]
  rfl

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

end PEqualNP.Outside.L_meta_18723

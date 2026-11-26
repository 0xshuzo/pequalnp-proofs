import PEqualNP.Defs

namespace OrderFourPool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev V := Fin 21
abbrev Port := Fin 42
def edges : List (Nat × Nat) := [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

abbrev Inc (p l : V) : Prop := (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
def flags (x : Port → Bool) : Prop :=
  ∃ u v : Port, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

theorem labels : ∀ u v : Port, (u.val, v.val) ∈ edges ↔
    u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat) := by
  decide +kernel

theorem privateLine : ∀ r a s : V, r ≠ a → r ≠ s →
    ∃ m : V, Inc r m ∧ ¬ Inc a m ∧ ¬ Inc s m := by decide +kernel

theorem privatePoint : ∀ s t : V, s ≠ t → ∃ p : V, Inc p s ∧ ¬ Inc p t := by decide +kernel

theorem uniqueJoin : ∀ a b : V, a ≠ b → ∃! t : V, Inc a t ∧ Inc b t := by
  change ∀ a b : V, a ≠ b → ∃ t : V, (Inc a t ∧ Inc b t) ∧
    ∀ l : V, (Inc a l ∧ Inc b l) → l = t
  decide +kernel

def board (P L : Finset V) : Port → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ P)) (fun i => decide (i ∈ L))

theorem board_correct (P L : Finset V) : flags (board P L) ↔ ∃ p ∈ P, ∃ l ∈ L, Inc p l := by
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    obtain ⟨hp,hl,hi⟩ := (labels u v).1 huv
    let p : V := ⟨u.val,hp⟩
    let l : V := ⟨v.val - 21,by have := v.isLt; omega⟩
    have eqp : u = Fin.castAdd 21 p := Fin.ext rfl
    have eql : v = Fin.natAdd 21 l := Fin.ext (by change v.val = 21 + (v.val-21); omega)
    have pu : p ∈ P := by simpa only [eqp,board,Fin.addCases_left,decide_eq_true_eq] using hu
    have lv : l ∈ L := by simpa only [eql,board,Fin.addCases_right,decide_eq_true_eq] using hv
    have ee : (p.val,21+l.val) ∈ edges := by simpa only [eqp,eql,Fin.val_castAdd,Fin.val_natAdd] using huv
    have same : ∀ a b : V, (a.val,21+b.val) ∈ edges ↔ Inc a b := by decide +kernel
    exact ⟨p,pu,l,lv,(same p l).1 ee⟩
  · rintro ⟨p,hp,l,hl,ii⟩
    have same : ∀ a b : V, (a.val,21+b.val) ∈ edges ↔ Inc a b := by decide +kernel
    exact ⟨Fin.castAdd 21 p,Fin.natAdd 21 l,(same p l).2 ii,
      by simpa only [board,Fin.addCases_left,decide_eq_true_eq] using hp,
      by simpa only [board,Fin.addCases_right,decide_eq_true_eq] using hl⟩

-- The monotonicity proof is from the accepted L-meta-1892, copied to respect
-- the single permitted import.
def m1892_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl m1892_stp x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem m1892_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl m1892_stp W1).getD i false = true → (gs.foldl m1892_stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (m1892_stp W1 g) (m1892_stp W2 g) (by simp [m1892_stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [m1892_stp, m1892_getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [m1892_ev_and g _ ha, m1892_ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [m1892_ev_or g _ ho, m1892_ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem m1892_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi

theorem evalMono1892 {N : ℕ} (gs : List Gate) (u : ℕ)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hle : ∀ p, x p = true → y p = true) :
    (Circuit.mk gs u).eval (List.ofFn x) = true →
      (Circuit.mk gs u).eval (List.ofFn y) = true := by
  rw [m1892_eval_eq, m1892_eval_eq]
  apply m1892_mono gs _ _ (by simp) hop _ u
  apply m1892_all_idx N _ _ (by simp)
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simpa only [List.getElem_ofFn] using hle ⟨i, hi⟩



def Act (C : Circuit) (P L : Finset V) := C.eval (List.ofFn (board P L)) = true

theorem enlarge {C : Circuit} (hm : Monotone2 C) {P L P' L' : Finset V}
    (hp : P ⊆ P') (hl : L ⊆ L') : Act C P L → Act C P' L' := by
  apply evalMono1892 C.gates C.output (fun g hg => (hm g hg).1)
  intro i
  refine Fin.addCases (m := 21) (n := 21)
    (motive := fun j => board P L j = true → board P' L' j = true) ?_ ?_ i
  · intro p
    simpa only [board,Fin.addCases_left,decide_eq_true_eq] using (fun h : p ∈ P => hp h)
  · intro l
    simpa only [board,Fin.addCases_right,decide_eq_true_eq] using (fun h : l ∈ L => hl h)

def SafeAnd (A B : Circuit) := ∀ x : Port → Bool,
  A.eval (List.ofFn x) = true → B.eval (List.ofFn x) = true → flags x

def PointPool (C : Circuit) (a b : V) := ∀ q : V, q = a ∨ q = b →
  ∀ m : V, Inc a m ∨ Inc b m → Act C {q} {m}

def LinePool (C : Circuit) (s t : V) := ∀ q : V, Inc q s ∨ Inc q t →
  ∀ m : V, m = s ∨ m = t → Act C {q} {m}

theorem four_ports {A B : Circuit} (am : Monotone2 A) (bm : Monotone2 B) (safe : SafeAnd A B)
    {q m p l : V} (ha : Act A {q} {m}) (hb : Act B {p} {l}) :
    Inc q m ∨ Inc q l ∨ Inc p m ∨ Inc p l := by
  have a : Act A {q,p} {m,l} := enlarge am (by simp) (by simp) ha
  have b : Act B {q,p} {m,l} := enlarge bm (by simp) (by simp) hb
  have hh := (board_correct _ _).1 (safe _ a b)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  obtain ⟨z,hz,w,hw,inc⟩ := hh
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> tauto

/-- If one AND operand pools two complete point stars, an accepted nonflag in
the other operand must use their unique common line. The operands may share gates. -/
theorem pinned {A B : Circuit} (am : Monotone2 A) (bm : Monotone2 B)
    (safe : SafeAnd A B) {a b : V} (ab : a ≠ b) (pool : PointPool A a b)
    {p l : V} (miss : ¬ Inc p l) (other : Act B {p} {l}) : Inc a l ∧ Inc b l := by
  have one {u v : V} (uv : u ≠ v) (get : ∀ m : V, Inc v m → Act A {u} {m}) :
      Inc u l ∨ p = v := by
    by_cases hit : Inc u l
    · exact Or.inl hit
    by_cases pv : p = v
    · exact Or.inr pv
    obtain ⟨m,vm,um,pm⟩ := privateLine v u p uv.symm (Ne.symm pv)
    rcases four_ports am bm safe (get m vm) other with h | h | h | h
    · exact False.elim (um h)
    · exact False.elim (hit h)
    · exact False.elim (pm h)
    · exact False.elim (miss h)
  have h₁ := one ab (fun m hm => pool a (Or.inl rfl) m (Or.inr hm))
  have h₂ := one ab.symm (fun m hm => pool b (Or.inr rfl) m (Or.inl hm))
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · exact ⟨h₁,h₂⟩
    · exact False.elim (miss h₁)
  · rcases h₂ with h₂ | h₂
    · exact False.elim (miss h₂)
    · exact False.elim (ab h₂.symm)

theorem point_point {A B : Circuit} (am : Monotone2 A) (bm : Monotone2 B) (safe : SafeAnd A B)
    {a b c d : V} (ab : a ≠ b) (cd : c ≠ d) (pool : PointPool A a b) :
    ¬ PointPool B c d := by
  intro second
  have exclude (z : V) (dz : d ≠ z) (which : z = a ∨ z = b) : False := by
    obtain ⟨m,dm,cm,zm⟩ := privateLine d c z cd.symm dz
    obtain ⟨am',bm'⟩ := pinned am bm safe ab pool cm (second c (Or.inl rfl) m (Or.inr dm))
    rcases which with rfl | rfl <;> contradiction
  by_cases ha : d = a
  · exact exclude b (by simpa [ha] using ab) (Or.inr rfl)
  · exact exclude a ha (Or.inl rfl)

theorem point_line {A B : Circuit} (am : Monotone2 A) (bm : Monotone2 B) (safe : SafeAnd A B)
    {a b s t : V} (ab : a ≠ b) (st : s ≠ t) (pool : PointPool A a b) :
    ¬ LinePool B s t := by
  intro second
  obtain ⟨p,hpt,hps⟩ := privatePoint t s st.symm
  obtain ⟨q,hqs,hqt⟩ := privatePoint s t st
  have hs := pinned am bm safe ab pool hps (second p (Or.inr hpt) s (Or.inl rfl))
  have ht := pinned am bm safe ab pool hqt (second q (Or.inl hqs) t (Or.inr rfl))
  obtain ⟨m,_,hu⟩ := uniqueJoin a b ab
  exact st ((hu s hs).trans (hu t ht).symm)

/-- Two false pairs on different private lines of the same other point
already suffice in each direction. No full-star assumption is needed. -/
def TwoPrivate (A : Circuit) (u v : V) := ∃ s t : V, s ≠ t ∧
  Inc v s ∧ Inc v t ∧ ¬ Inc u s ∧ ¬ Inc u t ∧ Act A {u} {s} ∧ Act A {u} {t}

theorem four_false_pairs {A B : Circuit} (am : Monotone2 A) (bm : Monotone2 B)
    (safe : SafeAnd A B) {a b : V} (ab : a ≠ b)
    (forward : TwoPrivate A a b) (backward : TwoPrivate A b a)
    {p l : V} (miss : ¬ Inc p l) (other : Act B {p} {l}) : Inc a l ∧ Inc b l := by
  have one {u v : V} (h : TwoPrivate A u v) : Inc u l ∨ p = v := by
    by_cases ul : Inc u l
    · exact Or.inl ul
    by_cases pv : p = v
    · exact Or.inr pv
    obtain ⟨s,t,st,vs,vt,us,ut,as',at'⟩ := h
    have ps : Inc p s := by
      rcases four_ports am bm safe as' other with z | z | z | z <;> tauto
    have pt : Inc p t := by
      rcases four_ports am bm safe at' other with z | z | z | z <;> tauto
    obtain ⟨w,_,hu⟩ := uniqueJoin p v pv
    exact False.elim (st ((hu s ⟨ps,vs⟩).trans (hu t ⟨pt,vt⟩).symm))
  have h₁ := one forward
  have h₂ := one backward
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · exact ⟨h₁,h₂⟩
    · exact False.elim (miss h₁)
  · rcases h₂ with h₂ | h₂
    · exact False.elim (miss h₂)
    · exact False.elim (ab h₂.symm)

end OrderFourPool

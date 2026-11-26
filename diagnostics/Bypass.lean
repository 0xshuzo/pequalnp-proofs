import PEqualNP.Defs

namespace Bypass9739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 10000
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



def shift (cut replacement i : Nat) : Nat :=
  if i < cut then i else if i=cut then replacement else i-1

def change (cut replacement : Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (shift cut replacement)⟩

def bypass (n : Nat) (pre post : List Gate) (o replacement : Nat) : Circuit :=
  ⟨pre ++ post.map (change (n+pre.length) replacement),shift (n+pre.length) replacement o⟩

def value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl m1892_stp xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,m1892_stp] <;> omega

theorem extendRead (old fresh : List Bool) (cut replacement : Nat)
    (size : old.length = fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement < cut ∨ fresh.length < replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false)
    (v : Bool) (i : Nat) :
    (old++[v]).getD i false = (fresh++[v]).getD (shift cut replacement i) false := by
  rw [m1892_getD_snoc,m1892_getD_snoc,agree]
  by_cases ie : i=old.length
  · have se : shift cut replacement i = fresh.length := by
      have gt : cut<i := by omega
      simp [shift,show ¬i<cut by omega,show i≠cut by omega] <;> omega
    rw [if_pos ie,if_pos se]
  · have se : shift cut replacement i ≠ fresh.length := by
      simp only [shift]
      split_ifs <;> omega
    rw [if_neg ie,if_neg se]

theorem foldAgree (cut replacement : Nat) (post : List Gate) (old fresh : List Bool)
    (size : old.length=fresh.length+1) (room : cut ≤ fresh.length)
    (valid : replacement<cut ∨ fresh.length+post.length ≤ replacement)
    (agree : ∀ i, old.getD i false = fresh.getD (shift cut replacement i) false) :
    ∀ i, (post.foldl m1892_stp old).getD i false =
      ((post.map (change cut replacement)).foldl m1892_stp fresh).getD (shift cut replacement i) false := by
  induction post generalizing old fresh with
  | nil => exact agree
  | cons g post ih =>
    have v : value old g = value fresh (change cut replacement g) := by
      unfold value change
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => agree i)
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    · simp [m1892_stp,size]
    · simp [m1892_stp] <;> omega
    · simp [m1892_stp,List.length_cons] at * <;> omega
    · intro i
      change (old ++ [value old g]).getD i false =
        (fresh ++ [value fresh (change cut replacement g)]).getD _ false
      rw [←v]
      apply extendRead old fresh cut replacement size room _ agree
      simp only [List.length_cons] at valid
      omega

theorem evalBypass (n : Nat) (pre post : List Gate) (o replacement : Nat)
    (valid : replacement<n+pre.length ∨ n+pre.length+post.length ≤ replacement)
    (x : Fin n → Bool) :
    (bypass n pre post o replacement).eval (List.ofFn x) =
      (let w := pre.foldl m1892_stp (List.ofFn x);
       post.foldl m1892_stp (w ++ [w.getD replacement false])).getD o false := by
  let w := pre.foldl m1892_stp (List.ofFn x)
  have len : w.length = n+pre.length := by simp [w,foldLength]
  rw [m1892_eval_eq]
  change ((pre ++ post.map (change (n+pre.length) replacement)).foldl m1892_stp _).getD _ false = _
  rw [List.foldl_append]
  change ((post.map (change (n+pre.length) replacement)).foldl m1892_stp w).getD _ false = _
  symm
  apply foldAgree (n+pre.length) replacement post (w++[w.getD replacement false]) w
  · simp
  · omega
  · omega
  · intro i
    rw [m1892_getD_snoc]
    by_cases lt : i < w.length
    · simp [shift,←len,lt,show i≠w.length by omega]
    by_cases eq : i=w.length
    · simp [shift,←len,lt,eq]
    · have h1 : w.length≤i := by omega
      have h2 : w.length≤i-1 := by omega
      simp [shift,←len,lt,eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,
        List.getElem?_eq_none h2]

theorem short (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate) :
    (bypass n pre post o r).size+1=(Circuit.mk (pre++g::post) o).size := by
  simp [bypass,Circuit.size] <;> omega

theorem legal (n : Nat) (pre post : List Gate) (o r : Nat) (g : Gate)
    (h : Monotone2 (Circuit.mk (pre++g::post) o)) : Monotone2 (bypass n pre post o r) := by
  intro z hz
  change z ∈ pre++post.map _ at hz
  rcases List.mem_append.mp hz with left|right
  · exact h z (List.mem_append_left _ left)
  · obtain ⟨old,mem,rfl⟩ := List.mem_map.mp right
    have hh := h old (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    simpa [change] using hh

end Bypass9739

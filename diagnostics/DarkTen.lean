import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_971_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Core: strict binary DAGs, evaluation, and the shared definitions -/

/-- Gate operation: `true` is AND, `false` is OR. -/
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

/-- A binary DAG: gate `j` is `(isAnd, a, b)` and, with `n` inputs, drives wire `n + j`. -/
abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

/-- One evaluation step: append the value of gate `g` read on the current wire list. -/
def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

/-- The wire list of `D` started from the wire list `w`. -/
def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

/-- Value of wire `w` of `D` on input `x` (`false` beyond the last wire). -/
def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

/-- Strict binary DAG on `n` inputs: both operands are earlier wires and they differ. -/
def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

/-- The gates reading wire `w`. -/
def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

/-- Every wire except the last one has a reader. -/
def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

/-- Strict, live, nonempty; the output is the last wire `n + D.length - 1`. -/
def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

/-- The output wire. -/
def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

/-- Singleton assignment. -/
def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

/-- Singleton support of a wire. -/
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

/-- Surplus carried by a set of wires. -/
def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

/-- The wires other than the output. -/
def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

/-- Branching wires. -/
def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

/-- Eligible labels: carried by some branching wire. -/
def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

/-- Multiplicity-aware surplus units `⟨w, i⟩` with `i + 1 < fanout w`. -/
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

/-- Arcs are operand positions `(gate, side)`; `false` is the first operand. -/
def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

/-- Union carrier of a label set `T`. -/
def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

/-- Difference carrier: wires carrying `x` and not `y`. -/
def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

/-- A choice of one pure branching carrier for every eligible label. -/
def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

/-! ### Evaluation lemmas -/

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

/-- The value of the gate `j` wire in terms of the wire list of the first `j` gates. -/
theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

/-- Wires of an initial segment agree with the full wire list below its length. -/
theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

/-- Values of an initial segment of a DAG. -/
theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

/-- The gate equation of a strict DAG. -/
theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]


end PEqualNP.Outside.L_meta_971_aux
namespace PEqualNP.Outside.L_meta_9792.Dark
open PEqualNP.Outside.L_meta_971_aux
open Finset
abbrev J := Fin 11
abbrev V := Fin 24
def line (i : J) : V := ⟨i.val+13,by have := i.isLt; omega⟩
def sat : V → Bool := fun v => decide (v.val<13)
def lit (i : J) : V → Bool := fun v => sat v || decide (v=line i)
def mark (D : Dag) (w : Nat) (i : J) := val D (lit i) w
def price (D : Dag) : ℕ → ℕ
  | 0 => 0
  | k+1 => price D k + if tag D k = false ∧ val D sat (24+k) = false then 1 else 0

def colors (c : J → J) : Finset J := univ.image c
def same (c : J → J) (u : J → Bool) : Prop :=
  ∀ a b, u a = true → u b = true → c a = c b

theorem unionColor (c : J → J) (u v : J → Bool) (hu : same c u) (hv : same c v) :
    ∃ d, same d (fun i => u i || v i) ∧
      (∀ a b, c a = c b → d a = d b) ∧ (colors c).card ≤ (colors d).card+1 := by
  classical
  by_cases a : ∃ i, u i = true
  · obtain ⟨i,hi⟩ := a
    by_cases b : ∃ j, v j = true
    · obtain ⟨j,hj⟩ := b
      let d : J → J := fun w => if c w = c j then c i else c w
      have here (w) (h : (u w || v w) = true) : d w = c i := by
        have z : u w = true ∨ v w = true := by simpa using h
        rcases z with z|z
        · simp [d,hu w i z hi]
        · simp [d,hv w j z hj]
      refine ⟨d,fun x y hx hy => (here x hx).trans (here y hy).symm,?_,?_⟩
      · intro x y e
        simp [d,e]
      · have sub : (colors c).erase (c j) ⊆ colors d := by
          intro w hw
          obtain ⟨ne,z⟩ := mem_erase.mp hw
          obtain ⟨x,_,rfl⟩ := mem_image.mp z
          exact mem_image.mpr ⟨x,mem_univ _,by simp [d,ne]⟩
        have le := card_le_card sub
        have mem : c j ∈ colors c := mem_image.mpr ⟨j,mem_univ _,rfl⟩
        have er := card_erase_add_one mem
        omega
    · have no (j) : v j = false := by by_contra z; exact b ⟨j,by simpa using z⟩
      exact ⟨c,by simpa only [no,Bool.or_false] using hu,fun _ _ e => e,Nat.le_succ _⟩
  · have no (i) : u i = false := by by_contra z; exact a ⟨i,by simpa using z⟩
    exact ⟨c,by simpa only [no,Bool.false_or] using hv,fun _ _ e => e,Nat.le_succ _⟩

theorem prefixCost {D : Dag} (hs : Strict 24 D) (k : ℕ) (hk : k ≤ D.length) :
    ∃ c, 11 ≤ (colors c).card + price D k ∧
      ∀ w < 24+k, val D sat w = false → same c (mark D w) := by
  induction k with
  | zero =>
    refine ⟨id,by simp [colors,price],?_⟩
    intro w hw z a b ha hb
    have lt : w<24 := by omega
    let v : V := ⟨w,lt⟩
    have off : sat v = false := by simpa [val_input D _ w lt,v] using z
    have la : v = line a := by simpa [mark,lit,val_input D _ w lt,v,off] using ha
    have lb : v = line b := by simpa [mark,lit,val_input D _ w lt,v,off] using hb
    have ne := congrArg Fin.val (la.symm.trans lb)
    apply Fin.ext
    simpa [line] using ne
  | succ k ih =>
    have g : k < D.length := by omega
    obtain ⟨c,num,all⟩ := ih (by omega)
    obtain ⟨lt,rt,_⟩ := hs k g
    have eq (x : V → Bool) := val_gate hs x k g
    by_cases bright : val D sat (24+k) = true
    · refine ⟨c,?_,?_⟩
      · simpa [price,bright] using num
      · intro w hw dark
        by_cases e : w=24+k
        · subst w
          simp [bright] at dark
        · exact all _ (by omega) dark
    · have dark : val D sat (24+k)=false := by simpa using bright
      cases tagv : tag D k
      · have sides : val D sat (opA D k)=false ∧ val D sat (opB D k)=false := by
          simpa [eq sat,tagv,gop] using dark
        obtain ⟨d,un,carry,le⟩ := unionColor c _ _ (all _ lt sides.1) (all _ rt sides.2)
        refine ⟨d,?_,?_⟩
        · simp [price,tagv,dark]
          omega
        · intro w hw hd
          by_cases e : w=24+k
          · subst w
            intro a b ha hb
            apply un a b
            · simpa [mark,eq (lit a),tagv,gop] using ha
            · simpa [mark,eq (lit b),tagv,gop] using hb
          · intro a b ha hb
            exact carry a b (all w (by omega) hd a b ha hb)
      · refine ⟨c,by simpa [price,tagv] using num,?_⟩
        intro w hw hd
        by_cases e : w=24+k
        · subst w
          intro a b ha hb
          have pair (i) (h : mark D (24+k) i = true) :
              mark D (opA D k) i = true ∧ mark D (opB D k) i = true := by
            simpa [mark,eq (lit i),tagv,gop] using h
          by_cases q : val D sat (opA D k) = false
          · exact all _ lt q a b (pair a ha).1 (pair b hb).1
          · have r : val D sat (opB D k) = false := by
              have s : val D sat (opA D k) = true := by simpa using q
              simpa [eq sat,tagv,gop,s] using dark
            exact all _ rt r a b (pair a ha).2 (pair b hb).2
        · exact all w (by omega) hd

theorem ten {D : Dag} (hs : Strict 24 D) (root : ℕ) (lt : root < 24+D.length)
    (dark : val D sat root = false) (all : ∀ i, val D (lit i) root = true) :
    10 ≤ price D D.length := by
  obtain ⟨c,n,uniform⟩ := prefixCost hs D.length (le_refl _)
  have uni := uniform root lt dark
  have h : colors c = {c 0} := by
    ext v
    constructor
    · intro hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_singleton.mpr (uni i 0 (all i) (all 0))
    · intro hv
      have e := mem_singleton.mp hv
      exact e.symm ▸ mem_image.mpr ⟨0,mem_univ _,rfl⟩
  rw [h,card_singleton] at n
  omega
end PEqualNP.Outside.L_meta_9792.Dark

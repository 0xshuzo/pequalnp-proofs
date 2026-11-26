import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23519.TwoProducts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [17, 3]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [14, 19]⟩], 20⟩
def isAnd (q : Gate) := match q.op with | .and => true | _ => false
def table := fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6*u.val+v.val)
theorem attained : ∃ C : Circuit, Monotone2 C ∧ C.size = 11 ∧ C.gates.countP isAnd = 2 ∧ Represents table C :=
  ⟨witness,by simp [Monotone2,witness],by decide,by decide,by decide +kernel⟩
abbrev W := BitVec 9
def samples : Fin 9 → Fin 4 × Fin 6 := ![(1, 0), (1, 3), (1, 4), (2, 0), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4)]
def rawWords : List W := [0, 7, 56, 448, 73, 0, 0, 146, 292, 0]
def pureWords : List W := [0, 7, 56, 63, 73, 79, 121, 127, 146, 151, 186, 191, 219, 223, 251, 255, 292, 295, 316, 319, 365, 367, 381, 383, 438, 439, 446, 447, 448, 455, 457, 463, 466, 471, 475, 479, 484, 487, 493, 495, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]
def target : W := 94
theorem rawOK : ∀ i : Fin 9, rawWords.map (fun w => w.getLsbD i.val) =
    oneEach (samples i).1 (samples i).2 := by decide +kernel
theorem outOK : ∀ i : Fin 9, target.getLsbD i.val = table (samples i).1 (samples i).2 := by decide +kernel

theorem pureZero : (0 : W) ∈ pureWords := by decide +kernel
theorem pureOne : (-1 : W) ∈ pureWords := by decide +kernel
theorem rawPure : rawWords ⊆ pureWords := by
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp (show rawWords.all (fun a => decide (a ∈ pureWords)) = true by decide +kernel)
    a ha)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pureOr : ∀ a ∈ pureWords, ∀ b ∈ pureWords, a ||| b ∈ pureWords := by
  have ht : pureWords.all (fun a => pureWords.all (fun b => decide (a ||| b ∈ pureWords))) = true := by decide +kernel
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp ht a ha) b hb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbids : ∀ a ∈ pureWords, ∀ b ∈ pureWords, ∀ c ∈ pureWords,
    c ||| (a &&& b) ≠ target := by
  have ht : pureWords.all (fun a => pureWords.all (fun b => pureWords.all (fun c => decide (c ||| (a &&& b) ≠ target)))) = true := by decide +kernel
  intro a ha b hb c hc
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ht a ha) b hb) c hc)
private def bit (k : Fin 9) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 9) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def headWord (ws : List W) (g : Gate) : W :=
  match g.inputs with
  | [] => if isAnd g then -1 else 0
  | [i] => ws.getD i 0
  | i::j::_ => if isAnd g then ws.getD i 0 &&& ws.getD j 0 else ws.getD i 0 ||| ws.getD j 0

def stepW (ws : List W) (g : Gate) := ws ++ [headWord ws g]
def evalWords (gs : List Gate) (ws : List W) (o : Nat) := (gs.foldl stepW ws).getD o 0
def phase (a b v : W) := v ∈ pureWords ∨ ∃ c ∈ pureWords, v = c ||| (a &&& b)

theorem disj_phase {a b v w : W} (hv : phase a b v) (hw : phase a b w) : phase a b (v ||| w) := by
  rcases hv with h | ⟨x,hx,rfl⟩ <;> rcases hw with k | ⟨y,hy,rfl⟩
  · exact .inl (pureOr _ h _ k)
  · exact .inr ⟨_,pureOr _ h _ hy,by ac_rfl⟩
  · exact .inr ⟨_,pureOr _ hx _ k,by ac_rfl⟩
  · refine .inr ⟨_,pureOr _ hx _ hy,?_⟩
    calc
      _ = (x ||| y) ||| ((a &&& b) ||| (a &&& b)) := by ac_rfl
      _ = _ := by rw [BitVec.or_self]

theorem get_stable (P : W → Prop) (ws : List W) (h0 : P 0) (h : ∀ w ∈ ws, P w) (i : Nat) :
    P (ws.getD i 0) := by
  rcases read_wire ws i with he | hm
  · exact he.symm ▸ h0
  · exact h _ hm

theorem noAndWord (P : W → Prop) (ws : List W) (g : Gate) (hn : isAnd g = false)
    (h0 : P 0) (ho : ∀ x y, P x → P y → P (x ||| y)) (hh : ∀ w ∈ ws, P w) : P (headWord ws g) := by
  have h := get_stable P ws h0 hh
  cases he : g.inputs with
  | nil => simpa [headWord,he,hn] using h0
  | cons i l =>
    cases l with
    | nil => simpa [headWord,he] using h i
    | cons j l => simpa [headWord,he,hn] using ho _ _ (h i) (h j)

theorem appendGood {P : W → Prop} {ws : List W} {g : Gate}
    (hh : ∀ z ∈ ws, P z) (h : P (headWord ws g)) : ∀ z ∈ stepW ws g, P z := by
  intro z hz
  rcases List.mem_append.mp hz with old | last
  · exact hh _ old
  · have e : z = headWord ws g := List.mem_singleton.mp last
    exact e.symm ▸ h

theorem orTail (a b : W) (gs : List Gate) (out : Nat) (hn : gs.countP isAnd = 0)
    (ws : List W) (hh : ∀ z ∈ ws, phase a b z) : phase a b (evalWords gs ws out) := by
  induction gs generalizing ws with
  | nil => exact get_stable _ ws (.inl pureZero) hh out
  | cons g gs ih =>
    cases e : isAnd g with
    | true => simp [List.countP_cons,e] at hn
    | false =>
      have ht : gs.countP isAnd = 0 := by simpa [List.countP_cons,e] using hn
      exact ih ht _ (appendGood hh (noAndWord _ ws g e (.inl pureZero)
        (fun _ _ x y => disj_phase x y) hh))

theorem andWord (ws : List W) (g : Gate) (ha : isAnd g = true) (hh : ws ⊆ pureWords) :
    ∃ a ∈ pureWords, ∃ b ∈ pureWords, headWord ws g = a &&& b := by
  have h := get_stable (fun z => z ∈ pureWords) ws pureZero (fun _ q => hh q)
  cases he : g.inputs with
  | nil => exact ⟨-1,pureOne,-1,pureOne,by simp [headWord,he,ha]⟩
  | cons i l =>
    cases l with
    | nil => exact ⟨_,h i,_,h i,by simp [headWord,he]⟩
    | cons j l => exact ⟨_,h i,_,h j,by simp [headWord,he,ha]⟩

theorem avoidGoal (gs : List Gate) (out : Nat) (limited : gs.countP isAnd ≤ 1)
    (ws : List W) (hh : ws ⊆ pureWords) : evalWords gs ws out ≠ target := by
  induction gs generalizing ws with
  | nil =>
    have h := get_stable (fun z => z ∈ pureWords) ws pureZero (fun _ x => hh x) out
    simpa [evalWords] using forbids 0 pureZero 0 pureZero _ h
  | cons g gs ih =>
    cases e : isAnd g with
    | false =>
      have ht : gs.countP isAnd ≤ 1 := by simpa [List.countP_cons,e] using limited
      exact ih ht _ (fun _ h => appendGood (fun _ q => hh q)
        (noAndWord _ ws g e pureZero (fun _ _ hx hy => pureOr _ hx _ hy) (fun _ q => hh q)) _ h)
    | true =>
      have ht : gs.countP isAnd = 0 := by
        simp only [List.countP_cons,e, ↓reduceIte] at limited
        omega
      obtain ⟨a,ha,b,hb,prod⟩ := andWord ws g e hh
      have one : phase a b (headWord ws g) := .inr ⟨0,pureZero,by simpa using prod⟩
      have val := orTail a b gs out ht (stepW ws g) (appendGood (fun _ h => Or.inl (hh h)) one)
      rcases val with hp | ⟨c,hc,hv⟩
      · simpa using forbids 0 pureZero 0 pureZero _ hp
      · exact fun h => forbids a ha b hb c hc (hv.symm.trans h)

theorem read_step (ws : List W) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) (k : Fin 9) :
    step (ws.map (bit k)) g = (stepW ws g).map (bit k) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases hop with rfl | rfl <;> simp [isAnd,step,stepW,headWord,GateOp.eval,bit]
  | cons i xs =>
    cases xs with
    | nil => rcases hop with rfl | rfl <;> simp [isAnd,step,stepW,headWord,GateOp.eval,read_bit]
    | cons j ys =>
      cases ys with
      | cons => simp at hlen
      | nil => rcases hop with rfl | rfl <;> simp [isAnd,step,stepW,headWord,GateOp.eval,read_bit,bit]

theorem eval_rows (gs : List Gate) (mono : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2)
    (ws : List W) (k : Fin 9) : gs.foldl step (ws.map (bit k)) = (gs.foldl stepW ws).map (bit k) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [read_step ws g (mono g (by simp)) k]
    exact ih (fun t h => mono _ (by simp [h])) _

theorem lowerAnd (C : Circuit) (hm : Monotone2 C) (hr : Represents table C) : 2 ≤ C.gates.countP isAnd := by
  by_contra small
  apply avoidGoal C.gates C.output (by omega) rawWords rawPure
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let k : Fin 9 := ⟨i,hi⟩
  have rows := eval_rows C.gates (fun g h => hm g h) rawWords k
  have e := congrArg (fun l : List Bool => l.getD C.output false) rows
  rw [read_bit] at e
  have raw : rawWords.map (bit k) = oneEach (samples k).1 (samples k).2 := by
    simpa only [bit,BitVec.getLsbD_eq_getElem k.isLt] using rawOK k
  rw [raw] at e
  change C.eval (oneEach (samples k).1 (samples k).2) = bit k (evalWords C.gates rawWords C.output) at e
  rw [hr] at e
  have hw := e.symm.trans (outOK k).symm
  simpa only [bit,BitVec.getLsbD_eq_getElem hi] using hw

end PEqualNP.Outside.L_meta_23519.TwoProducts
open PEqualNP.Outside.L_meta_23519.TwoProducts in
theorem PEqualNP.Outside.L_meta_23519 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    C.size = 11 ∧ C.gates.countP isAnd = 2 ∧ PEqualNP.Represents.Represents table C) ∧
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.Represents.Represents table C → 2 ≤ C.gates.countP isAnd :=
  ⟨attained,lowerAnd⟩

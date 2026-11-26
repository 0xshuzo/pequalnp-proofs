import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9939_rank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The pointwise monotonicity proof adapts the published L-meta-1892.
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


def Upper (v w : List Bool) : Prop :=
  v.length=w.length ∧ ∀ j, v.getD j false=true → w.getD j false=true
def Mono (p : List Gate) : Prop := ∀ g ∈ p, g.op=.and ∨ g.op=.or
def run (p : List Gate) (w : List Bool) := p.foldl m1892_stp w
theorem run_len (p : List Gate) (w : List Bool) : (run p w).length = w.length+p.length := by
  induction p generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (m1892_stp w g)).length = _
    rw [ih]
    simp [m1892_stp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem run_upper (p : List Gate) (hp : Mono p) {v w} (h : Upper v w) :
    Upper (run p v) (run p w) :=
  ⟨by rw [run_len,run_len,h.1], m1892_mono p v w h.1 hp h.2⟩
def H (a b : Bool) : Prop := a=true → b=true
theorem snoc_upper {v w} (h : Upper v w) {a b : Bool} (h' : H a b) :
    Upper (v++[a]) (w++[b]) := by
  refine ⟨by simp [h.1],?_⟩
  intro i
  rw [m1892_getD_snoc,m1892_getD_snoc,h.1]
  split
  · exact h'
  · exact h.2 i

def negwire (pins : List Nat) (w : List Bool) :=
  GateOp.not.eval (pins.map fun i => w.getD i false)
theorem neg_anti (pins : List Nat) {v w} (h : Upper v w) : H (negwire pins w) (negwire pins v) := by
  cases pins with
  | nil => exact fun _ => rfl
  | cons j js =>
    have hj := h.2 j
    cases a : v.getD j false <;> cases b : w.getD j false <;>
      simp_all [negwire,GateOp.eval,H]

def first (p : List Gate) (pins : List Nat) (x : Fin 11 → Bool) :=
  negwire pins (run p (List.ofFn x))
def afterFirst (p : List Gate) (pins : List Nat) (x : Fin 11 → Bool) :=
  (run p (List.ofFn x)) ++ [first p pins x]
def mid (p : List Gate) (pins : List Nat) (q : List Gate) (x : Fin 11 → Bool) :=
  run q (afterFirst p pins x)
def two (p : List Gate) (pins : List Nat) (q : List Gate) (keys : List Nat)
    (r : List Gate) (out : Nat) : Circuit :=
  ⟨p ++ [⟨.not,pins⟩] ++ q ++ [⟨.not,keys⟩] ++ r,out⟩

theorem two_eval (p pins q keys r out) (x : Fin 11 → Bool) :
    (two p pins q keys r out).eval (List.ofFn x) =
    (run r (mid p pins q x ++ [negwire keys (mid p pins q x)])).getD out false := by
  change ((p ++ [Gate.mk .not pins] ++ q ++ [Gate.mk .not keys] ++ r).foldl m1892_stp (List.ofFn x)).getD out false = _
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] <;> rfl

def mux (x : Fin 11 → Bool) :=
  (List.ofFn x).getD (3+(1*(x 0).toNat+2*(x 1).toNat+4*(x 2).toNat)) false

def rowNumbers : Fin 6 → Fin 6 → Nat := ![![168, 169, 185, 187, 251, 255],![168, 169, 185, 189, 445, 447],![152, 154, 186, 187, 251, 255],![152, 154, 186, 190, 702, 703],![56, 60, 188, 189, 445, 447],![56, 60, 188, 190, 702, 703]]

def rows (k t : Fin 6) (i : Fin 11) := (rowNumbers k t).testBit i.val
def special (a : Fin 8) (i : Fin 11) := (a.val+8*23).testBit i.val
def maj (a : Fin 8) : Bool := decide (a.val ∈ ([3,5,6,7] : List Nat))
theorem rows_inc : ∀ (k i j : Fin 6), i≤j → ∀ v : Fin 11, rows k i v=true → rows k j v=true := by decide +kernel
theorem mux_rows : ∀ (k : Fin 6), mux (rows k 0)=true ∧ mux (rows k 1)=false ∧ mux (rows k 2)=true ∧
    mux (rows k 3)=false ∧ mux (rows k 4)=true ∧ mux (rows k 5)=false := by decide +kernel
theorem upper_inputs (x y : Fin 11 → Bool) (h : ∀ i, x i=true → y i=true) :
    Upper (List.ofFn x) (List.ofFn y) :=
  ⟨by simp, m1892_all_idx 11 _ _ (by simp) (by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simpa using hj)]
    simpa only [List.getElem_ofFn] using h ⟨j,hj⟩)⟩

def row (x : Nat) (i : Fin 11) : Bool := x.testBit i.val
def fall (x y : Nat) : Nat := (mux (row x) && !mux (row y)).toNat
def value (a b : Bool) : Nat := 2*(!a).toNat + (!b).toNat
def rank (p pins q keys) (x : Nat) := value (first p pins (row x)) (negwire keys (mid p pins q (row x)))
theorem truth_order : ∀ a b c d f g : Bool, H c a → (H a c → H d b) →
    (H a c → H b d → H f g) → value a b + (f && !g).toNat ≤ value c d := by
  unfold H
  decide
theorem rank3 (p pins q keys x) : rank p pins q keys x ≤ 3 := by
  unfold rank value
  cases first p pins (row x) <;> cases negwire keys (mid p pins q (row x)) <;> decide
theorem rank_step (p pins q keys r out) (pm : Mono p) (qm : Mono q) (rm : Mono r)
    (ev : ∀ x, (two p pins q keys r out).eval (List.ofFn x)=mux x) (x y : Nat)
    (h : x &&& y = x) : rank p pins q keys x + fall x y ≤ rank p pins q keys y := by
  have hxy (i : Fin 11) : row x i=true → row y i=true := by
    intro hx
    have hh := congrArg (fun n : Nat => n.testBit i.val) h
    change x.testBit i.val=true at hx
    simpa [row,Nat.testBit_and,hx] using hh
  have pp := run_upper p pm (upper_inputs _ _ hxy)
  have mm (h : H (first p pins (row x)) (first p pins (row y))) :
      Upper (mid p pins q (row x)) (mid p pins q (row y)) :=
    run_upper q qm (snoc_upper pp h)
  apply truth_order
  · exact neg_anti pins pp
  · exact fun u => neg_anti keys (mm u)
  · intro u v
    have hh := (run_upper r rm (snoc_upper (mm u) v)).2 out
    rw [←two_eval,←two_eval,ev,ev] at hh
    exact hh

def lastAt (a : Nat) : List Nat → Nat
  | [] => a
  | x::xs => lastAt x xs
def inc (a : Nat) : List Nat → Bool
  | [] => true
  | x::xs => ((a &&& x)==a) && inc x xs
def falls (a : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => fall a x + falls x xs
theorem chain_lower (v : Nat→Nat) (edge : ∀ x y, x &&& y=x → v x + fall x y ≤ v y)
    (xs : List Nat) (a : Nat) (good : inc a xs=true) :
    v a + falls a xs ≤ v (lastAt a xs) := by
  induction xs generalizing a with
  | nil => simp [falls,lastAt]
  | cons x xs ih =>
    simp only [inc,Bool.and_eq_true,beq_iff_eq] at good
    have e := edge a x good.1
    have f := ih x good.2
    simp only [falls,lastAt]
    omega

structure Anchor where
  pt : Nat
  fromZero : List Nat
  toTop : List Nat
  lo : Nat
  hi : Nat
def valid (a : Anchor) := ((((inc 0 a.fromZero && (lastAt 0 a.fromZero == a.pt)) &&
  inc a.pt a.toTop) && (falls 0 a.fromZero == a.lo)) && (falls a.pt a.toTop + a.hi == 3))
theorem pin {v : Nat→Nat} (cap : ∀ x, v x ≤ 3) (step : ∀ x y, x &&& y=x → v x + fall x y ≤ v y)
    {a : Anchor} (h : valid a=true) : a.lo ≤ v a.pt ∧ v a.pt ≤ a.hi := by
  simp only [valid,Bool.and_eq_true,beq_iff_eq] at h
  have lb := chain_lower v step a.fromZero 0 h.1.1.1.1
  have ub := chain_lower v step a.toTop a.pt h.1.1.2
  have cp := cap (lastAt a.pt a.toTop)
  rw [h.1.1.1.2,h.1.2] at lb
  omega

def parity3 (a : Fin 8) : Bool := decide (a.val∈([1,2,4,7] : List Nat))
def day15 : List Anchor := [⟨120,[120],[124, 252, 253, 509, 511, 2047],0,0⟩,⟨121,[104, 105, 121],[125, 509, 511, 2047],1,1⟩,⟨122,[72, 74, 122],[126, 1022, 1023, 2047],1,1⟩,⟨123,[8, 10, 42, 43, 123],[127, 2047],2,2⟩,⟨124,[120, 124],[252, 253, 509, 511, 2047],1,1⟩,⟨125,[104, 105, 121, 125],[509, 511, 2047],2,2⟩,⟨126,[72, 74, 122, 126],[1022, 1023, 2047],2,2⟩,⟨127,[8, 10, 42, 43, 123, 127],[2047],3,3⟩]
def day27 : List Anchor := [⟨216,[216],[218, 250, 254, 1022, 1023, 2047],0,0⟩,⟨217,[200, 201, 217],[221, 509, 511, 2047],1,1⟩,⟨218,[216, 218],[250, 254, 1022, 1023, 2047],1,1⟩,⟨219,[136, 137, 153, 155, 219],[223, 2047],2,2⟩,⟨220,[8, 12, 220],[221, 509, 511, 2047],1,1⟩,⟨221,[8, 12, 220, 221],[509, 511, 2047],2,2⟩,⟨222,[8, 12, 220, 222],[1022, 1023, 2047],2,2⟩,⟨223,[136, 137, 153, 155, 219, 223],[2047],3,3⟩]
def day29 : List Anchor := [⟨232,[232],[233, 249, 253, 509, 511, 2047],0,0⟩,⟨233,[232, 233],[249, 253, 509, 511, 2047],1,1⟩,⟨234,[200, 202, 234],[238, 1022, 1023, 2047],1,1⟩,⟨235,[136, 138, 170, 171, 235],[239, 2047],2,2⟩,⟨236,[8, 12, 236],[237, 509, 511, 2047],1,1⟩,⟨237,[8, 12, 236, 237],[509, 511, 2047],2,2⟩,⟨238,[8, 12, 236, 238],[1022, 1023, 2047],2,2⟩,⟨239,[136, 138, 170, 171, 235, 239],[2047],3,3⟩]
def day39 : List Anchor := [⟨312,[312],[316, 508, 510, 1022, 1023, 2047],0,0⟩,⟨313,[296, 297, 313],[315, 379, 383, 2047],1,1⟩,⟨314,[264, 266, 314],[315, 379, 383, 2047],1,1⟩,⟨315,[264, 266, 314, 315],[379, 383, 2047],2,2⟩,⟨316,[312, 316],[508, 510, 1022, 1023, 2047],1,1⟩,⟨317,[8, 9, 25, 29, 317],[319, 2047],2,2⟩,⟨318,[264, 266, 314, 318],[1022, 1023, 2047],2,2⟩,⟨319,[8, 9, 25, 29, 317, 319],[2047],3,3⟩]
def day51 : List Anchor := [⟨408,[408],[410, 442, 443, 507, 511, 2047],0,0⟩,⟨409,[392, 393, 409],[411, 507, 511, 2047],1,1⟩,⟨410,[408, 410],[442, 443, 507, 511, 2047],1,1⟩,⟨411,[392, 393, 409, 411],[507, 511, 2047],2,2⟩,⟨412,[264, 268, 412],[414, 1022, 1023, 2047],1,1⟩,⟨413,[8, 12, 140, 141, 413],[415, 2047],2,2⟩,⟨414,[264, 268, 412, 414],[1022, 1023, 2047],2,2⟩,⟨415,[8, 12, 140, 141, 413, 415],[2047],3,3⟩]
def day53 : List Anchor := [⟨424,[424],[425, 441, 443, 507, 511, 2047],0,0⟩,⟨425,[424, 425],[441, 443, 507, 511, 2047],1,1⟩,⟨426,[392, 394, 426],[427, 507, 511, 2047],1,1⟩,⟨427,[392, 394, 426, 427],[507, 511, 2047],2,2⟩,⟨428,[264, 268, 428],[430, 1022, 1023, 2047],1,1⟩,⟨429,[8, 12, 140, 141, 429],[431, 2047],2,2⟩,⟨430,[264, 268, 428, 430],[1022, 1023, 2047],2,2⟩,⟨431,[8, 12, 140, 141, 429, 431],[2047],3,3⟩]
def day71 : List Anchor := [⟨568,[568],[572, 764, 765, 1021, 1023, 2047],0,0⟩,⟨569,[552, 553, 569],[571, 635, 639, 2047],1,1⟩,⟨570,[520, 522, 570],[571, 635, 639, 2047],1,1⟩,⟨571,[520, 522, 570, 571],[635, 639, 2047],2,2⟩,⟨572,[568, 572],[764, 765, 1021, 1023, 2047],1,1⟩,⟨573,[552, 553, 569, 573],[1021, 1023, 2047],2,2⟩,⟨574,[8, 10, 42, 46, 574],[575, 2047],2,2⟩,⟨575,[8, 10, 42, 46, 574, 575],[2047],3,3⟩]
def day83 : List Anchor := [⟨664,[664],[666, 698, 699, 763, 767, 2047],0,0⟩,⟨665,[648, 649, 665],[667, 763, 767, 2047],1,1⟩,⟨666,[664, 666],[698, 699, 763, 767, 2047],1,1⟩,⟨667,[648, 649, 665, 667],[763, 767, 2047],2,2⟩,⟨668,[520, 524, 668],[669, 1021, 1023, 2047],1,1⟩,⟨669,[520, 524, 668, 669],[1021, 1023, 2047],2,2⟩,⟨670,[8, 12, 140, 142, 670],[671, 2047],2,2⟩,⟨671,[8, 12, 140, 142, 670, 671],[2047],3,3⟩]
def day85 : List Anchor := [⟨680,[680],[681, 697, 699, 763, 767, 2047],0,0⟩,⟨681,[680, 681],[697, 699, 763, 767, 2047],1,1⟩,⟨682,[648, 650, 682],[683, 763, 767, 2047],1,1⟩,⟨683,[648, 650, 682, 683],[763, 767, 2047],2,2⟩,⟨684,[520, 524, 684],[685, 1021, 1023, 2047],1,1⟩,⟨685,[520, 524, 684, 685],[1021, 1023, 2047],2,2⟩,⟨686,[8, 12, 140, 142, 686],[687, 2047],2,2⟩,⟨687,[8, 12, 140, 142, 686, 687],[2047],3,3⟩]
def words : List Nat := [15, 27, 29, 39, 51, 53, 71, 83, 85]
def entries : List Anchor := day15 ++ day27 ++ day29 ++ day39 ++ day51 ++ day53 ++ day71 ++ day83 ++ day85
set_option maxRecDepth 8192 in
theorem all_good : entries.all valid=true := by decide +kernel
def loc (d : Nat) (a : Fin 8) := entries.find? (fun e => e.pt == 8*d+a.val)
def rightCode (d : Nat) (a : Fin 8) : Bool :=
  match loc d a with
  | none => false
  | some e => e.lo == 2*(maj a).toNat + (parity3 a).toNat && e.hi == e.lo
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem nine : words.all (fun d => decide (∀ a : Fin 8, rightCode d a=true))=true := by decide +kernel
theorem inject_value : ∀ a b m t : Bool, value a b=2*m.toNat+t.toNat → a= !m ∧ b= !t := by decide
theorem decoder_slices (p pins q keys r out) (pm : Mono p) (qm : Mono q) (rm : Mono r)
    (ev : ∀ x, (two p pins q keys r out).eval (List.ofFn x)=mux x) (d : Nat) (hd : d∈words) (a : Fin 8) :
    first p pins (row (8*d+a.val))= !(maj a) ∧ negwire keys (mid p pins q (row (8*d+a.val)))= !(parity3 a) := by
  have ok : ∀ i : Fin 8, rightCode d i=true := of_decide_eq_true (List.all_eq_true.mp nine _ hd)
  have thisCode := ok a
  cases eq : loc d a with
  | none => simp [rightCode,eq] at thisCode
  | some e =>
    have fe : entries.find? (fun t => t.pt == 8*d+a.val)=some e := eq
    have member := List.mem_of_find?_eq_some fe
    have test : (e.pt == 8*d+a.val)=true := List.find?_some fe
    have point : e.pt=8*d+a.val := beq_iff_eq.mp test
    simp only [rightCode,eq,Bool.and_eq_true,beq_iff_eq] at thisCode
    have z := pin (rank3 p pins q keys) (rank_step p pins q keys r out pm qm rm ev) (List.all_eq_true.mp all_good e member)
    apply inject_value
    change rank p pins q keys (8*d+a.val) = _
    rw [←point]
    omega
end PEqualNP.Outside.L_meta_9939_rank

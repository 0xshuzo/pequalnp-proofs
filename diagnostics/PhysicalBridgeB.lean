import PEqualNP.Defs

namespace Paid17719

inductive Reach {α : Type} (op : Bool → α → α → α) (goal : α) : Nat → Set α → Prop
  | out {k S} (h : goal ∈ S) : Reach op goal k S
  | gate {k S a b} (d : Bool) (ha : a ∈ S) (hb : b ∈ S)
      (h : Reach op goal k (insert (op d a b) S)) : Reach op goal (k+1) S

theorem Reach.mono {α : Type} {op : Bool → α → α → α} {goal : α} {k : Nat} {S : Set α}
    (p : Reach op goal k S) : ∀ {S' : Set α}, S ⊆ S' → Reach op goal k S' := by
  induction p with
  | out h => exact fun h' => .out (h' h)
  | gate d ha hb _ ih =>
    intro T h
    exact .gate d (h ha) (h hb) (ih (Set.insert_subset_insert h))

section
variable {α β : Type} {op : Bool → α → α → α} {ob : Bool → β → β → β}
variable (phi : α → β) (zero : β)
def image (S : Set α) : Set β := insert zero (phi '' S)

theorem map_mem {S : Set α} {w : α} (h : w ∈ S) : phi w ∈ image phi zero S :=
  Set.mem_insert_of_mem _ ⟨w,h,rfl⟩

theorem map_insert (S : Set α) (v : α) : image phi zero (insert v S) =
    insert (phi v) (image phi zero S) := by
  ext y
  simp only [image, Set.image_insert_eq, Set.mem_insert_iff]
  tauto

theorem simulate {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b)) :
    Reach ob (phi goal) k (image phi zero S) := by
  induction h with
  | out h => exact .out (map_mem _ _ h)
  | gate d ha hb _ ih =>
    apply Reach.gate d (map_mem phi zero ha) (map_mem phi zero hb)
    rw [map_insert,hom] at ih
    exact ih

theorem paid_projection {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b))
    (different : α → Prop)
    (unchanged : ∀ d a b, ¬different a → ¬different b → ¬different (op d a b))
    (erasable : ∀ d a b, phi a = zero ∨ phi b = zero →
      phi (op d a b) = zero ∨ phi (op d a b) = phi a ∨ phi (op d a b) = phi b)
    (target_changes : different goal) (survives : phi goal ≠ zero)
    (initial : ∀ w ∈ S, different w → phi w = zero) :
    ∃ l < k, Reach ob (phi goal) l (image phi zero S) := by
  classical
  induction h with
  | out h => exact False.elim (survives (initial _ h target_changes))
  | @gate k S a b d ha hb cont ih =>
    by_cases hits : different a ∨ different b
    · have hz : phi a = zero ∨ phi b = zero := hits.imp (initial a ha) (initial b hb)
      have ready : phi (op d a b) ∈ image phi zero S := by
        rcases erasable d a b hz with e | e | e
        · rw [e]; exact Set.mem_insert _ _
        · rw [e]; exact map_mem phi zero ha
        · rw [e]; exact map_mem phi zero hb
      have p := simulate phi zero cont hom
      rw [map_insert] at p
      exact ⟨k, by omega, p.mono (Set.insert_subset ready (Set.Subset.rfl))⟩
    · have next : ∀ w ∈ insert (op d a b) S, different w → phi w = zero := by
        intro w hw diff
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · exact False.elim ((unchanged d a b (fun hn => hits (Or.inl hn))
              (fun hn => hits (Or.inr hn))) diff)
        · exact initial _ hw diff
      obtain ⟨l,hl,p⟩ := ih next
      rw [map_insert,hom] at p
      exact ⟨l+1, by omega, .gate d (map_mem phi zero ha) (map_mem phi zero hb) p⟩

end
end Paid17719
namespace Theta17719

open Paid17719
structure W where
  bit : Fin 24 → Bool
  x : Fin 3
  y : Fin 3
deriving DecidableEq

def sat (a b : Fin 3) : Fin 3 := ⟨min 2 (a.val+b.val), by omega⟩
def bot : W := ⟨fun _ => false,2,2⟩
def meet (d : Bool) (a b : W) : W :=
  if d then ⟨fun i => a.bit i && b.bit i, sat a.x b.x, sat a.y b.y⟩
  else ⟨fun i => a.bit i || b.bit i, min a.x b.x,min a.y b.y⟩
def cut (t : Nat) (w : W) : W :=
  ⟨fun i => if i.val < t then w.bit i else false, w.x,w.y⟩

theorem weq (a b : W) : a = b ↔ (∀ i, a.bit i = b.bit i) ∧ a.x = b.x ∧ a.y = b.y := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl,rfl,rfl⟩
  · rintro ⟨h,x,y⟩
    cases a with
    | mk f ax ay =>
      cases b with
      | mk g bx by' =>
        have fg : f = g := funext h
        change ax = bx at x
        change ay = by' at y
        cases fg; cases x; cases y; rfl

theorem map_meet (t : Nat) (d : Bool) (a b : W) :
    cut t (meet d a b) = meet d (cut t a) (cut t b) := by
  cases d <;> apply (weq _ _).mpr <;> refine ⟨?_,rfl,rfl⟩
  all_goals
    intro i
    by_cases hi : i.val < t <;> simp [cut,meet,hi]

theorem zeros : (∀ g : Fin 3, sat 2 g = 2 ∧ sat g 2 = 2 ∧ min 2 g = g ∧ min g 2 = g) := by
  decide

theorem killL (d : Bool) (a : W) : meet d bot a = if d then bot else a := by
  rcases a with ⟨f,x,y⟩
  cases d <;> simp [meet,bot,zeros]

theorem killR (d : Bool) (a : W) : meet d a bot = if d then bot else a := by
  rcases a with ⟨f,x,y⟩
  cases d <;> simp [meet,bot,zeros]

def rows : List Nat := [129, 130, 2049, 2080, 4098, 4128, 4160, 8193, 8256, 99, 224, 2114, 2240, 4097, 8226, 8352, 10242, 14464, 2064, 2048, 136, 128, 8196, 8192]
def raw (t : Nat) (j : Fin 25) : W :=
  ⟨fun i => decide (i.val<t) && (rows.getD i.val 0).testBit j.val,
   if j.val=0 then 0 else if j.val=7 then 1 else 2,
   if j.val=7 then 0 else if j.val=0 then 1 else 2⟩
def target (t : Nat) : W :=
  ⟨fun i => decide (i.val<t ∧ (i.val<9 ∨ i.val=18 ∨ i.val=20 ∨ i.val=22)),2,2⟩
def bank (t : Nat) : Set W := {w | w = bot ∨ ∃ j : Fin 25, w = raw t j}
def diff (t : Nat) (w : W) : Prop := w.bit (Fin.ofNat 24 t) ≠ w.bit (Fin.ofNat 24 (t+1))

def stage (k : Fin 3) := 18+2*k.val

theorem facts : ∀ j : Fin 3, let t := stage j
    cut t (target (t+2)) = target t ∧ target t ≠ bot ∧ diff t (target (t+2)) ∧
    cut t bot = bot ∧ ¬ diff t bot ∧
    ∀ i : Fin 25, cut t (raw (t+2) i) = raw t i ∧
      (diff t (raw (t+2) i) → cut t (raw (t+2) i) = bot) := by
  simp only [weq,diff]
  decide +kernel

theorem step (j : Fin 3) (n : Nat)
    (p : Reach meet (target (stage j+2)) n (bank (stage j+2))) :
    ∃ l < n, Reach meet (target (stage j)) l (bank (stage j)) := by
  let t := stage j
  obtain ⟨hgoal,hnon,hd,hbot,hnod,hraw⟩ := facts j
  have e : ∀ d a b, cut t a = bot ∨ cut t b = bot →
      cut t (meet d a b) = bot ∨ cut t (meet d a b) = cut t a ∨ cut t (meet d a b) = cut t b := by
    intro d a b h
    rw [map_meet]
    rcases h with h | h
    · rw [h,killL]; cases d <;> simp
    · rw [h,killR]; cases d <;> simp
  have un : ∀ d a b, ¬ diff t a → ¬ diff t b → ¬ diff t (meet d a b) := by
    intro d a b ha hb
    simp only [diff,not_not] at ha hb ⊢
    cases d
    · change (a.bit (Fin.ofNat 24 t) || b.bit (Fin.ofNat 24 t)) = (a.bit (Fin.ofNat 24 (t+1)) || b.bit (Fin.ofNat 24 (t+1)))
      rw [ha,hb]
    · change (a.bit (Fin.ofNat 24 t) && b.bit (Fin.ofNat 24 t)) = (a.bit (Fin.ofNat 24 (t+1)) && b.bit (Fin.ofNat 24 (t+1)))
      rw [ha,hb]
  have init : ∀ w ∈ bank (t+2), diff t w → cut t w = bot := by
    rintro w (rfl | ⟨i,rfl⟩) h
    · exact hbot
    · exact (hraw i).2 h
  have hn : cut t (target (t+2)) ≠ bot := hgoal ▸ hnon
  obtain ⟨l,hl,h⟩ := paid_projection (cut t) bot p (map_meet t) (diff t) un e hd hn init
  rw [hgoal] at h
  refine ⟨l,hl,h.mono ?_⟩
  rintro w (h | ⟨v,hv,rfl⟩)
  · exact Or.inl h
  · rcases hv with rfl | ⟨i,rfl⟩
    · exact Or.inl hbot
    · exact Or.inr ⟨i,(hraw i).1⟩

theorem theta_of_source (s : Nat) (hs : s ≤ 15)
    (p : Reach meet (target 24) s (bank 24)) :
    ∃ l ≤ 12, Reach meet (target 18) l (bank 18) := by
  obtain ⟨u,hu,h₁⟩ := step 2 s p
  obtain ⟨v,hv,h₂⟩ := step 1 u h₁
  obtain ⟨l,hl,h₃⟩ := step 0 v h₂
  exact ⟨l,by omega,h₃⟩
end Theta17719

namespace Theta17719
open Paid17719 PEqualNP.CircuitLowerBounds
private def scan (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

private theorem scan_cons (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

private theorem scan_append (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

private theorem scan_length (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [scan_cons, ih]; simp; omega

private theorem scan_prefix (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem read_gate (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
    (hstep : ∀ p, step p gs[j] = op (p.getD a d) (p.getD b d)) :
    (scan step gs w).getD (w.length + j) d =
      op ((scan step gs w).getD a d) ((scan step gs w).getD b d) := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j+1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre (i : ℕ) (hi : i < w.length + j) : (scan step gs w).getD i d = pre.getD i d := by
    rw [hs]
    exact scan_prefix _ _ _ _ _ (by omega)
  rw [hpre a ha, hpre b hb, hs, scan_cons, scan_prefix _ _ _ _ _ (by simp [hp]),
    List.getD_append_right _ _ _ _ (by omega)]
  simpa [hp] using hstep pre

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem inputValue (C : Circuit) (x : Fin 25 → Bool) (i : Fin 25) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (scan gateValue C.gates (List.ofFn x)).getD i.val false = _
  rw [scan_prefix _ _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem valueAt (C : Circuit) (x : Fin 25 → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (ha : a < 25 + j) (hb : b < 25 + j)
    (op : Bool → Bool → Bool)
    (h : ∀ w, gateValue w C.gates[j] = op (w.getD a false) (w.getD b false)) :
    (C.wires (List.ofFn x)).getD (25+j) false =
      op ((C.wires (List.ofFn x)).getD a false) ((C.wires (List.ofFn x)).getD b false) := by
  change (scan gateValue C.gates (List.ofFn x)).getD (25+j) false =
    op ((scan gateValue C.gates (List.ofFn x)).getD a false)
      ((scan gateValue C.gates (List.ofFn x)).getD b false)
  simpa only [List.length_ofFn] using
    read_gate gateValue C.gates (List.ofFn x) false j hj a b
      (by simpa only [List.length_ofFn] using ha) (by simpa only [List.length_ofFn] using hb) op h

private theorem gateOr (C : Circuit) (x : Fin 25 → Bool) (j a b : Nat)
    (h : C.gates[j]?=some ⟨.or,[a,b]⟩) (ha : a<25+j) (hb : b<25+j) :
    (C.wires (List.ofFn x)).getD (25+j) false =
      ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false) := by
  obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp h
  exact valueAt C x j hj a b ha hb (·||·) (by intro ds; simp [gateValue,eq,GateOp.eval])

private theorem gateAnd (C : Circuit) (x : Fin 25 → Bool) (j a b : Nat)
    (h : C.gates[j]?=some ⟨.and,[a,b]⟩) (ha : a<25+j) (hb : b<25+j) :
    (C.wires (List.ofFn x)).getD (25+j) false =
      ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) := by
  obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp h
  exact valueAt C x j hj a b ha hb (·&&·) (by intro ds; simp [gateValue,eq,GateOp.eval])


def positive : List Nat := [129, 130, 136, 2064, 2080, 2049, 4128, 4160, 4098, 8256, 8193, 8196]
def negative : List Nat := [1919, 2036, 3918, 4036, 5917, 6036, 7948, 8068, 10042, 10160, 12042, 14104, 14224, 16136, 16256]
def sourceMask : List Nat := [129, 130, 2049, 2080, 4098, 4128, 4160, 8193, 8256, 1919, 2036, 3918, 4036, 5917, 10042, 10160, 12042, 16256, 2064, 3918, 136, 2036, 8196, 10042]
def physicalMask : List Nat := [129, 130, 2049, 2080, 4098, 4128, 4160, 8193, 8256, 33539967, 33540084, 33541966, 33542084, 33543965, 33548090, 33548208, 33550090, 33554304, 2064, 33541966, 136, 33540084, 8196, 33548090]
def sample (r : Fin 24) (j : Fin 25) : Bool := (physicalMask.getD r.val 0).testBit j.val
def assigned (m : Nat) (b : Bool) := (List.ofFn fun j : Fin 14 => m.testBit j.val) ++ List.replicate 11 b

theorem mask_correct : ∀ r : Fin 24, if (target 24).bit r then
    sourceMask.getD r.val 0 ∈ positive ∧ List.ofFn (sample r) = assigned (sourceMask.getD r.val 0) false
  else sourceMask.getD r.val 0 ∈ negative ∧ List.ofFn (sample r) = assigned (sourceMask.getD r.val 0) true := by
  decide +kernel

def localbit (r : Fin 24) (a b : Bool) : Prop :=
  ((target 24).bit r = true → a=b) ∧ (a=true → b=true)

theorem local_and (r : Fin 24) (a b x y : Bool) (h : localbit r a x) (k : localbit r b y) :
    localbit r (a && b) (x && y) := by
  cases he : (target 24).bit r <;> cases a <;> cases b <;> cases x <;> cases y <;> simp_all [localbit]

theorem local_or (r : Fin 24) (a b x y : Bool) (h : localbit r a x) (k : localbit r b y) :
    localbit r (a || b) (x || y) := by
  cases he : (target 24).bit r <;> cases a <;> cases b <;> cases x <;> cases y <;> simp_all [localbit]

theorem input_local : ∀ i : Fin 25, ∀ r : Fin 24, localbit r ((raw 24 i).bit r) (sample r i) := by
  unfold localbit
  decide +kernel

theorem from_steps (n o : Nat) (ho : o<25+n) (predicate : Nat → W → Prop)
    (base : ∀ i : Fin 25, predicate i.val (raw 24 i))
    (advance : ∀ i < n, ∃ (d : Bool) (a b : Nat), a<25+i ∧ b<25+i ∧
      ∀ x y, predicate a x → predicate b y → predicate (25+i) (meet d x y))
    (last : ∀ w, predicate o w → w = target 24) :
    Reach meet (target 24) n (bank 24) := by
  have go : ∀ (l j : Nat) (S : Set W), j+l=n →
      (∀ i < 25+j, ∃ w ∈ S, predicate i w) → Reach meet (target 24) l S := by
    intro l
    induction l with
    | zero =>
      intro j S hj hav
      obtain ⟨w,hw,wp⟩ := hav o (by omega)
      exact .out (last w wp ▸ hw)
    | succ l ih =>
      intro j S hj hav
      obtain ⟨d,a,b,ha,hb,step⟩ := advance j (by omega)
      obtain ⟨x,hx,px⟩ := hav a ha
      obtain ⟨y,hy,py⟩ := hav b hb
      apply Reach.gate d hx hy
      apply ih (j+1) _ (by omega)
      intro i hi
      by_cases he : i=25+j
      · exact ⟨_,Set.mem_insert _ _,he ▸ step x y px py⟩
      · obtain ⟨v,hv,pp⟩ := hav i (by omega)
        exact ⟨v,Set.mem_insert_of_mem _ hv,pp⟩
  apply go n 0 _ (by omega)
  intro i hi
  let t : Fin 25 := ⟨i,by omega⟩
  exact ⟨raw 24 t, Or.inr ⟨t,rfl⟩,base t⟩

theorem sat_advance (p q t : Nat) (a b : Fin 3)
    (hp : min 2 p ≤ a.val) (hq : min 2 q ≤ b.val) (ht : t ≤ p+q) :
    min 2 t ≤ (sat a b).val := by
  change min 2 t ≤ min 2 (a.val+b.val)
  omega
theorem min_advance (p q t : Nat) (a b : Fin 3)
    (hp : min 2 p ≤ a.val) (hq : min 2 q ≤ b.val) (ht : t ≤ min p q) :
    min 2 t ≤ (min a b).val := by
  change min 2 t ≤ min a.val b.val
  omega

private theorem gate_eq_of_fields (g : Gate) (q : GateOp) (l : List Nat)
    (hq : g.op = q) (hl : g.inputs = l) : g = ⟨q,l⟩ := by
  cases g with
  | mk op inputs =>
    change op = q at hq
    change inputs = l at hl
    cases hq; cases hl; rfl

theorem posted_implies_core : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧ (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7))) →
    ∃ l ≤ 12, Reach meet (target 18) l (bank 18) := by
  rintro ⟨C,hsize,_,ho,hs,hp,hn,hr⟩
  apply theta_of_source C.size hsize
  obtain ⟨u,hu0,hu7,hur,huo,hug⟩ := hr true
  obtain ⟨v,hv7,hv0,hvr,hvo,hvg⟩ := hr false
  simp only [if_true, Bool.false_eq_true, if_false] at hu0 hu7 hv7 hv0
  let val (i : Nat) (r : Fin 24) := (C.wires (List.ofFn (sample r))).getD i false
  let rel (i : Nat) (w : W) := (∀ r, localbit r (w.bit r) (val i r)) ∧
    min 2 (u i) ≤ w.x.val ∧ min 2 (v i) ≤ w.y.val
  have truth (r : Fin 24) : val C.output r = (target 24).bit r := by
    change C.eval (List.ofFn (sample r)) = _
    have h := mask_correct r
    cases e : (target 24).bit r with
    | true =>
      simp only [e,if_true] at h
      exact h.2 ▸ hp _ h.1
    | false =>
      simp only [e,Bool.false_eq_true,if_false] at h
      exact h.2 ▸ hn _ h.1
  apply from_steps C.gates.length C.output ho rel
  · intro i
    constructor
    · intro r
      change localbit r ((raw 24 i).bit r) ((C.wires (List.ofFn (sample r))).getD i.val false)
      rw [inputValue C (sample r) i]
      exact input_local i r
    · by_cases h0 : i.val=0
      · simp [raw,h0,hu0]; omega
      · by_cases h7 : i.val=7
        · simp [raw,h7, hv7]; omega
        · have a := hur i.val i.isLt h0 h7
          have b := hvr i.val i.isLt h0 h7
          simp [raw,h0,h7,a,b]
  · intro i hi
    let g := C.gates[i]
    have hg : C.gates[i]? = some g := List.getElem?_eq_getElem hi
    obtain ⟨hop,a,b,he,_,ha,hb⟩ := hs i g hg
    have hu := hug i g a b hg he
    have hv := hvg i g a b hg he
    rcases hop with e | e
    · refine ⟨true,a,b,ha,hb,fun x y px py => ?_⟩
      have eg : g = ⟨.and,[a,b]⟩ := gate_eq_of_fields _ _ _ e he
      have hvv (r : Fin 24) : val (25+i) r = (val a r && val b r) := gateAnd C _ i a b (hg.trans (congrArg some eg)) ha hb
      refine ⟨fun r => ?_,sat_advance _ _ _ _ _ px.2.1 py.2.1 (hu.1 e),sat_advance _ _ _ _ _ px.2.2 py.2.2 (hv.1 e)⟩
      rw [hvv]; exact local_and r _ _ _ _ (px.1 r) (py.1 r)
    · refine ⟨false,a,b,ha,hb,fun x y px py => ?_⟩
      have eg : g = ⟨.or,[a,b]⟩ := gate_eq_of_fields _ _ _ e he
      have hvv (r : Fin 24) : val (25+i) r = (val a r || val b r) := gateOr C _ i a b (hg.trans (congrArg some eg)) ha hb
      refine ⟨fun r => ?_,min_advance _ _ _ _ _ px.2.1 py.2.1 (hu.2 e),min_advance _ _ _ _ _ px.2.2 py.2.2 (hv.2 e)⟩
      rw [hvv]; exact local_or r _ _ _ _ (px.1 r) (py.1 r)
  · rintro ⟨bits,x,y⟩ hw
    have bEq : bits = (target 24).bit := by
      funext r
      have h := hw.1 r
      rw [truth] at h
      cases e : (target 24).bit r <;> cases eb : bits r <;> simp_all [localbit]
    have hx := hw.2.1
    have hy := hw.2.2
    have ex : x = 2 := by apply Fin.ext; change x.val=2; simp only at hx; omega
    have ey : y = 2 := by apply Fin.ext; change y.val=2; simp only at hy; omega
    cases ex; cases ey
    exact congrArg (fun f => W.mk f 2 2) bEq

end Theta17719

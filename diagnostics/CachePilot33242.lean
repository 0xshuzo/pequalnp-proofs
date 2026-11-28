import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_33242.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_33242
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffffffe,0xfffeffffffeeffffffaa,0xffeeffeeeeccaa00ffff,0xffffffffffffffffffff,0xfffefffeffffffeeffff,0xffaaffeeffeeeeccaa00]))
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a == b) || ((a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x)))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  rcases Bool.or_eq_true.mp h with eq | h
  · exact congrArg List.toFinset (beq_iff_eq.mp eq)
  simp only [Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws) ws).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag query xs, xs ∈ links tag query → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List Sig → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

abbrev SixBits := Bool × Bool × Bool × Bool × Bool × Bool
abbrev SixRows := Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512
def readSix (r : SixRows) (v : Sig) : SixBits := ⟨bit r.1 v,bit r.2.1 v,bit r.2.2.1 v,bit r.2.2.2.1 v,bit r.2.2.2.2.1 v,bit r.2.2.2.2.2 v⟩
def sixCost (x : SixBits) : Nat := (#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[1 * x.1.toNat+2 * x.2.1.toNat+4 * x.2.2.1.toNat+8 * x.2.2.2.1.toNat+16 * x.2.2.2.2.1.toNat+32 * x.2.2.2.2.2.toNat]?.getD 3
def crossOp (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b
def applySix (d : Nat) (a b : SixBits) : SixBits := ⟨crossOp d a.1 b.1,crossOp d a.2.1 b.2.1,crossOp d a.2.2.1 b.2.2.1,crossOp d a.2.2.2.1 b.2.2.2.1,crossOp d a.2.2.2.2.1 b.2.2.2.2.1,crossOp d a.2.2.2.2.2 b.2.2.2.2.2⟩
theorem readSix_bin (r : SixRows) (d) (a b : Sig) :
    readSix r (bin d a b) = applySix d (readSix r a) (readSix r b) := by
  simp only [readSix,applySix,bit_bin,crossOp]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem six_cost_binary : ∀ (d : Fin 4) (a b : SixBits),
    sixCost (applySix d a b) ≤ sixCost a + sixCost b := by decide +kernel

theorem measure_live_tree (w : Sig → Nat) (hb : ∀ {d u} (a b), allowed u d →
    w (bin d a b) ≤ w a + w b) {u T k S} (h : Live u T k S) :
    S.card = k+1 → w T ≤ ∑ s ∈ S, w s := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb' ab fr tail ih =>
    intro saturated
    have zU : bin d a b ∉ U := fun m => fr (by simp [m])
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem zU] at bound
    have bc := Finset.card_insert_le (a:=b) (s:=U)
    have ac := Finset.card_insert_le (a:=a) (s:=insert b U)
    have aU : a ∉ insert b U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated
      omega
    have bU : b ∉ U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated ac
      omega
    rw [Finset.card_insert_of_notMem aU,Finset.card_insert_of_notMem bU] at saturated
    have tp : (insert (bin d a b) U).card = k+1 := by rw [Finset.card_insert_of_notMem zU]; omega
    have step := ih tp
    rw [Finset.sum_insert zU] at step
    rw [Finset.sum_insert aU,Finset.sum_insert bU]
    have price := hb a b hd
    omega

theorem six_cut {u T k S} (r : SixRows) (size : S.card = k+1)
    (cost : (∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r T)) :
    ∀ t, t ≤ k → ¬ Live u T t S := by
  intro t ht live
  have wid := live_size live
  have eq : S.card=t+1 := by omega
  apply Nat.not_lt_of_ge (measure_live_tree (fun a => sixCost (readSix r a)) (by
    intro d v a b h
    rw [readSix_bin]
    obtain h|h|⟨_,h⟩|⟨_,h⟩ := allowed_four h
    all_goals subst d
    · exact six_cost_binary 0 _ _
    · exact six_cost_binary 1 _ _
    · exact six_cost_binary 2 _ _
    · exact six_cost_binary 3 _ _) live eq) cost

def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩

private def sixWordsP0 : Array Nat := #[123567819853842,81475698442320,73748934836304,123567819919635,123567820380186,73748936941680,44122735970313,53957963702370,167237839388802,81475700547696,150089779709961,53957959491618,79445083883529,159511075782786,123386626326600,176068426367106,44019254108193,79203626205249,61684723097634,211692496109640,176482358026338,193995892359360,176482353815586,149572370399361,71506927829064,141875672023176,176508124012584,176478058782753,108071074930728,36322555732008,108041009700897,123356561228355,123567819849746,123356561096769,21178538266704,61684727308386,108234787586835,211662430879809,176064131334273,44122736101899,246713122193538,141978752811168,73986214593035,176094196564104,142423263543561,123902030266560,211416544477320,10479862808961,108234788047386,36456219803913,28905301872720,29240548393602,142116193861824,123386626458186,81652730628105,213727272009888,211662431011395,10067539656993,150089779841547,88382910959891,36971623743873,71778567717129,12206467997808,81411273065027]
private def sixWordsP1 : Array Nat := #[79212249809473,12176285786224,46226900852769,81652730759691,123292942473242,149842957467840,211692496241226,21101465846370,143083649925280,142526344331553,21513784787586,144117681119344,10204980707649,79445084015115,143082576183456,54357915599169,74089295282336,143625860170338,151780017143937,142526348542562,36870147277065,108715831206048,211386479247489,12275190612066,176069500108930,73714574688842,108234787520530,151844444725360,143018169491568,213594125992065,123292942012691,149705516417184,12206465892432,114767431796745,73986214593291,36870147285032,72054519382088,71506927960650,27599866847330,74089295251496,74089295249697,88382911420442,144083318767752,12412627583555,123434675867666,81785876676768,71778567716873,54357915730755,81652730757643,61783909926921,81411273081411,81652732690592,36456219935499,71549878026320,12245008400482,10584948998433,142526344333352,246773252686611,73986214469672,79749095375040,81411281264800,141978752780328,81441206591600,72054519365897]
private def sixWordsP2 : Array Nat := #[61783910979609,81411272949825,46497483817089,167750953666569,44019254100001,79276641632336,81785876644129,149572370399265,28695087562882,79212249825345,107135276419610,142423263675147,211588881058330,79203626336835,10583344679048,144323840606400,10721320503432,10722390049089,10722390050888,71515551433288,10584949000232,73986214461705,142397497565282,79445083881481,141875673075864,36322556784696,176064131334153,12516644094241,21513784803520,71950903804434,107135275893266,74501618409632,36837959671968,176508124004617,176094196531465,141875671998504,211588880597779,213727271979048,37942856786080,10479862816928,10037357478048,108041010184328,144186403733602,12275186401569,211284474216520,73714574590088,144186399524904,73714574565416,36322555871818,152050604212416,142663785513795,61680429117489,38530202476584,176478059835441,36837951815752,28828225241377,143083647862793,27969636534344,149641359331457,54357915600968,71506927820840,71950904330778,53957959516290,176508124020808]
private def sixWordsP3 : Array Nat := #[114771726794881,28828229452386,46226900877441,108105435712026,62054496995400,73744625197168,108041009692705,10204980839235,53957963694178,10067539689632,12412627583811,123902030250626,151913167339618,176482353807394,54117394812953,81544416952449,81956733788193,54357915631808,151913163129121,213624191221896,71549913686128,142116227416256,150089780762649,21101461635618,71515551449160,73714574705226,27569684635746,53957959508002,175999442640994,150089779707913,27599866855554,213594127992872,176508124136203,108041018017928,46226909184192,176094196663051,81644140694025,108096811762451,37866043869722,62054497026240,29240548393345,151844442619984,176478058774561,108234787521042,149572403953793,10583344677249,213624190738465,36322555756680,10721320501633,12245004222624,10479862825152,10174798528704,71506927845512,28695087562944,10037357447208,54117393760521,142663785384008,54117394813209,44668205140104,44123809712137,61680429109297,107238891470920,36456219836552,142116193830984]
private def sixWordsP4 : Array Nat := #[36844381298786,37702330745097,44122735968265,149572370399297,149842957467713,107238891462696,176237541072936,71506927944266,38530202501256,71778567848459,211416544444681,176478058922563,211416578031752,107616319570305,28828225241634,108715831198338,38071135371906,142663785382209,141978753863856,74229978513600,159639926767776,72022331769024,39045606416544,53957959483426,79445083884041,80953693176097,149645384908930,123356561096713,12516644126880,108715822876681,81411273065025,176094196563977,81652730634273,44536663443465,88547193782537,10037361656418,44289841299777,71549911580752,37465051119696,36322555740232,143018167386192,36972697485697,141875672006728,149572370514497,44289841332416,108105435251475,44122735970825,81785876645928,10174798497864,12412625387680,108041009725569,176478058782729,27969636532545,12176283680848,38801842372873,123469035606034,10449680605344,10479863861649,150779658928258,10449680599176,28244518635656,54531321233673,54357915732554,27599866830882]
private def sixWordsP5 : Array Nat := #[36971624798360,211662430879753,108041010159656,10449680613568,12928967248008,108071074496641,12275186434208,71515551433290,10204980740288,10722390180675,144117679013968,10067540709681,45640470110242,10584950051121,159511075758114,142526345386040,123292941946898,72294005211521,39317246312833,37110669247299,142423263551528,28141036765569,142397493354530,142423264604216,36870148329753,149705516417057,27599862636578,36870148337720,38217734685057,36837959665800,142423264596249,143048351703152,211692496241194,73986214494344,71778567848715,12687509553537,72054519497483,71778567749768,142423263691338,72054519513674,38770720669832,73817661638792,74089301543048,79749128929472,150222925725736,10037357445160,213727271977249,141875672137800,143358527799585,79276677292144,37702330777736,211416544576267,79453707504137,79212249825857,81644140825099,21178540372080,53983730741304,54499134673072,123291868205074,159639927787696,167750954719257,193729600323714,159536845979784,193755370520712]
private def sixWordsP6 : Array Nat := #[159536846999704,44564723277984,176094197616792,246708827160705,141875672138314,53983730733112,176508125065272,44122736001153,81652732659752,88172197316744,149842957598818,193995888265739,123902022517259,141918621302914,123253481881665,88650272540681,123386626326537,79212249809475,37535330009665,37565395239496,123356569419968,211386512801825,81411281258632,149572374519906,108062485020808,123356561227841,71506927960136,114831857353491,36971623744130,74149927586330,96869095120929,21101461637160,96869095145601,159511079968866,79203626205761,176508124143656,38347087020417,71787191337483,74089293709448,74501610545192,81652730694155,81411273015875,73986222334112,193995892359240,211386512801921,44019287662625,176508124012553,108586478870688,71890773418018,211692496109577,12516644096040,213594126426152,27728714666289,12275190596130,108071074471969,27569684512898,27599866724482,27569684512960,27599866724544,29240548409536,141978756989538,149705520595554,12382443176096,10067543868002]
private def sixWordsP7 : Array Nat := #[142047741743264,79445620754441,38564562747472,44123272841225,167233545375889,12240707781410,72293971657089,61684723089442,62054496993601,73748934819920,81475698425936,82198191480865,96869095276674,81785874645121,36322555871304,73817653805192,152050602082593,38770728503432,176508124152362,82198193504545,73714574573640,108039935959073,141944660955272,176163185496200,36322555748424,108071074922761,39045606424768,150360366776392,44122736099851,36456219935243,10449680597128,123567819919378,61680428064801,10174798495816,62054496993352,108170370353288,12657327341953,193995892359233,167237839388706,89142339838112,12206467989584,10479896363393,81956742105224,73714582429856,44019254124577,88382910894098,144083318743080,150222929936994,74229970640936,36837959688352,159511075782690,44027877728289,36322555863080,246713124159648,37941783044256,81652730626057,81644140825097,44019255160881,149572371452049,176551345938530,167366690373792,28141037818001,27728714666033,28110855606424]
private def sixWordsP8 : Array Nat := #[141875705577608,246773253147162,167233544355969,193725305290881,44092541263970,27698532454456,12382445371978,79453707504139,46772370022560,61783910977561,176064132386961]
private def sixWords : Array (Array Nat) := #[sixWordsP0,sixWordsP1,sixWordsP2,sixWordsP3,sixWordsP4,sixWordsP5,sixWordsP6,sixWordsP7,sixWordsP8]
private def sixMenuStartsP0 : Array Nat := #[0,2,33,49,65,82,114,145,161,178,210,246,337,353,371,418,449,466,498,530,562,594,626,658,690,722,753,770,802,834,867,914,946,978,1010,1045,1122,1154,1185,1201,1219,1267,1314,1346,1380,1442,1475,1521,1538,1570,1602,1634,1666,1697,1713,1729,1746,1778,1809,1826,1857,1874,1905,1921]
private def sixMenuStartsP1 : Array Nat := #[1938,1969,1986,2019,2066,2100,2163,2209,2226,2258,2289,2306,2338,2369,2386,2417,2433,2449,2466,2497,2513,2529,2546,2578,2609,2626,2657,2676,2737,2753,2769,2788,2850,2881,2898,2930,2961,2977,2994,3025,3042,3073,3090,3122,3154,3187,3234,3265,3281,3297,3317,3393,3414,3509,3589,3670,3765,3845,3925,4004,4069,4148,4211,4259]
private def sixMenuStartsP2 : Array Nat := #[4309,4386,4419,4469,4547,4598,4692,4756,4820,4883,4934,5028,5092,5154,5189,5270,5363,5411,5460,5523,5571,5621,5699,5749,5826,5857,5875,5925,6003,6051,6098,6131,6179,6227,6275,6322,6353,6369,6385,6404,6465,6482,6516,6579,6627,6675,6721,6737,6753,6772,6837,6913,6930,6962,6995,7042,7080,7204,7267,7316,7377,7393,7409,7427]
private def sixMenuStartsP3 : Array Nat := #[7474,7507,7557,7634,7666,7700,7763,7813,7889,7907,7954,7989,8069,8148,8215,8329,8468,8531,8579,8627,8673,8690,8724,8786,8821,8898,8933,9011,9061,9141,9218,9250,9282,9314,9347,9395,9443,9490,9523,9569,9585,9602,9633,9652,9714,9746,9777,9794,9826,9857,9873,9890,9923,9970,10002,10035,10085,10162,10197,10274,10305,10324,10388,10452]
private def sixMenuStartsP4 : Array Nat := #[10516,10579,10628,10697,10834,10869,10948,11013,11092,11153,11170,11202,11233,11253,11330,11362,11393,11412,11474,11506,11543,11651,11698,11729,11746,11777,11794,11826,11862,11964,12152,12277,12356,12424,12551,12658,12692,12758,12853,12930,12965,13044,13107,13155,13204,13270,13363,13410,13443,13490,13524,13586,13619,13667,13714,13748,13811,13860,13922,13954,13986,14018,14050,14083]
private def sixMenuStartsP5 : Array Nat := #[14131,14178,14211,14259,14313,14455,14566,14668,14855,14961,14981,15059,15106,15141,15218,15252,15314,15346,15379,15426,15458,15490,15527,15638,15735,15845,15926,16019,16067,16114,16153,16296,16420,16487,16596,16663,16772,16837,16917,16998,17090,17123,17172,17235,17283,17332,17395,17443,17491,17538,17571,17619,17666,17698,17730,17762,17795,17842,17876,17940,18003,18052,18117,18196]
private def sixMenuStartsP6 : Array Nat := #[18259,18307,18357,18436,18499,18547,18595,18643,18693,18774,18867,18917,18995,19042,19074,19107,19156,19219,19266,19299,19347,19396,19459,19509,19588,19652,19713,19730,19764,19827,19874,19907,19954,19985,20002,20034,20068,20134,20225,20242,20274,20309,20385,20402,20435,20484,20548,20611,20659,20706,20739,20787,20835,20882,20914,20947,20995,21043,21092,21155,21203,21251,21301,21381]
private def sixMenuStartsP7 : Array Nat := #[21458,21490,21522,21556,21618,21652,21714,21749,21829,21909,21988,22053,22132,22195,22247,22356,22418,22451,22499,22547,22595,22643,22691,22739,22788,22851,22898,22932,22995,23043,23091,23139,23186,23218,23254,23348,23413,23491,23539,23586,23623,23731,23781,23860,23923,23970,24003,24050,24083,24130,24162,24194,24227,24275,24322,24356,24420,24482,24514,24548,24610,24644,24706,24738]
private def sixMenuStartsP8 : Array Nat := #[24772,24837,24915,24963,25010,25042,25075,25122,25154,25185,25202,25234,25266,25299,25346,25380,25441,25460,25523,25570,25602,25633,25649,25666,25698,25731,25778,25811,25859,25908,25971,26019,26067,26113,26131,26180,26244,26306,26339,26387,26437,26515,26561,26578,26610,26644,26705,26722,26754,26788,26850,26882,26914,26946,26978,27010,27042,27075,27122,27155,27202,27235,27283,27330]
private def sixMenuStartsP9 : Array Nat := #[27365,27443,27492,27555,27604,27666,27700,27767,27881,28022,28119,28228,28296,28425,28565,28642,28674,28706,28738,28770,28803,28850,28882,28914,28948,29011,29059,29106,29146,29302,29395,29448,29576,29700,29764,29829,29908,29970,30002,30034,30066,30099,30146,30178,30210,30242,30275,30323,30370,30401,30418,30449,30466,30497,30514,30548,30610,30642,30674,30706,30739,30786,30820,30883]
private def sixMenuStartsP10 : Array Nat := #[30931,30980,31042,31076,31140,31203,31251,31301,31379,31428,31490,31524,31587,31635,31683,31729,31748,31813,31891,31939,31988,32051,32098,32129,32146,32179,32226,32258,32292,32356,32420,32484,32548,32611,32658,32691,32738,32770,32802,32834,32867,32914,32946,32978,33010,33042,33073,33090,33123,33172,33234,33265,33282,33314,33346,33378,33412,33475,33522,33554,33586,33618,33649,33666]
private def sixMenuStartsP11 : Array Nat := #[33698,33730,33763,33810,33842,33875,33923,33971,34020,34084,34148,34213,34292,34355,34401,34418,34451,34499,34549,34626,34662,34755,34801,34817,34833,34849,34866,34900,34963,35013,35093,35171,35223,35329,35345,35365,35443,35490,35522,35554,35586,35619,35666,35698,35729,35746,35780,35844,35907,35956,36018,36050,36083,36134,36227,36274,36309,36387,36435,36481,36498,36531,36578,36613]
private def sixMenuStartsP12 : Array Nat := #[36691,36739,36788,36850,36884,36947,36996,37060,37122,37154,37186,37218,37250,37282,37315,37363,37410,37442,37478,37572,37636,37700,37763,37812,37873,37889,37906,37938,37970,38003,38055,38165,38243,38290,38325,38408,38530,38564,38628,38690,38722,38756,38819,38868,38935,39046,39138,39171,39219,39266,39298,39330,39365,39441,39457,39474,39506,39542,39635,39684,39748,39810,39844,39906]
private def sixMenuStartsP13 : Array Nat := #[39940,40002,40034,40066,40100,40162,40194,40225,40242,40274,40310,40404,40468,40529,40545,40561,40578,40614,40705,40721,40738,40770,40803,40849,40867,40916,40981,41061,41140,41202,41236,41298,41331,41378,41410,41442,41478,41571,41619,41667,41716,41781,41860,41924,41987,42034,42065,42082,42113,42130,42161,42180,42246,42339,42385,42402,42436,42499,42547,42593,42610,42642,42673,42690]
private def sixMenuStartsP14 : Array Nat := #[42721,42737,42753,42770,42801,42817,42833,42849,42868,42929,42946,42979,43025,43042,43075,43121,43139,43185,43201,43217,43233,43249,43265,43282,43315,43363,43412,43475,43523,43572,43635,43684,43748,43812,43875,43923,43969,43988,44050,44085,44164,44228,44291,44339,44386,44419,44467,44513,44532,44593,44611,44659,44705,44724,44788,44852,44915,44963,45013,45090,45125,45203,45251,45300]
private def sixMenuStartsP15 : Array Nat := #[45363,45409,45427,45476,45541,45621,45701,45780,45844,45907,45955,46003,46051,46099,46147,46196,46260,46324,46387,46435,46484,46548,46611,46659,46707,46755,46804,46866,46900,46963,47011,47059,47107,47156,47219,47267,47315,47363,47410,47442,47473,47490,47524,47587,47635,47683,47731,47778,47811,47857,47875,47924,47987,48035,48083,48129,48145,48161,48178,48209,48225,48241,48259,48307]
private def sixMenuStartsP16 : Array Nat := #[48355,48403,48449,48467,48515,48563,48611,48659,48712,48835,48886,48981,49060,49124,49188,49257,49398,49493,49573,49654,49746,49777,49796,49857,49877,49961,50101,50178,50212,50279,50387,50438,50532,50594,50628,50689,50709,50791,50900,50967,51077,51155,51209,51350,51444,51510,51602,51636,51700,51763,51811,51860,51926,52020,52082,52117,52196,52258,52292,52354,52388,52455,52565,52642]
private def sixMenuStartsP17 : Array Nat := #[52678,52769,52789,52868,52930,52963,53011,53062,53161,53300,53367,53478,53574,53667,53715,53763,53811,53859,53908,53974,54067,54120,54245,54329,54470,54565,54644,54706,54740,54805,54885,54967,55078,55174,55267,55315,55364,55427,55475,55523,55571,55620,55683,55734,55829,55908,55974,56068,56131,56182,56276,56340,56406,56500,56566,56661,56739,56791,56900,56963,57013,57095,57202,57238]
private def sixMenuStartsP18 : Array Nat := #[57330,57365,57442,57479,57594,57750,57843,57891,57939,57989,58068,58133,58214,58310,58407,58515,58568,58696,58820,58885,58965,59044,59105,59121,59140,59204,59266,59298,59332,59395,59442,59475,59525,59605,59683,59731,59780,59843,59892,59955,60004,60067,60115,60163,60211,60259,60307,60358,60452,60516,60580,60644,60709,60790,60884,60948,61013,61095,61205,61283,61333,61411,61459,61507]
private def sixMenuStartsP19 : Array Nat := #[61556,61619,61667,61719,61828,61892,61955,62003,62052,62119,62229,62308,62372,62436,62498,62531,62578,62612,62677,62756,62822,62916,62980,63043,63091,63139,63193,63331,63379,63429,63507,63556,63620,63685,63765,63845,63929,64071,64180,64245,64323,64373,64454,64547,64599,64708,64774,64866,64901,64980,65044,65110,65204,65266,65300,65364,65427,65477,65555,65603,65652,65716,65780,65845]
private def sixMenuStartsP20 : Array Nat := #[65923,65972,66036,66099,66147,66195,66244,66307,66357,66434,66469,66547,66597,66679,66790,66885,66963,67012,67075,67121,67138,67172,67235,67283,67334,67429,67508,67571,67621,67699,67747,67796,67861,67939,67987,68035,68084,68148,68213,68292,68355,68406,68503,68613,68692,68755,68804,68868,68933,69015,69125,69207,69318,69412,69475,69526,69623,69730,69766,69863,69974,70067,70116,70181]
private def sixMenuStartsP21 : Array Nat := #[70261,70341,70419,70469,70550,70644,70711,70828,71010,71045,71130,71287,71396,71463,71572,71640,71766,71863,71975,72087,72194,72227,72274,72307,72356,72419,72467,72517,72596,72663,72775,72883,72931,72979,73028,73092,73154,73188,73251,73304,73430,73523,73575,73684,73749,73828,73892,73956,74021,74099,74151,74261,74342,74435,74485,74564,74628,74693,74773,74855,74963,75012,75075,75123]
private def sixMenuStartsP22 : Array Nat := #[75171,75221,75304,75427,75476,75540,75606,75704,75829,75908,75972,76036,76100,76166,76260,76325,76404,76468,76530,76563,76613,76690,76722,76754,76786,76820,76883,76931,76980,77044,77107,77156,77222,77316,77380,77444,77507,77556,77619,77667,77717,77799,77908,77973,78053,78130,78164,78226,78259,78306,78339,78387,78436,78499,78551,78662,78756,78819,78867,78916,78983,79092,79154,79189]
private def sixMenuStartsP23 : Array Nat := #[79269,79347,79396,79463,79574,79668,79732,79797,79876,79944,80069,80148,80211,80259,80308,80371,80425,80562,80596,80660,80727,80836,80902,80996,81063,81171,81223,81339,81509,81588,81657,81798,81895,82009,82150,82241,82260,82322,82356,82422,82517,82594,82626,82658,82694,82788,82855,82965,83045,83124,83186,83219,83272,83395,83442,83479,83589,83669,83749,83827,83874,83906,83941,84021]
private def sixMenuStartsP24 : Array Nat := #[84097,84117,84196,84258,84289,84305,84322,84354,84388,84451,84499,84545,84564,84627,84676,84737,84754,84786,84820,84884,84948,85012]
private def sixMenuStarts : Array (Array Nat) := #[sixMenuStartsP0,sixMenuStartsP1,sixMenuStartsP2,sixMenuStartsP3,sixMenuStartsP4,sixMenuStartsP5,sixMenuStartsP6,sixMenuStartsP7,sixMenuStartsP8,sixMenuStartsP9,sixMenuStartsP10,sixMenuStartsP11,sixMenuStartsP12,sixMenuStartsP13,sixMenuStartsP14,sixMenuStartsP15,sixMenuStartsP16,sixMenuStartsP17,sixMenuStartsP18,sixMenuStartsP19,sixMenuStartsP20,sixMenuStartsP21,sixMenuStartsP22,sixMenuStartsP23,sixMenuStartsP24]
private def sixMenuWordsP0 : Array Nat := #[2,391,279,1,4,4,68,59,116,48,394,1,280,1,14,24,42,62,183,281,395,32,34,0,282,397,0,218,0,117,133,0,10,0,398,0,399,0,283,0,102,0,185,0,154,0,184,84,0,155,0,7,0,18,0,11,18,0,57,0,119,0,285,0]
private def sixMenuWordsP1 : Array Nat := #[49,63,64,219,286,401,0,6,0,219,57,49,0,84,134,64,402,403,0,186,186,220,0,11,18,22,23,25,84,135,404,108,0,288,0,79,0,1,0,16,0,135,90,405,182,0,115,0,221,186,0,406,17,0,80,79,104,0,65,11,0,290,16,49]
private def sixMenuWordsP2 : Array Nat := #[407,87,136,9,24,53,76,9,53,222,408,48,409,36,410,137,115,182,115,392,83,182,393,107,42,281,182,396,132,45,10,154,184,32,184,184,283,400,284,57,64,87,118,64,286,120,6,63,154,287,64,219,187,0,289,0,103,103,188,118,136,291,138,411]
private def sixMenuWordsP3 : Array Nat := #[50,1,121,5,9,1,190,1,3,11,3,7,194,36,311,0,3,4,34,50,15,0,3,5,8,13,308,0,1,2,47,315,0,1,2,10,314,0,1,2,3,237,312,0,1,2,8,307,0,3,4,8,65,0,3,8,65,155,0,1,2,3,0,1]
private def sixMenuWordsP4 : Array Nat := #[5,119,168,0,1,84,239,0,7,35,0,47,315,0,3,18,240,323,8,321,0,3,20,0,7,18,145,243,0,127,244,0,2,5,57,246,436,0,2,6,332,0,1,18,154,0,7,76,304,0,12,67,0,1,4,29,49,249,0,4,24,61,0,6]
private def sixMenuWordsP5 : Array Nat := #[34,186,1,66,0,1,2,3,9,0,1,2,4,99,254,0,16,172,0,14,135,0,3,75,150,0,209,256,0,24,345,0,3,5,79,111,0,1,253,0,3,5,31,104,0,112,18,0,3,35,0,4,11,100,357,0,17,262,0,28,259,0,3,0]
private def sixMenuWordsP6 : Array Nat := #[20,80,0,5,261,0,29,260,0,29,485,1,5,498,5,189,1,2,14,292,14,138,189,9,14,189,412,1,14,292,2,157,158,157,158,293,157,158,413,1,2,9,223,9,14,19,122,157,2,2,13,2,14,1,2,60,2,19,13,19,27,46,60,157]
private def sixMenuWordsP7 : Array Nat := #[159,414,1,2,21,115,1,38,73,13,21,46,60,21,60,13,1,2,50,46,53,9,60,224,9,46,91,122,123,8,13,14,139,27,60,160,191,9,14,27,19,21,69,159,161,8,2,19,192,19,69,1,2,3,9,225,1,2,3,14,21,2,26,28]
private def sixMenuWordsP8 : Array Nat := #[43,3,9,11,35,38,73,192,3,4,11,28,45,80,83,92,416,9,19,28,46,70,71,193,2,7,11,2,3,59,38,7,19,3,7,11,71,4,80,4,21,26,80,92,1,2,9,14,43,124,417,26,59,116,9,28,46,92,226,9,21,28,80,162]
private def sixMenuWordsP9 : Array Nat := #[1,3,4,11,1,7,3,116,26,70,83,69,92,227,9,21,45,1,11,24,42,107,418,228,1,419,299,1,2,164,300,24,42,48,140,195,48,230,14,164,71,302,138,228,77,140,164,229,302,195,301,1,14,300,1,2,3,196,231,2,194,29,42,49]
private def sixMenuWordsP10 : Array Nat := #[107,232,4,105,59,1,2,4,141,73,107,304,424,24,42,60,425,28,42,107,232,24,42,73,24,42,183,197,3,4,9,20,48,81,109,303,427,59,229,24,42,61,183,197,7,35,45,71,3,7,35,55,71,3,4,48,94,198,4,165,132,234,109,1]
private def sixMenuWordsP11 : Array Nat := #[2,4,93,428,68,230,4,30,306,23,58,82,194,39,59,59,105,3,6,11,39,66,77,429,1,3,4,1,4,23,235,293,235,4,16,1,233,3,4,7,58,77,236,3,4,10,40,45,47,51,74,142,237,307,430,25,27,44,51,60,68,88,166,1]
private def sixMenuWordsP12 : Array Nat := #[2,40,185,308,1,2,79,238,1,2,3,5,9,21,34,199,1,2,50,105,167,200,431,0,282,1,2,3,34,0,1,2,8,34,51,8,13,47,142,237,3,4,8,13,167,312,313,3,5,13,314,0,40,143,0,3,199,0,2,21,45,0,3,5]
private def sixMenuWordsP13 : Array Nat := #[8,15,311,0,2,313,0,238,0,4,102,0,187,0,3,8,15,0,2,0,2,316,0,1,5,0,50,0,15,102,318,0,88,319,0,68,102,310,0,25,0,44,0,60,0,27,0,166,0,2,320,0,1,317,0,432,0,15,126,0,7,15,10,11]
private def sixMenuWordsP14 : Array Nat := #[18,22,47,144,240,321,433,0,8,10,13,47,144,240,8,13,47,95,103,322,3,4,8,13,15,22,36,48,62,65,155,434,3,11,13,62,65,242,323,96,3,7,11,13,36,0,22,78,0,11,0,3,7,8,11,0,13,0,3,13,18,0,169,0]
private def sixMenuWordsP15 : Array Nat := #[324,0,15,62,0,62,0,35,0,20,1,2,5,12,76,145,146,1,2,9,24,61,325,0,1,2,12,76,145,146,0,1,2,103,118,0,1,24,61,85,325,0,80,326,0,1,29,0,41,5,6,7,35,57,119,148,154,287,4,9,29,45,49,72]
private def sixMenuWordsP16 : Array Nat := #[136,245,24,89,147,327,1,2,7,54,199,243,328,1,2,55,201,1,2,7,67,146,202,329,1,4,103,120,11,18,57,119,148,11,18,168,201,331,5,11,148,246,332,333,0,5,0,2,331,0,1,2,333,0,7,199,0,2,54,0,7,18,329,4]
private def sixMenuWordsP17 : Array Nat := #[187,248,0,9,124,0,9,222,0,72,0,2,335,0,1,247,0,24,0,61,0,29,0,45,0,4,149,0,120,1,2,5,12,2,10,23,25,85,87,437,0,1,85,438,0,1,25,44,134,0,1,44,134,0,8,73,64,147,203,6,10,16,29,74]
private def sixMenuWordsP18 : Array Nat := #[0,10,23,25,0,2,6,12,28,30,0,2,10,17,63,137,45,64,147,156,443,6,10,16,29,203,336,6,63,89,12,17,63,89,156,10,23,25,63,64,17,24,45,63,89,12,63,64,89,17,63,64,34,50,2,6,12,2,132,205,2,3,134,447]
private def sixMenuWordsP19 : Array Nat := #[1,2,205,1,2,4,13,337,1,2,16,200,1,2,23,25,7,0,34,0,6,220,448,0,6,34,0,22,0,18,22,0,220,40,15,40,0,15,5,8,9,79,6,10,12,13,16,29,12,0,12,0,251,0,40,336,449,450,6,0,451,0,7,197]
private def sixMenuWordsP20 : Array Nat := #[0,15,42,49,0,17,40,63,0,6,12,0,41,78,10,12,0,49,206,0,16,252,0,23,452,0,453,0,17,0,52,454,0,10,11,0,52,110,0,42,61,110,0,17,63,0,61,110,2,44,134,2,10,12,23,25,1,2,205,279,455,0,58,44]
private def sixMenuWordsP21 : Array Nat := #[456,457,458,10,23,25,235,0,247,0,42,110,149,4,5,16,25,47,49,208,16,49,84,99,135,23,29,44,57,207,1,2,3,14,0,1,2,111,209,0,2,104,171,29,116,171,1,2,5,14,172,253,339,1,2,200,340,0,108,0,2,341,0,207]
private def sixMenuWordsP22 : Array Nat := #[459,0,14,108,0,2,108,0,2,4,0,11,104,0,13,108,0,3,66,190,0,11,460,0,19,0,1,2,5,0,208,461,0,2,343,0,1,3,0,1,344,0,47,0,23,16,49,84,99,135,345,3,5,14,24,24,99,172,249,344,18,342,346,0]
private def sixMenuWordsP23 : Array Nat := #[9,108,0,338,1,2,14,79,172,253,256,0,2,347,14,49,84,172,347,0,3,5,111,0,11,339,0,256,0,69,116,0,150,0,3,31,0,254,0,126,0,122,6,16,462,6,8,16,51,203,16,45,57,466,10,23,27,160,6,73,68,88,45,72]
private def sixMenuWordsP24 : Array Nat := #[161,166,6,16,1,2,24,36,16,33,8,337,1,8,24,51,5,12,17,30,33,1,2,4,2,4,468,1,15,2,3,0,16,31,0,30,0,56,141,0,141,0,39,0,37,0,15,349,0,33,0,15,33,349,33,0,3,30,115,0,3,66,0,160]
private def sixMenuWordsP25 : Array Nat := #[0,73,46,19,0,159,0,14,0,15,30,0,197,0,7,469,0,14,24,0,1,2,350,0,91,351,0,38,160,0,21,72,27,0,2,27,0,1,43,252,0,6,470,471,0,472,0,40,294,0,1,2,0,33,40,63,129,0,16,352,16,0,258,0]
private def sixMenuWordsP26 : Array Nat := #[473,0,15,150,348,9,0,9,0,21,46,319,352,474,0,123,0,295,0,191,0,257,0,161,0,69,0,239,0,17,33,0,244,0,221,258,0,173,0,112,475,0,112,476,0,353,0,15,42,104,477,0,112,478,1,2,30,200,0,206,479,0,1,252]
private def sixMenuWordsP27 : Array Nat := #[480,27,346,0,112,481,482,3,4,23,24,44,76,130,4,11,17,22,61,100,127,259,260,0,23,24,44,76,130,0,17,61,100,127,259,260,26,44,80,326,3,4,7,11,28,29,36,354,3,5,11,29,98,100,261,262,356,1,7,14,81,96,0,355]
private def sixMenuWordsP28 : Array Nat := #[0,130,0,4,0,250,0,358,0,4,354,0,263,0,484,0,76,0,3,18,356,0,89,263,0,3,11,0,357,4,20,22,28,61,81,104,261,262,359,0,3,4,11,18,359,0,20,22,5,12,17,33,36,48,264,486,8,9,12,14,17,62,140,487]
private def sixMenuWordsP29 : Array Nat := #[15,105,195,488,1,14,81,96,4,13,35,40,489,3,13,40,363,129,263,0,28,0,139,0,490,0,8,491,0,86,0,109,0,351,0,125,0,17,151,0,25,110,0,46,86,0,55,151,17,33,30,0,492,0,15,42,265,0,188,0,151,0,494,0]
private def sixMenuWordsP30 : Array Nat := #[364,0,42,265,37,96,0,42,110,265,0,63,129,0,112,365,1,2,14,56,23,47,4,5,9,53,29,57,87,210,0,2,210,0,47,366,29,44,57,210,366,10,23,85,10,23,136,367,170,204,6,16,87,204,0,23,47,0,23,80,0,2,85,58]
private def sixMenuWordsP31 : Array Nat := #[10,23,43,124,10,23,45,72,162,10,23,45,1,4,125,1,2,59,163,1,14,330,4,255,234,0,296,0,23,53,18,334,0,111,5,9,29,53,5,9,14,53,5,14,53,222,5,9,26,53,6,9,16,27,0,9,58,0,267,0,75,92,0,497]
private def sixMenuWordsP32 : Array Nat := #[0,92,0,162,0,175,0,364,365,0,38,0,163,0,298,0,368,0,266,268,48,499,1,2,33,5,9,14,33,36,500,3,3,28,3,369,2,4,16,57,6,16,85,501,6,16,87,51,87,137,268,74,137,13,137,94,3,94,13,268,3,59,12,13]
private def sixMenuWordsP33 : Array Nat := #[140,94,363,5,14,12,31,53,15,58,502,0,264,370,9,16,17,70,9,12,17,33,6,9,16,33,10,23,62,86,176,0,151,258,503,6,9,16,156,14,121,19,122,223,9,73,115,19,115,121,159,190,122,159,9,19,21,38,46,91,21,91,223,294]
private def sixMenuWordsP34 : Array Nat := #[53,295,415,19,192,21,43,225,226,21,28,226,46,59,60,80,124,3,14,28,80,124,3,4,48,9,28,38,43,46,59,225,125,70,4,60,68,80,92,3,83,296,92,297,26,297,11,163,92,298,3,70,83,107,192,42,194,420,83,421,42,164,229,301]
private def sixMenuWordsP35 : Array Nat := #[48,140,195,230,91,231,422,91,231,303,423,91,92,73,81,42,59,109,3,73,107,109,196,426,7,109,198,4,93,42,60,82,164,305,61,110,232,61,110,183,233,38,196,132,165,233,4,299,4,60,68,140,306,4,68,92,32,119,142,32,84,142,166,44]
private def sixMenuWordsP36 : Array Nat := #[166,65,155,185,238,65,88,185,9,65,167,309,9,65,68,310,119,142,167,168,119,316,84,142,167,317,65,318,84,90,320,144,145,169,44,169,127,144,0,95,144,145,169,241,0,44,169,322,0,103,127,144,0,44,95,241,62,79,435,96,168,242,243,62]
private def sixMenuWordsP37 : Array Nat := #[242,25,96,25,168,145,324,9,61,146,29,85,87,118,136,147,170,0,29,61,136,146,147,201,245,120,327,49,60,72,89,124,9,32,49,72,85,89,124,148,24,147,4,149,245,328,98,120,146,330,49,148,201,247,148,248,249,334,49,90,335,0,44,87]
private def sixMenuWordsP38 : Array Nat := #[134,6,10,64,87,118,439,440,6,64,87,118,170,204,6,63,5,6,63,17,64,137,441,442,23,64,444,445,10,60,250,305,446,251,63,17,156,17,64,5,12,62,65,79,196,62,65,251,32,47,99,207,32,57,99,208,75,209,0,75,104,209,75,338]
private def sixMenuWordsP39 : Array Nat := #[5,14,75,340,47,99,99,341,57,99,99,246,255,342,57,343,187,255,75,104,150,207,463,6,10,25,38,72,464,6,32,72,84,16,44,72,465,51,348,257,13,65,12,33,36,121,190,467,161,65,6,84,128,350,6,84,90,150,47,100,130,18,76,100]
private def sixMenuWordsP40 : Array Nat := #[483,0,47,80,100,130,0,26,76,100,174,0,26,47,174,100,355,7,100,125,202,103,125,5,14,163,76,358,20,79,130,360,4,17,44,264,361,362,12,18,127,0,130,360,0,80,109,0,47,165,174,0,17,44,361,362,0,12,127,165,0,44,109,241]
private def sixMenuWordsP41 : Array Nat := #[0,103,165,14,33,129,67,139,493,11,56,162,170,174,204,210,6,29,85,118,170,174,0,10,29,367,291,495,38,43,208,496,3,58,83,3,83,368,266,10,120,5,267,163,10,248,111,370,173,173,267,175,31,191,138,1,2,5,9,98,1,13,1,5]
private def sixMenuWordsP42 : Array Nat := #[41,73,14,26,1,3,26,371,3,7,14,82,78,121,66,272,271,7,21,14,26,93,14,23,56,0,3,4,8,0,50,375,0,3,8,0,5,7,8,0,1,25,0,1,15,44,0,1,5,41,0,1,8,73,0,3,62,0,8,96,44,0,18,20]
private def sixMenuWordsP43 : Array Nat := #[52,8,273,0,1,4,29,376,0,1,22,49,0,1,18,60,0,4,24,0,61,98,1,8,2,6,13,12,45,63,378,0,6,22,34,117,0,6,39,0,6,67,507,0,2,6,128,0,2,10,214,0,2,6,22,0,13,17,0,12,21,0,2,10]
private def sixMenuWordsP44 : Array Nat := #[15,381,1,171,0,1,2,3,4,0,19,57,0,14,47,0,5,7,111,0,1,19,176,1,2,5,2,6,8,141,0,3,8,13,33,0,1,2,3,38,0,1,2,8,27,0,3,8,30,0,1,3,27,0,16,46,0,16,19,0,9,25,0,3]
private def sixMenuWordsP45 : Array Nat := #[38,0,27,46,0,24,385,0,3,31,33,0,3,30,31,0,3,27,31,0,3,16,0,3,27,0,1,3,16,0,2,6,8,0,3,4,0,26,76,0,28,47,0,5,26,0,3,18,86,8,37,0,3,18,37,0,8,45,0,17,43,0,30,43]
private def sixMenuWordsP46 : Array Nat := #[0,17,26,0,3,56,86,0,37,43,0,29,123,0,29,45,0,3,17,8,12,1,27,388,0,77,0,1,18,38,0,14,23,0,14,27,0,23,28,0,28,37,0,75,0,20,55,516,0,24,95,0,2,10,18,0,29,69,0,21,29,0,1,14]
private def sixMenuWordsP47 : Array Nat := #[74,22,20,51,216,85,88,72,13,16,33,0,5,10,8,33,101,0,6,277,275,0,5,20,0,25,30,0,5,6,18,37,101,0,5,29,5,13,14,19,41,73,138,158,1,2,19,1,2,5,14,50,98,5,19,21,69,224,5,9,14,21,1,2]
private def sixMenuWordsP48 : Array Nat := #[5,21,1,2,3,28,3,4,9,11,19,28,41,48,60,1,2,7,19,83,98,5,9,28,116,227,1,2,5,14,269,5,11,19,26,202,269,372,504,81,19,78,82,270,373,1,2,28,36,271,9,28,36,48,51,66,78,121,272,9,28,39,51,374]
private def sixMenuWordsP49 : Array Nat := #[28,48,1,2,3,9,3,4,21,26,43,48,82,1,3,36,3,4,9,14,26,28,1,2,3,82,2,28,1,2,26,43,26,1,2,3,4,141,48,51,95,138,193,236,270,3,9,35,193,3,4,19,46,48,55,82,3,4,11,36,66,3,36,95]
private def sixMenuWordsP50 : Array Nat := #[3,4,9,20,28,45,48,55,81,3,4,9,13,82,236,3,9,28,95,3,4,9,19,26,46,19,28,3,4,36,55,3,4,7,48,71,193,211,1,3,55,1,2,3,7,3,20,21,55,81,91,1,3,7,71,7,70,1,2,4,19,373,4,43]
private def sixMenuWordsP51 : Array Nat := #[55,93,4,55,4,21,26,55,9,43,9,14,43,77,9,28,39,46,58,91,123,23,39,58,82,93,28,58,9,20,21,26,54,55,28,3,39,77,116,372,3,4,20,39,3,39,26,81,177,9,69,123,3,7,20,58,77,81,4,9,25,40,41,44]
private def sixMenuWordsP52 : Array Nat := #[45,51,73,1,2,5,40,1,2,4,5,21,50,101,1,2,3,7,9,50,0,1,2,8,50,51,8,25,41,8,41,152,3,5,15,0,40,177,0,4,101,0,1,21,45,0,5,7,8,9,15,0,1,152,11,18,22,25,44,52,96,273,0,8]
private def sixMenuWordsP53 : Array Nat := #[25,44,52,5,7,8,15,22,40,62,71,96,4,5,8,18,52,62,3,7,11,40,71,0,7,8,11,0,8,0,7,18,40,1,9,24,52,61,0,1,24,52,61,9,20,29,35,41,49,60,1,2,35,52,101,149,1,2,20,24,98,178,18,29]
private def sixMenuWordsP54 : Array Nat := #[41,18,41,153,5,22,29,274,0,1,153,0,1,274,0,35,101,0,1,149,0,18,20,178,2,5,12,1,2,21,34,54,212,10,11,12,17,24,12,17,21,61,3,5,9,11,22,212,2,10,21,44,2,20,22,1,2,7,11,18,21,10,74,85]
private def sixMenuWordsP55 : Array Nat := #[203,0,2,12,85,0,10,12,13,17,24,12,13,21,61,0,2,10,12,23,25,0,2,10,21,44,0,2,12,0,1,2,8,13,34,74,5,6,71,74,74,212,213,6,10,72,88,94,0,6,10,16,29,39,97,6,49,3,5,6,10,45,72,45]
private def sixMenuWordsP56 : Array Nat := #[74,6,7,10,23,25,10,44,3,5,20,22,40,88,213,3,4,5,7,11,20,35,71,94,97,1,2,54,71,81,213,1,2,12,2,6,20,2,15,205,5,6,12,13,17,6,12,13,17,2,20,22,40,81,1,2,8,13,20,74,1,2,3,8]
private def sixMenuWordsP57 : Array Nat := #[13,74,1,2,5,21,34,54,97,1,2,34,1,2,3,4,34,55,59,97,5,11,13,52,54,97,101,141,13,21,54,149,7,20,21,35,71,1,2,7,52,54,1,2,54,55,39,77,6,10,16,29,6,10,23,25,6,13,3,6,0,6,7,34]
private def sixMenuWordsP58 : Array Nat := #[0,22,34,6,11,3,6,22,41,113,131,153,505,41,113,131,152,506,0,5,15,5,9,13,0,5,88,275,0,54,94,0,5,22,72,0,6,15,0,5,7,11,0,5,7,0,1,276,0,2,78,0,2,113,0,2,131,0,2,41,0,1,2,21]
private def sixMenuWordsP59 : Array Nat := #[34,67,0,11,67,97,0,2,21,97,0,2,7,54,0,2,131,379,1,2,6,7,97,0,1,2,6,39,67,3,4,6,131,128,179,376,380,0,6,15,39,67,0,2,6,7,40,67,97,0,2,6,131,380,1,2,6,0,11,143,177,275,0,5]
private def sixMenuWordsP60 : Array Nat := #[45,0,3,54,0,10,12,0,20,52,143,0,20,52,0,7,13,3,4,11,12,13,55,97,0,11,12,67,0,12,13,67,0,2,13,0,12,13,0,2,113,377,1,2,7,10,23,25,54,5,10,23,25,113,0,2,10,113,0,7,54,58,0,2]
private def sixMenuWordsP61 : Array Nat := #[10,54,4,26,3,4,5,3,5,25,29,47,57,1,2,3,7,14,0,1,2,111,1,2,5,14,19,178,0,11,13,171,3,5,14,153,19,29,152,0,11,178,6,16,51,3,4,26,27,38,40,43,51,74,6,16,43,6,16,27,6,16,27,38]
private def sixMenuWordsP62 : Array Nat := #[41,6,27,73,3,4,40,70,3,4,9,39,1,2,24,30,36,1,2,14,33,40,1,4,8,24,51,3,6,8,9,13,14,15,16,36,3,5,6,13,16,30,33,1,24,40,271,1,2,4,13,40,2,3,13,1,2,7,24,39,3,4,13,25]
private def sixMenuWordsP63 : Array Nat := #[36,39,1,2,3,3,4,7,13,24,30,52,1,2,3,52,0,1,2,8,39,66,8,21,0,1,2,21,31,5,8,30,31,0,1,2,31,0,8,30,36,66,171,0,30,31,66,2,8,6,30,39,66,8,13,38,43,3,5,13,0,3,5,8]
private def sixMenuWordsP64 : Array Nat := #[15,0,3,30,0,4,35,0,3,41,66,0,3,8,73,0,3,16,66,0,8,14,15,24,0,16,35,0,5,8,24,0,1,2,382,0,2,383,0,2,31,0,2,16,0,1,2,25,0,1,16,0,1,2,25,31,0,31,0,6,34,39,50,3]
private def sixMenuWordsP65 : Array Nat := #[25,153,0,4,8,15,39,0,4,5,8,15,31,39,0,7,8,40,89,98,0,1,2,3,384,0,16,70,6,16,43,385,3,5,6,24,6,19,3,6,19,375,3,5,24,3,5,25,4,6,15,38,46,53,0,4,13,15,53,0,3,13,176,0]
private def sixMenuWordsP66 : Array Nat := #[15,98,1,2,19,20,33,0,2,386,6,19,386,0,3,5,31,0,19,70,143,177,0,39,69,0,20,224,0,27,30,0,21,31,52,0,5,39,52,0,3,9,15,126,0,5,13,31,0,3,5,3,4,7,13,30,39,0,4,8,15,30,31,39]
private def sixMenuWordsP67 : Array Nat := #[0,3,15,30,106,0,3,13,31,0,3,106,0,1,3,511,1,2,3,4,0,1,2,31,38,4,11,22,24,25,47,76,0,24,25,47,76,3,4,7,11,28,71,101,3,5,22,24,26,139,0,7,18,139,0,7,11,12,17,51,106,180,215,11]
private def sixMenuWordsP68 : Array Nat := #[18,19,22,37,46,86,17,76,3,4,5,12,17,37,4,11,12,17,22,46,123,11,12,17,37,52,86,12,37,273,3,4,22,78,3,4,11,22,215,0,8,13,46,86,0,8,13,26,37,0,12,17,0,12,17,46,123,0,12,17,37,52,86,0]
private def sixMenuWordsP69 : Array Nat := #[12,17,26,29,36,48,71,129,215,512,3,4,5,8,9,13,15,22,28,30,36,48,17,30,4,5,8,29,51,3,8,9,12,13,15,17,28,36,62,5,8,12,17,33,36,513,4,15,29,272,4,13,15,22,28,40,74,3,13,20,36,3,11,13]
private def sixMenuWordsP70 : Array Nat := #[25,29,77,101,129,3,4,13,25,36,77,3,4,7,13,29,36,41,3,4,7,11,29,36,77,3,4,7,11,25,36,41,0,106,0,8,250,0,211,0,17,37,0,4,25,106,0,8,25,0,4,77,0,4,7,8,11,0,4,13,18,4,12,15]
private def sixMenuWordsP71 : Array Nat := #[43,53,62,86,0,4,8,13,15,53,94,0,3,13,0,26,78,0,33,37,0,22,41,78,0,5,33,37,8,41,0,3,35,106,0,11,13,4,12,20,22,26,30,70,81,0,3,4,11,18,70,0,3,180,3,4,11,20,28,37,77,0,18,56]
private def sixMenuWordsP72 : Array Nat := #[93,0,4,18,56,77,0,3,37,180,0,3,11,56,1,2,14,93,1,2,5,19,37,23,37,47,4,10,11,19,22,23,69,3,4,5,9,53,1,2,4,7,11,22,10,23,216,0,1,2,19,37,0,23,37,47,0,1,2,37,0,10,19,23]
private def sixMenuWordsP73 : Array Nat := #[69,0,1,2,216,387,5,7,26,27,35,38,43,23,27,47,10,23,38,176,10,23,26,10,38,60,4,7,20,1,2,7,19,56,1,2,7,24,58,67,82,139,4,14,56,1,2,5,14,1,2,3,59,3,11,19,29,58,75,3,5,11,24,56]
private def sixMenuWordsP74 : Array Nat := #[93,114,178,1,7,14,20,71,11,18,26,27,5,11,26,181,0,1,2,181,0,7,18,56,5,29,128,152,214,514,0,1,2,214,0,1,2,128,389,0,67,89,98,10,23,26,95,4,181,24,26,214,29,179,181,274,515,5,18,0,176,0,93,0]
private def sixMenuWordsP75 : Array Nat := #[227,1,2,14,20,0,2,390,10,14,390,0,1,2,56,0,1,179,517,0,11,388,0,11,56,269,4,20,22,28,70,81,0,4,11,70,0,20,22,371,0,114,202,518,1,2,37,5,9,19,37,19,52,277,3,4,22,1,2,8,50,51,0,5]
private def sixMenuWordsP76 : Array Nat := #[6,16,19,52,69,5,8,13,52,1,2,5,52,216,6,38,68,88,114,38,43,4,10,27,114,26,27,6,13,74,5,28,5,6,9,3,4,15,15,58,374,519,26,41,160,4,5,6,15,31,38,114,0,3,4,8,13,15,0,15,112,114,0,31]
private def sixMenuWordsP77 : Array Nat := #[88,0,15,31,31,38,43,53,6,31,46,53,75,86,91,5,9,38,43,0,278,10,14,33,278,520,10,28,30,56,70,0,31,72,0,5,20,72,3,4,20,21,31,53,55,5,9,21,31,53,55,1,2,33,278,0,1,179,521,6,179,181,276,522]
private def sixMenuWordsP78 : Array Nat := #[14,20,33,55,4,12,20,22,30,56,114,143,0,3,4,11,18,0,112,114,151,0,22,56,20,28,30,26,27,56,70,21,26,28,3,14,26,41,42,55,78,82,121,42,51,3,4,48,270,3,4,48,51,9,26,43,46,55,59,91,19,70,107,211]
private def sixMenuWordsP79 : Array Nat := #[3,9,28,42,59,94,3,19,42,177,5,10,12,21,22,52,69,11,17,54,0,6,10,12,21,52,69,5,6,10,22,32,41,63,72,78,85,95,0,11,32,45,97,7,20,32,74,5,6,9,12,15,22,62,65,88,12,13,17,20,54,71,2,12]
private def sixMenuWordsP80 : Array Nat := #[13,17,54,96,309,5,9,11,54,59,62,65,94,212,3,20,52,54,69,213,377,6,10,41,95,6,379,41,95,113,131,5,6,9,12,62,65,6,10,90,276,508,4,509,26,510,26,206,6,16,25,27,32,43,32,39,51,89,3,6,8,13,14,30]
private def sixMenuWordsP81 : Array Nat := #[66,0,21,30,31,39,6,16,25,27,43,16,27,382,383,6,384,20,30,70,4,12,17,18,25,37,46,106,4,11,45,11,22,0,12,17,25,26,37,46,4,12,13,48,129,3,13,22,36,215,8,17,37,106,211,22,33,55,11,93,0,387,7,32]
private def sixMenuWordsP82 : Array Nat := #[82,83,89,5,58,59,75,93,389,5,38,53,75,86,5,15,30,88,2,9,41,67,2,21,2,78,0,2,15,381,0,13,21,0,2,22,217,0,1,8,15,0,5,46,0,1,19,217,29,0,43,0,26,0,1,18,22,0,1,14,217,0,10,54]
private def sixMenuWordsP83 : Array Nat := #[67,0,6,54,67]
private def sixMenuWords : Array (Array Nat) := #[sixMenuWordsP0,sixMenuWordsP1,sixMenuWordsP2,sixMenuWordsP3,sixMenuWordsP4,sixMenuWordsP5,sixMenuWordsP6,sixMenuWordsP7,sixMenuWordsP8,sixMenuWordsP9,sixMenuWordsP10,sixMenuWordsP11,sixMenuWordsP12,sixMenuWordsP13,sixMenuWordsP14,sixMenuWordsP15,sixMenuWordsP16,sixMenuWordsP17,sixMenuWordsP18,sixMenuWordsP19,sixMenuWordsP20,sixMenuWordsP21,sixMenuWordsP22,sixMenuWordsP23,sixMenuWordsP24,sixMenuWordsP25,sixMenuWordsP26,sixMenuWordsP27,sixMenuWordsP28,sixMenuWordsP29,sixMenuWordsP30,sixMenuWordsP31,sixMenuWordsP32,sixMenuWordsP33,sixMenuWordsP34,sixMenuWordsP35,sixMenuWordsP36,sixMenuWordsP37,sixMenuWordsP38,sixMenuWordsP39,sixMenuWordsP40,sixMenuWordsP41,sixMenuWordsP42,sixMenuWordsP43,sixMenuWordsP44,sixMenuWordsP45,sixMenuWordsP46,sixMenuWordsP47,sixMenuWordsP48,sixMenuWordsP49,sixMenuWordsP50,sixMenuWordsP51,sixMenuWordsP52,sixMenuWordsP53,sixMenuWordsP54,sixMenuWordsP55,sixMenuWordsP56,sixMenuWordsP57,sixMenuWordsP58,sixMenuWordsP59,sixMenuWordsP60,sixMenuWordsP61,sixMenuWordsP62,sixMenuWordsP63,sixMenuWordsP64,sixMenuWordsP65,sixMenuWordsP66,sixMenuWordsP67,sixMenuWordsP68,sixMenuWordsP69,sixMenuWordsP70,sixMenuWordsP71,sixMenuWordsP72,sixMenuWordsP73,sixMenuWordsP74,sixMenuWordsP75,sixMenuWordsP76,sixMenuWordsP77,sixMenuWordsP78,sixMenuWordsP79,sixMenuWordsP80,sixMenuWordsP81,sixMenuWordsP82,sixMenuWordsP83]
private def sixMenuAtP0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2,3,4,5,6,4,3,3,0,0,0,0,7,8,0,7,9,10,11,12,13,14,15,16,16,16,16,16,0,0,17,16,18,16,0,19,16,16,16,16,16]
private def sixMenuAtP1 : Array Nat := #[16,16,16,16,0,0,16,16,0,0,20,0,0,0,16,0,16,16,0,0,16,0,21,16,16,0,0,22,22,23,16,16,16,0,0,0,16,0,0,0,24,25,16,0,0,16,16,0,16,0,16,16,16,16,16,16,0,16,16,0,0,0,16,16]
private def sixMenuAtP2 : Array Nat := #[26,0,0,0,0,0,0,0,16,16,0,0,0,0,0,0,0,0,0,16,16,16,16,18,0,27,28,27,16,16,16,16,0,0,16,16,16,16,16,16,16,29,30,16,0,15,15,16,0,16,16,16,31,0,32,33,34,12,35,16,0,0,0,0]
private def sixMenuAtP3 : Array Nat := #[0,0,17,36,16,16,36,0,0,0,0,0,0,0,16,0,0,0,31,16,16,16,16,16,16,37,16,38,0,0,16,16,34,16,0,0,0,0,16,16,0,34,16,16,39,0,16,16,16,16,16,16,40,41,0,16,16,16,0,0,0,16,16,16]
private def sixMenuAtP4 : Array Nat := #[42,16,43,16,44,16,16,16,0,0,0,16,45,16,16,16,0,16,0,12,46,16,16,16,16,47,16,16,16,16,0,48,16,16,49,50,0,16,0,0,0,0,0,0,16,0,16,16,0,0,0,0,0,16,16,16,0,16,51,0,0,0,16,0]
private def sixMenuAtP5 : Array Nat := #[0,0,52,0,16,0,0,16,16,0,0,16,16,16,0,0,53,16,49,0,0,16,16,16,16,31,54,16,0,16,0,0,55,56,16,16,16,16,16,0,0,16,0,0,0,16,16,57,16,16,58,0,0,16,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP6 : Array Nat := #[16,16,16,16,0,0,16,16,16,16,59,16,16,60,61,0,62,63,64,0,0,16,16,16,0,0,0,16,16,16,0,16,16,16,16,16,16,16,16,16,0,16,16,0,0,16,0,0,16,16,65,16,16,66,16,16,0,0,67,68,52,51,16,0]
private def sixMenuAtP7 : Array Nat := #[0,0,69,70,0,0,16,0,71,72,73,74,0,16,0,0,0,0,75,76,0,0,0,0,0,0,0,0,0,0,77,78,0,0,0,0,5,0,79,80,81,82,83,4,0,0,0,84,0,85,86,87,88,0,0,0,0,0,0,0,0,53,0,0]
private def sixMenuAtP8 : Array Nat := #[0,85,0,18,18,16,0,89,0,90,90,0,0,0,0,91,33,92,93,94,95,96,0,0,0,0,0,0,0,12,0,0,0,0,0,0,97,0,0,0,0,0,16,98,99,0,0,100,0,0,101,0,0,0,0,0,0,0,0,0,0,98,0,0]
private def sixMenuAtP9 : Array Nat := #[102,103,0,0,0,0,104,0,105,106,107,108,0,3,77,0,109,110,111,0,0,0,0,112,0,113,114,115,116,50,117,118,119,120,121,122,123,124,16,125,16,16,16,126,0,64,127,85,128,129,130,131,29,132,16,133,134,135,136,137,50,138,139,0]
private def sixMenuAtP10 : Array Nat := #[0,140,16,16,16,16,141,16,142,143,16,144,145,146,147,16,148,149,150,16,151,16,16,152,16,16,16,153,154,155,156,157,158,159,160,161,162,16,29,163,16,164,165,0,16,16,166,0,0,0,167,168,169,170,171,172,173,174,175,176,177,0,178,179]
private def sixMenuAtP11 : Array Nat := #[180,181,182,181,183,168,184,185,186,0,0,187,188,189,190,191,192,193,194,195,196,197,198,199,168,200,77,0,0,201,0,202,0,0,203,204,205,206,207,208,209,210,211,212,213,0,214,179,0,0,215,0,4,216,5,217,218,219,220,221,222,4,223,224]
private def sixMenuAtP12 : Array Nat := #[225,226,227,228,0,3,229,0,0,0,0,0,0,0,230,3,0,0,0,231,0,0,0,232,233,0,234,0,0,0,0,0,0,105,235,236,0,0,237,238,7,168,239,240,241,242,232,0,168,243,244,245,246,247,7,9,0,3,10,3,10,248,0,249]
private def sixMenuAtP13 : Array Nat := #[3,3,250,251,252,0,253,0,254,255,256,257,258,259,260,4,261,262,263,264,110,265,0,3,3,266,267,268,0,269,0,0,0,0,0,0,270,271,4,272,4,5,5,251,4,0,273,0,274,275,0,275,3,0,276,4,224,222,277,278,279,4,278,280]
private def sixMenuAtP14 : Array Nat := #[281,0,282,4,3,278,0,251,3,0,283,0,284,0,0,3,3,4,3,4,5,3,278,0,285,12,286,287,105,288,289,191,290,16,291,0,292,293,16,16,16,16,49,16,16,16,16,16,294,295,296,16,297,3,298,299,300,301,16,302,179,123,16,22]
private def sixMenuAtP15 : Array Nat := #[115,16,303,16,304,22,305,16,16,306,16,16,16,16,16,16,16,16,16,16,307,308,16,16,16,16,16,16,307,309,16,16,16,16,16,16,16,16,16,0,16,310,16,16,16,115,115,0,17,16,311,312,313,16,314,315,316,317,318,16,0,0,16,0]
private def sixMenuAtP16 : Array Nat := #[16,16,16,319,49,50,16,320,16,16,0,16,16,16,321,50,50,16,315,16,0,322,28,323,16,16,16,16,16,16,50,16,16,50,16,16,16,16,16,324,325,326,16,16,327,328,329,330,331,16,332,16,333,28,334,335,16,336,16,16,16,337,28,16]
private def sixMenuAtP17 : Array Nat := #[16,16,115,338,339,16,339,16,16,16,16,16,16,16,315,16,16,0,16,340,16,340,340,340,28,28,28,340,28,16,16,16,341,16,16,16,16,16,16,16,16,16,16,16,0,342,343,344,345,346,347,348,0,349,350,12,351,352,353,217,354,16,16,0]
private def sixMenuAtP18 : Array Nat := #[0,355,356,0,217,357,358,16,359,360,16,0,361,16,307,362,16,363,364,365,179,0,0,3,0,0,17,366,367,34,368,16,369,16,34,16,0,16,16,16,16,0,0,370,371,16,16,16,372,373,16,0,0,16,0,0,0,16,16,50,50,16,374,374]
private def sixMenuAtP19 : Array Nat := #[50,16,16,16,16,34,16,16,16,16,16,16,16,16,341,375,376,372,16,374,377,16,50,13,378,379,380,0,381,16,382,383,384,385,386,13,0,387,388,16,16,389,387,388,16,18,16,390,0,391,392,12,12,12,12,12,393,394,395,396,397,398,399,400]
private def sixMenuAtP20 : Array Nat := #[397,401,402,13,13,403,404,217,405,406,407,408,398,409,16,16,16,0,0,0,0,0,0,0,3,0,0,0,0,179,179,179,0,0,179,0,0,16,16,0,16,16,0,16,410,0,0,0,16,0,0,0,0,16,411,412,16,16,28,413,340,0,28,414]
private def sixMenuAtP21 : Array Nat := #[16,0,65,0,415,30,332,416,16,16,16,417,0,418,417,0,17,17,419,420,421,422,18,423,18,16,0,16,16,22,424,423,34,36,425,36,426,18,22,427,36,36,36,18,16,16,0,0,0,18,16,36,18,0,16,16,0,0,428,429,430,16,431,423]
private def sixMenuAtP22 : Array Nat := #[36,340,16,0,0,0,0,0,0,0,16,16,16,0,16,0,0,0,16,0,307,432,36,16,307,16,16,0,431,307,16,16,16,16,16,431,433,36,0,0,0,16,307,0,388,349,434,435,16,36,436,307,0,16,0,16,16,16,0,16,0,0,16,0]
private def sixMenuAtP23 : Array Nat := #[0,16,437,0,0,0,0,0,16,51,28,16,16,438,16,16,36,16,0,18,429,36,434,16,340,16,0,16,0,423,423,83,16,0,28,16,0,16,36,16,36,16,439,440,16,16,18,16,28,16,307,423,441,442,16,443,16,18,16,85,16,438,438,438]
private def sixMenuAtP24 : Array Nat := #[373,372,16,444,0,18,36,16,445,446,447,448,0,449,450,451,0,16,16,452,16,83,16,453,426,0,18,0,454,0,0,0,12,455,456,457,458,459,460,374,461,16,462,463,47,464,47,16,16,16,16,16,465,466,49,50,467,468,16,469,16,0,0,16]
private def sixMenuAtP25 : Array Nat := #[0,470,471,472,473,16,474,0,475,476,16,477,16,16,360,50,307,478,3,16,50,16,51,0,16,31,16,479,50,50,480,0,16,481,16,0,482,483,3,484,485,16,16,16,16,486,16,487,16,16,16,16,16,488,489,490,491,16,492,493,494,495,16,16]
private def sixMenuAtP26 : Array Nat := #[496,16,16,497,498,497,16,499,16,16,500,501,502,0,12,12,503,12,12,12,12,504,505,506,507,508,0,402,509,13,0,510,511,512,4,513,3,514,515,516,16,16,517,16,16,518,519,317,520,521,522,16,520,16,523,16,448,16,16,16,16,16,16,16]
private def sixMenuAtP27 : Array Nat := #[438,16,16,16,16,16,16,16,16,16,115,0,48,524,0,525,526,527,526,526,524,50,50,3,50,16,50,50,528,16,0,0,0,0,0,0,16,16,0,0,0,0,0,0,16,0,16,0,0,0,0,0,16,529,530,16,349,0,16,16,0,0,115,531]
private def sixMenuAtP28 : Array Nat := #[532,533,534,535,0,526,0,16,0,0,340,340,340,536,372,16,537,0,0,16,0,0,16,538,534,0,51,539,28,51,0,540,541,307,16,307,16,16,16,16,123,307,50,542,543,544,0,16,16,16,0,526,50,16,16,16,16,16,16,519,317,545,16,50]
private def sixMenuAtP29 : Array Nat := #[16,0,179,0,50,50,51,546,547,16,50,0,307,16,105,548,549,550,16,551,16,3,552,50,16,0,16,0,0,0,553,212,51,554,0,0,528,0,0,0,555,0,16,0,0,16,16,0,16,0,556,16,16,16,16,16,16,28,0,115,0,16,16,36]
private def sixMenuAtP30 : Array Nat := #[16,16,16,557,558,559,558,560,561,562,16,16,16,563,16,481,564,36,565,566,567,168,0,0,0,16,0,16,0,16,16,307,16,0,16,53,16,16,568,569,568,3,566,0,16,0,0,0,16,0,16,0,16,16,567,16,16,16,16,16,16,16,51,570]
private def sixMenuAtP31 : Array Nat := #[571,16,572,573,499,16,496,574,317,16,16,16,16,16,317,0,560,526,16,16,575,0,576,317,16,577,16,16,16,0,16,578,16,16,579,580,0,53,581,16,582,499,16,36,545,16,16,16,16,16,0,0,16,0,0,0,16,0,16,0,0,0,16,16]
private def sixMenuAtP32 : Array Nat := #[0,16,16,0,0,0,0,16,16,0,16,16,16,0,16,16,16,0,0,0,0,16,0,0,0,16,0,0,0,16,16,0,16,16,0,0,0,16,583,584,585,586,16,587,16,588,0,0,589,590,591,592,16,16,593,28,16,360,594,595,596,597,598,599]
private def sixMenuAtP33 : Array Nat := #[498,600,601,16,481,16,16,16,16,16,16,16,158,16,16,341,602,16,603,16,16,16,16,16,16,332,16,16,16,16,16,16,604,605,606,16,607,16,16,16,16,16,16,16,16,16,16,153,16,16,16,5,608,609,610,611,612,613,0,0,0,0,0,0]
private def sixMenuAtP34 : Array Nat := #[16,0,340,28,28,519,614,16,16,16,16,16,0,615,16,16,16,16,158,616,593,617,618,619,16,620,360,16,16,16,16,560,621,360,622,623,624,16,524,16,16,423,16,372,423,374,314,0,0,0,0,60,0,625,626,60,627,628,317,0,0,0,629,545]
private def sixMenuAtP35 : Array Nat := #[630,498,0,16,126,340,16,16,16,65,16,30,66,16,0,631,558,16,0,16,0,0,632,618,16,632,0,16,16,16,0,16,16,16,16,16,16,16,16,16,633,634,16,635,16,526,16,16,0,570,340,16,16,340,16,16,16,16,16,16,16,265,16,51]
private def sixMenuAtP36 : Array Nat := #[16,16,16,498,636,16,16,16,16,16,16,16,637,0,638,639,317,16,16,640,16,16,265,16,16,554,641,642,643,643,644,645,646,31,647,16,648,649,650,651,317,652,653,317,654,16,16,16,3,51,16,655,12,12,642,12,12,656,657,658,659,660,661,16]
private def sixMenuAtP37 : Array Nat := #[16,16,448,448,448,16,523,16,3,0,0,662,16,0,0,50,16,16,16,16,524,621,50,551,16,663,16,664,50,0,0,0,0,0,0,665,279,665,0,481,16,0,0,0,0,0,0,0,0,481,16,0,0,666,667,360,16,668,669,670,671,672,0,673]
private def sixMenuAtP38 : Array Nat := #[559,559,16,16,674,675,676,16,16,16,16,16,16,16,677,678,559,57,679,16,680,575,681,16,360,0,16,0,307,16,53,682,678,0,683,16,16,16,16,16,16,16,663,16,16,4,3,18,524,684,559,685,16,16,16,16,559,0,16,0,686,687,688,689]
private def sixMenuAtP39 : Array Nat := #[690,691,691,691,692,691,691,693,694,695,696,697,698,0,51,16,51,16,16,16,36,16,16,16,16,699,700,701,702,697,703,691,0,704,705,691,706,707,693,708,709,275,710,251,3,4,179,0,0,0,0,0,16,0,16,0,0,0,30,633,16,29,16,16]
private def sixMenuAtP40 : Array Nat := #[0,711,572,572,168,0,0,0,0,16,712,713,714,200,564,0,0,679,0,715,716,679,16,16,717,554,0,0,0,53,0,16,51,16,16,0,0,0,16,16,16,16,16,481,16,16,498,718,719,720,721,722,166,723,168,724,725,188,726,727,728,729,730,0]
private def sixMenuAtP41 : Array Nat := #[731,732,0,733,734,0,735,736,737,738,94,739,740,0,741,742,743,744,745,746,747,80,0,0,0,748,749,0,750,751,752,753,0,754,0,0,755,756,757,758,759,189,760,0,80,761,762,763,764,765,766,767,768,5,0,84,769,770,771,772,773,774,775,776]
private def sixMenuAtP42 : Array Nat := #[777,778,779,4,0,4,780,781,782,0,0,783,784,785,786,787,788,789,329,790,791,792,793,794,795,796,0,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,0,718,817,818,819,0,820,821,426,822,823,0,410,92,824,824,825]
private def sixMenuAtP43 : Array Nat := #[826,410,4,4,827,828,829,830,0,831,832,833,834,835,836,837,838,839,840,0,841,842,843,844,845,846,847,0,848,849,0,850,839,0,0,0,851,852,853,854,0,839,0,855,0,0,0,856,857,858,859,860,0,861,862,863,101,864,0,865,0,866,0,0]
private def sixMenuAtP44 : Array Nat := #[0,867,868,869,0,870,871,872,873,874,875,99,876,877,878,0,112,0,879,0,0,0,880,0,0,0,0,0,0,0,881,882,0,883,884,885,16,886,0,737,887,888,889,0,0,890,891,892,893,839,894,839,895,896,0,62,840,0,0,0,0,0,0,0]
private def sixMenuAtP45 : Array Nat := #[897,898,899,847,0,900,900,891,901,902,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,903,0,163,175,904,165,0,105,905,163,906,0,907,908,0,3,77,217,0,909,3,229,910,189,911,410,912,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP46 : Array Nat := #[0,913,0,914,0,0,0,0,0,0,0,0,0,845,915,916,112,917,0,112,918,0,0,236,0,0,0,0,0,0,0,919,0,0,0,4,4,920,0,0,274,702,0,691,913,691,845,112,4,410,691,0,0,691,691,0,0,0,0,3,691,912,921,691]
private def sixMenuAtP47 : Array Nat := #[912,0,691,0,16,16,922,475,16,923,115,924,16,478,16,16,50,925,50,926,927,928,929,28,28,0,930,360,130,931,314,932,933,934,16,50,935,936,937,341,938,939,50,50,0,940,941,0,12,942,0,13,0,16,0,0,0,0,0,0,0,3,943,179]
private def sixMenuAtP48 : Array Nat := #[0,413,944,332,16,16,418,0,0,0,945,946,423,947,36,16,948,16,16,0,949,390,949,0,16,16,16,0,0,0,16,0,0,0,16,307,16,0,423,950,16,0,16,0,36,951,423,18,137,188,952,0,360,85,0,953,423,307,0,388,423,0,954,85]
private def sixMenuAtP49 : Array Nat := #[0,0,0,0,0,0,955,16,956,16,475,957,958,158,16,16,158,959,960,16,0,12,961,0,105,962,200,963,0,916,523,545,16,16,114,115,964,50,965,966,16,16,0,16,16,0,16,0,922,967,0,123,968,0,50,0,474,0,969,0,970,0,969,970]
private def sixMenuAtP50 : Array Nat := #[16,16,16,16,28,115,115,0,16,971,158,16,972,973,560,314,16,16,0,16,16,974,975,960,16,16,16,16,0,16,976,977,0,16,0,978,979,0,50,960,16,545,980,50,691,981,973,16,16,16,16,16,16,16,16,16,16,0,0,0,16,0,16,0]
private def sixMenuAtP51 : Array Nat := #[16,0,16,16,153,982,28,983,984,158,158,985,16,16,0,200,0,153,0,126,0,360,986,987,130,988,989,0,0,0,990,991,992,992,16,16,115,0,971,158,16,993,994,626,314,16,16,16,16,16,16,0,360,985,985,995,996,0,997,360,0,998,991,217]
private def sixMenuAtP52 : Array Nat := #[163,3,3,999,12,1000,16,16,16,1001,1002,50,3,0,1003,1004,1005,1006,3,943,3,3,16,1007,1008,16,1009,16,16,16,1010,16,16,16,16,16,212,1011,1006,1012,1013,0,50,1014,1015,165,165,165,1016,691,1016,691,1017,1018,554,105,163,16,200,1019,0,0,16,16]
private def sixMenuAtP53 : Array Nat := #[16,1015,0,0,12,0,1020,1021,0,914,84,691,165,0,1022,190,691,691,13,0,115,691,115,181,1016,0,0,0,0,0,0,0,0,410,65,0,29,16,16,0,0,1005,1023,1023,1023,1024,165,165,165,16,16,1025,1026,1027,165,1028,165,0,16,0,1016,992,16,999]
private def sixMenuAtP54 : Array Nat := #[16,53,16,179,0,0,0,970,1029,1030,16,16,16,16,1031,165,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1033,202,0,1047,1048,1049,1050,1051,1052,105,1053,204,4,1054,1055,179,1056,1057,1058,1059,691,1060,1061,1062,1063,1064,1065,558,1066,1067,1068,1069,1070]
private def sixMenuAtP55 : Array Nat := #[1071,1072,1073,1074,1075,211,213,1076,4,1077,179,1078,1079,0,426,1017,0,1080,1081,1082,1083,558,1084,1085,1086,1087,1088,1089,295,1090,222,1091,1092,1093,1094,228,295,1095,1089,3,1089,3,1096,1097,1098,16,1099,1100,1101,165,1102,16,1103,3,16,16,16,1104,1105,1106,1107,16,1108,50]
private def sixMenuAtP56 : Array Nat := #[309,16,1109,1110,1111,1112,1113,331,16,29,16,1114,28,1115,1116,0,1117,1118,1119,1120,16,1121,0,3,1122,1123,16,1124,559,16,0,1125,16,50,1126,16,1127,1128,1129,0,0,1130,1131,13,378,1132,1133,1134,446,1135,1136,1137,1138,13,1139,1140,1141,16,1142,1143,1144,1145,1146,1147]
private def sixMenuAtP57 : Array Nat := #[1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,403,1159,1160,1161,1162,1163,1164,1165,402,0,1166,1167,1168,1169,1170,1171,1172,217,1173,16,16,16,16,16,1174,1175,85,0,179,0,179,217,1176,1177,1178,0,65,1179,16,28,0,1180,16,1181,65,1182,16,16,16,1183,115,0,1184]
private def sixMenuAtP58 : Array Nat := #[1185,16,16,16,16,1186,1187,360,16,16,36,16,36,1188,1189,18,18,1190,360,1191,1192,36,1193,16,16,16,0,16,28,1194,1195,1196,16,16,16,423,423,307,1197,388,1198,388,1198,16,16,16,16,16,0,0,16,1199,36,1200,1201,1202,307,307,1203,1204,1205,1206,1207,36]
private def sixMenuAtP59 : Array Nat := #[1208,1209,949,1210,423,423,28,16,0,16,16,1167,307,307,1211,36,307,341,1212,1213,1214,16,1215,1216,1215,1217,1218,1219,1220,423,1221,217,300,1222,364,1141,953,423,1223,16,1224,364,1225,16,1226,16,16,1196,16,1227,1228,1229,217,307,217,307,0,558,454,200,1230,0,1231,165]
private def sixMenuAtP60 : Array Nat := #[153,0,1230,4,0,1232,1233,1234,1235,1236,16,1237,1125,16,1108,1233,1238,3,1239,16,959,16,1240,1241,845,1242,695,1243,1244,1245,1246,1247,1248,1249,1250,554,1251,1252,1253,3,1254,1255,1256,292,1257,402,1258,1259,1260,1261,293,1262,293,402,1263,1264,1265,16,1266,1266,1267,1268,1269,1270]
private def sixMenuAtP61 : Array Nat := #[200,16,16,16,526,16,16,16,1271,295,1272,3,298,1273,16,123,16,16,16,16,16,1274,340,115,16,530,16,1275,340,536,530,1273,1276,1277,474,474,1278,1279,1280,1281,1282,16,123,1115,16,16,1283,16,16,530,519,50,1284,478,1285,1286,1287,1288,16,1289,1290,418,1291,3]
private def sixMenuAtP62 : Array Nat := #[1292,16,123,16,551,16,1293,16,1294,551,16,1295,474,16,16,16,16,16,16,695,0,16,16,1296,51,16,1297,1245,200,4,1298,1299,16,1300,16,16,105,1301,115,1302,1303,3,3,3,3,16,16,16,16,16,1304,1305,1306,16,1307,16,16,16,1308,1309,1310,1311,16,341]
private def sixMenuAtP63 : Array Nat := #[16,1312,1313,1314,16,16,1311,1315,1316,1315,1317,200,1318,1319,16,1320,1321,1265,1322,1323,1324,1325,16,16,16,28,16,1266,1326,50,1327,1328,123,968,1231,3,1311,50,16,16,16,16,16,16,16,340,16,16,16,0,28,16,16,16,16,0,16,16,16,16,0,16,16,1329]
private def sixMenuAtP64 : Array Nat := #[1330,1331,1332,1105,1333,1334,16,414,16,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1337,1345,1346,1347,1348,200,1349,16,1350,1351,1352,1353,1354,1355,165,1356,1357,1358,330,1359,1360,1361,1362,1363,153,331,16,333,28,335,1364,16,158,1115,1115,360,1365,1366,158,1367,1368,1367,1369,423,1370]
private def sixMenuAtP65 : Array Nat := #[1371,423,1370,1372,438,0,16,28,0,1373,1374,16,1375,419,1376,414,158,16,16,626,1377,1378,1379,414,16,16,16,1380,1381,602,28,1382,1325,28,16,16,16,1383,1384,606,16,29,1385,1385,1386,1387,1388,1389,16,1390,16,1385,0,0,1391,1392,1393,1394,3,1395,1396,1397,1398,1399]
private def sixMenuAtP66 : Array Nat := #[1400,1401,3,16,1402,913,1403,1404,1405,1406,1407,1408,1409,1410,1411,641,1412,1413,1414,1415,1416,448,0,217,1417,1418,360,16,1419,16,1420,16,1421,1422,551,16,1423,448,1420,1424,551,0,0,1404,665,0,217,217,1425,153,1426,1427,1428,1429,360,669,673,16,1430,16,16,1431,1432,681]
private def sixMenuAtP67 : Array Nat := #[360,681,360,16,16,16,1433,1434,1435,520,341,1436,1437,1438,1439,50,16,16,16,16,16,1440,1441,1442,16,153,1443,360,1444,1445,1446,1447,1448,1449,1450,1451,1446,16,1452,1453,1454,1455,1089,3,1456,1457,1458,1459,1460,688,689,217,217,1461,16,115,1462,200,1463,1464,1289,1465,16,1466]
private def sixMenuAtP68 : Array Nat := #[1289,1467,1468,1469,1470,1471,520,1472,360,1467,1473,1474,1475,1476,28,16,1477,307,1478,1479,16,50,16,1480,1027,16,16,1481,153,1482,1483,1484,16,520,1485,341,1486,16,1487,1488,1489,1490,80,1491,1492,1493,1494,1495,0,1496,1497,1498,1499,1500,1501,1502,1503,1504,0,1505,1506,1507,1508,1509]
private def sixMenuAtP69 : Array Nat := #[1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,0,1523,1524,1525,1526,1527,16,1528,0,1529,0,1530,1531,0,1532,1533,1534,1535,1536,0,1537,1016,16,1538,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP70 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP71 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1539,1540,179,0,1541,0,0,1541,0,0,0,1542,180,0,179,1543,16,0,179,0,0,0,16,16,16,307,16,0,1544,16,307,341]
private def sixMenuAtP72 : Array Nat := #[334,1545,1546,179,0,0,0,1547,163,517,1269,16,922,123,1548,16,115,0,691,3,16,16,158,1549,16,1550,16,16,16,16,0,200,1551,691,158,1115,158,16,1552,16,1553,0,3,3,1547,179,1554,0,3,1016,0,16,16,1555,16,614,0,0,0,0,0,179,0,0]
private def sixMenuAtP73 : Array Nat := #[314,0,16,1556,372,179,0,16,374,1017,1557,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAt : Array (Array Nat) := #[sixMenuAtP0,sixMenuAtP1,sixMenuAtP2,sixMenuAtP3,sixMenuAtP4,sixMenuAtP5,sixMenuAtP6,sixMenuAtP7,sixMenuAtP8,sixMenuAtP9,sixMenuAtP10,sixMenuAtP11,sixMenuAtP12,sixMenuAtP13,sixMenuAtP14,sixMenuAtP15,sixMenuAtP16,sixMenuAtP17,sixMenuAtP18,sixMenuAtP19,sixMenuAtP20,sixMenuAtP21,sixMenuAtP22,sixMenuAtP23,sixMenuAtP24,sixMenuAtP25,sixMenuAtP26,sixMenuAtP27,sixMenuAtP28,sixMenuAtP29,sixMenuAtP30,sixMenuAtP31,sixMenuAtP32,sixMenuAtP33,sixMenuAtP34,sixMenuAtP35,sixMenuAtP36,sixMenuAtP37,sixMenuAtP38,sixMenuAtP39,sixMenuAtP40,sixMenuAtP41,sixMenuAtP42,sixMenuAtP43,sixMenuAtP44,sixMenuAtP45,sixMenuAtP46,sixMenuAtP47,sixMenuAtP48,sixMenuAtP49,sixMenuAtP50,sixMenuAtP51,sixMenuAtP52,sixMenuAtP53,sixMenuAtP54,sixMenuAtP55,sixMenuAtP56,sixMenuAtP57,sixMenuAtP58,sixMenuAtP59,sixMenuAtP60,sixMenuAtP61,sixMenuAtP62,sixMenuAtP63,sixMenuAtP64,sixMenuAtP65,sixMenuAtP66,sixMenuAtP67,sixMenuAtP68,sixMenuAtP69,sixMenuAtP70,sixMenuAtP71,sixMenuAtP72,sixMenuAtP73]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def hotSix : Array Sig := #[(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0x0])),(BitVec.ofNat 512 (word80 [0xffaaffaa,0xffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaa])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffff,0xffffffffffffffffffff,0xffffffffaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xffffffff,0xaaaaaaaaffffffffaaaa,0xaaaaffffffffaaaaaaaa,0xffffffffaaaaaaaaffff,0xffffaaaaaaaaffffffff,0xaaaaaaaaffffffffaaaa,0xaaaaffffffffaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffff0000,0xffffffffffffffff,0xffffffff00000000ffff,0xffffffffffffffffffff,0xffffffffffff,0xffffffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffff00ff00ff00ff00,0xff00ff00ff00ff00ffff,0xffffffffffffffffffff,0xffffffffff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffff00000000,0xffffffff00000000ffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffaaaaaaaaaaaa,0xaaaaffffffffffffffff,0xaaaaaaaaaaaaaaaaffff,0xffffffffffffaaaaaaaa,0xaaaaaaaaffffffffffff,0xffffaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffff00ff00ff00,0xff00ffffffffffffffff,0xff00ff00ff00ff00ffff,0xffffffffffffff00ff00,0xff00ff00ffffffffffff,0xffffff00ff00ff00ff00]))]
private def hotTry : Array Nat := #[11,16,16,16,16,16,16,16,16,16,4,13,16,16,16,16,16,14,16,16,16,16,0,8,5,16,16,16,16,16,16,16,16,16,16,16,16,15,16,16,16,16,16,16,3,16,16,16,16,16,16,10,16,16,16,9,16,16,16,16,16,16,1,16,16,16,16,16,16,16,16,16,16,2,16,16,7,12,16,16,6,16,16]
private def paidSix0 : Array Nat := #[5,1410334785,1410334785,5,5,1410334785,1145406480,18088196,289476612,1410334785,1145406480,18088196,1145406480,289476612,2488287312,289476612,85542144,1477788736,18088196,2488287312,18088196,1699811392,18088196,356930560,2488287312,1367429136,1096040720,85542144,1096040720,1096040720,85542144,1477788736,6,1477788736,1410334785,18088196,5,1477788736,356930560,1145406480,289476612,307564800,1212844048,1367429136,1145406480,1699811392,1367429136,356930560,5,1145406480,1410334785,289476612,1699811392,2488287312,1145406480,307564800,1477788736,85542144,1145406480,17039621,356930560,1145406480,1409614913,2821014656]
private def paidSix1 : Array Nat := #[2821014664,1413480529,85542144,1145406480,1409286213,1699811392,2488287312,18088196,2858750336,85542144,289476612,1430261825,1477788736,1145406480,307564800,1477788736,291067136,18088196,356930560,85476612,1419089168,274010372,356930560,85525768,2839613572,2824880272,9,1426133057,1430541377,356930560,1409286213,307564800,1410663489,1145406480,1145406480,1435800848,2509542480,2488287312,84215044,1096369424,85542144,17039621,1367429136,1478133824,16860421,290803984,1212844048,1477788736,2223342624,1145406480,1477788736,274109712,1145406480,1410334789,1096024344,1444500752,1163412752,4263941,1096123664,1699811392,676926784,1381257488,1414545489,2241172560]
private def paidSix2 : Array Nat := #[1145406480,1477788736,627594560,1145406480,103368192,1410334789,89474320,627467776,1163203656,1477788740,82949,1145406480,4526341,1477788736,1452430608,1699811392,1637241936,2836747344,2840876112,2824880280,1448629520,1145406480,84165892,2223342624,1367429136,1096040720,2772853792,359220560,1431375940,16860421,82949,290870528,307564800,1146438928,1418023952,1368674576,4526341,1112887568,2858750336,357963008,1364529424,1359631632,307499272,85542144,2825147728,2438025296,1381257488,2438218064,1431322960,1699811392,1477788736,85542144,1096040720,85542144,642797904,85280004,2589332880,2573288784,646341634,1481720912,2438218064,16860421,290525444,1414807888]
private def paidSix3 : Array Nat := #[356815892,18088196,358176000,17039621,2488287312,1410679873,103368192,1477788736,35127812,358159616,1477788736,1698762820,303370504,36176388,1212844048,442783040,705779008,1498502208,370496768,1367429136,1410334789,1699811400,1145406480,18088196,2488287316,2488287312,1094975764,1427374404,290787589,2223342624,1163203652,1112970512,1146438928,1376359696,1247352128,1418023952,1145406484,17039621,1409286213,2505134160,356865028,1427181633,103368192,5,356930568,1452692752,93476112,1364283664,630608976,1364529424,1431704640,2505117776,2438025296,1230312516,1096040720,1145406480,1481917520,1145406480,1367429136,2823128208,103368192,2492765520,1430361104,1699762256]
private def paidSix4 : Array Nat := #[357848324,2504344912,2223342624,2523292800,1717151808,2241107280,1181242704,2824880272,1364283664,1212844048,1166365712,1410942272,1367429144,356930560,18088196,289476612,289476612,1477788736,307564800,1699811392,307564800,1699811392,307564800,36176388,1145406484,1177113936,289476613,1754612896,292115792,1149572116,2821014664,1770612752,89490704,1415222544,2241156177,1096024340,1428505924,1410334789,1427195201,1431322960,1431589953,2839958656,1435521104,1427526728,1432686916,17039621,1145406484,1096040720,2488287312,676926784,357127424,2242463264,2573550928,1414529105,2504361296,21054741,1368723728,356930560,1431393556,1367429136,1452430608,1419089168,1481720912,1426392388]
private def paidSix5 : Array Nat := #[1430410256,1487226016,1096369424,1435570256,1637241936,361256208,358159616,2824880276,1498747968,2836747344,1431310401,85542144,1427395860,1444500752,290722052,1163412752,1409286213,356930568,1715885376,1751471424,1163166992,356930560,85214468,1163166992,1419089168,710256896,85263620,1435800848,1715819840,1381060880,1145406480,1426149457,2589475472,1363514384,1145406480,356930560,2241172560,1363514384,1414825040,2509542480,1629573456,1629573456,1359631632,1699811400,2173993248,2173993248,106255616,1435521108,1181046080,1410334789,2504347984,1166365712,1145406488,1477788744,1145406484,1410334785,1096040720,308875776,1409286213,580264192,1145406480,289476612,1367429136,1367429136]
private def paidSix6 : Array Nat := #[1652711440,307564800,1367429136,356930560,1435521104,1114128912,1096040720,1430623248,1096123664,1778750800,1700405828,2823444560,2823444560,289476613,2573550928,1231426897,2757380240,2821014660,2821014664,2824880280,1498502208,363226632,1763005520,352982280,1363497236,1477788740,2488287316,4210709,356668420,16860421,420562244,1096040724,424956996,289673476,1477788740,1096040724,1699042372,1212844052,1376359696,1112970512,1212844048,1478133824,274109712,1699913824,356930568,85542152,1231440400,307564800,85017860,2489993360,1365853520,1100633360,85542144,1427703108,89474320,1162940504,1163203656,2236682324,1230312516,1431375940,307499268,303370500,2689929552,85525764]
private def paidSix7 : Array Nat := #[580264194,1179223568,1427112257,2856945296,646341632,1181058576,356930560,36176388,2488616016,2820669569,2820669569,110204176,357848132,373593360,1431322964,2451657040,705779008,2451657040,1448624720,93476112,2488287312,2838054272,1652711442,1652711442,1448362576,1162167568,1448153408,2492498016,2223342624,1212844048,2441187360,67453957,85542144,2492498016,2492498016,1359057940,1434735632,1704568896,560603652,1616187716,1426392385,356930568,1695633488,2689929552,1427719488,17039621,1368674576,1091846420,2723434832,1448415552,564732420,85542148,1096040724,274010372,307564800,2223342624,1145406488,85542144,356930560,18088197,307564800,424318976,152733952,2441187360]
private def paidSix8 : Array Nat := #[1367429144,4263941,356930560,356930560,18088197,2173993248,2492498016,1145406484,307564800,2223342624,356930560]
private def allSixPaid : Array (Array Nat) := #[paidSix0,paidSix1,paidSix2,paidSix3,paidSix4,paidSix5,paidSix6,paidSix7,paidSix8]
private def selectedRows (t : Nat) := cubRows (atSix sixWords (t % 523))
private def literalCost (t : Nat) (w : Sig) := sixCost (readSix (selectedRows t) w)
private def paidWeight (t j : Nat) := (atSix allSixPaid (t % 523) >>> (2*j)) % 4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem hot_weight : ∀ i : Fin 523, ∀ j : Fin 16,
    paidWeight i.val j.val = literalCost i.val (hotSix[j.val]?.getD zero) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem hot_goal : ∀ i : Fin 523, literalCost i.val (chartGoal 251) = 3 := by decide +kernel
private def quickWeight (t : Nat) (w : Sig) :=
  let j := hotTry[w.toNat % 83]?.getD 16
  if j < 16 ∧ w = hotSix[j]?.getD zero then paidWeight t j else literalCost t w
private theorem quickWeight_eq (t : Nat) (w : Sig) : quickWeight t w = literalCost t w := by
  unfold quickWeight
  split
  next h =>
    let j := hotTry[w.toNat % 83]?.getD 16
    have e := hot_weight ⟨t % 523,Nat.mod_lt _ (by decide)⟩ ⟨j,h.1⟩
    calc
      paidWeight t j = literalCost t (hotSix[j]?.getD zero) := by
        simpa only [paidWeight,literalCost,selectedRows,Nat.mod_mod] using e
      _ = literalCost t w := congrArg (literalCost t) h.2.symm
  next => rfl
private def goalWeight (t : Nat) (T : Sig) := if T = chartGoal 251 then 3 else literalCost t T
private theorem goalWeight_eq (t : Nat) (T : Sig) : goalWeight t T = literalCost t T := by
  unfold goalWeight
  split
  next h =>
    rw [h]
    have e := hot_goal ⟨t % 523,Nat.mod_lt _ (by decide)⟩
    simpa only [literalCost,selectedRows,Nat.mod_mod] using e.symm
  next => rfl
private def fitsWeight (t : Nat) : Nat → List Sig → Bool
  | _,[] => true
  | b,v::vs =>
    let z := quickWeight t v
    if z ≤ b then fitsWeight t (b-z) vs else false
private theorem fitsWeight_le (t : Nat) (xs : List Sig) (b : Nat) (nd : xs.Nodup)
    (h : fitsWeight t b xs=true) : (∑ w ∈ xs.toFinset, literalCost t w) ≤ b := by
  induction xs generalizing b with
  | nil => simp
  | cons v vs ih =>
    have splitNd := List.nodup_cons.mp nd
    have absent : v ∉ vs.toFinset := by simpa only [List.mem_toFinset] using splitNd.1
    simp only [fitsWeight] at h
    split at h
    next bound =>
      have rest := ih (b - quickWeight t v) splitNd.2 h
      rw [List.toFinset_cons, Finset.sum_insert absent]
      rw [quickWeight_eq] at bound rest
      omega
    next => contradiction
private def enoughWeight (t : Nat) (T : Sig) (xs : List Sig) :=
  let cap := goalWeight t T
  decide (0 < cap) && fitsWeight t (cap-1) xs
def closeSix (T : Sig) (k : Nat) (marks : List Nat) (ws : List Sig) : List (List Sig) :=
  if marks.isEmpty then [] else
    if ws.length = k+1 ∧ marks.any (fun t => enoughWeight t T ws) = true ∧ ws.Nodup then [ws] else []
theorem closeSix_sound {T k marks ws xs} (h : xs ∈ closeSix T k marks ws) (u : Bool) :
    Impossible u T k xs.toFinset := by
  unfold closeSix at h
  split at h
  next => simp at h
  next =>
    split at h
    next yes =>
      obtain ⟨t,_,valid⟩ := List.any_eq_true.mp yes.2.1
      have same : xs=ws := by simpa only [List.mem_singleton] using h
      subst xs
      apply six_cut (selectedRows t)
      · rwa [List.toFinset_card_of_nodup yes.2.2]
      · simp only [enoughWeight,Bool.and_eq_true,decide_eq_true_eq] at valid
        have sumBound := fitsWeight_le t ws _ yes.2.2 valid.2
        rw [goalWeight_eq] at valid sumBound
        change (∑ w ∈ ws.toFinset, literalCost t w) < literalCost t T
        omega
    next => simp at h


end PEqualNP.Outside.L_meta_33242

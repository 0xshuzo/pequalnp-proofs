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

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
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

def inlineSix (T : Sig) (k : Nat) (ws : List Sig) (word : Nat) : Bool :=
  let S := ws.toFinset
  let r := cubRows word
  decide (S.card = k+1) && decide ((∑ v ∈ S, sixCost (readSix r v)) < sixCost (readSix r T))

theorem inlineSix_sound {T k ws word} (ok : inlineSix T k ws word=true) (u : Bool) :
    Impossible u T k ws.toFinset := by
  simp only [inlineSix,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact six_cut (cubRows word) ok.1 ok.2

def closeSix (T : Sig) (k : Nat) (marks : List Nat) (ws : List Sig) : List (List Sig) :=
  if marks.any (inlineSix T k ws) then [ws] else []

theorem closeSix_sound {T k marks ws xs} (h : xs ∈ closeSix T k marks ws) (u : Bool) :
    Impossible u T k xs.toFinset := by
  unfold closeSix at h
  split at h
  next e =>
    obtain ⟨word,_,hw⟩ := List.any_eq_true.mp e
    have same : xs=ws := by simpa only [List.mem_singleton] using h
    subst xs
    exact inlineSix_sound hw u
  next => simp at h

private def sixWordsP0 : Array Nat := #[123567819853842,81475698442320,73748934836304,123567819919635,73748936941680,123567820380186,53957963702370,167237839388802,81475700547696,44122735970313,53957959491618,123386626326600,159511075782786,176068426367106,79445083883529,61684723097634,193995892359360,44019254108193,176482358026338,176482353815586,150089779709961,211692496109640,79203626205249,176508124012584,108071074930728,108041009700897,123356561096769,149572370399361,123567819849746,71506927829064,61684727308386,36322555732008,123356561228355,21178538266704,108234787586835,176478058782753,141875672023176,10479862808961,176094196564104,108234788047386,123902030266560,28905301872720,44122736101899,29240548393602,123386626458186,211416544477320,176064131334273,246713122193538,142423263543561,211662430879809,213727272009888,141978752811168,142116193861824,88382910959891,81652730628105,10067539656993,211662431011395,12176285786224,150089779841547,12206467997808,149842957467840,211692496241226,71778567717129,46226900852769]
private def sixWordsP1 : Array Nat := #[143083649925280,73986214593035,36456219803913,36971623743873,21101465846370,144117681119344,10204980707649,21513784787586,123292942473242,74089295282336,143625860170338,151780017143937,142526348542562,54357915599169,142526344331553,143082576183456,108715831206048,81652730759691,79445084015115,176069500108930,36870147277065,151844444725360,143018169491568,149705516417184,79212249809473,12275190612066,213594125992065,123292942012691,12206465892432,73986214593291,36870147285032,72054519382088,27599866847330,108234787520530,74089295251496,74089295249697,88382911420442,144083318767752,81785876676768,54357915730755,71506927960650,81411273081411,81652732690592,36456219935499,12245008400482,142526344333352,81411273065027,246773252686611,79749095375040,81411281264800,72054519365897,73714574688842,46497483817089,211386479247489,149572370399265,28695087562882,107135276419610,73986214469672,142423263675147,141978752780328,211588881058330,10583344679048,10584948998433,144323840606400]
private def sixWordsP2 : Array Nat := #[10721320503432,10722390049089,10722390050888,10584949000232,123434675867666,142397497565282,114767431796745,71549878026320,12516644094241,79212249825345,71950903804434,107135275893266,74501618409632,176508124004617,176094196531465,141875671998504,211588880597779,213727271979048,37942856786080,10479862816928,10037357478048,108041010184328,144186403733602,73986214461705,12275186401569,211284474216520,73714574590088,144186399524904,73714574565416,152050604212416,142663785513795,12412627583555,143083647862793,176064131334153,79276641632336,27969636534344,54357915600968,71950904330778,53957959516290,114771726794881,28828229452386,46226900877441,108105435712026,62054496995400,71778567716873,10204980839235,81441206591600,10067539689632,12412627583811,81544416952449,81956733788193,54357915631808,61783910979609,81411272949825,81652730757643,79445083881481,151913163129121,213624191221896,141875673075864,36322556784696,71549913686128,142116227416256,36322555871818,21101461635618]
private def sixWordsP3 : Array Nat := #[71515551449160,73714574705226,36837951815752,44019254100001,27569684635746,71506927820840,27599866855554,21513784803520,213594127992872,176508124136203,108041018017928,46226909184192,176094196663051,108096811762451,37866043869722,62054497026240,79203626336835,151844442619984,149572403953793,10583344677249,213624190738465,36322555756680,10721320501633,12245004222624,10479862825152,10174798528704,71506927845512,71515551433288,28695087562944,10037357447208,142663785384008,54117394813209,81785876644129,151913167339618,44668205140104,107238891470920,36456219836552,142116193830984,36844381298786,37702330745097,149572370399297,149842957467713,107238891462696,176237541072936,38530202501256,211416544444681,176478058922563,211416578031752,107616319570305,28828225241634,108715831198338,38071135371906,142663785382209,61783909926921,167750953666569,74229978513600,150089780762649,38530202476584,176478059835441,72022331769024,39045606416544,79445083884041,149645384908930,123356561096713]
private def sixWordsP4 : Array Nat := #[12516644126880,108715822876681,176094196563977,81652730634273,44536663443465,88547193782537,10037361656418,44289841299777,71549911580752,37465051119696,36322555740232,143018167386192,36972697485697,141875672006728,149572370514497,44289841332416,108105435251475,44122735970825,81785876645928,12412625387680,108041009725569,108234787521042,176478058782729,27969636532545,12176283680848,38801842372873,53957963694178,123469035606034,10449680605344,10479863861649,150779658928258,10449680599176,28244518635656,54531321233673,54357915732554,27599866830882,36971624798360,211662430879753,108041010159656,10449680613568,12928967248008,108071074496641,12275186434208,10204980740288,10722390180675,144117679013968,10067540709681,45640470110242,10584950051121,54117393760521,159511075758114,142526345386040,44123809712137,72294005211521,175999442640994,39317246312833,37110669247299,142423263551528,28141036765569,142397493354530,142423264604216,36870148329753,149705516417057,36870148337720]
private def sixWordsP5 : Array Nat := #[123902030250626,38217734685057,36837959665800,142423264596249,143048351703152,211692496241194,71778567848715,12687509553537,72054519497483,71778567749768,142423263691338,71506927944266,72054519513674,38770720669832,73817661638792,74089301543048,79749128929472,71778567848459,213727271977249,141875672137800,143358527799585,37702330777736,176508124020808,211416544576267,79453707504137,79212249825857,81644140825099,21178540372080,141978753863856,54499134673072,123291868205074,159639927787696,159639926767776,193729600323714,159536845979784,193755370520712,159536846999704,44564723277984,176094197616792,246708827160705,141875672138314,53983730733112,176508125065272,61680429117489,81652732659752,88172197316744,80953693176097,123902022517259,141918621302914,123253481881665,88650272540681,123386626326537,81411273065025,53957959508002,123356569419968,211386512801825,81411281258632,149572374519906,108062485020808,123356561227841,71506927960136,114831857353491,36971623744130,74149927586330]
private def sixWordsP6 : Array Nat := #[96869095120929,21101461637160,96869095145601,159511079968866,38347087020417,71787191337483,81644140694025,74089293709448,74501610545192,73986222334112,193995892359240,108041009692705,29240548393345,28828225241377,176478058774561,211386512801921,44019287662625,176508124012553,108586478870688,71890773418018,211692496109577,12516644096040,213594126426152,71515551433290,27728714666289,10174798497864,12275190596130,108071074471969,27569684512898,27599866724482,27569684512960,27599866724544,141978756989538,149705520595554,12382443176096,10067543868002,142047741743264,149641359331457,73744625197168,12240707781410,82198191480865,96869095276674,81785874645121,27599862636578,36322555871304,73817653805192,152050602082593,38770728503432,176508124152362,82198193504545,108039935959073,61680429109297,141944660955272,176163185496200,36322555748424,108071074922761,39045606424768,36456219935243,10449680597128,108170370353288,12657327341953,193995892359233,167237839388706,89142339838112]
private def sixWordsP7 : Array Nat := #[12206467989584,10479896363393,81956742105224,73714582429856,44019254124577,88382910894098,144083318743080,150222929936994,74229970640936,10037357445160,150222925725736,73986214494344,159511075782690,44027877728289,36322555863080,246713124159648,44122735968265,81652730626057,81644140825097,53983730741304,176482353807394,176551345938530,167366690373792,28141037818001,27728714666033,54117394812953,28110855606424,141875705577608,246773253147162,44092541263970,27698532454456,12382445371978,79453707504139,36837959671968,46772370022560,61783910977561]
private def sixWords : Array (Array Nat) := #[sixWordsP0,sixWordsP1,sixWordsP2,sixWordsP3,sixWordsP4,sixWordsP5,sixWordsP6,sixWordsP7]
private def sixMenuStartsP0 : Array Nat := #[0,1,17,34,66,97,114,146,177,193,211,258,289,306,338,370,402,434,466,498,530,562,595,642,674,708,771,818,850,882,913,930,962,993,1010,1042,1073,1090,1121,1137,1154,1185,1202,1235,1282,1316,1379,1425,1442,1474,1505,1522,1554,1585,1602,1633,1649,1665,1682,1713,1729,1745,1762,1794]
private def sixMenuStartsP1 : Array Nat := #[1825,1842,1874,1905,1924,1985,2001,2017,2036,2098,2129,2146,2178,2209,2225,2242,2273,2290,2321,2338,2370,2402,2435,2482,2513,2529,2545,2565,2641,2662,2754,2789,2869,2950,3045,3125,3205,3284,3349,3428,3491,3539,3589,3666,3699,3749,3827,3878,3972,4036,4100,4163,4214,4308,4372,4434,4469,4550,4643,4691,4740,4803,4851,4901]
private def sixMenuStartsP2 : Array Nat := #[4979,5029,5106,5137,5155,5205,5283,5331,5378,5411,5459,5507,5555,5602,5633,5649,5665,5684,5745,5762,5796,5859,5907,5955,6001,6017,6033,6052,6117,6193,6210,6242,6280,6404,6468,6529,6545,6563,6610,6643,6693,6770,6802,6835,6885,6961,6979,7026,7061,7141,7223,7337,7475,7523,7571,7617,7634,7668,7730,7765,7842,7877,7955,8005]
private def sixMenuStartsP3 : Array Nat := #[8085,8162,8194,8226,8258,8291,8339,8387,8434,8465,8484,8546,8577,8594,8626,8657,8674,8707,8754,8786,8819,8869,8946,8978,9009,9028,9097,9234,9268,9333,9412,9474,9506,9537,9557,9634,9666,9697,9716,9778,9810,9847,9955,10001,10018,10049,10066,10098,10134,10236,10424,10549,10628,10696,10823,10930,10964,11030,11125,11202,11237,11316,11379,11427]
private def sixMenuStartsP4 : Array Nat := #[11476,11542,11635,11682,11715,11762,11796,11858,11891,11939,11986,12020,12083,12132,12194,12226,12258,12291,12339,12386,12419,12466,12499,12553,12695,12806,12908,13095,13201,13221,13299,13346,13381,13458,13492,13554,13586,13619,13666,13698,13730,13767,13878,13975,14085,14166,14259,14313,14456,14583,14692,14759,14868,14933,15013,15094,15186,15219,15268,15331,15379,15428,15491,15539]
private def sixMenuStartsP5 : Array Nat := #[15587,15634,15666,15699,15747,15794,15826,15859,15906,15940,16003,16052,16116,16179,16226,16260,16325,16404,16466,16499,16546,16578,16612,16674,16707,16755,16802,16834,16867,16914,16949,17029,17109,17188,17253,17332,17395,17447,17556,17617,17635,17683,17731,17779,17827,17875,17923,17972,18035,18084,18147,18195,18243,18291,18338,18370,18406,18500,18565,18643,18691,18738,18775,18883]
private def sixMenuStartsP6 : Array Nat := #[18933,19012,19075,19122,19155,19202,19235,19282,19314,19346,19379,19427,19474,19508,19570,19602,19636,19698,19732,19794,19826,19860,19925,20003,20050,20082,20114,20146,20178,20211,20258,20292,20354,20385,20404,20467,20514,20545,20562,20594,20627,20675,20723,20772,20835,20883,20929,20947,20996,21060,21122,21155,21203,21253,21331,21377,21394,21428,21489,21506,21540,21602,21634,21666]
private def sixMenuStartsP7 : Array Nat := #[21698,21730,21762,21795,21842,21874,21909,21987,22039,22153,22294,22391,22500,22568,22697,22837,22914,22946,22978,23010,23042,23075,23122,23154,23186,23220,23283,23331,23378,23418,23574,23667,23720,23848,23972,24036,24101,24180,24242,24274,24306,24339,24386,24418,24451,24499,24546,24578,24610,24642,24674,24705,24722,24756,24818,24850,24883,24932,24994,25028,25092,25155,25203,25253]
private def sixMenuStartsP8 : Array Nat := #[25331,25380,25442,25475,25523,25571,25617,25636,25701,25779,25827,25876,25939,25986,26018,26050,26083,26130,26162,26196,26260,26324,26388,26451,26498,26530,26563,26610,26642,26674,26707,26754,26786,26818,26850,26882,26913,26930,26963,27012,27074,27105,27122,27154,27188,27251,27298,27330,27362,27394,27425,27442,27474,27507,27554,27586,27619,27666,27699,27748,27812,27876,27938,27972]
private def sixMenuStartsP9 : Array Nat := #[28033,28050,28083,28131,28181,28258,28294,28387,28433,28449,28465,28481,28498,28532,28595,28645,28725,28803,28855,28961,28977,28997,29075,29122,29154,29186,29218,29251,29298,29330,29361,29378,29412,29476,29539,29588,29650,29682,29715,29766,29859,29906,29937,29957,30035,30083,30129,30146,30179,30226,30261,30339,30387,30436,30498,30532,30595,30644,30708,30770,30802,30834,30866,30898]
private def sixMenuStartsP10 : Array Nat := #[30930,30963,31011,31058,31090,31126,31220,31284,31348,31411,31460,31521,31537,31554,31586,31618,31651,31703,31813,31891,31938,31973,32056,32178,32212,32276,32338,32370,32404,32467,32516,32583,32694,32786,32819,32867,32914,32946,32978,33013,33089,33105,33121,33138,33169,33186,33222,33315,33364,33428,33490,33524,33586,33620,33682,33714,33746,33780,33842,33874,33905,33922,33954,33990]
private def sixMenuStartsP11 : Array Nat := #[34084,34148,34209,34225,34241,34258,34294,34385,34401,34418,34450,34483,34529,34547,34596,34661,34741,34820,34882,34916,34978,35011,35058,35090,35122,35158,35251,35299,35347,35396,35461,35540,35604,35667,35714,35745,35762,35793,35810,35841,35860,35926,36019,36065,36082,36116,36179,36227,36273,36290,36322,36353,36370,36401,36417,36433,36450,36481,36497,36513,36529,36548,36609,36626]
private def sixMenuStartsP12 : Array Nat := #[36659,36705,36722,36755,36801,36819,36865,36881,36897,36913,36929,36945,36962,36994,37027,37075,37124,37187,37235,37284,37347,37396,37460,37524,37587,37635,37681,37700,37762,37797,37876,37940,38003,38051,38098,38131,38179,38225,38243,38292,38354,38385,38403,38451,38497,38516,38579,38628,38692,38755,38803,38853,38930,38965,39043,39091,39140,39203,39249,39267,39316,39381,39461,39541]
private def sixMenuStartsP13 : Array Nat := #[39620,39684,39746,39779,39827,39875,39923,39971,40019,40068,40132,40196,40259,40307,40356,40420,40483,40531,40579,40627,40676,40738,40772,40835,40883,40931,40979,41028,41091,41139,41187,41235,41282,41314,41345,41362,41396,41459,41507,41555,41603,41650,41683,41729,41747,41796,41859,41907,41955,42001,42017,42033,42050,42081,42097,42113,42131,42179,42227,42275,42321,42339,42387,42435]
private def sixMenuStartsP14 : Array Nat := #[42483,42531,42584,42707,42758,42853,42932,42996,43060,43129,43270,43365,43445,43526,43618,43649,43668,43729,43749,43833,43973,44050,44084,44151,44259,44310,44404,44466,44497,44517,44599,44708,44775,44885,44963,45017,45158,45252,45314,45348,45412,45475,45523,45572,45638,45732,45794,45829,45908,45970,46004,46066,46100,46167,46277,46354,46390,46481,46501,46580,46642,46675,46723,46774]
private def sixMenuStartsP15 : Array Nat := #[46873,47012,47079,47190,47286,47379,47427,47475,47523,47571,47620,47686,47779,47832,47957,48041,48182,48277,48356,48418,48452,48517,48597,48679,48790,48886,48979,49027,49076,49139,49187,49235,49283,49332,49395,49446,49540,49606,49700,49766,49860,49924,49988,50053,50131,50183,50292,50355,50405,50482,50518,50610,50642,50679,50794,50950,51043,51091,51139,51188,51253,51334,51430,51527]
private def sixMenuStartsP16 : Array Nat := #[51635,51688,51812,51877,51957,52036,52097,52113,52130,52164,52227,52274,52307,52355,52403,52452,52515,52564,52627,52676,52739,52787,52835,52883,52931,52979,53030,53124,53188,53252,53316,53379,53429,53507,53555,53603,53652,53715,53763,53811,53859,53908,53971,54018,54050,54084,54149,54228,54294,54388,54452,54515,54563,54611,54665,54803,54851,54899,54948,55012,55077,55157,55237,55321]
private def sixMenuStartsP17 : Array Nat := #[55463,55572,55637,55715,55765,55846,55939,55991,56100,56166,56258,56293,56372,56436,56502,56596,56658,56692,56756,56819,56869,56947,56995,57044,57108,57173,57251,57300,57364,57427,57475,57523,57572,57635,57685,57762,57797,57877,57959,58070,58165,58243,58292,58355,58401,58418,58452,58515,58566,58661,58740,58803,58853,58931,58979,59028,59093,59171,59219,59267,59316,59380,59445,59524]
private def sixMenuStartsP18 : Array Nat := #[59587,59638,59735,59845,59924,59987,60036,60103,60213,60295,60406,60500,60563,60614,60711,60818,60854,60951,61059,61109,61189,61269,61347,61397,61476,61543,61660,61842,61877,61962,62119,62228,62295,62404,62470,62567,62679,62791,62898,62931,62978,63011,63060,63123,63171,63221,63300,63367,63479,63587,63635,63683,63732,63796,63858,63892,63955,64008,64134,64227,64276,64341,64419,64471]
private def sixMenuStartsP19 : Array Nat := #[64581,64662,64755,64805,64884,64948,65013,65093,65175,65283,65332,65395,65443,65491,65541,65624,65747,65796,65860,65926,66024,66149,66228,66292,66356,66420,66484,66549,66628,66692,66754,66787,66834,66866,66898,66930,66962,66996,67059,67107,67154,67188,67252,67315,67364,67430,67524,67588,67652,67715,67764,67827,67875,67925,68007,68116,68181,68261,68338,68372,68434,68467,68514,68547]
private def sixMenuStartsP20 : Array Nat := #[68595,68644,68707,68759,68870,68964,69027,69075,69124,69191,69300,69362,69397,69477,69555,69604,69671,69782,69876,69940,70004,70072,70197,70276,70339,70387,70436,70499,70553,70690,70724,70788,70855,70964,71030,71124,71191,71299,71351,71467,71637,71716,71785,71926,72023,72137,72278,72369,72388,72450,72484,72550,72645,72722,72754,72786,72822,72916,72983,73093,73173,73252,73314,73347]
private def sixMenuStartsP21 : Array Nat := #[73400,73523,73570,73607,73717,73797,73877,73955,74002,74034,74069,74149,74225,74245,74324,74386,74417,74433,74450,74482,74516,74579,74627,74673,74690,74724,74787,74836,74897,74914,74946,74980,75044,75108,75170,75204]
private def sixMenuStarts : Array (Array Nat) := #[sixMenuStartsP0,sixMenuStartsP1,sixMenuStartsP2,sixMenuStartsP3,sixMenuStartsP4,sixMenuStartsP5,sixMenuStartsP6,sixMenuStartsP7,sixMenuStartsP8,sixMenuStartsP9,sixMenuStartsP10,sixMenuStartsP11,sixMenuStartsP12,sixMenuStartsP13,sixMenuStartsP14,sixMenuStartsP15,sixMenuStartsP16,sixMenuStartsP17,sixMenuStartsP18,sixMenuStartsP19,sixMenuStartsP20,sixMenuStartsP21]
private def sixMenuWordsP0 : Array Nat := #[1,5,5,72,53,107,39,1,253,1,11,28,33,0,254,368,0,196,0,135,162,0,369,0,370,0,255,0,96,0,163,0,160,0,136,0,15,0,10,15,0,257,0,9,0,10,15,19,84,118,374,0,259,0,17,0,118,97,0,77,0,55,375,0]
private def sixMenuWordsP1 : Array Nat := #[106,0,376,22,0,73,77,99,0,57,10,0,261,17,66,377,89,119,8,29,44,70,8,44,198,378,39,379,34,380,137,106,194,106,364,76,194,365,159,65,366,194,367,195,40,20,160,161,28,160,160,0,20,255,371,256,55,88,89,108,88,372,109,9]
private def sixMenuWordsP2 : Array Nat := #[110,161,258,88,373,164,0,260,0,98,98,197,108,119,262,120,381,41,1,111,4,8,1,166,1,3,10,3,6,169,34,283,0,3,5,33,41,13,0,3,4,7,12,279,0,1,0,1,2,37,287,0,1,2,20,286,0,1,2,3,211,284,0,1]
private def sixMenuWordsP3 : Array Nat := #[2,7,278,0,3,5,7,57,0,3,7,57,136,0,1,2,3,0,1,4,126,148,0,1,84,213,0,6,30,0,37,287,0,3,15,214,295,7,293,0,3,18,0,6,15,129,217,0,114,218,0,2,4,55,221,408,0,2,9,303,0,1,15,161]
private def sixMenuWordsP4 : Array Nat := #[0,6,70,409,0,14,81,0,1,5,31,66,223,0,5,29,62,0,9,33,421,1,63,0,1,2,3,8,0,1,2,5,94,228,0,17,153,0,11,118,0,3,69,133,0,179,230,0,29,318,0,3,4,77,103,0,1,227,0,3,4,32,99,0]
private def sixMenuWordsP5 : Array Nat := #[182,15,0,3,30,0,5,10,95,329,0,22,235,0,24,232,0,3,0,18,73,0,4,234,0,31,233,0,31,445,1,4,460,4,165,1,2,11,263,11,120,165,8,11,165,382,1,11,263,2,138,139,138,139,264,138,139,383,1,2,8,200,8,11]
private def sixMenuWordsP6 : Array Nat := #[21,121,138,2,2,12,2,11,12,21,35,45,67,138,140,384,1,2,16,106,12,16,45,67,16,12,1,2,41,44,45,8,67,201,8,45,85,112,121,7,12,11,122,8,11,35,16,21,60,140,141,7,2,21,167,21,60,1,2,3,8,202,1,2]
private def sixMenuWordsP7 : Array Nat := #[3,11,16,3,8,10,30,46,78,167,3,5,10,24,40,73,76,86,386,61,68,168,2,6,10,2,3,53,46,6,21,3,6,10,68,5,73,5,16,23,73,86,1,2,8,11,38,113,387,23,53,107,8,24,45,86,203,8,16,24,73,142,1,3]
private def sixMenuWordsP8 : Array Nat := #[5,10,1,6,3,107,23,61,76,60,86,204,8,16,40,1,10,270,1,2,144,271,39,124,170,39,206,11,144,273,120,390,82,124,144,205,273,170,272,1,11,271,1,2,3,171,207,2,169,5,100,53,1,2,5,208,3,5,8,18,39,74,102,274]
private def sixMenuWordsP9 : Array Nat := #[394,53,205,6,30,40,68,3,6,30,50,68,3,5,39,91,5,145,195,398,102,1,2,5,90,399,72,206,5,25,276,27,58,75,169,42,53,53,100,3,9,10,42,63,82,400,1,3,5,27,264,277,277,5,17,1,209,3,5,6,58,82,210,3]
private def sixMenuWordsP10 : Array Nat := #[5,20,37,40,43,47,71,125,211,278,401,35,36,43,48,67,72,83,146,1,2,47,163,279,1,2,77,212,1,2,3,4,8,16,33,173,1,2,41,100,147,282,402,0,254,1,2,3,33,0,1,2,7,33,43,7,12,37,125,211,3,5,7,12]
private def sixMenuWordsP11 : Array Nat := #[147,284,285,3,4,12,286,0,47,127,0,3,173,0,2,16,40,0,3,4,7,13,283,0,2,285,0,212,0,5,96,0,164,0,3,7,13,0,2,0,2,288,0,1,4,0,41,0,13,96,290,0,83,291,0,72,96,281,0,48,0,35,0,146]
private def sixMenuWordsP12 : Array Nat := #[0,2,292,0,1,289,0,403,0,13,174,0,6,0,6,13,10,15,19,20,37,128,214,293,404,0,7,12,20,37,128,214,7,12,37,87,98,294,3,5,7,12,13,19,34,39,57,59,136,405,3,10,12,57,59,216,295,92,3,6,10,12,34,0]
private def sixMenuWordsP13 : Array Nat := #[19,79,0,10,0,3,6,7,10,0,12,0,3,12,15,0,149,0,296,0,13,59,0,59,0,30,0,18,1,2,4,14,70,129,130,1,2,8,29,62,297,0,1,2,14,70,129,130,0,1,2,98,108,0,1,29,62,80,297,0,73,298,4,6]
private def sixMenuWordsP14 : Array Nat := #[9,30,55,126,131,161,258,5,8,31,40,64,66,119,220,1,2,6,54,173,217,299,1,2,50,175,1,2,6,81,130,176,300,1,5,98,109,10,15,55,126,131,10,15,148,175,302,4,10,131,221,303,304,0,4,0,2,302,0,1,2,304,0,6]
private def sixMenuWordsP15 : Array Nat := #[173,0,2,54,0,6,15,300,5,164,222,0,8,113,0,8,198,0,64,0,66,0,2,307,0,1,305,0,62,0,40,0,5,151,0,109,1,2,4,14,80,89,410,0,1,80,411,0,1,48,224,0,7,78,33,41,2,3,224,419,1,2,5,12]
private def sixMenuWordsP16 : Array Nat := #[309,0,9,310,420,0,19,0,15,19,0,310,0,13,4,7,8,77,0,14,0,6,422,0,2,9,0,51,0,423,0,52,172,4,5,17,36,37,66,178,17,66,84,94,118,27,31,48,55,177,1,2,3,11,0,1,2,103,179,0,2,99,152,31]
private def sixMenuWordsP17 : Array Nat := #[107,152,1,2,4,11,153,227,312,1,2,282,313,132,0,2,314,0,177,424,0,11,132,0,2,132,0,2,5,0,10,99,0,12,132,0,3,63,166,0,10,425,0,1,2,4,0,178,426,0,2,316,0,1,3,0,1,317,0,37,0,27,17,66]
private def sixMenuWordsP18 : Array Nat := #[84,94,118,318,3,4,11,29,29,94,153,223,317,15,315,427,0,8,132,0,311,1,2,11,77,153,227,230,0,2,319,11,66,84,153,319,0,3,4,103,0,10,312,0,230,0,60,107,0,133,0,3,32,0,228,0,174,0,121,9,17,428,7,9]
private def sixMenuWordsP19 : Array Nat := #[17,43,320,17,40,55,432,9,78,72,83,40,64,141,146,9,17,1,2,29,34,17,26,7,309,1,7,29,43,4,14,22,25,26,1,2,5,1,13,0,25,0,42,0,58,0,22,0,13,322,0,26,0,13,26,322,0,49,26,0,3,25,106,0]
private def sixMenuWordsP20 : Array Nat := #[3,63,0,78,21,0,140,0,11,0,13,25,0,6,434,0,11,29,0,1,2,323,0,85,324,0,16,64,35,0,2,35,0,1,38,435,0,9,436,437,0,438,0,47,265,0,1,2,0,26,47,110,181,0,17,325,17,0,439,0,13,133,321,8]
private def sixMenuWordsP21 : Array Nat := #[0,16,45,291,325,440,0,112,0,266,0,231,0,141,0,60,0,213,0,22,26,0,218,0,154,0,13,65,99,441,0,182,442,3,5,27,29,48,70,116,5,10,19,22,62,95,114,232,233,0,27,29,48,70,116,0,22,62,95,114,232,233,23,48]
private def sixMenuWordsP22 : Array Nat := #[73,298,3,5,6,10,24,31,34,326,3,4,10,31,93,95,234,235,328,1,6,11,74,92,0,327,0,116,0,5,0,226,0,330,0,5,326,0,331,0,444,0,70,0,3,15,328,0,115,331,0,3,10,0,329,5,18,19,24,62,74,99,234,235]
private def sixMenuWordsP23 : Array Nat := #[332,0,3,5,10,15,332,0,18,19,4,14,22,26,34,39,236,446,7,8,11,14,22,59,124,447,13,100,170,448,1,11,74,92,5,12,30,47,449,3,12,47,336,0,24,0,122,0,450,0,7,451,0,102,0,324,0,22,183,0,36,172,0,45]
private def sixMenuWordsP24 : Array Nat := #[0,31,0,36,0,50,22,26,25,0,452,0,13,65,337,0,197,0,454,0,65,337,1,2,11,56,27,37,4,5,8,44,31,55,89,184,0,2,184,0,37,338,31,48,55,184,338,20,27,80,20,27,119,339,150,225,0,27,37,0,27,73,0,2]
private def sixMenuWordsP25 : Array Nat := #[80,58,20,27,38,113,20,27,40,64,142,20,27,40,1,5,123,1,2,53,143,1,11,301,5,229,0,123,0,267,0,27,44,15,306,0,103,4,8,31,44,4,8,11,44,4,11,44,198,4,8,23,44,0,8,58,0,8,0,238,0,69,86,0]
private def sixMenuWordsP26 : Array Nat := #[86,0,142,0,156,0,457,458,0,459,0,143,0,269,0,340,0,237,239,39,461,1,2,26,4,8,11,26,34,462,3,3,24,17,55,9,17,80,463,9,17,89,43,89,137,239,71,137,12,137,91,12,239,3,53,12,14,124,91,336,4,11,14,32]
private def sixMenuWordsP27 : Array Nat := #[44,0,183,0,236,341,8,17,22,61,8,14,22,26,8,9,17,26,0,342,0,183,464,465,199,11,111,21,121,200,8,78,106,21,106,111,140,166,121,140,8,16,21,45,46,85,16,85,200,265,44,266,385,21,167,16,38,202,203,16,24,203,45,53]
private def sixMenuWordsP28 : Array Nat := #[67,73,113,3,11,24,73,113,3,5,39,8,24,38,45,46,53,202,123,61,5,67,72,73,86,3,76,267,86,268,23,268,10,143,86,269,3,61,76,159,167,65,169,388,76,389,65,144,205,272,39,124,170,206,85,207,391,85,207,274,392,85,86,74]
private def sixMenuWordsP29 : Array Nat := #[78,53,65,102,3,78,102,159,171,393,6,102,395,5,90,67,65,67,75,144,275,62,172,396,62,172,397,209,46,171,145,195,209,5,270,5,67,72,124,276,5,72,86,28,125,126,28,84,125,146,48,146,57,136,163,212,57,83,163,8,57,147,280,8]
private def sixMenuWordsP30 : Array Nat := #[57,72,281,125,126,147,148,126,288,84,125,147,289,57,290,84,97,292,128,129,149,48,149,114,128,0,87,128,129,149,215,0,48,149,294,0,98,114,128,0,48,87,215,59,77,406,92,148,216,217,59,216,36,92,36,148,129,296,8,62,130,31,80,89]
private def sixMenuWordsP31 : Array Nat := #[108,119,150,219,0,31,62,119,130,175,219,220,109,407,64,66,67,113,115,8,28,64,66,80,113,115,131,29,219,5,151,220,299,93,109,130,301,66,131,175,305,131,222,223,306,66,97,307,0,48,89,224,9,20,88,89,108,412,413,9,88,89,108,150]
private def sixMenuWordsP32 : Array Nat := #[225,9,110,4,9,110,22,88,137,414,415,27,88,416,417,20,67,226,275,418,308,9,110,22,199,6,22,88,4,14,57,59,77,171,57,59,308,28,37,94,177,28,55,94,178,69,179,0,69,99,179,69,311,4,11,69,313,37,94,94,314,55,94,94]
private def sixMenuWordsP33 : Array Nat := #[221,229,315,55,316,164,229,69,99,133,177,429,9,20,36,46,64,430,9,28,64,84,17,48,64,431,43,321,231,12,57,14,26,34,111,166,433,141,57,9,84,180,323,9,84,97,133,37,95,116,15,70,95,443,0,37,73,95,116,0,23,70,95,155]
private def sixMenuWordsP34 : Array Nat := #[0,23,37,155,95,327,6,95,123,176,98,123,4,11,143,70,330,18,77,116,333,5,22,48,236,334,335,14,15,114,0,116,333,0,73,102,0,37,145,155,0,22,48,334,335,0,14,114,145,0,48,102,215,0,98,145,11,26,181,81,122,453,10,56]
private def sixMenuWordsP35 : Array Nat := #[142,150,155,184,225,9,31,80,108,150,155,0,20,31,339,262,455,38,46,178,456,3,58,76,3,76,340,237,20,109,4,238,143,20,222,103,341,154,154,238,156,32,342,120,1,2,4,8,93,1,12,1,4,51,78,11,23,1,3,23,343,3,6,11]
private def sixMenuWordsP36 : Array Nat := #[75,79,111,63,243,242,29,65,6,16,11,23,90,11,27,56,0,3,5,7,0,41,347,0,3,7,0,4,6,7,0,1,36,0,1,13,48,0,1,4,51,0,1,7,78,0,3,59,0,7,92,48,0,15,18,52,7,244,0,1,5,31,467,0]
private def sixMenuWordsP37 : Array Nat := #[1,19,66,0,1,15,67,0,5,29,0,62,93,1,7,2,9,12,14,40,110,350,0,9,33,0,9,19,33,13,47,135,0,9,42,0,9,81,469,0,2,9,180,0,2,20,0,2,20,248,0,2,9,19,0,12,22,0,14,16,0,2,13,20]
private def sixMenuWordsP38 : Array Nat := #[353,1,152,0,1,2,3,5,0,21,55,0,11,37,0,4,6,103,0,1,21,190,1,2,4,2,7,9,208,0,3,7,12,26,0,1,2,3,46,0,1,2,7,35,0,3,7,25,0,1,3,35,0,21,0,17,45,0,17,21,0,8,36,0]
private def sixMenuWordsP39 : Array Nat := #[3,46,0,35,45,0,29,357,0,3,26,32,0,3,25,32,0,3,32,35,0,3,17,0,3,35,0,1,3,17,0,2,7,9,0,3,5,0,23,70,0,24,37,0,4,23,0,3,15,117,7,49,0,3,15,49,0,7,40,0,22,38,0,25]
private def sixMenuWordsP40 : Array Nat := #[38,0,22,23,0,3,56,117,0,38,49,0,31,112,0,31,40,0,3,22,7,14,1,35,360,0,82,0,1,15,46,0,11,27,0,11,35,0,24,27,0,24,49,0,69,0,18,50,477,0,29,87,0,2,15,20,0,31,60,0,16,31,0,1]
private def sixMenuWordsP41 : Array Nat := #[11,71,19,18,43,192,80,83,64,12,17,26,0,4,20,7,26,104,0,9,251,247,0,4,18,0,25,36,0,4,9,15,49,104,0,4,31,4,11,12,21,51,78,120,139,1,2,21,1,2,4,11,41,93,4,16,21,60,201,4,8,11,16,1]
private def sixMenuWordsP42 : Array Nat := #[2,4,16,1,2,3,24,3,5,8,10,21,24,39,51,67,1,2,6,21,76,93,4,8,24,107,204,1,2,4,11,240,4,10,21,23,176,240,344,466,74,21,75,79,241,345,1,2,24,34,242,8,24,34,39,43,63,79,111,243,8,24,42,43]
private def sixMenuWordsP43 : Array Nat := #[346,24,39,1,2,3,8,3,5,16,23,38,39,75,1,3,34,3,5,8,11,23,24,1,2,3,75,2,24,23,1,2,3,5,208,39,43,87,120,168,210,241,3,8,30,168,3,5,21,39,45,50,75,3,5,10,34,63,3,34,87,3,5,8]
private def sixMenuWordsP44 : Array Nat := #[18,24,39,40,50,74,3,5,8,12,75,210,3,8,24,87,21,24,3,5,34,50,3,5,6,39,68,168,185,1,3,50,1,2,3,6,3,16,18,50,74,85,1,3,6,68,6,61,1,2,5,21,345,5,38,50,90,5,50,5,16,23,50,8]
private def sixMenuWordsP45 : Array Nat := #[38,8,11,38,82,8,24,42,45,58,85,112,27,42,58,75,90,24,58,8,16,18,23,50,54,24,3,42,82,107,344,3,5,18,42,3,42,23,74,157,8,60,112,3,6,18,58,74,82,5,8,36,40,43,47,48,51,78,1,2,4,47,1,2]
private def sixMenuWordsP46 : Array Nat := #[4,5,16,41,104,1,2,3,6,8,41,0,1,2,7,41,43,7,36,51,7,51,186,3,4,13,0,47,157,0,5,104,0,1,16,40,0,4,6,7,8,13,0,1,186,10,15,19,36,48,52,92,244,0,7,36,48,52,4,6,7,13,19,47]
private def sixMenuWordsP47 : Array Nat := #[59,68,92,4,5,7,15,52,59,3,6,10,47,68,0,6,7,10,0,7,0,6,15,47,1,8,29,52,62,0,1,29,52,62,8,18,30,31,51,66,67,1,2,30,52,104,151,1,2,18,29,93,158,15,31,51,15,51,187,4,19,31,348,0]
private def sixMenuWordsP48 : Array Nat := #[1,187,0,1,348,0,30,104,0,1,151,0,15,18,158,2,4,14,1,2,16,33,54,188,14,16,22,62,3,4,8,10,19,188,2,16,20,48,1,2,6,10,15,16,20,71,80,320,0,2,14,80,12,14,16,62,0,2,16,20,48,0,2,14]
private def sixMenuWordsP49 : Array Nat := #[0,1,2,7,12,33,71,4,9,68,71,71,188,189,9,20,64,83,91,9,66,3,4,9,20,40,64,40,71,20,48,3,4,18,19,47,83,189,3,4,5,6,10,18,30,68,91,134,1,2,54,68,74,189,1,2,14,2,9,18,2,13,468,9]
private def sixMenuWordsP50 : Array Nat := #[12,14,22,2,18,19,47,74,1,2,7,12,18,71,1,2,3,7,12,71,1,2,4,16,33,54,134,1,2,33,1,2,3,5,33,50,53,134,12,16,54,151,6,16,18,30,68,1,2,6,52,54,1,2,50,54,42,82,3,9,0,6,9,33]
private def sixMenuWordsP51 : Array Nat := #[0,19,33,9,10,3,9,19,0,4,13,4,8,12,0,4,83,247,0,54,91,0,4,19,64,0,9,13,0,4,6,10,0,4,6,0,1,352,0,2,79,0,2,245,0,2,246,0,2,51,0,1,2,16,33,81,0,10,81,134,0,2,16,134]
private def sixMenuWordsP52 : Array Nat := #[0,2,6,54,0,2,246,351,1,2,9,0,10,127,157,247,0,4,40,0,3,54,0,14,20,0,18,52,127,0,18,52,0,6,12,0,2,12,0,12,14,0,2,245,349,3,4,5,5,23,3,4,31,36,37,55,1,2,3,6,11,0,1,2]
private def sixMenuWordsP53 : Array Nat := #[103,1,2,4,11,21,158,0,10,12,152,3,4,11,187,21,31,186,0,10,158,9,17,43,3,5,23,35,38,43,46,47,71,9,17,38,9,17,35,9,35,78,3,5,47,61,3,5,8,42,1,2,25,29,34,1,2,11,26,47,1,5,7,29]
private def sixMenuWordsP54 : Array Nat := #[43,3,7,8,9,11,12,13,17,34,3,4,9,12,17,25,26,1,29,47,242,1,2,5,12,47,2,3,12,1,2,6,29,42,3,5,12,34,36,42,1,2,3,3,5,6,12,25,29,52,1,2,3,52,0,1,2,7,42,63,7,16,0,1]
private def sixMenuWordsP55 : Array Nat := #[2,16,32,4,7,25,32,0,1,2,32,0,7,25,34,63,152,0,25,32,63,2,7,9,25,42,63,7,12,38,46,3,4,12,0,3,4,7,13,0,3,25,0,5,30,0,3,7,78,0,3,17,63,0,7,11,13,29,0,17,30,0,4,7]
private def sixMenuWordsP56 : Array Nat := #[29,0,1,2,354,0,2,355,0,2,32,0,2,17,0,1,2,36,0,1,17,0,1,2,32,36,0,32,0,9,33,41,42,0,5,7,13,42,0,4,5,7,13,32,42,0,6,7,47,93,115,0,1,2,3,356,0,17,61,9,17,38,357,3]
private def sixMenuWordsP57 : Array Nat := #[4,9,29,9,21,3,9,21,347,3,4,29,5,9,13,44,45,46,0,5,12,13,44,0,3,12,190,0,13,93,1,2,18,21,26,0,2,358,9,21,358,0,3,4,32,0,21,61,127,157,0,42,60,0,18,201,0,25,35,0,16,32,52,0]
private def sixMenuWordsP58 : Array Nat := #[4,42,52,0,3,8,13,174,0,4,12,32,0,3,4,3,5,6,12,25,42,0,5,7,13,25,32,42,0,3,13,25,101,0,3,12,32,0,3,101,0,1,3,474,5,10,19,29,36,37,70,0,29,36,37,70,3,5,6,10,24,68,104,3]
private def sixMenuWordsP59 : Array Nat := #[4,19,23,29,122,0,6,15,122,0,6,10,14,22,43,101,191,249,10,15,19,21,45,49,117,22,70,3,4,5,14,22,49,5,10,14,19,22,45,112,14,49,244,3,5,10,19,191,0,7,12,45,117,0,7,12,23,49,0,14,22,0,14,22]
private def sixMenuWordsP60 : Array Nat := #[45,112,0,14,22,23,31,34,39,68,181,191,475,3,4,5,7,8,12,13,19,24,25,34,39,22,25,4,5,7,31,43,3,7,8,12,13,14,22,24,34,59,4,7,14,22,26,34,476,5,13,31,243,5,12,13,19,24,47,71,3,12,18,34]
private def sixMenuWordsP61 : Array Nat := #[3,5,12,34,36,82,3,5,6,12,31,34,51,3,5,6,10,31,34,82,3,5,6,10,34,36,51,0,101,0,7,226,0,185,0,22,49,0,5,36,101,0,7,36,0,5,82,0,5,6,7,10,0,5,12,15,5,13,14,38,44,59,117,0]
private def sixMenuWordsP62 : Array Nat := #[5,7,12,13,44,91,0,3,12,0,23,79,0,26,49,0,19,51,79,0,4,26,49,7,51,0,3,30,101,0,10,12,5,14,18,19,23,25,61,74,0,3,5,10,15,61,0,3,249,1,2,11,90,1,2,4,21,49,27,37,49,5,10,19]
private def sixMenuWordsP63 : Array Nat := #[20,21,27,60,3,4,5,8,44,1,2,5,6,10,19,20,27,192,0,1,2,21,49,0,27,37,49,0,1,2,49,0,20,21,27,60,0,1,2,192,359,4,6,23,30,35,38,46,27,35,37,20,27,46,190,20,23,27,20,46,67,5,6,18]
private def sixMenuWordsP64 : Array Nat := #[1,2,6,21,56,1,2,6,29,58,75,81,122,5,11,56,1,2,4,11,1,2,3,53,3,10,21,31,58,69,3,4,10,29,56,90,105,158,1,6,11,18,68,10,15,23,35,4,10,23,250,0,1,2,250,0,6,15,56,0,1,2,248,0]
private def sixMenuWordsP65 : Array Nat := #[1,2,180,361,0,81,93,115,20,23,27,87,5,250,23,29,248,4,15,0,190,0,90,0,204,0,46,1,2,11,18,0,2,362,11,20,362,0,56,0,1,2,56,0,1,363,478,0,10,360,0,10,56,240,5,18,19,24,61,74,0,5,10,61]
private def sixMenuWordsP66 : Array Nat := #[0,18,19,343,0,105,176,479,1,2,49,4,8,21,49,21,52,251,3,5,19,1,2,7,41,43,0,4,9,17,21,52,60,4,7,12,52,1,2,4,52,192,9,46,72,83,105,38,46,5,20,35,105,23,35,9,12,71,4,24,4,8,9,3]
private def sixMenuWordsP67 : Array Nat := #[5,13,13,58,346,480,23,51,481,4,5,9,13,32,46,105,0,3,5,7,12,13,0,13,105,182,0,32,83,0,13,32,32,38,44,46,9,32,44,45,69,85,117,4,8,38,46,0,252,11,20,26,252,482,20,24,25,56,61,0,32,64,0,4]
private def sixMenuWordsP68 : Array Nat := #[18,64,3,5,16,18,32,44,50,4,8,16,32,44,50,1,2,26,252,0,1,363,483,11,18,26,50,5,14,18,19,25,56,105,127,0,3,5,10,15,0,105,182,183,0,19,56,18,24,25,23,35,56,61,16,23,24,3,11,23,50,51,65,75]
private def sixMenuWordsP69 : Array Nat := #[79,111,43,65,3,5,39,241,3,5,39,43,8,23,38,45,50,53,85,21,61,159,185,3,8,24,53,65,91,3,21,65,157,4,14,16,19,20,52,60,10,22,54,0,9,14,16,20,52,60,4,9,19,20,28,51,64,79,80,87,110,0,10,28]
private def sixMenuWordsP70 : Array Nat := #[40,134,6,18,28,71,4,8,9,13,14,19,57,59,83,12,14,18,22,54,68,2,12,14,22,54,92,280,4,8,10,53,54,57,59,91,188,3,18,52,54,60,189,349,9,20,51,87,9,351,51,87,245,246,4,8,9,14,57,59,9,20,97,352]
private def sixMenuWordsP71 : Array Nat := #[470,5,471,23,472,23,473,9,17,28,35,36,38,28,42,43,115,3,7,9,11,12,25,63,0,16,25,32,42,9,17,35,36,38,17,35,354,355,9,356,18,25,61,5,14,15,22,36,45,49,101,5,10,40,10,19,0,14,22,23,36,45,49,5]
private def sixMenuWordsP72 : Array Nat := #[12,14,39,181,3,12,19,34,191,7,22,49,101,185,19,26,50,10,90,0,359,6,28,75,76,115,4,53,58,69,90,361,4,44,46,69,117,4,13,25,83,2,8,51,81,2,16,2,79,0,2,13,353,0,12,16,0,2,19,193,2,3,0,1]
private def sixMenuWordsP73 : Array Nat := #[7,13,0,4,45,0,1,21,193,31,0,38,0,23,0,1,15,19,0,1,11,193,0,20,54,81,0,29,0,9,54,81]
private def sixMenuWords : Array (Array Nat) := #[sixMenuWordsP0,sixMenuWordsP1,sixMenuWordsP2,sixMenuWordsP3,sixMenuWordsP4,sixMenuWordsP5,sixMenuWordsP6,sixMenuWordsP7,sixMenuWordsP8,sixMenuWordsP9,sixMenuWordsP10,sixMenuWordsP11,sixMenuWordsP12,sixMenuWordsP13,sixMenuWordsP14,sixMenuWordsP15,sixMenuWordsP16,sixMenuWordsP17,sixMenuWordsP18,sixMenuWordsP19,sixMenuWordsP20,sixMenuWordsP21,sixMenuWordsP22,sixMenuWordsP23,sixMenuWordsP24,sixMenuWordsP25,sixMenuWordsP26,sixMenuWordsP27,sixMenuWordsP28,sixMenuWordsP29,sixMenuWordsP30,sixMenuWordsP31,sixMenuWordsP32,sixMenuWordsP33,sixMenuWordsP34,sixMenuWordsP35,sixMenuWordsP36,sixMenuWordsP37,sixMenuWordsP38,sixMenuWordsP39,sixMenuWordsP40,sixMenuWordsP41,sixMenuWordsP42,sixMenuWordsP43,sixMenuWordsP44,sixMenuWordsP45,sixMenuWordsP46,sixMenuWordsP47,sixMenuWordsP48,sixMenuWordsP49,sixMenuWordsP50,sixMenuWordsP51,sixMenuWordsP52,sixMenuWordsP53,sixMenuWordsP54,sixMenuWordsP55,sixMenuWordsP56,sixMenuWordsP57,sixMenuWordsP58,sixMenuWordsP59,sixMenuWordsP60,sixMenuWordsP61,sixMenuWordsP62,sixMenuWordsP63,sixMenuWordsP64,sixMenuWordsP65,sixMenuWordsP66,sixMenuWordsP67,sixMenuWordsP68,sixMenuWordsP69,sixMenuWordsP70,sixMenuWordsP71,sixMenuWordsP72,sixMenuWordsP73]
private def sixMenuAtP0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP3 : Array Nat := #[0,0,0,0,0,0,0,1,2,3,4,2,1,1,0,0,0,0,5,0,5,6,7,8,9,10,11,12,12,12,12,0,0,13,12,0,14,12,12,12,12,12,0,0,15,0,0,0,0,12,0,12,0,16,12,0,0,17,17,18,0,0,12,0]
private def sixMenuAtP4 : Array Nat := #[0,0,19,0,12,12,0,12,0,12,12,12,12,0,0,0,12,0,0,0,0,0,0,0,0,0,12,12,0,20,20,0,0,12,12,12,21,22,0,11,11,0,0,23,8,12,0,0,13,24,0,0,0,0,12,0,0,0,12,12,12,12,12,12]
private def sixMenuAtP5 : Array Nat := #[12,25,12,12,0,12,0,8,26,12,12,12,12,12,0,27,12,0,0,0,0,0,0,12,12,12,0,0,0,12,12,28,0,0,0,0,0,29,0,12,0,0,12,12,0,0,12,12,12,0,0,30,12,31,12,12,12,12,32,33,12,0,0,34]
private def sixMenuAtP6 : Array Nat := #[12,12,0,0,12,12,12,0,12,0,0,0,0,0,0,0,0,0,12,12,12,12,12,35,36,37,38,39,40,0,12,12,12,0,0,0,12,12,12,0,12,12,12,12,12,12,12,0,12,0,12,12,41,12,42,12,12,0,43,44,29,28,12,0]
private def sixMenuAtP7 : Array Nat := #[0,0,45,46,0,0,12,0,47,48,49,50,0,12,0,0,0,0,51,52,0,0,0,0,0,0,0,0,0,0,53,54,0,0,0,0,3,0,55,56,57,58,59,2,0,0,0,60,0,61,62,63,64,0,0,0,0,0,0,0,0,30,0,0]
private def sixMenuAtP8 : Array Nat := #[0,61,0,65,65,12,0,66,0,67,67,0,0,0,0,68,23,69,70,71,72,73,0,0,0,0,0,0,0,8,0,0,0,0,0,0,74,0,0,0,0,0,12,75,76,0,0,77,0,0,78,0,0,0,0,0,0,0,0,0,0,75,0,0]
private def sixMenuAtP9 : Array Nat := #[79,80,0,0,0,0,81,0,82,83,84,85,0,1,53,0,86,87,88,0,0,0,0,89,0,90,91,92,93,94,95,96,97,98,99,100,101,102,12,103,12,12,12,104,0,40,105,61,106,107,108,109,21,110,12,111,112,113,114,115,94,116,117,0]
private def sixMenuAtP10 : Array Nat := #[0,118,12,12,12,12,119,12,120,121,12,122,123,124,125,12,126,127,128,12,129,12,12,130,12,12,12,131,132,133,134,135,136,137,138,139,140,12,21,141,12,142,143,0,12,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP12 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP13 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP14 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP15 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP16 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP17 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP20 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,144,0,0,0,145,146,147,148,149,150,151,152,153]
private def sixMenuAtP21 : Array Nat := #[154,155,0,156,157,158,159,159,146,160,161,0,0,162,163,164,165,166,167,168,169,170,171,172,146,173,53,0,0,174,0,175,0,0,176,177,178,179,180,181,182,183,184,0,185,157,0,0,186,0,2,187,3,188,189,190,191,192,193,2,194,195,196,197]
private def sixMenuAtP22 : Array Nat := #[198,199,0,1,200,0,0,0,0,0,0,1,0,0,0,0,0,0,0,201,0,0,0,0,0,82,202,0,203,204,5,146,205,206,207,146,208,209,210,211,212,5,6,0,1,7,1,213,0,214,1,215,216,217,0,218,219,2,220,221,222,87,0,1]
private def sixMenuAtP23 : Array Nat := #[223,224,225,226,0,0,0,0,227,228,2,229,3,215,2,0,230,0,231,232,0,232,1,0,233,2,195,193,234,235,236,237,238,0,215,1,0,239,240,0,1,1,2,1,0,241,8,242,243,82,244,245,165,246,12,247,0,248,249,12,12,12,12,31]
private def sixMenuAtP24 : Array Nat := #[12,12,12,12,250,251,252,12,253,1,254,255,256,257,12,258,157,101,12,17,92,12,259,12,260,17,261,12,12,262,12,12,12,12,12,12,12,263,264,12,12,12,12,12,12,263,265,12,12,12,12,12,12,12,12,12,0,12,266,12,12,12,92,92]
private def sixMenuAtP25 : Array Nat := #[0,13,12,267,268,269,12,270,271,272,12,0,0,12,12,273,31,94,12,274,12,12,0,12,12,275,94,94,12,0,276,277,278,12,12,12,94,12,12,279,280,281,12,12,282,283,284,285,286,12,287,12,288,277,289,290,12,291,12,12,12,292,277,12]
private def sixMenuAtP26 : Array Nat := #[12,12,92,293,294,12,294,12,12,12,12,12,12,12,0,12,295,12,295,295,295,277,277,277,277,12,296,12,12,12,12,12,12,12,12,0,297,298,299,300,301,302,0,303,8,304,305,188,306,12,12,0,307,308,0,188,309,310,12,311,312,12,0,313]
private def sixMenuAtP27 : Array Nat := #[12,263,314,12,315,316,317,157,0,0,0,13,318,319,320,321,322,12,0,12,12,0,323,324,12,12,12,325,12,0,0,12,0,0,0,12,94,94,12,12,322,12,12,12,12,296,326,327,328,94,9,329,330,0,331,12,332,333,0,8,8,8,334,9]
private def sixMenuAtP28 : Array Nat := #[335,336,12,0,0,0,12,12,0,0,0,0,12,0,0,0,0,12,337,295,338,0,0,339,22,340,341,342,12,17,343,17,12,0,344,295,12,0,0,0,263,12,263,12,12,345,346,0,12,347,0,0,12,277,12,295,0,12,0,12,277,343,348,12]
private def sixMenuAtP29 : Array Nat := #[0,0,349,0,0,8,350,351,352,353,354,355,356,12,357,358,359,359,12,12,12,12,12,360,361,31,94,362,363,12,364,12,0,0,12,0,365,366,367,368,12,0,369,370,12,371,12,12,312,94,263,372,1,12,94,12,28,0,12,32,12,373,94,94]
private def sixMenuAtP30 : Array Nat := #[374,0,12,375,12,0,376,377,1,378,379,12,12,12,12,380,12,381,12,12,12,12,12,382,383,384,385,12,386,387,388,389,12,12,390,12,12,391,392,391,393,12,12,394,395,396,8,8,397,8,8,8,398,399,400,401,334,402,9,0,403,404,405,406]
private def sixMenuAtP31 : Array Nat := #[1,407,408,12,12,409,12,410,411,12,12,12,12,12,12,12,412,12,12,12,12,12,12,12,12,12,92,0,27,0,413,414,415,414,416,94,94,417,12,0,0,0,0,0,0,12,0,0,0,0,12,0,0,0,0,12,418,419,12,0,12,12,0,0]
private def sixMenuAtP32 : Array Nat := #[92,420,421,422,0,414,0,12,0,0,295,295,295,423,424,0,12,0,421,28,425,28,426,427,263,263,12,101,263,94,428,429,0,12,12,414,94,12,12,12,12,409,430,28,431,432,0,12,82,433,434,435,12,436,12,1,437,12,0,12,0,0,0,438]
private def sixMenuAtP33 : Array Nat := #[28,439,0,417,0,0,0,0,0,12,12,0,12,0,440,12,12,12,12,12,0,92,12,12,24,12,12,12,441,442,442,443,444,445,12,12,12,446,447,448,449,146,0,0,12,12,12,263,12,0,12,30,12,12,450,451,450,448,12,0,0,0,12,0]
private def sixMenuAtP34 : Array Nat := #[12,12,449,12,12,12,12,28,452,12,453,393,12,443,414,12,12,454,12,455,12,430,12,12,12,12,12,0,0,12,0,0,0,0,12,0,0,0,12,0,0,0,0,12,12,0,12,12,12,12,12,12,0,12,0,0,0,12,0,0,12,12,0,12]
private def sixMenuAtP35 : Array Nat := #[12,0,0,0,12,456,457,458,459,12,460,12,461,0,462,463,464,465,12,12,466,277,12,312,467,468,469,470,471,472,392,473,474,12,375,12,12,12,12,12,12,12,136,12,12,296,475,12,476,12,12,12,12,287,12,12,12,12,12,12,477,478,479,12]
private def sixMenuAtP36 : Array Nat := #[480,12,12,12,12,12,12,12,12,12,12,12,481,482,483,484,485,0,12,0,295,277,277,409,486,12,0,487,12,136,488,466,489,490,491,443,492,493,494,343,12,495,496,0,0,0,0,36,0,497,36,498,0,0,0,499,430,500,0,12,104,295,12,12]
private def sixMenuAtP37 : Array Nat := #[12,41,22,42,12,0,501,442,0,12,0,0,502,12,12,12,0,12,12,12,12,12,12,503,12,12,414,12,0,452,295,12,295,12,12,12,12,12,28,12,12,504,12,12,12,12,12,12,12,439,505,506,507,507,508,509,510,32,511,12,512,513,514,515]
private def sixMenuAtP38 : Array Nat := #[516,517,12,12,12,518,8,8,506,8,8,519,520,521,522,523,524,411,1,0,525,12,0,94,12,12,526,436,527,94,0,0,0,0,528,528,375,0,0,0,0,0,375,0,529,530,312,12,531,532,533,534,0,535,536,536,12,537,538,12,12,12,12,539]
private def sixMenuAtP39 : Array Nat := #[540,536,541,12,542,543,12,312,0,12,263,12,30,544,540,545,12,12,12,12,12,12,12,2,1,546,536,547,12,12,12,0,548,549,550,551,552,553,553,554,555,556,557,558,0,28,12,12,12,12,12,12,559,560,561,562,0,563,564,553,565,566,567,568]
private def sixMenuAtP40 : Array Nat := #[232,215,1,2,157,0,0,0,12,0,12,0,0,0,22,569,12,21,12,12,0,570,453,453,146,0,0,0,0,12,571,572,573,173,574,0,541,575,541,12,439,0,12,12,0,12,12,576,577,578,579,580,144,581,146,582,583,163,584,585,586,587,588,0]
private def sixMenuAtP41 : Array Nat := #[589,590,0,591,592,0,593,594,595,596,71,597,598,0,599,600,601,602,603,604,605,56,0,0,0,606,607,0,608,609,610,611,0,612,0,0,613,614,615,616,617,618,619,0,56,620,621,622,623,624,625,626,627,3,0,60,628,629,630,631,632,633,634,635]
private def sixMenuAtP42 : Array Nat := #[636,637,638,2,0,2,639,640,641,0,0,642,643,644,645,646,647,648,284,649,650,651,652,653,654,655,0,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,0,576,676,677,678,0,679,680,681,682,683,0,684,69,685,685,686]
private def sixMenuAtP43 : Array Nat := #[687,684,2,2,688,689,690,691,0,692,693,694,695,696,697,698,699,700,701,0,702,703,704,705,706,707,708,0,709,710,0,711,700,0,0,0,712,713,714,715,0,700,0,716,0,0,0,717,718,719,720,721,0,722,723,724,78,725,0,726,0,727,0,0]
private def sixMenuAtP44 : Array Nat := #[0,728,729,730,0,731,732,733,734,735,736,76,737,738,739,0,89,0,740,0,0,0,741,0,0,0,0,0,0,0,742,743,0,744,745,746,12,747,0,595,748,749,750,0,0,751,752,753,754,700,755,700,756,757,0,38,701,0,0,0,0,0,0,0]
private def sixMenuAtP45 : Array Nat := #[758,759,760,708,0,761,761,752,762,763,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,764,0,141,153,765,143,0,82,766,141,767,0,768,769,0,1,53,188,0,770,1,200,771,618,772,684,773,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP46 : Array Nat := #[0,774,0,775,0,0,0,0,0,0,0,0,0,706,776,777,89,778,0,89,779,0,0,780,0,0,0,0,0,0,0,781,0,0,0,2,2,782,0,0,231,562,0,553,774,553,706,89,2,684,553,0,0,553,553,0,0,0,0,1,553,773,783,553]
private def sixMenuAtP47 : Array Nat := #[773,0,553,0,12,12,784,369,12,785,92,786,12,372,12,12,94,787,94,788,789,790,791,277,277,0,792,312,108,793,496,794,795,796,12,94,797,798,799,296,800,801,94,94,0,802,803,0,8,804,0,9,0,12,0,0,0,0,0,0,0,1,805,157]
private def sixMenuAtP48 : Array Nat := #[0,806,807,287,12,12,808,0,0,0,809,810,343,811,24,12,812,12,12,0,813,814,813,0,12,12,12,0,0,0,12,0,0,0,12,263,12,0,343,815,12,0,12,0,24,816,343,65,115,163,817,0,312,61,0,818,343,263,0,345,343,0,819,61]
private def sixMenuAtP49 : Array Nat := #[0,0,0,0,0,0,820,12,821,12,369,822,823,136,12,12,136,824,825,12,0,8,826,0,82,827,173,828,0,777,410,430,12,12,91,92,829,94,830,831,12,12,0,12,12,0,12,0,784,832,0,101,833,0,94,0,834,0,835,0,836,0,835,836]
private def sixMenuAtP50 : Array Nat := #[12,12,12,12,277,92,92,0,12,837,136,12,838,839,443,496,12,12,0,12,12,840,841,825,12,12,12,12,0,12,842,843,0,12,0,844,845,0,94,825,12,430,846,94,553,847,839,12,12,12,12,12,12,12,12,12,12,0,0,0,12,0,12,0]
private def sixMenuAtP51 : Array Nat := #[12,0,12,12,131,848,277,849,850,136,136,851,12,12,0,173,0,131,0,104,0,312,852,853,108,854,855,0,0,0,856,857,858,858,12,12,92,0,837,136,12,859,860,497,496,12,12,12,12,12,12,0,312,851,851,861,862,0,863,312,0,864,857,188]
private def sixMenuAtP52 : Array Nat := #[141,1,1,865,8,866,12,12,12,867,868,94,1,0,869,870,871,872,1,805,1,1,12,873,874,12,875,12,12,12,876,12,12,12,12,12,183,877,872,878,879,0,94,880,881,143,143,143,882,553,882,553,883,884,439,82,141,12,173,885,0,0,12,12]
private def sixMenuAtP53 : Array Nat := #[12,881,0,0,8,0,886,887,0,775,60,553,143,0,888,164,553,553,9,0,92,553,92,159,882,0,0,0,0,0,0,0,0,684,41,0,21,12,12,0,0,871,889,889,889,890,143,143,143,12,12,891,892,893,143,894,143,0,12,0,882,858,12,865]
private def sixMenuAtP54 : Array Nat := #[12,30,12,157,0,0,0,836,895,896,12,12,12,12,897,143,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP55 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,899,175,0,913,914,915,916]
private def sixMenuAtP56 : Array Nat := #[917,918,82,919,177,2,920,921,157,922,923,924,553,925,926,927,928,929,930,442,931,932,933,934,935,936,937,938,939,182,184,940,2,941,157,942,943,0,681,883,0,944,945,946,947,442,948,949,950,951,952,953,251,954,193,955,956,957,958,199,251,959,953,1]
private def sixMenuAtP57 : Array Nat := #[953,1,960,961,962,12,963,964,965,143,966,12,967,1,12,12,12,968,969,970,971,12,972,94,265,12,973,974,975,976,977,286,12,21,12,978,277,979,980,0,981,982,983,984,12,985,0,1,986,987,12,988,536,12,0,989,12,94,990,12,991,992,993,0]
private def sixMenuAtP58 : Array Nat := #[994,995,9,329,996,997,998,999,1000,9,1001,1002,12,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,334,0,1023,1024,1025,1026,1027,1028,188,1029,12,12,12,12,12,1030,1031,0,0,157,188,0,41,1032,12,277,0,1033,12,1034,41]
private def sixMenuAtP59 : Array Nat := #[1035,12,12,12,1036,92,0,12,12,1037,1038,312,12,12,24,12,24,1039,1040,65,1041,312,1042,1043,24,1044,12,12,0,12,277,1045,1046,1047,12,12,12,343,263,1048,345,1049,345,1049,12,12,12,12,0,12,1050,24,1051,1052,1053,263,263,1054,343,277,0,12,12,1024]
private def sixMenuAtP60 : Array Nat := #[263,263,1055,24,263,296,1056,1057,1058,12,1059,1060,1059,1061,1062,188,256,1063,316,1002,818,343,1064,12,1065,316,188,263,188,263,0,442,349,173,0,1066,143,131,0,1067,2,0,1068,1069,1070,1071,1072,12,1073,989,12,972,1069,1074,1,1075,12,824,12,1076,1077,706,1078,555]
private def sixMenuAtP61 : Array Nat := #[1079,1080,1081,1082,1083,1084,1085,439,1086,1087,1088,1,1089,1090,1091,248,1092,334,1093,1094,1095,1096,249,1097,249,334,1098,1099,1100,12,1101,1101,1102,1103,1104,1105,173,12,12,12,414,12,12,12,1106,251,1107,1,254,1108,12,101,12,12,12,12,12,1109,295,92,12,419,12,1110]
private def sixMenuAtP62 : Array Nat := #[295,423,419,1108,1111,834,1112,1113,1114,1115,1116,12,101,979,12,12,1117,12,12,419,409,94,1118,372,1119,1120,1121,1122,12,1123,1124,808,1125,12,101,12,436,12,1126,12,1127,436,12,1128,834,12,12,12,12,12,12,555,0,12,12,1129,28,12,1130,173,2,1131,1132,12]
private def sixMenuAtP63 : Array Nat := #[1133,12,12,82,1134,92,1135,1,1,1,12,12,12,12,12,1136,1137,1138,12,1139,12,12,12,1140,1141,1142,1143,12,296,12,1144,1145,1146,12,12,1143,1147,1148,1147,1149,173,1150,1151,12,1152,1153,1100,1154,1155,1156,1157,12,12,12,277,12,1101,1158,94,12,12,12,12,12]
private def sixMenuAtP64 : Array Nat := #[12,12,295,12,12,0,277,12,12,12,12,0,12,12,12,12,0,12,12,1159,1160,1161,1162,969,1163,1164,12,338,12,1165,1166,1167,1168,1169,1170,1171,1172,1167,1173,1174,1175,173,1176,12,1177,1178,1179,1180,1181,1182,143,1183,1184,1185,285,1186,1187,1188,1189,131,286,12,288,277]
private def sixMenuAtP65 : Array Nat := #[290,1190,12,136,979,979,312,1191,1192,136,1193,1194,1193,1195,343,1196,1197,1196,1198,412,0,12,277,0,1199,1200,12,1201,341,1202,338,136,12,12,497,1203,1204,1205,338,12,12,12,1206,1207,475,277,1208,1157,277,12,12,1209,1210,479,12,21,1211,1211,0,0,1212,1213,1214,1215]
private def sixMenuAtP66 : Array Nat := #[1,1216,1217,1218,1219,1220,1221,1222,1,12,1223,774,1224,1225,1226,1227,1228,1229,1230,1231,1232,505,1233,1234,1235,1236,1237,411,0,188,1238,1239,312,12,1240,12,1241,12,1242,436,1243,411,1241,1244,436,0,0,1225,528,0,188,188,1245,131,1246,1247,1248,312,532,535,12,1249,12,12]
private def sixMenuAtP67 : Array Nat := #[1250,1251,1252,312,1252,312,12,12,12,1253,1254,1255,1256,296,1257,1258,1259,1260,94,12,12,12,12,1261,1262,1263,12,131,1264,312,1265,1266,1267,1268,1269,1270,1271,1272,1267,12,1273,1274,1275,1276,953,1,1277,1278,1279,1280,1281,550,551,188,188,1282,12,92,1283,173,1284,1285,1123,1286]
private def sixMenuAtP68 : Array Nat := #[12,1287,1123,1288,1289,1290,1291,1292,1256,1293,312,1288,1294,1295,1296,1297,277,12,1298,263,1299,12,94,12,1300,893,12,12,1301,131,1302,1303,1304,1256,1305,296,1306,12,1307,1308,1309,1310,56,1311,1312,1313,1314,1315,0,1316,1317,1318,1319,1320,1321,1322,1323,1324,0,1325,1326,1327,1328,1329]
private def sixMenuAtP69 : Array Nat := #[1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,0,1343,1344,1345,1346,1347,12,1348,0,1349,0,1350,1351,0,1352,1353,1354,1355,1356,0,1357,882,12,1358,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP70 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAtP71 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1359,1360,157,0,1361,0,0,1361,0,0,0,1362,158,0,157,1363,12,0,157,0,0,0,12,12,12,263,12,0,1364,12,263,296]
private def sixMenuAtP72 : Array Nat := #[289,1365,1366,157,0,0,0,1367,141,1368,1104,12,784,101,1369,12,92,0,553,1,12,12,136,1370,12,1371,12,12,12,12,0,173,1372,553,136,979,136,12,1373,12,1374,0,1,1,1367,157,1375,0,1,882,0,12,12,1376,12,486,0,0,0,0,0,157,0,0]
private def sixMenuAtP73 : Array Nat := #[496,0,12,1377,1378,157,0,12,495,883,1379,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def sixMenuAt : Array (Array Nat) := #[sixMenuAtP0,sixMenuAtP1,sixMenuAtP2,sixMenuAtP3,sixMenuAtP4,sixMenuAtP5,sixMenuAtP6,sixMenuAtP7,sixMenuAtP8,sixMenuAtP9,sixMenuAtP10,sixMenuAtP11,sixMenuAtP12,sixMenuAtP13,sixMenuAtP14,sixMenuAtP15,sixMenuAtP16,sixMenuAtP17,sixMenuAtP18,sixMenuAtP19,sixMenuAtP20,sixMenuAtP21,sixMenuAtP22,sixMenuAtP23,sixMenuAtP24,sixMenuAtP25,sixMenuAtP26,sixMenuAtP27,sixMenuAtP28,sixMenuAtP29,sixMenuAtP30,sixMenuAtP31,sixMenuAtP32,sixMenuAtP33,sixMenuAtP34,sixMenuAtP35,sixMenuAtP36,sixMenuAtP37,sixMenuAtP38,sixMenuAtP39,sixMenuAtP40,sixMenuAtP41,sixMenuAtP42,sixMenuAtP43,sixMenuAtP44,sixMenuAtP45,sixMenuAtP46,sixMenuAtP47,sixMenuAtP48,sixMenuAtP49,sixMenuAtP50,sixMenuAtP51,sixMenuAtP52,sixMenuAtP53,sixMenuAtP54,sixMenuAtP55,sixMenuAtP56,sixMenuAtP57,sixMenuAtP58,sixMenuAtP59,sixMenuAtP60,sixMenuAtP61,sixMenuAtP62,sixMenuAtP63,sixMenuAtP64,sixMenuAtP65,sixMenuAtP66,sixMenuAtP67,sixMenuAtP68,sixMenuAtP69,sixMenuAtP70,sixMenuAtP71,sixMenuAtP72,sixMenuAtP73]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def sixOffset : Nat → Nat
  | 6 => 0
  | 7 => 11
  | 8 => 582
  | 9 => 2893
  | 10 => 4454
  | 11 => 4684
  | 12 => 4707
  | _ => 0
private def inlineMenu (m k i : Nat) : List Nat :=
  if m=251 then
    let mnum := atSix sixMenuAt (sixOffset k+i)
    let offsetCode := atSix sixMenuStarts mnum
    (List.range (offsetCode % 16)).map (fun j => atSix sixWords (atSix sixMenuWords (offsetCode / 16+j)))
  else []

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag query xs hx
    rcases List.mem_append.mp hx with old | extra
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using old
      obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) h
    · exact closeSix_sound extra g.mode



abbrev LocalSix := BitVec 6
private def localFun (x : LocalSix) : Wire (Fin 6) := fun i => x.getLsbD i.val
private def localWord (f : Wire (Fin 6)) : LocalSix :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem local_read (f : Wire (Fin 6)) (i : Fin 6) :
    (localWord f).getLsbD i.val = f i := by
  simp only [localWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
private theorem local_ext {a b : LocalSix} (eq : ∀ i : Fin 6, localFun a i = localFun b i) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j h => eq ⟨j,h⟩
private theorem local_back (x : LocalSix) : localWord (localFun x)=x := by
  apply local_ext
  intro i
  exact local_read _ _
private theorem local_inv (a : Wire (Fin 6)) : localWord (inv a) = ~~~localWord a := by
  apply local_ext
  intro i
  change (localWord (inv a)).getLsbD i.val = (~~~localWord a).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not, local_read] <;>
    simp [inv, i.isLt]
private theorem local_combine (op : Bool) (a b : Wire (Fin 6)) :
    localWord (combine op a b) = if op then localWord a ||| localWord b else localWord a &&& localWord b := by
  cases op <;> apply local_ext <;> intro i
  · change (localWord (combine false a b)).getLsbD i.val = (localWord a &&& localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_and, local_read, local_read] <;> rfl
  · change (localWord (combine true a b)).getLsbD i.val = (localWord a ||| localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_or, local_read, local_read] <;> rfl
private def localBag (B : List LocalSix) := 0 :: 63 :: (B ++ B.map (fun a => ~~~a))
private theorem local_available {bank v} (ha : Available true bank v) :
    localWord v ∈ localBag (bank.map localWord) := by
  simp only [localBag,List.mem_cons,List.mem_append,List.mem_map]
  rcases ha with hv | ⟨b,rfl⟩ | ⟨_,hn⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_,hv,rfl⟩))
  · cases b
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (Or.inl (by decide +kernel))
  · right; right; right
    exact ⟨_,⟨_,hn,rfl⟩,by rw [local_inv]; simp⟩
private def genLocal (B : List LocalSix) :=
  ((localBag B).flatMap fun a => (localBag B).flatMap fun b => [a &&& b, a ||| b]).eraseDups
private theorem local_next {bank a b} (op : Bool) (ha : Available true bank a) (hb : Available true bank b) :
    localWord (combine op a b) ∈ genLocal (bank.map localWord) := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap]
  refine ⟨_,local_available ha,_,local_available hb,?_⟩
  cases op <;> simp [local_combine]
private def localMiss (M : LocalSix) : Nat → List LocalSix → Bool
  | 0,B => !(localBag B).contains M
  | n+1,B => !(localBag B).contains M && (genLocal B).all (fun w => localMiss M n (w::B))
private theorem local_prefix {roots p bank} (h : Reach true roots p bank) (M : LocalSix) :
    ∀ d, localMiss M (p+d) (roots.map localWord) = true → localMiss M d (bank.map localWord) = true := by
  induction h using Reach.ind with
  | start => intro d hd; simpa only [Nat.zero_add] using hd
  | two op h ha hb ih =>
    intro d hd
    have old := ih (d+1) (by simpa only [Nat.succ_add,Nat.add_succ] using hd)
    simp only [localMiss,Bool.and_eq_true,List.all_eq_true] at old
    exact old.2 _ (local_next op ha hb)
private def missesPair (M a b : LocalSix) :=
  decide (M ≠ (a &&& b) ∧ M ≠ ~~~(a &&& b) ∧ M ≠ (a ||| b) ∧ M ≠ ~~~(a ||| b))
private def fastLast (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (localBag B).all (fun a => (localBag B).all (missesPair M a))
private theorem fastLast_sound {M B} (h : fastLast M B=true) : localMiss M 1 B=true := by
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true,missesPair,decide_eq_true_eq] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => !(localBag (w::B)).contains M))=true
  rw [Bool.and_eq_true]
  refine ⟨h.1,List.all_eq_true.mpr ?_⟩
  intro w hw
  have grow : M ∈ localBag (w::B) → M=w ∨ M = ~~~w ∨ M ∈ localBag B := by
    simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
    tauto
  have outside : M ∉ localBag B := by simpa using h.1
  have absent : M ∉ localBag (w::B) := by
    intro hm
    have yes := grow hm
    simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hw
    obtain ⟨a,ha,b,hb,eq⟩ := hw
    have ne := h.2 a ha b hb
    rcases eq with rfl | rfl
    · exact yes.elim ne.1 (fun x => x.elim ne.2.1 outside)
    · exact yes.elim ne.2.2.1 (fun x => x.elim ne.2.2.2 outside)
  simpa using absent
private def fastTwo (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (genLocal B).all (fun w => fastLast M (w::B))
private theorem fastTwo_sound {M B} (h : fastTwo M B=true) : localMiss M 2 B=true := by
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => localMiss M 1 (w::B)))=true
  rw [Bool.and_eq_true]
  exact ⟨h.1,List.all_eq_true.mpr (fun w hw => fastLast_sound (h.2 w hw))⟩

private def majRoots : List LocalSix := [25,42,52]
private def majGoal : LocalSix := 56

private def permWord (p : Fin 6 → Fin 6) (w : LocalSix) := localWord fun i => localFun w (p i)
private theorem perm_not (p) (w) : permWord p (~~~w) = ~~~(permWord p w) := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (~~~localWord _).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not,local_read] <;>
    simp [localFun, (p i).isLt, i.isLt]
private theorem perm_and (p) (a b) : permWord p (a &&& b) = permWord p a &&& permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ &&& localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_and,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_and]
private theorem perm_or (p) (a b) : permWord p (a ||| b) = permWord p a ||| permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ ||| localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_or,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_or]
private def embeds (p : Fin 6 → Fin 6) (a b : List LocalSix) := (localBag a).all fun w => (localBag b).contains (permWord p w)
private theorem emb_ok (p) (a b) : embeds p a b = true ↔ ∀ w ∈ localBag a, permWord p w ∈ localBag b := by
  simp only [embeds,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
private theorem bag_cons (x w : LocalSix) (B : List LocalSix) :
    x ∈ localBag (w::B) ↔ x=w ∨ x = ~~~w ∨ x ∈ localBag B := by
  simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
  tauto
private theorem emb_cons {p a b} (h : embeds p a b=true) (w) :
    embeds p (w::a) (permWord p w::b)=true := by
  apply (emb_ok _ _ _).mpr
  intro x hx
  apply (bag_cons _ _ _).mpr
  rcases (bag_cons _ _ _).mp hx with rfl | rfl | old
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (perm_not _ _))
  · exact Or.inr (Or.inr ((emb_ok _ _ _).mp h x old))
private theorem emb_move {p a b w} (h : embeds p a b=true) (mw : w ∈ genLocal a) :
    permWord p w ∈ genLocal b := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at mw ⊢
  obtain ⟨x,hx,y,hy,hw⟩ := mw
  refine ⟨_,(emb_ok _ _ _).mp h x hx,_,(emb_ok _ _ _).mp h y hy,?_⟩
  rcases hw with rfl | rfl
  · exact Or.inl (perm_and _ _ _)
  · exact Or.inr (perm_or _ _ _)
private theorem pullMiss {p M} (fixed : permWord p M=M) (n : Nat) {a b}
    (cov : embeds p a b=true) (no : localMiss M n b=true) : localMiss M n a=true := by
  induction n generalizing a b with
  | zero =>
    simp only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at no ⊢
    intro hm
    exact no (fixed ▸ (emb_ok _ _ _).mp cov M hm)
  | succ n ih =>
    simp only [localMiss,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,List.all_eq_true] at no ⊢
    refine ⟨fun hm => no.1 (fixed ▸ (emb_ok _ _ _).mp cov M hm),?_⟩
    intro w hw
    exact ih (emb_cons cov _) (no.2 _ (emb_move cov hw))

private def axisData : Array Nat := #[181896,178256,153217,145937,120898,117258]
private def rootHints : Array Nat := #[0,8,10,0,12,0,0,0,64,72,74,0,0,0,0,0,65,73,0,0,76,0,0,0,0,0,0,77,0,75,0,67,67,0,75,0,77,0,0,0,0,0,0,76,0,0,73,65,0,0,0,0,0,74,72,64,0,0,0,12,0,10,8,0]

private def rootTag (w : LocalSix) := rootHints[w.toNat]?.getD 0
private def rootCase (w : LocalSix) := BitVec.ofNat 6 (rootTag w / 8)
private def rootAxis (w : LocalSix) (i : Fin 6) := Fin.ofNat 6 ((axisData[rootTag w % 8]?.getD 0 >>> (3*i.val)) % 8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem firstPortfolio : ∀ w ∈ genLocal majRoots,
    permWord (rootAxis w) majGoal = majGoal ∧ embeds (rootAxis w) (w::majRoots) (rootCase w::majRoots)=true ∧
      rootCase w ∈ ([0,1,8,9] : List LocalSix) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst0 : localMiss majGoal 2 (0::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst1 : localMiss majGoal 2 (1::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst8 : localMiss majGoal 2 (8::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst9 : localMiss majGoal 2 (9::majRoots)=true := by apply fastTwo_sound; decide +kernel

private theorem local_miss_three : localMiss majGoal 3 majRoots=true := by
  change (_ && _) = true
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel,List.all_eq_true.mpr ?_⟩
  intro w hw
  obtain ⟨fixed, emb, sel⟩ := firstPortfolio w hw
  apply pullMiss fixed 2 emb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at sel
  rcases sel with e | e | e | e
  · simpa only [e] using cheapFirst0
  · simpa only [e] using cheapFirst1
  · simpa only [e] using cheapFirst8
  · simpa only [e] using cheapFirst9

private theorem local_now {M n B} (h : localMiss M n B=true) : M ∉ localBag B := by
  cases n with
  | zero => simpa only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h
  | succ n =>
    simp only [localMiss,Bool.and_eq_true] at h
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h.1
theorem majority_six_price {p bank} (reach : Reach true (majRoots.map localFun) p bank)
    (ok : Available true bank (localFun majGoal)) : 4 ≤ p := by
  by_contra small
  have le : p ≤ 3 := by omega
  have start : localMiss majGoal (p+(3-p)) ((majRoots.map localFun).map localWord)=true := by
    rw [show p+(3-p)=3 by omega]
    change localMiss majGoal 3 [localWord (localFun 25), localWord (localFun 42), localWord (localFun 52)] = true
    simpa only [majRoots,local_back] using local_miss_three
  have no := local_now (local_prefix reach _ _ start)
  have yes := local_available ok
  rw [local_back] at yes
  exact no yes

private theorem majority_not_constant : ¬ Constant (localFun majGoal) := by
  rintro ⟨b,h⟩
  have h0 : false=b := congrFun h (0 : Fin 6)
  have h3 : true=b := congrFun h (3 : Fin 6)
  cases b <;> contradiction

theorem majority_restriction {T k} (r : Fin 6 → Row) (ws : List Sig) (nd : ws.Nodup)
    (target : restrictRows r (observe T) = localFun majGoal)
    (inputs : supply true (majRoots.map localFun) ((ws.map observe).map (restrictRows r)))
    (price : k < 4 + mass ((ws.map observe).map (restrictRows r))) :
    Impossible true T k ws.toFinset := by
  intro p hp hl
  have trace := list_run hl ws nd rfl
  have nonconst : ¬ Constant (restrictRows r (observe T)) := by rw [target]; exact majority_not_constant
  have lb : ∀ n bank, Reach true (majRoots.map localFun) n bank →
      Available true bank (restrictRows r (observe T)) → 4 ≤ n := by
    rw [target]
    intro n bank h hgoal
    exact majority_six_price h hgoal
  have h := projected_bound r trace nonconst Reach.start inputs lb
  omega


private def faceRows (word : Nat) (i : Fin 6) : Row := Fin.ofNat 512 ((word >>> (8*i.val)) % 256)
private theorem sampledFace (r : Fin 6 → Row) (w : Sig) :
    restrictRows r (observe w) = localFun (ofRows r w) := by
  funext i
  exact (ofRows_bit r w i).symm
private theorem faceInv (v : LocalSix) : localFun (~~~v) = inv (localFun v) := by
  funext i
  simp [localFun,inv,i.isLt]
private theorem faceZero : localFun 0 = fun _ => false := by funext i; simp [localFun]
private theorem faceOne : localFun 63 = fun _ => true := by decide +kernel
private theorem permittedFace {w : LocalSix} (mem : w ∈ localBag majRoots) :
    Available true (majRoots.map localFun) (localFun w) := by
  simp only [localBag,List.mem_cons,List.mem_append,List.mem_map] at mem
  rcases mem with rfl | rfl | hw | ⟨a,ha,rfl⟩
  · exact Or.inr (Or.inl ⟨_,faceZero⟩)
  · exact Or.inr (Or.inl ⟨_,faceOne⟩)
  · exact Or.inl (List.mem_map_of_mem hw)
  · right; right
    refine ⟨rfl,?_⟩
    rw [faceInv,inv_inv']
    exact List.mem_map_of_mem ha
private def flatWeight (w : LocalSix) :=
  if w = (0 : LocalSix) ∨ w = (63 : LocalSix) then 1 else 0
private theorem flat_le (w : LocalSix) : flatWeight w ≤ cost (localFun w) := by
  classical
  unfold flatWeight
  split
  next h =>
    have hc : Constant (localFun w) := by
      rcases h with rfl | rfl
      · exact ⟨_,faceZero⟩
      · exact ⟨_,faceOne⟩
    simp only [cost,if_pos hc,Nat.le_refl]
  next => exact Nat.zero_le _
private theorem faceMass (ws : List Sig) (r : Fin 6 → Row) :
    ((ws.map (ofRows r)).map flatWeight).sum ≤ mass ((ws.map observe).map (restrictRows r)) := by
  induction ws with
  | nil => simp [mass]
  | cons w ws ih =>
    simp only [List.map_cons,List.sum_cons,mass_cons]
    rw [sampledFace]
    exact Nat.add_le_add (flat_le _) ih
private def faceOK (T : Sig) (k : Nat) (ws : List Sig) (word : Nat) :=
  let r := faceRows word
  let vals := ws.map (ofRows r)
  decide ws.Nodup && (ofRows r T == majGoal) && vals.all (fun w => (localBag majRoots).contains w) &&
    decide (k < 4+(vals.map flatWeight).sum)
private theorem faceOK_sound {T k ws word} (ok : faceOK T k ws word=true) : Impossible true T k ws.toFinset := by
  simp only [faceOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,List.contains_eq_mem] at ok
  let r := faceRows word
  apply majority_restriction r ws ok.1.1.1
  · rw [sampledFace,ok.1.1.2]
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    rw [sampledFace]
    apply permittedFace
    simpa only [decide_eq_true_eq] using (ok.1.2 _ (List.mem_map_of_mem hw))
  · exact lt_of_lt_of_le ok.2 (Nat.add_le_add_left (faceMass ws r) _)

private def majorityTermsP0 : Array Nat := #[167234502168593,27699721607312,167233965297681,27699184734256,12383095554626,54499780669584,167367109283856,10038009727520,12383632362050,28113112209552,211387573895169,167748966553617,167882110539824,211417758203912,160185529143600,28113514868880,160082449928472,160185931796784,150359431448640,27700795349136,28112038467728,193726935765009,150358374484032,27701198032944,72293046813056,54632406585744,28143059997072,28141449384336,211387575992321,167235575910417,54117010510104,176095947161608,142661793087808,10177998848064,72293044715904,28141986255248,27729132523824,12383632427522,71777648640264,10205933338944,36455835500808,36971231576448,27699184736304,12383632427586,71777650737416,73985295516426,12413580215106,81412229841411,61680849006609,79204582973441,53984384593944,62328987981968,79989626112128,44019674013697,12245656603232,10175985551456,28044124297344,62228440559760,61680849031185,79752174518400,167367109283888,79750580691072,62226309853328,149846040805440]
private def majorityTermsP1 : Array Nat := #[149843910099008,54117010510096,160082449928464,159642593366064,54501793935504,72025527902336,54432806023296,193726935765008,44566208602240,79750043811968,73985295516418,54633346109840,10175985551424,167369239990320,54634419851664,79752174518912,81412229841410,44567265681536,176070072500226,79752174649472,10175985551426,10175985551936,73985295516170,12413580214850,167369239990288,72025527894144,211417756106760,142662732611904,12413580215042,79204582965249,44019673997313,176065760755713,12375008938498,10038009727008,10451937200256,27699184736272,143085225017344,10038009727024,10451937200272,10038009727072,12245656603202,27699184736400,36840618926208,143085225017376,79752174526592,53984384593936,211417756106752,142119394181184,71508118552584,44567265566848,73715765428746,73715765428738,193757117976592,20213995278432,159539111497744,141981418356832,141981418356800,37944425586816]
private def majorityTerms : Array (Array Nat) := #[majorityTermsP0,majorityTermsP1]
private def majorityIDsP0 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,9,10,11,12,11,13,14,9,15,14,16,17,18,19,20,21,11,22,23,24,12,12,25,25,12,25,26,27,16,28,27,2,2,12,27,27,29,0,29,9,30,11,31,32,32,33,34,22,34,26,35,35,22,35]
private def majorityIDsP1 : Array Nat := #[30,25,36,37,38,39,40,41,42,43,30,44,30,25,42,30,30,25,45,30,25,34,43,45,30,25,46,47,36,36,48,46,36,49,50,49,36,36,36,51,46,52,53,46,27,54,42,42,42,42,42,55,42,42,42,42,43,43,56,43,42,57,27,58]
private def majorityIDsP2 : Array Nat := #[9,9,30,36,16,27,59,60,61,62,62,63,64,62,62,30,62,65,66,36,62,42,42,67,68,16,27,27,69,42,3,70,70,42,71,63,38,39,72,73,73,45,73,74,66,75,46,73,68,76,43,4,43,68,17,77,78,21,17,57,59,79,80,81]
private def majorityIDsP3 : Array Nat := #[82,82,83,80,84,7,82,85,82,42,80,42,86,87,80,87,59,59,88,9,9,42,9,68,89,68,68,68,7,68,42,68,89,89,68,89,9,68,16,16,21,90,29,17,29,28,26,29,26,21,29,29,21,26,29,29,78,21,21,29,91,26,48,29]
private def majorityIDsP4 : Array Nat := #[10,29,10,10,48,21,92,93,94,95,36,46,48,49,48,21,47,36,30,48,48,48,48,21,47,48,21,10,46,47,48,21,9,29,96,42,42,9,42,43,42,42,9,42,9,42,42,42,9,37,96,97,98,42,37,42,9,37,37,37,42,9,9,42]
private def majorityIDsP5 : Array Nat := #[42,99,9,100,42,43,9,101,102,42,76,42,76,9,76,9,29,9,9,9,97,9,97,97,9,42,42,43,42,55,42,42,48,42,42,42,99,42,43,42,56,43,43,42,42,43,42,42,42,42,9,42,43,9,43,9,43,43,42,103,48,42,42,42]
private def majorityIDsP6 : Array Nat := #[42,42,104,42,43,42,9,42,9,43,43,43,9,42,9,42,43,42,42,48,42,42,42,42,9,29,9,9,42,55,55,55,9,42,9,55,42,42,9,21,42,48,55,42,42,105,42,9,42,42,9,42,21,9,42,9,9,9,57,9,9,42,42,42]
private def majorityIDsP7 : Array Nat := #[42,21,42,42,42,43,42,42,42,42,9,9,9,9,9,36,42,43,42,9,30,48,42,42,48,42,48,42,29,9,43,42,9,9,42,42,42,43,9,43,9,10,76,10,103,9,43,43,9,59,43,9,43,9,43,42,10,103,43,43,47,47,43,47]
private def majorityIDsP8 : Array Nat := #[42,42,9,9,29,9,9,98,76,29,9,9,9,9,29,29,9,43,29,42,42,57,48,29,59,48,42,106,67,42,68,68,42,107,42,50,68,42,42,42,42,42,68,89,77,108,67,68,67,67,89,67,67,67,67,42,68,67,63,47,68,63,68,42]
private def majorityIDsP9 : Array Nat := #[59,42,50,68,29,29,77,42,67,69,77,77,29,68,50,68,42,29,77,42,68,68,50,68,77,68,67,69,109,68,68,70,42,42,67,68,67,67,42,69,69,69,55,42,77,42,68,68,10,68,109,110,21,68,68,68,89,89,68,68,68,42,68,42]
private def majorityIDsP10 : Array Nat := #[68,42,42,68,68,67,42,68,21,67,68,68,67,21,68,67,42,42,63,63,57,59,59,77,77,57,57,57,93,21,47,111,68,89,89,37,112,89,76,76,76,113,111,111,111,29,63,76,111,114,89,43,29,63,43,89,89,114,89,29,63,47,43,111]
private def majorityIDsP11 : Array Nat := #[115,68,89,43,111,111,111,111,43,68,68,89,115,116,21,89,10,111,117,89,43,89,63,111,76,10,111,68,10,89,111,10,117,111,43,68,68,68,68,68,68,9,9,9,67,111,68,89,89,106,68,68,57,89,68,29,9,9,106,118,67,111,68,69]
private def majorityIDsP12 : Array Nat := #[68,68,89,106,68,68,119,120,67,111,118,67,68,57,89,68,68,9,89,68,59,9,68,121,121,121,121,68,68,42,68,42,68,59,121,121,107,106,97,77,63,111,57,68,68,42,68,57,68,68,68,42,117,111,89,59,89,89,89,57,59,9,43,9]
private def majorityIDsP13 : Array Nat := #[121,43,9,42,9,42,43,43,9,9,42,9,42,42,9,42,9,9,9,43,43,9,42,42,42,42,42,42,42,42,42,43,9,43,43,43,43,9,9,9,9,9,9,9,9,9,9,57,68,68,59,42,42,68,68,68,68,68,68,68,68,68,68,68]
private def majorityIDsP14 : Array Nat := #[59,89,121,89,43,43,89,89,89,89,89,89,89,89,89,9,9,68,89,68,89]
private def majorityIDs : Array (Array Nat) := #[majorityIDsP0,majorityIDsP1,majorityIDsP2,majorityIDsP3,majorityIDsP4,majorityIDsP5,majorityIDsP6,majorityIDsP7,majorityIDsP8,majorityIDsP9,majorityIDsP10,majorityIDsP11,majorityIDsP12,majorityIDsP13,majorityIDsP14]
private def majorityWord : Nat → Nat → Nat
  | 6,i =>
    if 0 ≤ i ∧ i < 5 then atSix majorityTerms (atSix majorityIDs (0+i-0)) else 0
  | 7,i =>
    if 0 ≤ i ∧ i < 177 then atSix majorityTerms (atSix majorityIDs (5+i-0)) else 0
  | 8,i =>
    if 104 ≤ i ∧ i < 749 then atSix majorityTerms (atSix majorityIDs (182+i-104)) else 0
  | 9,i =>
    if 579 ≤ i ∧ i < 669 then atSix majorityTerms (atSix majorityIDs (827+i-579)) else 0
  | _,_ => 0
private def majorityAt (g : Forest) (k i : Nat) :=
  g.mode && faceOK (targetOf g) k (stateSet g k i) (majorityWord k i)
private theorem majorityAt_sound {g k i} (h : majorityAt g k i=true) :
    Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [majorityAt,Bool.and_eq_true] at h
  rw [h.1]
  exact faceOK_sound h.2
private def validAt (g : Forest) (k i : Nat) := nodeVerified g k i || majorityAt g k i

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => validAt g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    validAt g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    have check := block_at (rows _ hk) i (by omega) (by omega)
    simp only [validAt,Bool.or_eq_true] at check
    rcases check with normal | major
    · apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
      exact normal
    · exact majorityAt_sound major
  | succ k ih =>
    intro hk i hi
    have check := block_at (rows _ hk) i (by omega) (by omega)
    simp only [validAt,Bool.or_eq_true] at check
    rcases check with normal | major
    · apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega))
      exact normal
    · exact majorityAt_sound major

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)) (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) (query : List Sig) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag query, ys=xs.map BitVec.toNat := by
  suffices old : ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, ys=xs.map BitVec.toNat by
    obtain ⟨xs,mem,eq⟩ := old
    exact ⟨xs,List.mem_append_left _ mem,eq⟩
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨by simp [validAt,h (start+n) (by omega) (by omega)],ih (fun i le lt => h i le (by omega))⟩

private def majorityBatch (g : Forest) (k start n : Nat) :=
  (List.range n).all fun j => majorityAt g k (start+j)
private theorem majorBlocks {g k start n} (h : majorityBatch g k start n=true) : block g k start n=true := by
  have go : ∀ i, start ≤ i → i < start+n → majorityAt g k i=true := by
    intro i lo hi
    have tx := List.all_eq_true.mp h (i-start) (List.mem_range.mpr (by omega))
    simpa only [Nat.add_sub_of_le lo] using tx
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨by simp [validAt,go (start+n) (by omega) (by omega)],ih (fun i lo hi => go i lo (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,3]⟩,⟨.or,[1,8]⟩,⟨.or,[2,5]⟩,⟨.or,[1,6]⟩,⟨.or,[4,7]⟩,⟨.or,[5,7]⟩,⟨.and,[12,11]⟩,⟨.and,[13,9]⟩,⟨.and,[3,0]⟩,⟨.and,[6,8]⟩,⟨.and,[7,10]⟩,⟨.or,[14,15]⟩,⟨.or,[19,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 7, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 7, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort 
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim
def g41Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g41D3 (j : Nat) := if j=0 then 0x7 else 0
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(137,[117,101]),(161,[83,67,116,100]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(193,[99,67,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43A : List (List Nat) := [[],[48]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K41 V41) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K41 5 [(43,[]),(89,[65,33,101]),(178,[80,65,32,115,33,99]),(195,[99,67,117]),(202,[48,32,98,66,117]),(209,[65,33,115,101,83]),(216,[48,65,32,114,101,82]),(226,[16,96,32,83,66,115,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V41 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) := if j=0 then 0xf else 0
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : block g51 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B3 : block g51 3 0 1=true := g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=65605) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 4 [(51,[]),(58,[48,32]),(83,[65,101]),(90,[16,96,32,50,67,84]),(99,[16,100]),(106,[16,48,32,100]),(113,[64,16,33,50,83,99]),(114,[80,65,32,50,97,49]),(120,[64,49,32,82,98]),(147,[117,101]),(154,[48,32,117,101]),(240,[64,113,32,49,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3e58e3ffc1ffcff3e,0x58e3ffc1ffcff3e58e3f])),(BitVec.ofNat 152 (word80 [0x200012490842080200,0x1249084208020001249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfcfa71c7ffe0ff3fcf,0xa71c7ffe0ff3fcfa71c7])),(BitVec.ofNat 152 (word80 [0x400024921084100400,0x2492108410040002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0e81f8ffff003ff0,0xe81f8ffff003ff0e81f8])),(BitVec.ofNat 152 (word80 [0x804ec924a108a2a804,0xec924a108a2a804ec924]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0xa99c924c210c030a9,0x9c924c210c030a99c924]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(32,0,73,0,4)]
def g105A : List (List Nat) := [[],[101],[48],[48,101]]
def g105D4 (j : Nat) := if j=0 then 0x1f else 0
def g105L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g105D4)
  | _ => emptyPacking
def g105I (_ _ : Nat) : Option (Nat × Nat) := none
def g105 : Forest := ⟨105,4,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : block g105 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : block g105 4 0 1=true := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=3) (before_sound K51 V51) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K51 5 [(105,[]),(163,[80,33,49,113,97]),(225,[115,67]),(232,[48,16,33,114,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V51 low105 (by decide +kernel)
def g169Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g169C : List ColumnInfo := [(1,0,168,0,4),(8,0,161,0,4),(32,0,137,0,4),(128,0,41,0,4)]
def g169A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[48],[48,117],[48,80],[48,80,112],[48,112,80],[48,112],[80,48],[80,48,115],[80],[80,112],[80,115],[80,115,48],[112,48,83],[112,48],[112,80],[112],[112,83,48],[112,83]]
def g169D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g169D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g169H4 (j : Nat) := if j=0 then 0xe else 0
def g169D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g169H5 := limbs80 #[#[0x10000280c49030031720,0x104]]
def g169D6 (j : Nat) := if j=0 then 0x3904f else 0
def g169H6 := limbs80 #[#[0x280000000000000000,0x80202d0280000]]
def g169L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g169D3)
  | 4 => (3,2,2,0,0,5,0,g169D4)
  | 5 => (1,1,2,0,0,0,0,g169D5)
  | 6 => (1,0,2,0,0,0,0,g169D6)
  | _ => emptyPacking
def g169I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 2 0 3 1 0 g169H4
  | 5 => lookupShort 2 13 3 7 2 3 g169H5
  | 6 => lookupShort 1 23 0 7 0 5 g169H6
  | _ => fun _ => none
def g169 : Forest := ⟨169,6,fun i => g169Y[i]?.getD (0,0),g169C,g169A,g169L,g169I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P3_0 : block g169 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B3 : block g169 3 0 2=true := g169P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P4_0 : block g169 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B4 : block g169 4 0 3=true := g169P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P5_0 : block g169 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B5 : block g169 5 0 1=true := g169P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P6_0 : block g169 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B6 : block g169 6 0 1=true := g169P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169T : checkedTables g169 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g169 0 0 0 = true)
  · exact (rfl : block g169 1 0 0 = true)
  · exact (rfl : block g169 2 0 0 = true)
  · exact g169B3
  · exact g169B4
  · exact g169B5
  · exact g169B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169G : graphValid g169 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low169 : Lower true (varsX 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K105 V105) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K105 7 [(169,[]),(201,[101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V169 : Known true K169 := extend_ok (m:=169) V105 low169 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,16,41,2,5),(16,0,43,0,5),(1,0,58,0,4),(2,16,41,0,4),(8,0,51,0,4)]
def g59A : List (List Nat) := [[],[48]]
def g59D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g59D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g59H5 (j : Nat) := if j=0 then 0x4 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 (j : Nat) := if j=0 then 0x1208000270005 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g59H5
  | 6 => lookupShort 1 11 0 5 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K169) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K169 V169) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K169 7 [(59,[]),(91,[65,101]),(155,[117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V169 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff00ffc3fffff007fe,0x1ff0fffff45e030f00ff])),(BitVec.ofNat 152 (word80 [0xa0a02880800a05014,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffff0003fc3ffff800,0x1fff0ff014b4f9000f00])),(BitVec.ofNat 152 (word80 [0x2c0c4b105092c46258,0x8940244214b4b1777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffc003fffffff,0xe0000fff2bb526f0f00f])),(BitVec.ofNat 152 (word80 [0x30100c006103008060,0x1844080299020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x40a090228224090480,0x12000904024948888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80c0e00300380e0701,0x1c088e084628c4cccccc]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,73,32,5),(2,0,105,0,5),(64,0,43,0,5),(1,0,106,0,4),(8,0,99,0,4),(32,2,73,0,4)]
def g107A : List (List Nat) := [[],[48]]
def g107D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g107D5 (j : Nat) := if j=0 then 0xc8404fd20 else 0
def g107H5 (j : Nat) := if j=0 then 0x3 else 0
def g107D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g107H6 (j : Nat) := if j=0 then 0x8 else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (1,1,3,0,0,0,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g107H5
  | 6 => lookupShort 1 2 0 2 0 0 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : block g107 6 0 1=true := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 7 [(107,[]),(121,[65,33,101]),(179,[80,65,115,49,16,96]),(186,[80,65,32,115,33,99]),(241,[65,33,115,101]),(248,[48,65,32,114,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ffffff003ff,0xff87ffc3545d520f83e0])),(BitVec.ofNat 152 (word80 [0xa0a80a209002a0a814,0x910008a445812318c63]))),((BitVec.ofNat 152 (word80 [0xfffc000ff87ffffc01,0xfff87ffcd372a6007c1f])),(BitVec.ofNat 152 (word80 [0xc0310c402120c43118,0x8201210052302694a529]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x2c05002c20b00c020,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb02608b044c090241,0x30004c100907c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc03800c00700e0381,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(1,0,114,0,4),(2,0,113,0,4),(16,0,99,0,4),(32,0,83,0,4),(64,0,51,0,4)]
def g115A : List (List Nat) := [[],[65,101],[16,100],[16,96,64,84],[64,16,81,97],[64,81],[80,65,97,16],[80,97],[96,84],[96,81,65,64]]
def g115D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g115D5 (j : Nat) := if j=0 then 0xc1a0fd30fd10 else 0
def g115H5 (j : Nat) := if j=0 then 0x2 else 0
def g115D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g115H6 := limbs80 #[#[0x900000000000000003e2,0x9c0000000002a8000601,0x40033000005000]]
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (2,1,3,0,0,4,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g115H5
  | 6 => lookupShort 2 37 2 6 1 3 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : block g115 4 0 1=true := g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 2=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : block g115 6 0 1=true := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=65605) (before_sound K107 V107) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K107 7 [(115,[]),(122,[16,96,32,50,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V107 low115 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,7)]
def g171A : List (List Nat) := [[],[117],[48],[48,117]]
def g171D7 (j : Nat) := if j=0 then 0x3f else 0
def g171L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact (rfl : block g171 6 0 0 = true)
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K115 V115) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K115 8 [(171,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V115 low171 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(4,0,169,0,7)]
def g173A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g173D7 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g173D7)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,7,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P7_0 : block g173 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B7 : block g173 7 0 1=true := g173P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact (rfl : block g173 6 0 0 = true)
  · exact g173B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 8 := lower_forest (g:=g173) (i:=0) (hints:=1795) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 8 [(203,[33,101]),(217,[66,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffff0fffc01f,0xf0fffff0c8d71c00f0f0])),(BitVec.ofNat 152 (word80 [0x20a8541412200a8540,0xa2120022881714333333]))),((BitVec.ofNat 152 (word80 [0xffffe01fff0ffffe0,0xff0fff2c347b0f000f])),(BitVec.ofNat 152 (word80 [0x423118984402230184,0xc404224008047b555555]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xff000fff33b526000f0f])),(BitVec.ofNat 152 (word80 [0x88c0602118448c2611,0x98488032b104aaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c06088300806,0x200304014868444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0201018000c03018,0x8c08c0846a080888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(2,0,209,0,5)]
def g211A : List (List Nat) := [[],[65,118]]
def g211D5 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g211D5)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,5,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P5_0 : block g211 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B5 : block g211 5 0 1=true := g211P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact g211B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 6 := lower_forest (g:=g211) (i:=0) (hints:=65606) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K173 6 [(211,[]),(218,[48,32]),(242,[80,65,32,50,97,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc3fe00ff87f87ffc0,0x7fffffe3dba15000ff0f])),(BitVec.ofNat 152 (word80 [0x288140a05101100285,0x502004842a141111111]))),((BitVec.ofNat 152 (word80 [0x3ffff0007ff87fff,0x807f1ffc2adc600f00f0])),(BitVec.ofNat 152 (word80 [0x310984c26212011306,0x260444812acc43333333]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff80007fff,0xff801fff949db0f000ff])),(BitVec.ofNat 152 (word80 [0x421209048024222408,0x82889001410b4444444]))),((BitVec.ofNat 152 (word80 [0xffc000000000007fff,0xffffe0000b66bf000f00])),(BitVec.ofNat 152 (word80 [0x801c0e070438443810,0x30300e120946b6666666]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x2010080040004020,0x40401000000008888888]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5),(2,0,225,0,5),(32,0,195,0,5),(64,0,163,0,5)]
def g227A : List (List Nat) := [[],[80,97]]
def g227D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g227L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g227D6)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,6,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P6_0 : block g227 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B6 : block g227 6 0 1=true := g227P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact (rfl : block g227 5 0 0 = true)
  · exact g227B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 7 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K211 V211) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K211 7 [(227,[]),(234,[48,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V211 low227 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe03f9fc07f3f8ffc,0xfff9ff3e70000f0f0ff])),(BitVec.ofNat 152 (word80 [0x204081008102010008,0x20810020000111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc01fff803ff1ff,0xf03fe7fce0e00f0f0f0f])),(BitVec.ofNat 152 (word80 [0x408102010204020010,0x41020040000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf000001fffffc001ff,0xffc007ff1d60f0000ff0])),(BitVec.ofNat 152 (word80 [0x850a144a14281424a0,0x821452805d6444444444]))),((BitVec.ofNat 152 (word80 [0xffffffe000000001ff,0xfffff8000bbf000ff000])),(BitVec.ofNat 152 (word80 [0x60c180c18309848c1,0x418030a8bb444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x81020102040200102,0x8200400000888888888]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(32,0,201,0,7)]
def g233A : List (List Nat) := [[],[101],[115],[115,101],[48],[48,101],[48,112],[48,112,101],[112,48],[112,48,101],[112],[112,101]]
def g233D7 (j : Nat) := if j=0 then 0x3f else 0
def g233L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g233D7)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,7,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P7_0 : block g233 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B7 : block g233 7 0 1=true := g233P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : checkedTables g233 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g233 0 0 0 = true)
  · exact (rfl : block g233 1 0 0 = true)
  · exact (rfl : block g233 2 0 0 = true)
  · exact (rfl : block g233 3 0 0 = true)
  · exact (rfl : block g233 4 0 0 = true)
  · exact (rfl : block g233 5 0 0 = true)
  · exact (rfl : block g233 6 0 0 = true)
  · exact g233B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 8 := lower_forest (g:=g233) (i:=0) (hints:=3) (before_sound K227 V227) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K227 8 [(233,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V227 low233 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff722c9,0xc6ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0xc0ca80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d52c,0x5d8c60000000fe03f80])),(BitVec.ofNat 152 (word80 [0x310b1050080823d12c,0x54840468d1a3468d1a3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ca,0x93211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x400c0160809000504a,0x912012142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c2,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880611,0x228304a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048915,0x424004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,73,48,6),(0,16,41,66,6),(2,16,41,64,5),(18,0,105,0,5),(32,2,73,16,5),(34,0,89,0,5),(64,16,41,2,5),(80,0,43,0,5),(3,0,120,0,4),(9,0,114,0,4),(10,0,113,0,4),(17,0,106,0,4),(33,0,90,0,4),(40,0,83,0,4),(48,0,73,0,4),(65,0,58,0,4),(66,0,41,0,4),(66,16,41,0,4),(72,0,51,0,4)]
def g123A : List (List Nat) := [[],[65,101],[48],[48,65,101]]
def g123D5 := limbs80 #[#[0x509404836a5d54250120,0x483ca5515250120dab75,0x1cb70595408fb805d954,0x8185b54f033a]]
def g123D6 := limbs80 #[#[0x50120d9510d891054910,0x59120585205512054520,0x551405494050940d9120,0x58154d9540d894059540,0x7efd7bbbdbe7f3bd8154,0xa10ff5eef573f7dbbd7e,0x2b9085750aee000dc996,0x8bba8d5751e2a83d5486,0x8aeb214b74336ca43dcc,0x9522baa077538eec515d,0x5d5aeaa3695453eca975,0x4dc98bb830b725e6e0b1,0xe1dc991b93207264ee0c,0xc844002b94137278ae4,0x7231964a0471f8d05824,0x88bc5a2ad469b48a24f8,0x8a331180be5dce46e341,0xa0194044b000a7532954,0x8007c118854168f18110,0x44808040200c04000290,0x2000080804d0501ba,0x210030140400c84c8400,0x116100000000800e]]
def g123H6 := limbs80 #[#[0x12004000000,0xcc00000000710,0x8480000021000000000,0x1100000c000000]]
def g123D7 := limbs80 #[#[0xfbbefedd545454048110,0x85a804eca0ec406c6fff,0xa92a88ec492848ec84ac,0x2626262a40ec10eca8ac,0x4a2c862a862c262a2628,0x122caa2c6a2a6a2c4a2a,0xc19c490b81a0026c122c,0x25092643cf3344b026c7,0xe7ede7749bb66d805a55,0xe0070c4a6e9624388a0,0xa824a4c722029028f14,0x3008523004428e2628a8,0x8d3040b0b138e3c1cb86,0x36192ba58288dc88a508,0xe1444ec280903feb09af,0xf109cff87004ebd605bf,0x4841de80771de00a03fe,0x99c898eb9131df1107ef,0xce26449d7052469c7a48,0x37a3156c248f06275b02,0x18778491bc240bc4f223,0x51ea]]
def g123H7 := limbs80 #[#[0x4260042000000740,0x0,0x42c0000000001cb8,0x208000000020e000,0x8c001220000000000000,0x110000000018a800005,0x26000000,0x3c006040048c00000000,0xe840000000000000002,0x1818000000000000001,0x41a002a20d800000,0x8ba3800001430,0x9400001610008d000000,0x1876,0x2400000000000003e000,0x832320000000000001,0x2312b00000222000,0x14858000040200000000,0x5ae0ec29066,0x12000000000000000000,0x4,0x890000000182800878]]
def g123D8 := limbs80 #[#[0xd41fe98ff503fa41fd10,0x62a0d830007f553faa3f,0x26506222300a1e40fc6,0x8a100a24718f9648e108,0x8b1e280930a147484963,0x42038a02971658a08c81,0x1628212a330]]
def g123H8 := limbs80 #[#[0x97044c0d00080284245f,0x8cd9320000000090061c,0x122ab196868000188004,0x52186723a4d81d719e8c,0xf490740c012f0082c00b,0x92000496500025542552,0xb8f1e00000039193c2eb,0x100062c]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x4b610006005,0xb1800254000680134000,0x2000740000006000000,0x480208000]]
def g123L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g123D5)
  | 6 => (33,3,5,917521,69,9,1037,g123D6)
  | 7 => (26,2,5,327685,51,10,1065,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 47 0 7 3 2 g123H6
  | 7 => lookupShort 11 173 3 10 6 2 g123H7
  | 8 => lookupShort 11 59 5 9 5 2 g123H8
  | 9 => lookupShort 3 41 1 7 3 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 5=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : block g123 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 33=true := (@block_merge g123 6 0 2 31 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_1 : block g123 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_12 : block g123 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 26=true := (@block_merge g123 7 0 1 25 g123P7_0 (@block_merge g123 7 1 11 14 g123P7_1 g123P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 7=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K233 V233) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K233 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V233 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7226,0xe00bab00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x20032b05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0394a,0x8766308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082390a,0x844210030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb05846c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000984,0x905800ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956adc0000000000fc0])),(BitVec.ofNat 152 (word80 [0x2b0540ac00ae048045,0x6914adfcf3cf3cf3cf3c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088070,0x820c010410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104401,0x43800420820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(0,16,169,2,8),(16,0,171,0,8),(1,0,186,0,7),(2,16,169,0,7),(8,0,179,0,7),(32,0,155,0,7),(128,0,59,0,7),(9,0,178,0,5),(33,0,154,0,4),(40,0,147,0,4),(129,0,58,0,4),(136,0,51,0,4)]
def g187A : List (List Nat) := [[],[117],[48],[48,117]]
def g187D5 := limbs80 #[#[0x50120549404814250120,0x50142541405d95448154,0xdc165503625414055150,0xca3caeab8edab3ab3a3e,0xe2cab2a85eea1aea2a,0xe5cf0562a98b0b32a507,0x69d19f365c8cc9110010,0xc05010000800284025]]
def g187D6 := limbs80 #[#[0x50940591205512050120,0x59540551405494054140,0xd815458154d9540d8940,0xcedf6ef5f7ebddbe7f3b,0x4f0aa252841faf77ab9f,0x2ea0eb285aa818a9006e,0x90eec22bb0aac829ba82,0xb29aaca6fb125a8483ba,0xd7b830aeb0aaa44aa8ab,0xe4efb839ee4e9b8396e4,0x9ee542b948ee4edb93b0,0x281147a3313048002b95,0xb957285328d3d1c8cc5b,0x3f0e833f1e0e56c32d82,0x80508238d56853a9949e,0x8aac040424a1db620dcf,0x1017011cf02bac08d32,0x843b91804a0b01603484,0x6823414040180e58400c,0x301005d2100203a83484,0x2d8778218000]]
def g187H6 := limbs80 #[#[0xc300000000d1000000,0xc800,0xc90000000000000000,0x580000,0x840000c10094000000,0x0,0x2562000000e700,0xf40000000046000000,0xc50000000000,0x0,0xca00000000,0x8700,0x0,0x4000e1,0x0,0x82000000000000]]
def g187D7 := limbs80 #[#[0x9403fffbbefd5450120,0x16555513625509950459,0x657589d5275503608d95,0x8541f0982400f60b582d,0xe2f067a38990ae4ca08d,0x1232aa4450eb4b8e644b,0xb00a5a286936c16020a9,0x4ab3c03df10130ec03b,0x5e4091f9203bed00c7d8,0x8475831179564c59e113,0x18e1256eb207570259]]
def g187H7 := limbs80 #[#[0xf1808a90020030d9308,0xac166c10d4006b53b99c,0x99a0625c00f4545952b8,0x14f56000001cd762f9,0x112800000034807a200,0xc6c940a91006cc010e00,0x13e760231960001a1f92,0x16404a0e20]]
def g187D8 := limbs80 #[#[0xc69a9007f553fa81fd20,0x98d145a822cc715a3599,0x11a48c5]]
def g187H8 := limbs80 #[#[0x3240054032282d45400,0xb92e0803b40000,0x3794000000000000021c,0x98000000000002040003,0x130010fa001280002,0x3400000000000000000,0x3a161800000344,0x0,0x0,0x2c00000020210000000]]
def g187D9 (j : Nat) := if j=0 then 0x1654231bf else 0
def g187H9 := limbs80 #[#[0xc80000000000000000,0x2055125d0000]]
def g187L : Nat → Packing
  | 5 => (11,4,4,458760,51,7,1027,g187D5)
  | 6 => (30,3,4,851980,68,9,1042,g187D6)
  | 7 => (15,2,4,262147,34,9,1047,g187D7)
  | 8 => (3,1,4,0,0,7,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 4 163 0 8 4 2 g187H6
  | 7 => lookupShort 11 59 6 9 5 2 g187H7
  | 8 => lookupShort 6 97 3 8 4 2 g187H8
  | 9 => lookupShort 1 23 0 6 2 2 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 11=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_3 : block g187 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 30=true := (@block_merge g187 6 0 3 27 g187P6_0 g187P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_9 : block g187 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 15=true := (@block_merge g187 7 0 9 6 g187P7_0 g187P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 3=true := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff6266,0xe02b3300000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204402242,0x20033305145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0290a,0x8f76708003f000000fc0])),(BitVec.ofNat 152 (word80 [0x8612c22802082290a,0x8c7250134d34d34d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffbd84,0xb04846c0fc0000fc003f])),(BitVec.ofNat 152 (word80 [0x80300b0409009884,0x804840ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc000003f000fc0])),(BitVec.ofNat 152 (word80 [0x2304408c008e048045,0x61042decb2cb2cb2cb2c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830080130,0x18308010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104401,0x43800420820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(2,0,217,0,8)]
def g219A : List (List Nat) := [[],[65,118],[48],[48,65,118]]
def g219D8 (j : Nat) := if j=0 then 0x7f else 0
def g219L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g219D8)
  | _ => emptyPacking
def g219I (_ _ : Nat) : Option (Nat × Nat) := none
def g219 : Forest := ⟨219,8,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact (rfl : block g219 7 0 0 = true)
  · exact g219B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=65603) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 9 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003ff87fe1fffff6,0x243b1000007c1f003ff])),(BitVec.ofNat 152 (word80 [0xa02805100440020d2,0x2031004210842108421]))),((BitVec.ofNat 152 (word80 [0xffffc0007ffe1ff055,0x3cdb028000f800007c00])),(BitVec.ofNat 152 (word80 [0x2c2309621280444255,0x3cdb001ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80001fff28,0xf4691c001f003e0f801f])),(BitVec.ofNat 152 (word80 [0x300401800308808028,0xf4400008421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00010,0xab842f83e000000fffe0])),(BitVec.ofNat 152 (word80 [0x404812002400090400,0x1042fa1084210842108]))),((BitVec.ofNat 152 (word80 [0xe,0x11bac77c00003ff00000])),(BitVec.ofNat 152 (word80 [0x80701c0438110e0804,0x1b8c7318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x8020004000100000,0x42108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(32,0,203,0,8),(64,0,171,0,8),(1,0,234,0,7),(8,0,227,0,7),(128,0,107,0,7),(0,2,73,160,6),(3,0,232,0,5),(9,0,226,0,5),(128,2,73,32,5),(129,0,106,0,4),(136,0,99,0,4)]
def g235A : List (List Nat) := [[],[48]]
def g235D5 (j : Nat) := if j=0 then 0x2ece117254110 else 0
def g235D6 := limbs80 #[#[0x379b12a0887715254110,0x97ee8b2a41da5495048,0x435fba2ca907f1725411,0x471eda9652016fdd1625,0x4d03f111a0ae42788b61,0x2c98f8f0104f2e2204e,0x81642]]
def g235H6 (j : Nat) := if j=0 then 0x2 else 0
def g235D7 := limbs80 #[#[0xffbf7f37efef55048110,0x55062a40d880b10d503f,0x226019628ec5254a2b2b,0x2a159631cfcd0ae84684,0xf403242aa387a1781119,0x19f500c202de0241810,0x175248e00af28040e]]
def g235H7 := limbs80 #[#[0x4480060023d480000262,0x1]]
def g235D8 := limbs80 #[#[0x48a4b807f543fa41f510,0x1ca384a2818073568394,0x2a851ca11]]
def g235H8 := limbs80 #[#[0x118000900000000000,0x3a0001200000,0x1000000000000,0x0,0x0,0x0,0x0,0x0,0x1c000000000000000000,0x0,0x9800084000000,0x10830000000000000,0x0,0x0,0x0,0x50]]
def g235D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g235H9 (j : Nat) := if j=0 then 0x6012006d4 else 0
def g235L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g235D5)
  | 6 => (7,3,4,0,0,8,0,g235D6)
  | 7 => (9,2,4,458755,50,8,1039,g235D7)
  | 8 => (3,1,4,0,0,7,0,g235D8)
  | 9 => (1,0,4,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g235H6
  | 7 => lookupShort 2 13 2 6 3 1 g235H7
  | 8 => lookupShort 2 179 0 7 4 1 g235H8
  | 9 => lookupShort 1 7 0 5 2 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 1=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_4 : block g235 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 7=true := (@block_merge g235 6 0 4 3 g235P6_0 g235P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_3 : block g235 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_8 : block g235 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 9=true := (@block_merge g235 7 0 3 6 g235P7_0 (@block_merge g235 7 3 5 1 g235P7_3 g235P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 3=true := (@block_merge g235 8 0 1 2 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffffc1fffe066ae,0xa0655800000fc0fc0fc0])),(BitVec.ofNat 152 (word80 [0x54028048400042228e,0xa00150030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfe003fffe0ffff2942,0xa6aab28003f00003f03f])),(BitVec.ofNat 152 (word80 [0x182304100210802102,0x24a29209249249249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x995842c000003f00003f])),(BitVec.ofNat 152 (word80 [0x610421608485001c84,0x895840e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x804809800026048041,0x1542994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0x700e010838088161,0x10a08c18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x180300210c0104c10,0x4a000060820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,7),(16,0,227,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,16,161,66,6),(1,0,242,0,6),(32,0,211,0,6),(2,16,161,64,5),(17,0,226,0,5),(18,0,225,0,5),(34,0,209,0,5),(48,0,195,0,5),(64,16,161,2,5),(65,0,178,0,5),(3,0,240,0,4),(50,0,193,0,4),(66,0,161,0,4),(66,16,161,0,4),(81,0,162,0,4),(82,0,161,0,4),(96,0,147,0,4),(129,0,114,0,4),(130,0,113,0,4),(144,0,99,0,4),(160,0,83,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[80,97]]
def g243D5 := limbs80 #[#[0x4c11054530441414c110,0x441534c51054d3044152,0x5055044131541105d943,0x54510551504415354110,0x441635491054d5144152,0x5463044176551105d953,0x54530dc5504c36154130,0x5415454140d95524c152,0x5c66054552581515c764,0x5421054d30841524c210,0x8c1535423058d5284153,0x54d509016354a3058551,0xcc64058d529017654640,0xcb71bbd2cea6e3787d41,0xe6796e578ed6b59d5b53,0x2a903250c0f93d8f53cc,0xa91ed594356ea1415306,0x190f550782a6313833e2,0x94e58ca62ca22d6425ab,0xa0e145170a631632ddb1,0xd595956eac0783383c19,0x54d16aa680b856dab1b4,0x49d6ac6e09814cb3b248,0xa26ac6f8f83505c2bce5,0x60f06a8b85843c1c065d,0x903814060012a92e7dcd,0x99a8c459281107834160,0xb59aad469b49a2d067b3,0x6fb79badc6db69b2d86b,0x1c0399cae471b89c2e0,0x20622b0c0,0x8000402642000]]
set_option maxRecDepth 16000 in
def g243D6 := limbs80 #[#[0x4c110594305843054830,0x5411050d10505104c510,0x5511054d105491054510,0x8c110595105911058d10,0xd9510d9110d8d1094110,0x54530541305053054d20,0xd8530941305953054930,0x551405494054140d9530,0x54541cc54094d4059540,0x5515050550d894159541,0xd855098d505895058550,0x5815154951d9150d8d50,0xd9151d8d51d815198151,0x542104c210d815218152,0x58e1058a1054e1054a10,0x5423058e205862054e20,0x5863054e3054a3054630,0x54640542405064058e30,0x94e4058e4054e4054a40,0xfafcfe773758e50cc640,0x3b7d7e7f377ebedeeef6,0x7afd6e7f3b97bedeeef7,0x7e7edf5f77b7bdddedf6,0xdd9c01b98e595211fcfd,0x103bb002565006aa4041,0xaa1d276530a2a65895c8,0x31f71060aea951550f24,0x520706e20e05441c0a08,0x682ca0dd54c1baa1837d,0xa23c8dd4190ba8343650,0xc85d47a0b28f7d521f02,0x8c3b2a98781410f02621],#[0xb2aa0723730e86c61d05,0x19081312086c81d05903,0x715308f2a41085cc820b,0x5087eca10f59420eba04,0x7aca15a5502b4a1851d7,0x621854c40eba853f650a,0xf59040fb9883f63107ac,0xc49cb1891f74107ec820,0x8b18a09760c46e018ed8,0xc3f711812ec28a59451,0x9752212e8442dd4605ba,0x1a12ec2cb590591b80b0,0x2ea4825cc905ba8d0b73,0x38cdcc718398e17731c1,0x5d0984b9930b741c16e6,0xb20b2b675536cfaa4d82,0xb1b765536e46ead885d5,0x931637272a6e8e58dc20,0x702816eaec25d9c94b2b,0x862c6f08dc1e1ea9bd23,0xa6582dd5f04bb3c29657,0x88dc4b21b0962b652caa,0x84d33b29643642ccaa85,0x8db9153f612a42e2690d,0x91b0a762ebaa45c29d8a,0x2b653012ea6c25d0d9ca,0x13816e264ad94cafb298,0x82c6fd954dfa0b0bf097,0xd005dce02ea9403d6180,0xa59611cb1c139528612e,0x1132a99d0b758812ed08,0x4bb2111744212ec8845d],#[0xc60b734016e2804dccf8,0x1638ccaa7190586336a0,0x8ad2a31425da634a0cc4,0x2ed1cf586396b2c52d63,0x24a596498b1c93963901,0xdc6504bb4b31639612ed,0x326aa261b724c16eb282,0xa9ab17735028e6a0bd91,0xa13745212e8ac25cd594,0x734e12e8b025c5610b82,0x616e33425cd684b8ad0f,0xe6bd7549785b8241f704,0x35d582ea9301d71602e,0x8d704ba3109736212ecc,0x84b83309746412e0c975,0x9b519736812e6d425cd9,0x2d82381900d8078000cb,0xf06905e05284d0428380,0x9608d88688287e87406,0xb50b10ad0a90a40a009a,0xd0d70d28cc0c30bf0bb0,0x8fb8f78f38ef0ea8e40d,0x2291d11911310a9068ff,0x615194d94393f93692d1,0x97797316c96696015c15,0x9b99699298c98818097b,0x49bd1b69b19aa9a399f9,0x9e09dc9d89d49cf9c89c,0x19fd9f99f29ee9ea9e6,0xe21a215a11a0da09a05a,0xa39a35a3022c228222a1,0x5e257251a4da4824223d],#[0xba77a73a6e26a2662622,0x29c297a93a8d28628227,0xc02bc2b82af2aaaa52a1,0x22de2da2d32ceaca2c4a,0x2fbaf7af3aefaeaae62e,0x1ab16b12b0eb0ab05301,0x933332f32b32732331eb,0x357b5334eb48b4233e33,0x7537136d36936536135d,0x8b93b8fb8bb87b83b7bb,0xbb3badba9ba5ba1b9cb9,0xd93d43d03c63c23bbbb7,0x64023f93f53f13eb3e33,0x1c23c1a41641140d40,0xb0a68b5182030880828,0x6e00a90c025451201075,0x1a2c28cd206918c23114,0x46687675c9350699105b,0xe443519a19d5c90ebc8d,0x32829c43185f843a43b,0x8044588b610000d8d21a,0x16420000008080590,0x8b0c6c3a82018b0ee684,0xbc4200d6040000000201,0x622f0c531b4360201643,0x1006a0804017510c00b5,0xb6034040002b0232170,0x7d81348800010100b210,0x404d22002e06e0240,0xd22000000b21000,0x3010080004000000000,0x40290ca0804000290800],#[0x1808000000036c2c0,0x8080400682691005584,0xb01008000436c401a420,0x1010080000016c20100,0x60200c040000,0x202642000000000100,0xc040201b21701,0x2f88aac200000,0x2c840000010100404,0x946868080691a1805584,0x9100706c40001643b885,0x3b83100202006]]
def g243H6 := limbs80 #[#[0xced12b000001012086,0xa10000002000004f12,0x1c9c0000001a60000000,0x280000610000000001,0x5c01a28700030000,0x3380,0x3b400000000000000011,0x254225900000018f0000,0x318004a000000000,0x506169312000029704,0xe00cb08f3e8d0c80000,0x40000000003374c81618,0xb8780103000004b8b004,0xa180248002,0x268000]]
set_option maxRecDepth 16000 in
def g243D7 := limbs80 #[#[0x54550505404c12044030,0xdbb9f942408c22084152,0x629fffefdfbefdfdbbfb,0x41650158809610258685,0x406630194c0515271d89,0x85446141184c46650195,0x413d8c4d63179485d521,0x53093d944d6513d904d6,0xe8d659358e5d52995426,0x540cd65075480d65a358,0x37948dd5233d84e65039,0x52b3586e550b3d94cd65,0x1d52495410d65b358edd,0x871941c95430d6546551,0x3d858d65c358f1d52c35,0x1d3d91955463d8d95536,0xf607359561515358f4d6,0x21c6083d820f6473d8dc,0x54c69431a540693017d8,0x9a59469641a55069631a,0x413a540e953aa54ca953,0xe9523ad84e9613a544e9,0x46eb653a594eb623a588,0xa5452b314a4c52953ba5,0x3ca5472b31ca94d29534,0x9616a505a9216a94f295,0x1e9646a98da9636a589a,0x29647a58dea607a58,0x2b024c1d018c1340f007,0x8c50c4a844c3dc358310,0x47ec77c70c6a864c5f45,0xa74a0c9c09608fc8b885],#[0xf8ca8c5cc20bd4b4cae8,0xcf40ef0ec0e50de0d88c,0x20d1911310d106d008fb,0x914313c53693012b1265,0xd7416d16515d55594dd4,0xa1d9a19418f98958357a,0x51bfdbbdb79b09ad5a85,0x9e39dfddb1d75d1dcd1c,0x4a005fa9f55f05ec5e8,0xfe1be18e1521120d2096,0x23b23563062c226e23e1,0x5ea59256a52a4ca45e40,0x8386a32a1a6ca682636,0x4843c0300418a2220b05,0x4924d4464bc61e0210c0,0xd00bc50482687170cac6,0x4f28d144944a4e260912,0x47274224748f4ce0e518,0x85127a5a882488d51a3a,0xc088b63f7a228a94934e,0x36288d518864e870c7a7,0xcb228933e21ac798883e,0x3d0e08a3d0e08bb87144,0x4891d2333941335e9012,0xf3404c4749348f11079a,0xc7925049f025df30ca2d,0xbb43bc246e0116a82d34,0xe489e67c433c263c928c,0x49cb9c1500c9d8609cd0,0x48972ea2623a484b8f2,0x7800a16711130f31137c,0x1113b817d9416af4876e],#[0x409439e8130d834458f3,0xf52451f8ce48a7388ccf,0x152fc08119467c0234f1,0xf9d0508c3f431107d959,0x1113e0438859319c612e,0x124c66e89313cdd1464e,0x64431428d258646815ea,0x6da4156313191b310c76,0x36278062650cd916798c,0x99aa1e7831599107224c,0xdd019f2239aa1574a63,0xc855a46c05390a7108f8,0x22cca1c1c8c75086406b,0xe44889e498e5aa08fec1,0x1f490d01da4253c544df,0x6cad449350c6ea1b6d04]]
def g243H7 := limbs80 #[#[0xc01ce002009202004081,0x42410013400000090952,0x5200d5460c900200,0x400c300908e2cf504005,0x20435840800008003810,0xb1e27c0018a800000001,0x690a6c0ca9c6d95a9a,0xa66501ea2d2657120000,0x1c0064de20000002,0x11480000000000000,0x208004a20f54fa85c6,0x4840004fc0000085a0,0xab90000005078e000000,0x70000000000014a0009e,0x9c5996050008b21176,0x30400747d4e88206e360,0x50fb6025511c0c60e961,0x43a5000000004ac4e726,0xcf20f8000000ed8001,0x8681bb620158eb03f1f8,0x1280770899a000067,0x100078c4d79540052700,0x12000000272c5f8,0x44200002000ab7886988,0x8eb00010f461c5c00000,0x10cc55b39817b140065,0x42941793d3b008d824b0,0x68e8009274a400000d68,0xa6a2000902d2019c9e82,0x8de580030843a76a0030,0x98c002,0xc300004a800000000],#[0x38a70c55f2e00000,0x3200000000158d730ae0,0x57f08a4bb8b60c249a3b,0x90c00198c4a000003a3,0x14418b434df05180,0x20d0daa9001228007250,0x5a917024400174001,0x297000b025503b87200,0x17a8dc12800046ccc0,0xad60005d000814003098,0xc0004a00092a0e0000ae,0x360002da002270b64c,0x2892fd919c6cafed80,0x71bd8600145cbc52c8d4,0x883b09d08d45d42002aa,0x2455b1905904c0004dc7,0xad6158a4276158002926,0xf8ae980008733df7bc62,0x3024a7dac92f51e11f17,0xbf0a59272ec4c9340010,0x5019fc0048c50e000006,0x4000000009505a03e821,0xf8000008e98580900058,0x5df70d3cdd40029c0019,0x8000019bc00762000000,0x5660003810d00096f0b,0x1afa2400]]
def g243D8 := limbs80 #[#[0xc41483085104a454bffb,0x3942a8640a818c298430,0xe481504c0154aa8d41a4,0xa1cf36d31d72a3439b0a,0x700a3410c88edd4e9b48,0x10216285344b3c680c48,0xf0e0834c24b3110d654e,0xef74d81ed604a1019cf,0x52b8486026ed088fff02,0x243e9058f2b24d70f02,0x710678ff1b083fc60637,0x1d]]
def g243H8 := limbs80 #[#[0x62e7cd0a002820005083,0x3178256541821000d003,0x418bb80049b542550202,0x94e0675126ad697911c5,0x11b6dc838ccc8737c0e4,0x1d5f5e56f345ac14d21c,0xcd750bc189f0f70f0015,0xc0000524862d6465ac85,0x7516bcb880010800348a,0xcbf680440000009539c,0xa8d800b7e4c8d62b12c0,0x80024d466414b61d0011,0xea32277472e0001f002a,0x48832b3725949ced4e3,0xca3de796230032c0000,0xc92260021cf4c16eb80,0x76b69003a05ba471b00,0xf02a12a1b63002580ec0,0xa0004f002c94ffb870e5,0xbce4000021305e3a01e4,0x8e840000000000000031,0xe00054ccd4600000c0a0,0x4aa438f0c2000000031,0x462550c282d982978c0,0x5c00983130455b0d22e1,0x6d42b063b8773d316411,0xa3e016b461993404329,0xc806]]
def g243D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g243H9 := limbs80 #[#[0x476177800008c034884,0x66863e5800072a632568,0x300000000248014e2b1d,0x400003580f5679445000,0x6266d141802]]
def g243L : Nat → Packing
  | 5 => (38,4,5,1245219,86,9,1029,g243D5)
  | 6 => (198,3,5,2162766,103,12,1057,g243D6)
  | 7 => (111,2,5,720910,68,12,1072,g243D7)
  | 8 => (17,1,5,131073,16,9,1048,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 12 131 3 9 6 1 g243H6
  | 7 => lookupShort 65 389 6 11 8 1 g243H7
  | 8 => lookupShort 38 191 7 10 7 1 g243H8
  | 9 => lookupShort 7 41 5 8 5 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 38=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_12 : block g243 6 12 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_108 : block g243 6 108 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 198=true := (@block_merge g243 6 0 12 186 g243P6_0 (@block_merge g243 6 12 96 90 g243P6_12 g243P6_108))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_7 : block g243 7 7 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_68 : block g243 7 68 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 111=true := (@block_merge g243 7 0 7 104 g243P7_0 (@block_merge g243 7 7 61 43 g243P7_7 g243P7_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : block g243 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 17=true := (@block_merge g243 8 0 2 15 g243P8_0 g243P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 1=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=65605) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 10 [(243,[]),(250,[48,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffe88,0xcd40ac540007c00f83ff])),(BitVec.ofNat 152 (word80 [0x902401009080010280,0xc8400014210842108421]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe007fffc1fffd97,0x210154ac00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x20080a012004020106,0x21014400421084210842]))),((BitVec.ofNat 152 (word80 [0xffffff800001ff80d7,0xc5f4434000003e000000])),(BitVec.ofNat 152 (word80 [0xc4310c45c1091408d7,0xc5c44342f7bdef7bdef7]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a201f0000007fe0])),(BitVec.ofNat 152 (word80 [0x14050160000581021,0x41c3a218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x18060180210602000,0x103888a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180600421804018,0x282014a108421084210]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,16,169,64,8),(16,0,233,0,8),(32,0,217,0,8),(1,0,248,0,7),(8,0,241,0,7),(64,16,169,0,7),(128,0,121,0,7),(9,0,240,0,4),(129,0,120,0,4),(136,0,113,0,4)]
def g249A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g249D6 := limbs80 #[#[0x26fb9aca887715154110,0xdbee6b2a2177dcd6544,0x420dc527287d46bf1180,0x171e01e3e3c03e3d]]
def g249D7 := limbs80 #[#[0xfd9510bf59510fe54110,0x590884603600ff59510b,0x2481f1cb51881c3c725b,0x78d25b1c085b1cb51c5,0x92]]
def g249H7 := limbs80 #[#[0x6000000005,0xb]]
def g249D8 (j : Nat) := if j=0 then 0xf1b1072a8ffd10 else 0
def g249H8 (j : Nat) := if j=0 then 0xc00cc2611 else 0
def g249D9 (j : Nat) := if j=0 then 0x6413251bf else 0
def g249H9 (j : Nat) := if j=0 then 0x40000030000009000 else 0
def g249L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g249D6)
  | 7 => (4,2,4,0,0,8,0,g249D7)
  | 8 => (1,1,4,0,0,0,0,g249D8)
  | 9 => (1,0,4,0,0,0,0,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 23 0 4 2 0 g249H7
  | 8 => lookupShort 1 7 0 6 2 2 g249H8
  | 9 => lookupShort 1 17 0 4 0 2 g249H9
  | _ => fun _ => none
def g249 : Forest := ⟨249,9,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_2 : block g249 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 4=true := (@block_merge g249 6 0 2 2 g249P6_0 g249P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_3 : block g249 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 4=true := (@block_merge g249 7 0 3 1 g249P7_0 g249P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 1=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P9_0 : block g249 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B9 : block g249 9 0 1=true := g249P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact g249B6
  · exact g249B7
  · exact g249B8
  · exact g249B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 10 := lower_forest (g:=g249) (i:=0) (hints:=393219) (before_sound K243 V243) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K243 10 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V243 low249 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf0000ff00fe080106a,0x300fa047c6f3679fc7ab])),(BitVec.ofNat 152 (word80 [0x505050505060040022,0x10012402022303880208]))),((BitVec.ofNat 152 (word80 [0xff00ff001000093,0xc0300186090399f80000])),(BitVec.ofNat 152 (word80 [0x323232323221000012,0x40100186010288b88000]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000000fe000e31c,0x3c041f831fc1e1fe8cd])),(BitVec.ofNat 152 (word80 [0xa0a0a0a0a080084110,0x40488011401c10a000]))),((BitVec.ofNat 152 (word80 [0xff0020303e0,0xc007e003e001fe00e10])),(BitVec.ofNat 152 (word80 [0xc9c9c9c9c9c20303e0,0x24006e003e0017400e10]))),((BitVec.ofNat 152 (word80 [0xffffff0001c03fc00,0xfff80003fffe0000f10])),(BitVec.ofNat 152 (word80 [0x50505050510210000,0x8eaa00296c8000010c00]))),((BitVec.ofNat 152 (word80 [0xf0000000001ffc0000,0xfffffffc0000000301f])),(BitVec.ofNat 152 (word80 [0x60606060619300000,0xb3c1175800840020000]))),((BitVec.ofNat 152 (word80 [0x1fffffff,0xf0000000000000003fe0])),(BitVec.ofNat 152 (word80 [0x80808080802429acd,0x40000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,16,169,66,9),(32,0,219,0,9),(2,16,169,64,8),(18,0,233,0,8),(34,0,217,0,8),(48,0,203,0,8),(64,16,169,2,8),(80,0,171,0,8),(0,2,73,176,7),(3,0,248,0,7),(10,0,241,0,7),(17,0,234,0,7),(24,0,227,0,7),(50,0,201,0,7),(65,0,186,0,7),(66,0,169,0,7),(66,16,169,0,7),(72,0,179,0,7),(82,0,169,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,121,0,7),(136,0,115,0,7),(144,0,107,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,16,168,66,6),(8,16,161,66,6),(9,0,242,0,6),(16,2,73,160,6),(32,2,73,144,6),(32,16,137,66,6),(33,0,218,0,6),(40,0,211,0,6),(128,2,73,48,6),(128,16,41,66,6),(25,0,226,0,5),(35,0,216,0,5),(42,0,209,0,5),(49,0,202,0,5),(56,0,195,0,5),(73,0,178,0,5),(144,2,73,32,5),(160,2,73,16,5),(162,0,89,0,5),(11,0,240,0,4),(67,0,168,0,4),(67,16,168,0,4),(74,0,161,0,4),(74,16,161,0,4),(89,0,162,0,4),(97,0,154,0,4),(98,0,137,0,4),(98,16,137,0,4),(104,0,147,0,4),(131,0,120,0,4),(137,0,114,0,4),(138,0,113,0,4),(145,0,106,0,4),(152,0,99,0,4),(161,0,90,0,4),(168,0,83,0,4),(176,0,73,0,4),(176,2,73,0,4),(193,0,58,0,4),(194,0,41,0,4),(194,16,41,0,4),(200,0,51,0,4)]
def g251A : List (List Nat) := [[],[48]]
def g251D6 := limbs80 #[#[0x50940481a0619741d120,0x48185595425012059563,0x59152501205d95454940,0x58120549615055048185,0x59554dc960501741d162,0xdc960543a25538258140,0xc2ba2553825815059154,0xf88f41782b615a8ad155,0x6523b278bb23698e2ec5,0x292cb05a206d2b561447,0x6d54203040400cb22a59,0x2414e81009c04d8ad528,0x160004f721483,0x6a080003c03700c60600]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x55151501105894250110,0xdc951501106095150110,0x58952501105515250110,0x54961501105096150110,0xe496150110dc96150110,0x55372501105d96450110,0x58952505105937250110,0x59372505105d96450510,0x59562549105516254910,0x58b80549106456254910,0x54941581105892158110,0xdc941581105914158110,0x5895258110dc95158110,0x59154581106095258110,0x5c96258110dd15458110,0xdd56258110dd16258110,0xdd564581105d16458110,0x55372581105d56558110,0x59772581105937258110,0x5d164585105d16358510,0x58f7258510dd56458510,0x59382585105937258510,0x641861d120619741d120,0x65874501206547450120,0x58d42501205514250120,0x59542501205914250120,0x61542501205d94250120,0x98d42501206194250120,0xe154250120dcd4250120,0x5095150120e194250120,0x58551501205515150120,0x5c551501205895150120],#[0x58d52501205515250120,0x59552501205915250120,0x65152501206155250120,0x991525012098d5250120,0xe195250120a515250120,0x5955450120e595250120,0xe5954501205d95450120,0x1d162501205096150120,0x551625012054d6250120,0x59562501205916250120,0x61962501205cd6250120,0x651625012064d6250120,0xa5162501209516250120,0xe556250120e156250120,0x55163501201d16350120,0x95163501205956350120,0x61564501205d96450120,0xe556450120e156450120,0x25176501206156550120,0x64a54501205da5450120,0x50b715012064a6450120,0x58541541205494154120,0x5c541541205894154120,0x591525412058d5254120,0x61952541205d15254120,0x9d152541209915254120,0xe115254120a115254120,0x5915454120e195254120,0x5d954541205d15454120,0x9d154541209915454120,0x5496154120e595454120,0x55162541205c56154120],#[0x61962541205956254120,0xe1162541206456254120,0x5956354120e516254120,0xe516554120e116354120,0x58971541205497154120,0x54b41541205957154120,0x597845412058b4154120,0x55161545206415454520,0x55171545206416554520,0x66176551205957154520,0x58951581205d07458120,0x5c551581205955158120,0x59154581206055158120,0x5d154581205955458120,0x1d162581205d55458120,0x5d162581205516258120,0x95162581205d56258120,0xa1162581209d16258120,0xdcd6258120d0d6258120,0xdd56258120dd16258120,0xe156258120e116258120,0x9d164581205d16458120,0xe556458120dd56458120,0xe5165581205d56558120,0x5d254581205925458120,0x547415812064a5458120,0x593415812058b4158120,0x58b715812064b4158120,0x59774581205977158120,0x5955458d205d07458d20,0x65d5458d205d15458d20,0x6416558d205d56558d20],#[0xa5d6558d2065d6558d20,0xe597458d205957458d20,0x65e5458d205d25458d20,0x5977458d2065e7458d20,0x25176591206537558d20,0x610845d9206427459120,0xdd551d05205918095120,0x59180d052061d63d0520,0x59563509405916250930,0x59162549405516254940,0x58942581405956254940,0x5d542581405954258140,0x65942581406094258140,0xdd54258140dc94258140,0x5095158140e554258140,0x59551581405515158140,0x5515258140e4d5158140,0x59152581405895258140,0x59154581405d55258140,0x64554581405955458140,0xe4954581406595458140,0x95162581405c96258140,0xdd56258140a516258140,0x5d56458140e556258140,0xdd5645814064d6458140,0xe556458140e496458140,0xa5165581405d56558140,0x5518158140e496558140,0x5974258140e498358140,0xdd742581405d74258140,0x593715814058b7158140,0x64b71581405977158140],#[0x59372581405537258140,0x95372581405977258140,0x64b815814050b8158140,0x59382581405538258140,0x95382581405978258140,0xdd564589406438258540,0x64a5458940a118058940,0xe495458d406438158940,0x65d6558d405d56558d40,0xa5d6558d40a516558d40,0xe41875954064b7558d40,0x60962dc54059563d0940,0x59554dc94058d82dc540,0x59563dc94055163dc940,0x64164585415d56458541,0x64b80585415938058541,0x59161505505496150550,0x59141581505494158150,0x58952581506054158150,0xdd152581506595258150,0x5915458150e515258150,0x64554581506115458150,0xa1154581506595458150,0x5c96258150e495458150,0xe516258150dd16258150,0x9d164581505d16458150,0x6516558150e496458150,0xe496558150a516558150,0xe457458150e516558150,0x55181581505498158150,0xe4981581506118158150,0x5967458150e458458150],#[0x54b41581505968458150,0x59741581505934158150,0x58b715815064b4158150,0x553725815064b7158150,0x59772581505937258150,0x59774581506537258150,0x553825815064b7458150,0xdd382581505978258150,0x64b74589506455458550,0x6516558d506496558d50,0x5967458d50a516558d50,0x64b7458d506427458d50,0x610845d95065f8159150,0x66176d055060962d0550,0x59154dc95060962dc550,0x641545855161163dc950,0x64154545605538058551,0x6427455160e497154560,0x64382551606438155160,0x60951d0560e498095160,0x59180d056054580d0560,0xe4980d0560dc980d0560,0x64254dc960e4954dc960,0x64b80551636416555163,0x5516254b406195454b40,0x5956254b405916254b40,0x5517258b405956354b40,0x551635cb405917258b40,0xae99e96793787e87b86f,0xea9ea5da379ea9da9ba9,0xb17b0faeaadaaceabaaa,0x33b2eb2db2bb27b1eb1b],#[0x7b6eb5ab4eb4bb3ab35b,0xba6b9eb9ab96b8eb8bb8,0xcabc6bb8bb2baebacbaa,0xfc37beabe8be2bdabceb,0xcbacaecadc9ec97c7ac4,0x2bd27d1ed1bd17ceacda,0xad4ed47d3ad35d2ed2dd,0xda6d9ed9dd96d8ed87d6,0xcadbadb2daedaddacdaa,0xbe27e1ee1be17de2ddad,0xe8de87e6ae5ae2ee2de2,0xaae9ee9de9ce9ae96e8e,0xaed2eceecaeaeeaceabe,0xf1bf1af0ef0bf07ee2ed,0x2ef2cf2bf2af1ef1df1c,0xdf4cf4af3cf3af38f34f,0xf8bf8af86f6cf5af4ef4,0xa2f9cf9af99f92f8ef8d,0xafc2fb8facfaafa9fa4f,0x530c00fe8fe2fd8fccfc,0x659426bcba0ad13940f3,0x2d40cded7619bdaec326,0x5761c9eb2c35615d86a2,0xeec3411698727acb0e58,0x5d88023d28d9ab861b3d,0xbb1095996203730c4083,0x76220835043765d886f6,0xc586a618a278cb11181,0xa0a612d496425a92c353,0x295425a42d8734c5a0e6,0x633a232c4c755d8961dd,0xc6144658cc7ac319d257],#[0x8c612d118d7d76312fae,0x1912176172215260445d,0x3a3b2ec6f1e694cab6bb,0x753c658eac0bb1d47da7,0x6ccc31fc43a4388834c,0xdc3ba4408434a840e699,0x3adaec8d40658f2eabb1,0x44665d6880bb21c21a24,0xeedbaa5511975a9db30b,0x71a7522032ab8466556,0x3b2ea9e7b5d13c1cd429,0x1c69d42f6ba28471a74f,0x39d2a7def744f87350a1,0x71a55307350a21c69d44,0x734aa80e6a14638d3a8c,0xc6914e39d2281db75500,0x8cba65d5754c87348a91,0x1974d2232c9b75595368,0x32cb14465d6080cb2710,0xe955489caaa9efa25522,0xd12b465a4560cb4eab19,0x755783b44af40655720e,0x50cd5f5d99e2bd22b901,0x9978e6b2af02ba66705b,0x33100fa65e9f32ebb16e,0x56181d52c203e998a2dd,0x8be3e6558e07d33180da,0x99026d2b044fa56009f4,0x3297d7666017409303e9,0x7e0934ac9186859288bb,0x53d64a0888b23fd1992,0xb688cb35c19a96b1d2c9],#[0x841ba56c8334cdc44659,0x603352eb40659c896cb3,0x206691dc38d13b419a97,0x632d13c447a2830e7450,0x8d3968c2eac91706689e,0x8b450c1469da8e8bb34,0x425da1a74b243835a686,0x35d144477a28c8bb450b,0xd8928a81f4d1413e9622,0x2cb464664a8a1fd05c0,0x5e924c0ad34a1019693a,0x9d152015a5988e345300,0x165a61c3313f10e8a9a3,0x2cb5c01e8ab60ad14e10,0x596ae3bd1574fd65a8ad,0xb181a11540180f45583e,0x6404beac8087f58c1126,0xea1419e881488cb03145,0x943af0b2861f5640bc06,0xa8951194120e3441f1ce,0x5100cf4420755943880c,0xc0f15e884432d208467a,0x548aca0a463a20721b2,0x89c63a2138df44264365,0x272c7263b186905031d2,0x326ee1460b0c99a64963,0x62e4c28c6496518b570c,0xe1cb851bb930a3772e14,0xa88d50336e6146664d08,0x53de586ac3bb0d5bb851,0x47bcb0e587761c88f4c3,0x6396520cc2a841116947],#[0x3830a46985508ce0c290,0x56e5880ddc31020f7620,0xdcc2908bba6201734c40,0x25a9239734a476e6148e,0x4b52482e694905dd2914,0xe988879cb1118376220,0x4b294425a4250834a491,0x985291434c5828698a31,0x34a4f28e94a4d5c2949a,0x698b251d315ca1a62797,0xd117e25652eb330a5328,0x852f13b4c5c2d694b862,0xc6749dd8ce12d113595,0x14d07ac29a027a6339ef,0x18bd41a21784f4a683de,0x839387086e3c661169ed,0x876106a0e820d41cc41a,0x5064ad31fe29643f8834,0x21595654312f48806659,0x3d97744782e688f51cd1,0xb646a5d6810d11f0b9a2,0x48a8c9add53934aa82c8,0x78b1a1528e54ea425695,0xe8e54ea12b68d423953a,0xd7b5d13a56d1a74b1a14,0x4a0b22c872a74e92b4a9,0x121954a14344ab28e895,0x20b2cba476557488cb25,0x5f68058a8c92fc13a95d,0x6acab2ced9216ae3462c,0x8da66f27ac8e000ea596,0xdac8da40655fc88cabf4],#[0x8e99b0f7bab55ed756ab,0xababe52d956b3aaead62,0x1967d03352f94b655f2e,0x2eae28a551c488cb3ed1,0xa5dc6eabab8c8da670bb,0xd13b0a1a27594748ea44,0xa6818cb4d00755960050,0x2b0219e960288cac0465,0x9a121ad3419916583203,0x2c1d7f7583afaeb070d6,0x574baeeae55b5d6101bd,0x4e823e89cc0cd33a52d6,0x5e489babc91175790374,0x3bdd7757794f42f00669,0x7aa02eaf606691ec33d1,0xa15e89e80cd4bd48da5,0x2ce6bac59cd75689d2c9,0x69d175699134cd262616,0x9252cb0f5961636e6b2c,0x1136962627d144085a58,0x4e8badc889a6b8ba2ed7,0x51a7b9ad30f735d61ee,0xbb4d7574596eab2c3dd,0x4b65684e6b2ddd0b95bb,0xad4d0d0197a1a232f42,0xd564a392f4b2f76dd24a,0x2cb4a44652902ad351d,0xc69a9ac8b253457a4a4a,0x6b24b833a4a72dacb4f0,0xfa69511f45290569a5c9,0xb4b3405e8a5846d34b48,0x69e6646d2ccc8fa59902],#[0xd152c15a99fa032f3f19,0xa99b02b49374065e802b,0x2f554c596acb2b2d7815,0x82a649d0548de98aa9f3,0x4d644da7aa123415424e,0x4b533acb686c592d001d,0x96c3ae56d274b25ad7d6,0x2c888b25b4fd65b6212c,0xd94e964b29c2cb643a59,0x8f9d2c9664b596c670b2,0x6018e8238bcbac78e564,0x443d25b8dd65b7b1ac9,0x22695403cd344019a550,0x2482ca05995500b10aa0,0xb2fe98090dbb01269a10,0xb2ec285083a605c32ca0,0xa09650bc8aca15965902,0xc82a81997684332cc285,0x716143520b286a41850c,0x1ac286df96411c0b0a1d,0x3d650947aca0d945901b,0xbd2e117765c2316b2042,0x65907b34aa0f675421eb,0x2b28ee69541fcea843f9,0x1651f4aac83e995507d3,0x748312fe987932d10f24,0x590a139d38c4cfa718ce,0xd194a55642b4aac85495,0x5236cb2c86b9b548d72a,0xc88b90594d932b21aa6d,0x48fd20b2a315d9645cca,0xb2221d7444482c87d9b5],#[0x645482ca8957e59110eb,0x4b3905950461d09c1e97,0x9312eb125d55655b4bac,0xa5641544ac8aca989758,0x48c62c88f906892d21ba,0x90576491cf2bb24a1574,0xbd2ab1375f297682bb24,0xddf9857ec6b48df8d699,0xc4ab06d59554daa54d33,0x49659248a6cb39d4d647,0x31ad2c8e41629148acb2,0xd3965a229ac9449058a8,0xa72cb3d9058a749ccc50,0x2669a76dec24ee35649d,0x9ccb4ae356495b4acb3c,0x39659c95743328d68652,0x62c92026e866a9cb2cf9,0xc592a0d6b256a31a590c,0xab2d89a165b3b6aeb698,0x9958ea732d618d592c29,0xc0020004000118b257d4,0x8001c0060014004000,0xe003400c002c00a0024,0x4004c0120044010003c0,0x64018005c016005401,0x7c01e007401c006c01a,0x94024008c02200840200,0xc02a00a4028009c02600,0x3000bc02e00b402c00a,0x3600d403400cc03200c4,0xc00ec03a00e403800dc0,0x10404000fc03e00f403],#[0x11c0460114044010c042,0x3404c012c04a01240480,0xc0520144050013c04e01,0x58015c0560154054014,0x5e017405c016c05a0164,0x4018c0620184060017c0,0x1a4068019c066019406,0x1bc06e01b406c01ac06a,0xd407401cc07201c40700,0xc07a01e407801dc07601,0x8001fc07e01f407c01e,0x860214084020c0820204,0xc022c08a0224088021c0,0x244090023c08e023408,0x25c0960254094024c092,0x7409c026c09a02640980,0xc0a202840a0027c09e02,0xa8029c0a602940a4028,0xae02b40ac02ac0aa02a4,0xd82e88b5a2c40b002bc0,0xa3350c9a3180c202ff0b,0x37d8db83628d5234b8d0,0xc60ee23b08e8e3948e24,0xe90484058fd63ea0f623,0x11ee469115e44390b041,0x3864d292fe4b1927c48a,0xcc528947850e140a4f19,0x56b955c54e951853d94,0x5ca16f45b3166e58795d,0x23185860317b85e31760,0x8199e65d192e63a18b66,0x1ab06a19a6c68c1a0a67],#[0xbc86e81b706d11b226be,0x647439cca7221c5c7021,0xa7a09e487841de076a1d,0x7fd9f967da9f2c7be9ec,0x64216c84920da825a04c,0xa23c88421ea871a1a08,0xa3a08d6232c8b8a2ae8a,0x554943a4c891c242a8f2,0xec9aba66098b25ec9652,0x9fda7bc9e5a7509c826,0xa67a93ea3f28b6a17283,0xc8aad8aaeaa68a8b29ca,0xe2c56b0b2be6aed2b6aa,0xadc4b642d34b3cac96b1,0xf38bb72eaeba52e6eb85,0x9ec18b016bfbafd0be32,0xec7cb196c5ab132c3d30,0xcdab32ecc0b2c8c9eb22,0x35348ed18341ccfab3a6,0xf35dcd6ab568d50b514d,0x377cdc8b6d8da8b66cd8,0x914e38387ee0d3800df0,0xe8ea73a4ce82b9cae5ab,0xf153c08ef1bb84ecb3a,0xf8ebdd8f60bd24f3dbca,0xe9bf7cfd5bf0efb1be7e,0x7c12303840b10153ffef,0xc27308e4207074c1a105,0x41d0fe43a10d6c3010b0,0xa7157452913b44a7115c,0xf1b94699194461317545,0x215c8391fa47ad1dec73],#[0x6b497f2534909235c897,0x4cb012a8ca7528ac9db2,0xccd13264c4b3014b9f2d,0xe8f3974e013674d71347,0xa53e1cf693cecee73ae4,0x142cd0814144ffd3f5cf,0x47351a345e514d44350d,0xc752d94ae527d498d20d,0x9543d501d3d54ded3574,0xd583555d51f536548151,0x689593561b57f55d156b,0x895d3571b5bdd6d55b15,0x36145833605d7e95eb57,0x66bd961649d8f962c588,0xb65a9d69e5a5768a59ef,0xedc036ebdb716cd5ae96,0x5d8174bdcff72ddc5d70,0xe77795de39782ddef76f,0x9f7dcdf2f7bb5ec97ae5,0x381260398035feb7f6df,0x864e16384ae0dd82be09,0xc262dd8aae25988761cf,0x2642f8fee3d98e2e3518,0xe50b92c6495921646991,0xe6c100c80d01365af95b,0xdc2f0078000a01780f00,0xc104f013dc20116c0818,0x701c90a3c280fb003c25,0x8216c188ce816c200dc8,0xc510c815a0a3c104c,0x2c0a1c65c1a8704f807d,0x780f41741a0d1c51876c],#[0x42c0d7428cb20cc45012,0x7907014412740b0d1855,0x781e429c41c3a0b80ba0,0x13016802a8b2c510f90f,0xa6414cb2c3c4b1179452,0x4079133c08c218078208,0xc65012cb58160b505285,0x1f8108ba116439cb543a,0xb0540f48501e5c0897bc,0x1dc477422920233854c2,0xe8198086070c121220d8,0xb81b8201d1422c081081,0xc31458152c2ac350b507,0x389360281f1c5c13417e,0x683a0f021e4564b58009,0xcfc4fe0d50d18c94fcc6,0xfcc530610d60a09214f0,0x84b9116c018d0cce0640,0xc3010600085088612700,0x218104acc24c3b0104b1,0xc15a09b00982c8618230,0x179c2e03c45d03e0501a,0x22c5bc308e016017545a,0x5c3413a0e3815028c5e4,0xf02484e342e857c1cc3,0x624b3070c610bd83cc1e,0x492681ac1e0344658524,0xf90600ec8a50658230a,0xd40714ae45d4ad441435,0x68088ac0d90520724508,0x12402f02c4b94b98b08b,0x812943902383c415421],#[0xa0f81fc0844270102202,0xc120ea08820014c0aa40,0x2380640e020192824c0c,0x10dd075c01c0500c5205,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5a025200000000000000,0x17a1c5839bb0b62a41bb,0xc0326e7fb022f60c49d3,0xb42c61d50767308a308f,0x1e722636f712643988c7,0x6426f0c7775a8b6f8415,0xf0839142df16911bc762,0xbd9aa68403ec885526aa,0x3aa20c18b3c21035b319,0xf449433a09383c71541e,0xfe21158059bca16dd99b],#[0x7d821900ff2101488c08,0x59aa0690a07d9dc4952a,0x484cdbd41a5981bbd20f,0xc7c1411a5c16ea125edd,0x53ca187edc23201bc259,0x3ccb16718a56286a6743,0xb345785da5814e90d742,0x299da62dcd21b306e834,0xb441073e88787ba62a05,0x317aac65eab1c1d0051d,0x267f87c40cb9fe1a4103,0x64200e3308ee448be2c2,0x14f2878fd1312121faa4,0x3236e045e0a1d39a2561,0x208832c57c936839fd09,0x31c6be4958628ac31d7f,0x1528df88151df611d7d0,0x726594205e287a7ea61c,0xee4017cd618bf39d9650,0xa1221bf0cc1fb9738309,0x662f1183267c85326f,0x8a5cb0638f30632f155,0x1668d829af30245fcd9,0x36690b8ff5af10217c8,0xf4af280a4ef0f881951d,0x5d410012646aff308109,0xf10cb076514ba822e18a,0xca44796a0cc99240efa,0x47fd12132c69cc6d7de4,0x88487b337e8928627b12,0x132cbc10f059435b37c1,0x81c48a4fc16ea1003d7a],#[0xf81c48b2f03bc2250d3f,0x190003e4b2b367df8c7b,0x32877e31e7df8c75f868,0x93785b48a1d588bcb1b1,0xc5d96470c1f612778681,0x85d964708015c382900a,0xa60fb0900e20618da29,0xe5299ca9946560059a36,0xc3e61cb525da1ea964e1,0x84b7dc324a4afe12c465,0x8a2b0c72f6f54a113705,0x84c7c5cc010218e81d61,0x2263e4e400810dcf8442,0x202963fe1c408cc3f40,0xc54e18f6833810defc40,0xe5fb0103313fe0250090,0x90fc08de01ae3e9008dd,0xa1a968f100a33bf28e0a,0xfe204487a1010907e120,0xa3f7e0cc20021b73e43d,0x9406636e83a1a152eb46,0x99373e432f8db324521e,0x75f692103c13664cd7e5,0xb8318785928cbcd05835,0x87cfc519092feac6a133,0xc448728394265b43d85e,0x37489afaff02c910d3d8,0x4e2334e7ad44a2d16c8b,0x88d080d7f88488864f7a,0x49ae8dc1c56350b2a3e6,0x3bff9e04512196fc5a1b,0x86f267210a14bb9f0a2],#[0x16513f522a307bdbfa75,0x8a148ef37b7610a56f9a,0x882094b85fa2232ade64,0x7f28099734e810cad7a9,0xe34f21090a0f7d8a242a,0x88ce32b1122e44ee8852,0x317ff4c4086680f1ff48,0x4bfdc6265033fe1f9684,0x197b8f948196df121021,0x1a947b4871e18a3fd191,0xd16b7c1d1a94ac0939d,0xb3420f832243f1833085,0x9386d9a112eb46a3978b,0x2734160fc8e6830e9b31,0xb26497d5f91685ce92f3,0x5a8a4a7c5bad074337a6,0xb9f3155f804241529597,0x81943f6f0a119b556748,0x98d01c1fb50c909d2fe0,0xcf488a6fb893cf82e814,0x200d7261524348a8845f,0xc000003e974b47a0125d,0x99d73464b23c2335b8a8,0xbabe8eed0e5f114c852b,0x32eb8160c0e3fa28c0c,0xd8553db0b5b13069f6b0,0xcb618a4f7f8922a85a9e,0x93839f800486cbe545f7,0xa8fee300a49347a00352,0xb47315481785d6180029,0x42d5ea15180021ed7a4c,0xd12b5a3fa8a1744f27a2],#[0x924300f687124614d375,0x159368a2761852fdd712,0x87a20008a06ee9736ee,0xb4da0887cd85d6866d0b,0xd86155f85111f10d0054,0x3a8118657d5251f9a191,0xb860e282071417d93452,0x7b4193fbace494a3380b,0x6007af94272e0ec17854,0x5781b7a502f840f4114,0xac3052e8360c67f98400,0x85d524dfa2411352c303,0xfaa2cbea885baae0dcf4,0xb7bc2eb425c8b1d8f072,0x8200049ebd18127af46b,0x9edcd478361c210f8477,0x870cad101f7cd4629f08,0xd2527363b75741ab81cd,0x186568f0cad15d510cc,0x20f166a630c8f332cad2,0x635f0def046dbd123f96,0x46eedc110c28005f7cd4,0xdc0e21b67e9961b9ec65,0xba14b916204bab831796,0x64308af82c42900abc46,0x4476d9d1c9b592d0696d,0x5dc081ef43d60537eb8,0xf8649f0807be505a1317,0xe091a2b2cea9a900004d,0x695b459162000ad79a8,0xaf76289e021be02c7520,0xf8a2db358a307b3c21d0],#[0x607195f9a91afc98a3e3,0x1c2cb501d5352e5b34b4,0x51b5c59135253d705fb6,0x245e080f52312c443913,0x2011b0eae0f584034fc,0x64b41a603f9d66a252cb,0x46f8f10042f8f0c2f66d]]
def g251H7 := limbs80 #[#[0x280d402889c602a80880,0x642400380008710650c1]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0x485105d1214415448510,0x4412150110dd52144176,0x54940441515011050940,0x50110585404415450110,0x44172501105914044162,0xdc94044182501105d940,0x50510549414438150110,0x44176505105914144162,0xdc941441865051061541,0x50910589424415450910,0x44185509105d94244164,0xdd542442875091061d42,0x54510509514438750910,0x44165545105895144154,0xdc95144186545105d951,0x54910589524415454910,0x44186549106115244176,0xe0152442875491061d52,0x551105d5544416455110,0x442875511061d5444176,0x505604412158110dd154,0x58110545604414258110,0x44162581105516044152,0x5c960441655811059160,0x581105d5604417458110,0x44372581106116044182,0x509614437558110dd160,0x58510551614415258510,0x44172585105916144163,0xdc96144175585105d161,0x58510e09614437558510,0x44164589105516244385],#[0x61d62441815891059562,0x58910dd1624428758910,0x44174591105d16344375,0xdd56444187591105d964,0x5951061d654417559510,0x441655c9105517244287,0xe0974443815d110e1572,0x5d910e0975443855d110,0x44154dc910e157644382,0x5977244164dc91058f72,0xdd11060b7444186dc910,0x44186dd51060b7544186,0x5d874481741d12060b76,0x1d12060c74481811d120,0x482871d1206187448185,0x5454048142501201d140,0x5012054d404815250120,0x48162501205854048154,0x59540481645012058d40,0x501205cd404817150120,0x48185501206054048176,0x98d40482545012061940,0x50120dc5404826450120,0x4838150120dd14048373,0xe19404838550120e0940,0x50d20591414816150520,0x48152541205055048176,0x58950481615412055150,0x54120591504816354120,0x48174541205c55048165,0x6115048181541205d950,0x5412098d504818654120],#[0x48284541209d15048264,0xe11504837554120d0550,0x54520551514838654120,0x48171545205955148161,0xdd55148176545205d151,0x55120591544838354520,0x48175551205d15448165,0x6195448180551205d954,0x55120991544818755120,0x4837455120a1d5448274,0xe19544838155120dd954,0x581201d1604838755120,0x48151581205056048131,0x58960481545812054d60,0x58120595604816458120,0x48174581205cd6048171,0x60d6048181581205d560,0x58120615604818458120,0x48284581209d16048254,0xdc5604834358120d0560,0x58120dd1604837358120,0x4838458120dd96048375,0x58d614815458520e1560,0x585205c5614816458520,0x4838558520dd16148187,0x211634807458d20e1d61,0x58d20595634815458d20,0x4825458d205d56348174,0xdd5634837458d209d163,0x591205d9644817459120,0x482745912061d6448180,0xdd5644837459120a1d64],#[0x59120e15644838159120,0x48176595205d56548387,0xa1d65481875952060165,0x59520e11654838159520,0x481655c5205517148387,0x5d971481755c5205d171,0x5d1205d574481655d120,0x481865d1206157448176,0xe0574483805d120dd174,0x5d520e1974483855d120,0x481865d5206117548176,0xe1175483755d520a1175,0x5d92021176483865d520,0x481845d92060d7648181,0xdd976482845d92061576,0x5d920e1176483815d920,0x48174951205925448385,0x60e5448180951205da54,0x95120a1e544818795120,0x4817498d205526348376,0x5d6644817499120dd663,0x9912061e644818099120,0x481769d1205d67448375,0xdd274481879d12060274,0xd0520dda74483759d120,0x48164d052058f4148151,0x6034148176d05205d741,0xd0520a1f4148187d0520,0x48176d0d20ddb4148375,0x61f4348185d0d2060343,0xdc520ddb4348287d0d20,0x48165dc52058f7148154],#[0xa0f7148263dc52060f71,0xdd1205977448181dcd20,0x48184dd52061b7448181,0x6137648181dd92061b75,0x50930589424c284dd920,0x4c186dc930591624c186,0x58d42501545094061b74,0x50940595425016450940,0x50263509405d94250175,0xe01425037650940dd542,0x54540551515014254540,0x50165545405895150161,0xdc55150287545405c951,0x54940e0d515037254540,0x50163549405895250154,0x5d552501655494059152,0x54940611525017654940,0x502635494061d5250186,0xa1d52502845494099152,0x54940e05525037654940,0x5038754940e195250384,0x5d954501655514059154,0x55140609545018155140,0x5037655140dd55450186,0x509605038655140e0954,0x58140549605015158140,0x50162581405516050153,0x5c560501655814059160,0x581405cd605017258140,0x50182581406056050175,0x95160501855814060d60,0x58140dc5605034258140],#[0x5037558140dcd6050372,0xe09605038158140dd960,0x58540549615014258540,0x50171585405916150154,0xdc961502875854061d61,0x58540e15615038258540,0x501545894054d6250387,0x5c962501655894059162,0x589405d9625017558940,0x501845894060d6250180,0xa1162502545894061d62,0x58940dd5625028758940,0x5038558940e116250381,0x595635015458d40e1d62,0x58d40951635017558d40,0x50182591405d56450375,0xdd564501855914060d64,0x59140e09645037659140,0x50187595405d56550385,0xe05655028759540a1165,0x59540e11655038259540,0x501635c9405517250387,0x5d972501755c94059172,0x5c940e0172502645c940,0x501765d540e117250381,0xdd575501865d54060975,0x5d540e0975503815d540,0x501825d9406057650386,0xdd976501855d94060d76,0x5d940e0976503815d940,0x50182951405da5450385,0x5d6635015498d40dda54],#[0x991405d6645037598d40,0x50163d0940dd66450182,0x5db4250175d094059742,0xd0940a1f4250185d0940,0x50152dc540ddb4250375,0x5937150162dc54055371,0xdc54060b7150165dc540,0x50163dc9405537250185,0x6177250165dc94059372,0xdc9409537250186dc940,0x50182dd5409937250263,0x6177650182dd94061b75,0x585415d5615056458541,0x50580591415d56450780,0x61d6550580595415d565,0x5d941e0176507805d541,0x54161505505494154385,0x58d52541645055058941,0x549505d9525417454950,0x54374549509d15254264,0x5d9545416455150dd952,0x55150609545418155150,0x54376551509915454186,0x505605438655150e0954,0x58150551605415258150,0x54165581505916054162,0x5d16054172581505c560,0x58150609605418158150,0x54284581509d16054184,0xdc9605437158150d0560,0x58550e09605437458150,0x54164585505516154152],#[0xe096154187585505c961,0x58950551625438758550,0x54176589505c96254165,0x61d62541815895060162,0x58950dd1625428758950,0x5438758950e116254381,0x5d1635416558d5055163,0x59150dd1635427458d50,0x542745915061d6454174,0xe05645437459150a1d64,0x59550e1d645438259150,0x54284595506116554182,0x5c9715438459550e0965,0x5c9509d172541635c950,0x541765d1505957454385,0x21176543855d150e0574,0x5d95060976541815d950,0x543815d950a117654184,0x55263543845d950e0976,0x9d150596745418799150,0x541859d1506027454176,0x58b4154152d055061e74,0xd05505974154164d0550,0x54185d055060b4154176,0xddb4154372d055061f41,0xdc95060b7154162dc550,0x54164dc95058f7254154,0x61b7254184dc95059772,0xdd1509937254263dc950,0x54186dd15060b7454165,0x60154545765515161376,0x58551551615458655151],#[0x5458059551e056454780,0x60164553805d95161165,0x59554601655538059154,0x551645c154e056555380,0x60176551765c15459570,0x99154e0576553805d954,0x55165dc1545937055180,0x5977155186dc15460b70,0x505606037655180dc554,0x58171505605954158164,0x589515815454560dc941,0x545605c5515816554560,0x5838354560dc95158172,0x5d154581655516059154,0x55160605545818055160,0x582745516061d5458186,0xe05545837455160a1d54,0x58960e1d545838255160,0x58175589605d16258173,0xd0d62582745896095162,0x59160dd5625837458960,0x58183591606096458175,0xe1564583825916061564,0x59560611655818259560,0x5838459560e096558284,0x59171581625c56055171,0x5c5605d171581655c560,0x581655c9605917258382,0x59173583865c9609d172,0x5d16059574583825cd60,0x5818095160e197458381,0x59674581879516060a54],#[0x9d16060274581759d160,0x58162d05605474158187,0x5d74158165d056059341,0xd056060b4158180d0560,0x58375d0560dcb4158187,0x5537158187d0d6060343,0xdc9606177158182dc560,0x58165dc9605937258154,0x6177258184dc96060772,0xdd160d0f7258254dc960,0x58185dd16060b7458181,0x6137558182dd56060775,0x55161601545856455161,0x5877455161a1d5458581,0xe09705858059161e0154,0xdd16160b7058554dc161,0x58d801d1636037558580,0xe015458d805516359554,0x595636116558d8059563,0x58d82dc1636025458e84,0x60b70591735c16460374,0xdc5646037159185dc164,0x596745c1656037559185,0x6137059582dc16561e74,0x5c2546037459580dc565,0x9938055263e197095382,0x55152d03855c264e0970,0x54b4058d52d016254b40,0xd017554b4059552d0164,0x61d52d018654b405d952,0x5534059554d038654b40,0xd016458b4055162d0186],#[0x61d62d017258b4059562,0x58f4055163d038558b40,0xd03825974061d65d0165,0x59172d01635cb4055172,0x54741e1972d03855cb40,0xd07805974161d65d0565,0xe0970d05645c34154570,0x5c343e1970d07855c341,0xff1ee3bc6fe1970d0f82,0x3fa7ecfb9ef3be6fcbf8,0xabed7baef5beafd3fa6f,0xbdafb5d67ecf597aff5f,0xd7b9f73adfdbeb7b6eed,0xbdb7aef55e7bbf77aedd,0xd7f6fe5fabed7d6f7dee,0xdf3ae6fcbf93f1fe2fbf,0x4fe9ed2f9ff3f67dcf79,0x6bdd77aeb5beafd5dab7,0xfdbdb776d6d7d9faff5f,0xf5bdb77eeeddbbab73ed,0xc7f8f717dfdbf77e6fbd,0xf9d737e6bcbf9772de57,0xdf5aeafd3f9ff3ee7bce,0x6ded7dabb3f5febdd77a,0xef9defbd776eebdbfb77,0xfe5bc7f8ef1be1fbf77d,0x9fcff9ef3be73cdf9af2,0xda7aff5deb7d67abf55e,0x7bdf79eefdd7b8f6ded7,0xff9df37e67cbf95f1fdf,0xc5f7beefdbfb5f5be97c,0xfb7f67ebfd5fa3f3fe6f],#[0x4027fcff5fe7fb7f2fdd,0x4c6ac604ccaa8035328,0xb2eaec05b72e402c4ac8,0x412ca1cc4ac81bc82c41,0xcaea1f2eae81eb0ae41e,0xac627afac6262e2ec09a,0xe825afee8252fae8252f,0x63f3728448807282bae2,0x3f2730a3f51cc63f51ac,0xf376ec3f372ec3f2770a,0x4baa8402770c3f2730c3,0x130c4243ac84224b0a40,0xb24482eaec4312b24472,0xc64e0bb2c3e8f32a3e92,0xc4e24f084e4ecc64e4ea,0x4e24b0c4e346ec4e342e,0x2130c4fc02ca4fa4f0c,0xb0ac46facaec513f2ca5,0x170867b0ee867b0ae867,0x70a67b0eea67b0aea67a,0x30ab2caea68aeae86821,0xa7885f2c791ab02ab80b,0x3b1830c3b1930a3b2c2e,0xb9fac8d72eac8d480730,0xbb2cd40bb2ccbc3ac4c,0xe2cacd9fac8d7aeac8d5,0xf24ce8bb2cd38bb2ccdb,0x2aceaeeeaceaeaeace8b,0xae7bd2cae72caeacf0bf,0xacadac9ab01724ee2c2e,0x2cacb272c2ebad3d2cb,0xacacb278ab2d20402c52],#[0xab2d20be2c9209e2cb28,0xf29220af25222cacb280,0xc9842c2cb34ac2cb4d8a,0xb101f2c9111fac97e1fa,0x991dacb97bdac954ae2e,0x51432c02a830c028a32b,0x2830c041cb0c07a2b0c0,0xc30c018e32c1d0e32c1c,0xf240b1c30c0b96f20089,0x20241c30c1384f2a0b04,0x8289c2e8289c70a2616f,0xf84b28291c2ea2884b2,0x781f2a0e857200e01b30,0x8532817a5aa817a9ac41,0x5720160532c17a5aca17,0xf2a2b81b302d1a7082c8,0x303701b2c3281b283281,0x42f01b302f81b303781b,0x3388b243301f2a2f01f2,0x81b2c3401b243401b2c,0x1b283501b2c3481f243,0x1b283581b243581b2a35,0xb0c403aaec403aaec3f0,0xc4138aec411632c4029,0xc432830c4738aec47283,0x43b22ec43b8aec3eb22e,0xb1caec4b1caec4605330,0x3892845326ec450532c4,0x9f2446a2f0c46b8f2845,0xb0c4eb5aec4e8572a46a,0xec578932e56322ec50a5,0x45435f2a528532c579ca],#[0x6e8932e6e857285429f2,0xf0932a6fb5eea6605330,0x38ae867053306f0932e6,0x8ae86d0932e6735aea67,0x2ea68053306d0932e6d3,0xca6a3af246a38ee86a32,0xe6db272c6a0972a6a322,0x6e0932a70853306d8932,0xa8532a72053306e0932e,0x8932871097286ab5eea6,0xcaeca3af2ec4c8532872,0x30ea19c30ea1356eaa11,0xaa29a30ea22f2eca21b,0xca301b30a501b30a299b,0xa581f30a301b30a318b0,0x481f2ca401f2aa401b30,0x356ea5a356ea5901b2ca,0x32e8589b2ec5c1b2e85c,0x2ec5986f2a5a86d2e58b,0x225b99b0e5b86d2e59ad,0xa5b06b2c5b86b285bb53,0x75af2e874302e87386f2,0x6837287501b2e761a708,0x98f0c8799f0a871a7088,0xa308a91b2ecaa9b2e8aa,0xb0aaa01b30a919b0aa91,0x284d01b30aa18b0caa19,0x8a619aeca71caeca6877,0xa601b30a618b0ca60772,0x801f2ca781b30a881f30,0x36ae8780672c7901b2ca,0x6ae87a07b2e7833aea78],#[0x7207936ee87907b2e7a3,0x2c7907f2a79302ca793a,0xa7b07b2e7ab6ee87ab07,0x79b032e7887b2e7787b2,0x987b287b87f2879b3eea,0x7b2e99b3aea99b6ae89,0xc2e8ac07b289a87f2a9a,0x2ea5c81b2e631c2ecac1,0x2e5c9a30e5caf2ec5cb3,0xe609a30e60b32ea60873,0x5db8f205db32ea5d8732,0xd9a30c5db372a5db32ca,0x332ea610772c5d9a70c5,0x1b306206b2a620732e61,0xb2e5d19b0e5d2d2ec5d0,0x2c5e19f0c5e19b0c5e06,0x5e81b305e98b0c5e86f,0x6286b2a62873286281f3,0x1cf206001b2e6381b30,0x873286181f2c6019f2a6,0xcaec9701b2c6181b2861,0x30e95af2ec959b2ec979,0x2c961a30c960732e959a,0x9681b309698b0c96877,0x9801b3099073289901f3,0x53208001b2c9881f2c,0x1a70a7c38f207c01b2e8,0xf2ec7e2f72c7c0772a7c,0xb307f0632c7f0732e7e2,0x307f8632c7f873287f81,0xe8098aec80853208081b,0x7caf7287caf1287c81b2],#[0xd9a7287d9cf207d98930,0x98f2c7d81f2a7d81f287,0x53208101b287e873287e,0x7309b0772a9b1a30a9b0,0x289d01b309b99b0a9b9a,0xc3c01f2a9c81b309d073,0x3b99aec3d1b2ec3c9c2e,0xab8ee88b01b2c3e01f30,0x77288919f0a888732c8,0x932c8b3af048b18f0c89,0x7208981d308801b2a8b8,0x2a8c897208a01b2c8c09,0xa9d8732c9f9caec9e81b,0x9e077289e01b30a019b0,0xf01f2a9f01b30a098b0c,0x98b0cac99b0aac81f2c9,0x53208401f2aad81b30ac,0xaea84853208481b2e840,0x288181b2e8498aec8499,0x8831cf20832d72a8206f,0x8386b2a8399f2a8301f2,0x501b288381b30838632c,0x6b2c8f06b288f053208,0x93208e897208d86f2a8d,0xb2890097208e01b2c8f8,0x289381f28ae81f2cae01,0x89107128910972091063,0x9181b2a9407b26940772,0x88b229086f2a9189720,0x97209206b2a9087b269,0x1b2a949a708930932093,0xf2aaf81b289509720928],#[0x24d709324d485720b101,0x4bb89324d60e32ccc853,0xbb332ecb89b2ecbc88b2,0xb01b2edc81b2edc01b24,0x1b310603328dd01b24d,0x1b310718b0d071bb0507,0xf2b089a2c9089b2c7088,0x2eb481b310801f2d0881,0xcb69a30cb69a30cb5073,0xb5b7f24b5af6ecb58732,0x40732d050732f028772a,0x9a731038772b039a2ed0,0x32ecbd312ecbd81b2ec4,0xb2ebf05320c523b0cbd3,0x30c401f30c019b0cbf86,0x4c381b2ec581f2ec101b,0xe528508e101b2cc38832,0xe01b2ee503328e505320,0x83330e32f2ece32f2ecd,0x632edf05320e583330e3,0xb30e48632ce488324e48,0x2ee603328e605320e601,0x4e40672ae0b1724e081b,0xf383328e68632ce40832,0xb1a30d0c9a30d0998f0c,0x81f2b0c01b310b087250,0x7b250007b24e93032ee7,0x724c7af6ecc79a2ecca8,0xecfe07324ca3372ac787,0x4fe9a730fd87724fd9a2,0x183324ed07324eb8732,0x81b2ef001b2eef87325],#[0x8724ee01b2ef085320f,0xb924ee1cf20ee04724ee,0x728ee01f24ee1bf24ee1,0x2cee19f2aee01f28ee1a,0xcf601b24ef0632cef18f,0xf901b2cf881b24f818f0,0xb81f250e81f2d0e01b24,0x1b24fc07728f986324f,0x7728fa09720fa01b2afc,0x728fa88f22fa81b2afc8,0x28fb08724fb09720fb07,0xda381f2b0f01b24fd077,0xa701b31a699b0da623b0,0xc1a30fa981f2fa705721,0x1f2bab81b2fac03329a,0x533125893252701b2db0,0xb314919aed4a09325280,0x2b3b81b2f2b81f314901,0x14c18b0d4c1bb054c06f,0x1a19acb4c99aa94c81b3,0x8b4f251886b2d1a19b0d,0x2b2b31053213106f291,0x832530ad2ed2c81b2f31,0x3213181b31308632d308,0x252e01b2f3182b2b3185,0xd300832530067292e317,0x3c82b2b3205321320632,0xe19b0d4d06b2b3c89321,0x81f294f81b314e087254,0x6f251b99aed1e87b2534,0xb251e337291bb31291b8,0x2d3701b2f3801b2f3786],#[0x13884725358872535863,0x461caed4598f0d3e0532,0x198b0d45077294519aed,0x2b253b01f255219acb5,0x97214081b254206f2b40,0x7214101b294286f2b408,0x214186f2b41087254109,0x54306b2b419a70941893,0x8598b0f821c30f8181b2,0x501f258501b318601b31,0x1f298818ac98801f2b8,0x9b0b879a3098781f2b88,0xf298881f258881b31879,0x2f6f0632f6e8632f6f81,0x9708632b70023316f063,0x7a9a7097a893217a8632,0x9087258901b318c8632d,0x1b318919b0b891a3098,0x1f2b8b01b318c1a3098c,0xb2f6b81f258701f298b8,0xeb6a332eb6781b2f6c01,0x56986b2b6b0732f6a332,0x7381f257f073296a8872,0x101f2581077298002325,0x1f258e01f2b8d81f2b8,0x1f298f02325760632f75,0xb2d1401f211381f258f8,0x211501b2b1481b251481,0xdb401b25b401b2db381b,0x5704b215581b25b481b2,0x181b319401b295701b25,0x1b25b581b2db5073299],#[0x2b215982b25590332558,0xb2da101b215c81b255c0,0x2b9b88f239b01b25a181,0x59d81f2b9c81f259c81f,0x9e1a7099e01b25a301f2,0x1f299f0632d9e06b2b,0x1f25a081f29a001f25a,0x4a840316f2a0254aa802,0xee404d4a8404bbee4035,0x2a04d4aa80496f2404bb,0x80816b240854a840816f,0x2d4b220296b2a0854aa,0x29432a02d22c602d3ac4,0xb8eec02b8aec029472a0,0xdaa8039472c02a870c02,0x2c607b8aa80645ac8054,0x2c07b8ac807b8aa807ba,0x40454b22041472807093,0x438aec044daca041472,0x41432c042870c0438eec,0x49aca1b09724069472c0,0x9ac41b96f2a1b3beea1b,0xac41cc9aca1bbbee41bc,0xc81c48ac41c3bee41cc9,0x21e422ca1d48ac41d45a,0x1e326e81e322e81e49b2,0xe322ea1e0e7281e22f08,0xb22ca1f8e72a1e326ea1,0xcf0822322c8220972a1f,0x32a22322ca2209328221,0xe81dc5ac81d8e72c2109,0xa1e8e32c1dc22ca1db8e],#[0x20322ca200972420326e,0xf49b221f322ca228972a,0x9724208e7281f0e7241,0x86e80009328230932423,0x70c0188b280188f2a00b,0xc80908f2a0108b2c019c,0xa0bb82c80bb9ac60bc52,0xa04f240a88b2c0b9c30,0x3c1aca11cd2a81088f24,0x88b2c13b52ca13b52a81,0x72c62384f241308f2412,0xac82788f2a26452c823c,0xa2788b28279c70827b1,0x828a22c82888b2a279c7,0x2484b2a289c6ea289c6e,0x5a7f0824b86e824c52c8,0x8f2a2688f2426b1eea2,0x8b282808b242808f2427,0x2ea0c442c80c84b24290,0x300d883240faf2ec0d33,0xa10073280f077280e81f,0x15336e81440aca1481b2,0x7083241706f2a1681f30,0x2d2ea2aaf2e82a06b2a1,0x77282b887242b883242d,0x708318632c2c0672c2b8,0x83681d303201d30319a,0x83701b303619b0a361b3,0x3819b0a3798b0c371a30,0x807f242d81f2a3801f28,0xb32ca1a873241aaf2ec1,0x77281906f24188732c1a],#[0x3281a01f241981f30190,0x282f8772a2e077242e07,0x433067242e8632c2f873,0x3881b2a3384b2a3304b2,0x1f2a3901f243901f2a,0x8632c3106f2a3086f243,0x1f2c3981f283981b2834,0xf2a3a81f283a01f243a0,0xa83f95f263fd3a843f81,0x841c7ac641d3a8441cda,0x4438ee84453a844445ac,0x895b2648d3a844894728,0x53a844a53a8445b8aa84,0x3ac83f53aa83f562c63f,0xf0a3f29b0a3f53ee83f5,0xc3f29b0c3f3aeec3f29,0x63f53ac63f53aa63f29f,0x3f53b063f53ee63f53ae,0xf53aea3f53aca3f53f06,0x53f0a3f53b0a3f53eea3,0x3b0c3f53eec3f53aec3f,0x4c640562c64053f0c3f5,0xc84053ac8404faa84056,0x84053d284053b284053c,0x404feea404faca401672,0x29f0c403aeec404fb0a,0x53ca84253aa8421672c4,0x3ee842538e84248ac842,0x7284253d284253b28425,0xa4229b0a4248aca4216,0xc4248eec421672a4229f,0x4ad3aa84ad62c64ac8b0],#[0xaa9b0a4ad3ee84ad3ac8,0x9632c4aa9b0c4a9632a4,0x20e842d24a842d22a842,0x30a42c7aca42d26e842d,0xa47d22a847a970a42a9,0xa4116b22492970a47a93,0x414daca4153b244125f0,0x138eec414df0a414daea,0x1472c411432c412870c4,0x432c472870c4738eec47,0x30a4353b244322f0c431,0xec431472a432870a4328,0xa482830a4845f0c4345a,0x3e9432c3e9432a482870,0x39432c49b8aec4994530,0x16724460553043a5b0a4,0xceec4629f244625f0a46,0x728451ceec4b0572c461,0xa44d8532a4b967244694,0xa569632456cfaa456cfa,0x51cfaa44f05330569132,0xe4faa4531172a51cfaa4,0x4fae84e4fcc84e4fac84,0xfd084e4fb084e4fce84e,0xaa84fcfb0c4e4faec4e4,0x284fa9f084fc8ac84fcf,0xc4fcfb2a4fcfeea4f967,0x5029708504f2a85048b0,0xecfb244ecf2a854cf6ea,0xcdae84ecdcc84ecdac84,0x5f0c4eb5eec4ecdce84e,0x324551172c4e9132c4ea],#[0x245205330551132a5516,0xa5596324559172a52167,0x53967245385330559132,0x61132a5616324561172a,0x4fb245125aca57853305,0x132857422ec511172851,0x72a529132c5735aec571,0xc4650532858167245411,0x46ec5ac865c8ac465c8a,0x6ec5ac86e963246ec8ac,0x648ac4660952e6e8e32c,0x48ac469422ca6615f266,0x8ac46f8e72c69326ec69,0xac46b322ca6f95b266fc,0x8667c8a8667967246b48,0x667c8ae667c8aa667c8e,0x67c8aa867c8b0667c8ee,0x7c8ae867c88e867c8ca8,0xc8b0867c8ee867c8ce86,0x8eea67c8aea67c8d0867,0x32a6f163246f48b0a67c,0x22700952e6f0e32c6f11,0xa6745ac867167246b96b,0x6d0952e670e32c67422c,0xd45ac86d15b266d16324,0x48b24680952e6d0e32c6,0x5ce868322e86845ae868,0x72a68326ea68326e8684,0xe86495b266496b22648e,0xe648e32c649132a64b8a,0x6a326ec6a167246a0952,0x8e32c6d963246d8e72c],#[0xe72c6c167246c322ca7,0x8b24688e32c6e163246e,0x7246cc22ea688e72868c,0xc84c472c64c0e3287196,0x8a3a92c6a3aaaa2a3c52,0xa39ceeca38572aa3a82c,0xc1b6e85c1b50ea18572c,0xc72c67483b2c5c1b6ec5,0x5320768572075306e873,0x72ca69ceeca683f30a98,0x2e783faca7819eeca705,0x7a07d2e7a15b207a07d,0x7736ae877153227703d3,0x707d2e770cb2c771032a,0x8cf2c7915f207903d307,0x5b2077b02ca7b15b207a,0xaea78c7b207887d2e779,0x206329b045f3052e78bf,0xa5d947205d9432060853,0x6381f2e5f943206106f2,0x70532064057206005320,0x8572c971ceec97282c89,0x47207c29b047d1b6ec97,0x3207e0672c7c2f2ec7c1,0x2a9c057207d877287d94,0x3d9a7303b1a30c3b057,0x8b29f048b20b263da2b2,0xe8572a9e8532c8b0532a,0x81f2aad0572c9e9ceec9,0x6f2a832d2ec81a9b0482,0xf2aaf1a3089085720830,0x28b2442c8b089320b001],#[0x8cc15f26cc01f24b281f,0xcfc22cacc45ac8cc4daa,0x4b22c4d4c5ac8d4c5ac8,0xc5ac8d18932ad4b22cad,0x82a8d728284d714728d1,0xac8cbbaee4cbc8ac4cba,0x4cbd3ee4cb8e32ccbc5,0xacbb8aeacbc5acacbd3b,0xcb9472acb9432acbb8ee,0x445acad445b2ccbc5eec,0x1432ad438eead438aead,0xdaa8ccc8ac4cc9452ed4,0xaeaccc22caccc5ac8ccc,0xa8ce48ae4ce0952eccb5,0x8ce45b28ce45ca8ce45a,0xce322eace0e728ce45d2,0x45ac8d00e72ace326ea,0xe72cd0326ecd014728d,0x8ca8d538aa8d545ac8d5,0x32ad5322cad5322c8d53,0x2cd214728d245ac8d209,0x8d7a84a8d7a82a8d78e7,0xd79caead7a2acad7a2ac,0x5c5ac8d0c5ac8cd1ceea,0x94728d2c5ac8d2c5ac8d,0x5eeacdc22cacdc5ac8cd,0xeeacd94724cd8e32ccdb,0x2ccdc5eeccdcdb0acdcd,0xaceb22eace94324d3c5b,0xcec5b24cec5b22ceb26e,0xec5eeacec5aeacec5b26,0xe724cf45b2acec5b0ac],#[0xe728cf45d28cf45b28cf,0x6ecd135eead1422eacf0,0x2cd109724d10e72cd132,0xad68e324d694728d3327,0xbbc52c8b94d2a8b90e32,0xc1b706bc26f06b84d2a8,0x9b6ecbca6ac8bcb32a8b,0x3b0cb8b36ecb883b2cbc,0x2c6da0ff2cb88fb2cb8a,0xc6dbc32c6d8452c8da47,0x8dc05320dc2f2c8dbb02,0xdcaf6ead9af2ead9a02c,0x601b2adb03728da85320,0x1a30b07af2c90719b0b0,0x1f2d0901f250919b0b08,0x2c8b7a82a8b7a92c6b78,0xecb4336eab30532cb7a8,0x4b788724b588724b52f6,0xb7a830ab7d22c6b7d3ee,0x3c32cab39432cb7a830c,0x36aeab636eeab3b6aeab,0x752eb4b32eab4b6eeab6,0xf24b5336eab513724b50,0xcb68772cb51a70cb537,0xb020732ab713724b59a7,0x236eeb0236aeb02432c,0x2b32eb02a6d0f0226b0b,0x1a30d030333102a3b0b0,0xa6ed041a30d050772d03,0x32d048732b0583731039,0xa8bd83328c4a3aa8c483,0xabdc0acabdc42c8bdcc2],#[0xbe3facabe4b2a8be34ae,0x24b2a8c21b50ebe33aea,0x23f0cbd336ecbd33aeac,0x32eabe8ff2cbd0fb2cbd,0xb2ac2b32eac29a50ebeb,0x24c30ff2ac083330c28f,0x4bf83330c30fb2ac3133,0xc406f2cbf99f0cbfb4f2,0x188724c183328c586b2a,0x3328c606b2ac386f2ac,0xe72ce128308e145ac8e1,0x728dfc42c8dfa02c8e50,0x2cde3eacade312ecdf93,0xce313324e31a50ede0c3,0xdeaf6eadeaf2eade8c32,0x393324e38c72ce20c72a,0x81f30e02d2eadf0c32ce,0x3728e28672ce288724e2,0xf08f228708f481b2ae40,0xaf1b36eaf1a0f0cf226,0xf42070cf2af6ecf2a3f,0xa19f0af30332cf58353,0xa302cb0a36ca90a36aa9,0x9b30b0d36aa90d1b30b0,0x772d098732d09b32cb09,0x72b0a9a30b0a8732d0c8,0xb0b0732b0d9a30b0d87,0xae73facae701f2d0b99b,0xe8cb6eae712724e733ee,0x7c3528e7c3328e792324,0x33eeae83052ee7bfaeae,0x7f24ff92724ff07f24e8],#[0xb24c9af6ecc6b36eac68,0x20c906f2ac786b2cc986,0xccaa3acaca94720c8857,0xc70ff22c70332cca9a6e,0x9b32ecc98fb24c98ff24,0x14720c90ff2ac78fb2cc,0x3324cb03724c928720c9,0x730fd8372cfe1a6ecfe0,0x20ea06324ec0672ce983,0xaec9a6eaec9a2eaec947,0xe9b36eae993f22ea8332,0x987724e98c72ce9af6ec,0xc324ec14720eb2f72ce,0x372b011a6eb011a2eb01,0x73100877250083731008,0xeaf003328f003328ef9a,0xee8c32cee8fb2aee99a,0xee2d72ced86f24ed8333,0xf03728ee0672cee06f2a,0x86b24f783328f106b2ae,0x9720f686f2af606b2cf7,0x728f708724f709720f70,0xc9a44c2a9a401f250f87,0xda434aeba440acba4442,0xa4cb2a9a49bb0fa4312e,0x39b30fa4b3aeba4bfacb,0xfb2da3a3f0da3b32eda,0x9b0fa59a30fa5332eba5,0x329a819f0da606b2fa59,0xa9ab01f2da781b2fa803,0xba98872bab312cbab37a,0xaa0c32da9af2eda9beac],#[0xf0632faaad2ebaaaf2eb,0x9b70baf302cbaf36aa9a,0x732dae9a70daeb32cbae,0x329ad01b2bb09a70baf8,0x25a90ff25a8b032fad43,0xbae03329ae1a72fa9037,0x1f81f25ad81b2fae19ae,0x6c5ac926c22cb1fc5ac9,0x8e32d269132b26c22cb2,0x22c527422cb228932f26,0xb05201172b24422cb243,0x292035ee920422c9204f,0x92148ae5214232d20117,0x210e72921326e921422a,0x79172b23422cb234232b,0x8932927b22c927b5aa92,0x5aa9289172b24c22cb24,0x725209cee928a2ac928a,0x920cdb0920c22c92091,0x9218e72521c232d20cdd,0x21b26e921c5ce921c5ae,0x39172b23c22cb23c232b,0x9132b25c22cb258e72d2,0x22cb250932f258e32d25,0x2cb260e72d251172b254,0x2f260e32d261132b2642,0x92242325224232322093,0x47452c91642529224232,0x801b314b19b0b4b19b0f,0x99b0f489a30f4823b0b4,0x1b314b99eed4a02b3148,0xac92981f2d4a81f254a8],#[0x212c02f2b2b23f0929be,0x917ad2cb4c02b2b2c053,0x1990f251806b2f1933ee,0x986b2f1990b251991321,0x86b291a90f251882b311,0xacb2da5b0b2ec22cb2e,0xac92cb12ed2d90f2b2dc,0x292d2d2cb308b32d2cbe,0xb2f857212f887252f8b7,0x3d2470b3c3facb3c02f2,0xdb3aa94d82b2d3d02b29,0x1b3095033aa9501b3094,0x6b2d4d334c94d332c94d,0x309509a3094e06f2d4d0,0xcb4f01b315086b2b509a,0x53286f294e81f2d4f19a,0x341072b33bfacb339072,0x41032b343facb3415b21,0x3fb253303d313407b2f3,0x72543bfd29333fb2933,0xeed1ea3ac91e917211c9,0x251d8ff251b02b2d1e99,0x11d117211d0ff291b8fb,0x3782b251f02f251d25f2,0x60ff2b3502b2b3802b2b,0x8732f360fb2b36143213,0x2f2b3585721358772935,0xf254402b2b3887329368,0x2d3f02b253f1ef0d3d81,0xd45a5acb45857254582b,0x4499b0f449eb0d448572,0x101f2d4681f254682b31],#[0x82b293a917213906f255,0xb32d3a113213a1172139,0x3093f82b313a06b2f3a0,0xc962c52c96201f25529a,0x3841eb0b61a030b612f2,0x841cee58422ac5842aaa,0x18572b8422acb8405725,0xa230d81c1acb81c52c98,0x2c98498b0d85af2c985,0x331831eb0b832030b82a,0x765a0f0763c1acb6482,0x96620ac9662d2cb659b7,0x640b32d633eac9631b6e,0x82070977a1f05770b729,0x8e3216faf2c9879ef0b7,0xe3216e8d7256d0b32b6f,0x3216f0d7256d8cb276e8,0x9798d7256e0d3256f0e,0xb8a823297b1ef0b7a207,0x8c86b2b8c893218c81f2,0x92d2cb892f2c9890632d,0x7b278c093218c0632d8,0x672b898632d8c2f2c98c,0x7097b8572586867298a0,0xd68422cb6845ac96820,0xb6ba02c96b853216ba2b,0x6c053216c0232d6b9eac,0x68232d6c1eacb6c202c9,0xbeacb67beaeb668c7256,0xeacb6a143216a0c72d67,0xf21690b725670c32d6a3,0x21698772969827256922],#[0x16c8272d698472569857,0x7e857257e0232d6c8532,0x20232b730e72171a02c9,0x8e721728c729710df237,0x232b7d823257d9ef0b7c,0x72b80a2acb8085725808,0x258d023317f9eb0b7f85,0x9758e7217401f2b8d01f,0x750e321750e721748232,0x101f258e82331750b32b,0x45321101c2eb1104b251,0x77211188f2110c532b10,0x705b281b251406f21128,0xdb2b52cbb2b82c9b29c,0xbb39a2c9b39b2c7b39c7,0xb201b2bb49a70bb301b2,0x501f21b181b2fb219aeb,0x222c955252a95504b255,0x8ac994a0ac79386f2153,0x2c99401f2b9481f29949,0xc991202c99299b0b942f,0xb9501f25950732192452,0x9a01f299581f259581f2,0x703f299a01f259a81f29,0xbfb219683b2597bfacb9,0x3f259a83f259603f2599,0xb09980cf259820b05980,0x21990cf21988cf299820,0xd5aa070d5a03b25a20cb,0x5e9a2c95e98f0d5b1ef0,0xe077255d81f2d5e99acb,0x1f256001f255f06f255],#[0x1f2d6019acb601a2c960,0xf2958837255d0ff2b578,0x2b5b877295b887255b8f,0x59c1a2c9a101f256086f,0x9f81b2ba281f219d01f2,0x4d83040301f219e81f25,0xd7ac403d5aca02d82a40,0x12ca03d5b2803d5ac803,0xaca0555aa8053ceec03d,0x240455aa8073caca07ca,0x41bd830a1b55b0c0455b,0x1c55aa81c5830a1bd82a,0xd512a81d57b041d4aaca,0x4ab2c1d5130a1d4aac81,0xab2a1e4ab0a1e4aaa81e,0xaca213caa8223cb0a1fc,0xa1dd5b081dabb0a214a,0x41f4aaca21cab0a1ed13,0x8d52c808d72c408cab2,0xbca2ca093c6ec08d0aca,0xd0b241250b24113c2ca0,0xc2a827d0aa824552a823,0x3220c492ca0cd42a80cb,0x2c0c396ec0c4e2ca0c55,0x814d02a814d73221494f,0x143b52e14bb32e14c92c,0x4366ec144e2c81450b22,0x17f201617f201591f2c1,0x2b0e2ac62c829ca2ca2b,0x2ca36392c83632d0e2ab,0xe23fd82c23f89f2c3636,0xa3fd5ac83fd7ac43fd82],#[0x4455aa841d7aa441d12c,0x257aa64255aa84457aa4,0xd5ac840d7b264257ae64,0x6f2e42d6f284297f2e42,0xb264355b224155ac844d,0xc44dd82e24dd82c24dd5,0x456d12ca4dd5ac84dd7a,0x56d12ca56d5ac856d7ac,0x1caac84f582e24f17b2c,0xd12ca51bcae851d7ac45,0x7b224f97f2c51bcaec51,0x2a26ecaaca6597f22525,0x266582e2664aaca6ed8,0xa664aac866512a866583,0x66caaca6b4aaca69516e,0x84aac86bcaac869caac8,0x50acaa12bacaa3cab266,0xa2c85950aa8592b30ca1,0x2e85a50aa85a50eea594,0x2c5a3c2ec5a50aca5a3c,0x858ce2c858d132058977,0x5a977225a91f2c58ce2e,0xbc2aec59d13205991f2a,0x11f2a5b11b2c5bb62ec5,0x2aec86392e885c62c873,0xa84cc32d0eb1bb52eb0b,0xcad4d5aa8d4caac4cc55,0xad1d5aa8d1bcb0ad4caa,0xce55b06cbd5aa6cbcaac,0x2cab26ce4ab06ce4aaa6,0x4ab22cf55b22cd97f24d,0xe2a8b9ce2cab855284b9],#[0x2a8bac2acab9c62c8b9c,0x28ba4e32cb8ce324b8ce,0x2d9462c8d8ce2a8d8ce3,0x6ce2cb06c632ad9d532,0xd52f28b3a8b0d06b92ed,0xc62c8e1c62c8ddce322b,0xe2cac828aa8f546326de,0xf22c7ce322c728b0cc84,0xa51fd83031f94f22c914,0x526d12a526caac51fd12,0x2417b312697b2526caac,0x417f25244aac524512a5,0x2bb09244aac924512a92,0xab2321d132320cab2321,0xaa51617f232517f2323c,0xcb16c62c916ce2c915d0,0xd474e2c9474e32b1742a,0x47c62c947aa30547a630,0x9a8ac949a330d47c2acb,0x91f2b2ac2ac929262cb4,0x2b2b2a462e92a50b2329,0x30d1c4e2c91c42acb2f4,0x231d11f231bce3231b26,0xd3ea62cb3e94f233511f,0x6211f233989f233e1d2e,0x44632b61462eb614a2cb,0xab30581ca2c581abaeb8,0x330f83462eb82a32cb84,0x72564ca2c564a330d83a,0x216342acb6542aa96397,0x96442b256442b2d63513,0x76c62c976a32cb7942b2],#[0xc32acb788eb2d76b92e9,0xa330d68c62c968a32c97,0x32cb7d42b23674632366,0x2eb1328b0b120ef2374a,0x553d0b2154d0b21b136,0xd53a630d53ce2c953a63,0x56263055611f215411f2,0x91f215691f295626309,0xa330b934632190462c99,0x330000363215f91f235a,0xdd005a8022000c000,0x3a6019600b900504022,0xac405120267011c80830,0x980d2c063802f5016a80,0x21c0103407be03ad01b,0x55e0295813b00962047c,0x3e06560313817840b3a0,0xe8c0718037881b280d,0x20380fc607c103c501db,0x8a823541152086704180,0x4f9026e81308094704,0xb24057802aa014e60a3,0x82c0beb05d982dcc16a0,0xd819780c910631831041,0x378c1b4a0d67069a833,0x77d03af81d100e560708,0xfd07ea03ec01ebc0f2c0,0x610bd08480418c20600f,0x2396119f08b7844a021d,0xc142594129c092f84840,0x184ecc270a134d099284,0xa4f051b0288e141b09f],#[0x4c60a5f052d8295c14a6,0xdc14e60a6f05358299c1,0x82a1c15060a7f053d829,0x54d82a5c15260a8f0545,0xaf055582a9c15460a9f0,0x60abf055d82adc15660a,0x15a60acf056582b1c158,0xb9c15c60adf056d82b5c,0xd82bdc15e60aef057582,0x58582c1c16060aff057,0xb1f058d82c5c16260b0f,0x660b2f059582c9c16460,0xc16860b3f059d82cdc16,0x2d5c16a60b4f05a582d1,0xb582d9c16c60b5f05ad8,0xf05bd82ddc16e60b6f05,0xb8f05c582e1c17060b7,0x7460b9f05cd82e5c1726,0xdc17660baf05d582e9c1,0x82f1c17860bbf05dd82e,0x5ed82f5c17a60bcf05e5,0xef05f582f9c17c60bdf0,0x60bff05fd82fdc17e60b,0x18260c0f06058301c180,0x9c18460c1f060d8305c,0xd830dc18660c2f061583,0x6258311c18860c3f061,0xc5f062d8315c18a60c4f,0xe60c6f06358319c18c60,0xc19060c7f063d831dc18,0x325c19260c8f06458321,0x558329c19460c9f064d8],#[0xf065d832dc19660caf06,0xccf06658331c19860cb,0x9c60cdf066d8335c19a6,0xdc19e60cef06758339c1,0x8341c1a060cff067d833,0x68d8345c1a260d0f0685,0x2f06958349c1a460d1f0,0x60d3f069d834dc1a660d,0x1aa60d4f06a58351c1a8,0x59c1ac60d5f06ad8355c,0xd835dc1ae60d6f06b583,0x6c58361c1b060d7f06b,0xd9f06cd8365c1b260d8f,0x660daf06d58369c1b460,0xc1b860dbf06dd836dc1b,0x375c1ba60dcf06e58371,0xf58379c1bc60ddf06ed8,0xf06fd837dc1be60def06,0xe0f07058381c1c060df,0xc460e1f070d8385c1c26,0xdc1c660e2f07158389c1,0x8391c1c860e3f071d838,0x72d8395c1ca60e4f0725,0x6f07358399c1cc60e5f0,0x60e7f073d839dc1ce60e,0x1d260e8f074583a1c1d0,0xa9c1d460e9f074d83a5c,0xd83adc1d660eaf075583,0x76583b1c1d860ebf075,0xedf076d83b5c1da60ecf,0xe60eef077583b9c1dc60,0xc1e060eff077d83bdc1d],#[0x3c5c1e260f0f078583c1,0x9583c9c1e460f1f078d8,0xf079d83cdc1e660f2f07,0xf4f07a583d1c1e860f3,0xec60f5f07ad83d5c1ea6,0xdc1ee60f6f07b583d9c1,0x83e1c1f060f7f07bd83d,0x7cd83e5c1f260f8f07c5,0xaf07d583e9c1f460f9f0,0x60fbf07dd83edc1f660f,0x1fa60fcf07e583f1c1f8,0xf9c1fc60fdf07ed83f5c,0xd83fdc1fe60fef07f583,0x8058401c20060fff07f,0x1f080d8405c2026100f,0x66102f08158409c20461,0xc2086103f081d840dc20,0x415c20a6104f08258411,0x358419c20c6105f082d8,0xf083d841dc20e6106f08,0x108f08458421c2106107,0x146109f084d8425c2126,0xdc216610af08558429c2,0x8431c218610bf085d842,0x86d8435c21a610cf0865,0xef08758439c21c610df0,0x610ff087d843dc21e610,0x2226110f08858441c220,0x49c2246111f088d8445c,0xd844dc2266112f089584,0x8a58451c2286113f089,0x15f08ad8455c22a6114f],#[0xe6116f08b58459c22c61,0xc2306117f08bd845dc22,0x465c2326118f08c58461,0xd58469c2346119f08cd8,0xf08dd846dc236611af08,0x11cf08e58471c238611b,0x3c611df08ed8475c23a6,0xdc23e611ef08f58479c2,0x8481c240611ff08fd847,0x90d8485c2426120f0905,0x2f09158489c2446121f0,0x6123f091d848dc246612,0x24a6124f09258491c248,0x99c24c6125f092d8495c,0xd849dc24e6126f093584,0x94584a1c2506127f093,0x29f094d84a5c2526128f,0x6612af095584a9c25461,0xc258612bf095d84adc25,0x4b5c25a612cf096584b1,0x7584b9c25c612df096d8,0xf097d84bdc25e612ef09,0x130f098584c1c260612f,0x646131f098d84c5c2626,0xdc2666132f099584c9c2,0x84d1c2686133f099d84c,0x9ad84d5c26a6134f09a5,0x6f09b584d9c26c6135f0,0x6137f09bd84ddc26e613,0x2726138f09c584e1c270,0xe9c2746139f09cd84e5c,0xd84edc276613af09d584],#[0x9e584f1c278613bf09d,0x3df09ed84f5c27a613cf,0xe613ef09f584f9c27c61,0xc280613ff09fd84fdc27,0x505c2826140f0a058501,0x158509c2846141f0a0d8,0xf0a1d850dc2866142f0a,0x144f0a258511c2886143,0x8c6145f0a2d8515c28a6,0x30296b14a18a44451cc2,0x4548e2a1b14fd8a71453,0xabe455a22ab4154c0a9d,0xe80aec057062b4a158d8,0x516248b04057e82be215,0x2cfc16740b2f4591c2c6,0xb662d9216af8b4f05a3a,0x7c5c882e2416fc0b7845,0xbc5c5dc42eb517418b9,0x7f18bee85f202f6817a0,0xb418408c128604230031,0x314918948c43861c230,0x644c31fa18e30c69062f,0xb70656e329219358c940,0xd0cddc6692332919808c,0x1a1f0d05c67d033c119c,0x4f41a640d2a4690c345c,0x6435901ab68d52c6a483,0x6c9436231afe0d7446b,0xdbf46db036b51b4b0d9c,0xeb8decc6f0837601b910,0x41c320e0f4702e37f71b,0x39071c730e3207150388],#[0x356398c1cb90e53c7254,0xa874863a141cfa0e7407,0xebbc75943aa91d450e9,0xdec0eee0770c3b411d88,0x8c1e338f124785a3bfc1,0x3d5a1e990f40c79a03c,0x7c2e3df31ee48f6a47b1,0xb007d363e7f1f348f8d4,0xa8fd107e483f001f700f,0x1ffd8ff287f543f891fb,0xd520571020480a6402a,0x9641a120bd104fc821a4,0x8466421e2104107bc83,0xb7485644295213c1095,0xd010e1486a6432c21809,0xc22261107487ee43cb21,0x453b22829130c8946447,0xc82460922f4116d88adc,0xb08d8c46a32340919908,0x91e788ed2473e238a11b,0x44292168905447f523e9,0x7224a81242c91d648ba2,0xe4a3725009270c933e49,0x96944afb256112a3494a,0x124984a4bf225dd92e04,0x19341499b44caa263f93,0x26de935e89ab64d42269,0xe692720938409bfe4dcd,0x884f22277913b209d464,0x9f804fa627c593dac9e,0x4240a0da5043280093f8,0x8d143fca1c850c928561],#[0xb28e914684a2d2513528,0x52a2293d1493ca45251f,0x6f45346299014be4a5a4,0xc8a82e53ea29de94e88a,0x152c8a92454742a2a150,0xabb15584aa6454ff2a71,0x402b1595800abae559a2,0xa56cc2b5915a54acd256,0xaeb057392b9495c3cadd,0xf54af7257a92bc615de4,0x796228b09e58112bf915,0x2cb6964d4b1f858d72c5,0xa9d2d3516874b398599a,0x2c5b612d9616bd8b5905,0x4b8225bed2deb96ee0b7,0x73b8b9885c952e2e970b,0xe117650bacc5d372e891,0x12f2117890bc045de22e,0x5f152f7717b10bd385e7,0xf4e5f862fb517d38be56,0xc4c0205ff42fec17f08b,0x18354c13a60773027180,0xbc18574c278611a3079,0x6d31119880cc38261933,0xe6306316d18ad4c52862,0xc84063fc31db18e08c68,0x3f8c9866494323b99100,0xc196d4cb2a654c328d19,0x336599a18cc8c660932e,0x7d233cf99de4ce8e6706,0xa0689934301a0c0d0006,0x8d3066965349d1a43cd1],#[0xa8dcd41869e634e09a68,0x831ab68d56e6a97352e1,0x835d69ae40d6b26b2a35,0x6c81362b1b0bcd8186bd,0xa486d0936711b308d936,0x90db726d8936b59b518d,0x9b968dc766e1f37009b7,0x78e9bbecddc26eb43749,0xfc37f01bedcdf266f4c3,0xc708938339c120e0466f,0xe32a715c388f1c364e15,0x96ce45671fc38e51c6b4,0x91cbc0e58e72a939449c,0x39ef9cea0e6ec733c398,0x4d03a4c9d1ace88c7416,0x4675763aa61d478e9f67,0x8eca8762f3afd1d75ceb,0xdcc0edde76c83b501d9e,0xe61de90ef0077653ba49,0x63c321e100f02e77f33b,0x791b3c7e1e378f178789,0x3d679b53ccb9e5b0f282,0x18f4d87a4f3d1b9e860f,0x9ed00f62e7ad73d589ea,0xdf91ef68f76e7b873db3,0xea3e621f240f8c87c383,0xc7d8e3eb01f4c8fa227c,0xfce27e543f0b9f7b4fb7,0xdb0fe567f043f639fa70,0xd2011500347fd83fd71f,0x4091a03d50178808e403,0x1e140dba068d02dc8148],#[0x6c829441222087903fe8,0xd06ea834b418420b6105,0x1109081883e241e0a0e6,0x89213cd09b28493423a2,0xd42bfa15ad0aaa853242,0x86a14342a18d90bfc85b,0xec2874e439121bf10d78,0x610fd287c643cd21e090,0x223e91170887d442ca20,0x4f2226ad13168960448f,0xdb4556229ad14848a044,0xa8b9645afa2cdd16008a,0x19388c5e462023031177,0x5c51aa48d364674a32fd,0xf237e51bbc8dbd46c4a3,0x475ca3a551ce08e3a470,0xfa647bca3d291e408ef6,0xa90664821240311fca8,0x122ae912a4879242c921,0x48a5240291c648cda45f,0x75a4afd2528926849242,0xb49cda4dbd268a932349,0x946d4a1ca506127ee93c,0xa6495064a76252f92926,0xb52b8495974abba55612,0xa5a792cf2964d4b0e257,0xba425c812e0496df4b5d,0xee4be025e892efc97664,0xa989e4c3d26129304097,0x32f8996a4c9d2643d31a,0x87933fa99ee4ce426689,0xa26b1d35409a694d21a6],#[0x4deda6ead36f69b4a4d8,0xced4e56a719d38669bfd,0x709d884eb5a74e93a2a9,0xd3ce49e494f0ea77b13b,0x7d093e2a9eed4f64a7a6,0xf127f2d3f5c9f934fb72,0x1503b2818940509ff84f,0xa1585094283d541a8a0a,0x462a1ff50eaa86ad42ec,0x454564a293513ba89714,0xa8dd546b2a33a518428b,0x2292904d47d4a3c851c8,0x1a527ba93354958a4755,0xaa5bf52c3295694a70a5,0x4d82a67e5321a98614bd,0xe094ed6a7385385a9be5,0x32a0d15004a7c453d0a9,0x54872a37d5176a88e543,0x9c254ccaa5e952a2a92d,0x22aa6b551f2a84d53cca,0x1564eab04556faaaed55,0xaef95734ab8155b7aad2,0x47ab1895876ac1755fba,0x6569dab44559c6acb956,0xade756e42b6b95b22ad6,0xd2cae6957272b8d95c16,0x95e52aeef57682bac95,0xabf8d5f7aaf8e57b42bd,0x83a2c1656092b02a5806,0x2e58862c3a96182b09e5,0xb1ca58d5ac63d62deb1,0x64e0b25159172c83563c],#[0xcb16624b2ce59582ca31,0x92d005676cb39059af2c,0x5a74ad2e1690cb45c5a1,0x5f05ade2d6016a92b517,0xecb6c55b462d9516c46b,0xd6f12b7645b9dadc496d,0xe1417054b8045beaadeb,0x992e41d71a0b8aa5c3d2,0x15d042e779733cb95e5c,0xbae15d562ea0174b0ba3,0x762bb885dab2ecb17616,0xf178e2bc4c5e012ef697,0x2f5ed7a88bd145e75af2,0xf2faf8fd7c18bde65ed5,0x3c5f882fb657d4ebe7c5,0xabff75fe2afe457ed2bf,0x81e4c0b56042b0145803,0x68982eec16060a230445,0x309a1845ec20960e930,0x61af30c9185f8c2e1615,0x42c61feb0f19875ec38d,0xe0c4d26259311d58894c,0x98b28c56962a0b147189,0x1acd8ce2c63a63023171,0xc631d918e62c70863703,0x2641e320418fc2c7b263,0xc91b647bb2309911cc86,0x3bec9b564c73257d928c,0x594b6ca34650b327e99,0xb2d19961ecad26554b2a,0x60a32fa59774cb9365bb,0xd8665c3321d98cecc406],#[0x4cd6566a4b34c99a1ecc,0x9c8ace0166ed336b99b1,0xcb59e24ced86758b39f5,0x933fb19f74cf8c67afb3,0x68553421da0c6d03c680,0x19b68b2b44c5a202d0d5,0xc8d23f690cb47c9a380d,0x1a63cd2ec695634a0da4,0x4feda79ed39c69ba34d2,0x63b5281a8fcd45e6a14b,0xc6aa4354c9aa10d4ec6a,0xd5f86aedb56e9ab2ad56,0xd78d68d6b2e358c1ac1e,0xf5aec4d7376b88b5ba5a,0x3607dafeed7cf6bd4b5d,0xc8736371b166d8816c2a,0xfc6ce3b6665b2e4d94b6,0xdab06d3cb6931b466d9,0xb756db7f6da336c49b5b,0x1a9b88edc136df836f2d,0x83748dba00dcce6e47b7,0x6ef1b770dbb3edd7b6ea,0xea66f393792dbc42de03,0x50df7f6fa037c3dbdcad,0x9c09ae0266ffeb7f51bf,0x845dc1e0e0c1704b381d,0x6b876dc360e17c70a13,0x87156b8a31c4b4e23471,0xe3b271b6b8ca9c5f6e2c,0x91ce46d721f3905dc7de,0x2dcad4e539727eb9315c,0xb98f9cc32e5f972dfb96],#[0x38a39b6dcd5ae6887331,0xfd73e939ecdcef2e7427,0xee8a8743e3a14dd042e7,0xd2dae94474893a3b9d18,0x905d434e9e774dbba649,0xc3abb1d582ea9075343a,0x75de3ae31d6c8eb33758,0xc95762c3b0cdd824ebe7,0xc6ed327687bb3b1d99ee,0x1dc0eede076db3b621da,0xbaf9dd24ee757724bb8b,0xdabbe15deb8ef2377773,0x878243c065dff6efd677,0xf11e787a3c351e14ef07,0x41cf1de78dbbc631e2aa,0xc9e574f29079323c8e9e,0x3cea1e6f6f34d7989bcb,0xa443d19de868f41079ea,0x547a99bd449e9bcf4b57,0x4f6087aeabd685eae0f5,0xedbaf6ae7b423d935ec5,0xf15ef36f7617b9a3dc21,0x6be205f09ef82c7c093d,0x7cbebe501f22af8e57c5,0xa527d163e839f3c2f9ae,0xf8fad17d5c3ea59f4e2f,0xdf716fb627d9d3ec89f5,0xf115f846fc057deebeec,0x74bf321f94afc817e323,0xb7ec03f569fa5efd0c7e,0xfe427f0b3f7adfb80fda,0xe0afee87f613fa59fcd6],#[0x7dff06ff617fa5bfc91f,0x4012e0048fff97fe63fe,0x6b402d6011700788037,0x6180a0c048a01fd00f48,0xb01dc80de40672030501,0x4d502408113c083a03f,0xc5205bf02c48153409f6,0x140e3a06e1034a8196c0,0x820b40fb207ad03bf81d,0x4a28248411da08bd044d,0xa3052682864139e09910,0x20b8105b182c6c15c20a,0x18c20c27060282f3c176,0x6cc1ad20d1706738327c,0xf83af41d160e3f06f483,0x7ed83e1c1ea20f17076,0x13d087a8431420fa1021,0x46125908ff846fc23161,0x427b21377099c84bc425,0x567c2a7614d70a358510,0xad85c042d3e164d0afb8,0x10c298603c2fbe17a50b,0x19c10cb7864d431f218a,0x5f21ad10d48869443416,0xd437a21ba50db486cd43,0x8749c39e61cc10e4e870,0xf598795c3c021dc10ec0,0xf50fd387dec3e461ee90,0xe215f1091882e4409e1f,0x44fe2255110e8874c435,0xdf446b2231f117688aec,0xd891ac484623ef11de88],#[0x12e7896344a7e250b125,0x6c313428994c4c2e25df,0xe627b513bd89c7c4dd62,0x4526628d714468a1144f,0xa8fc541e29cf14d18a5c,0x9e8ac1455ca2ab3153b8,0x3161a8afcc575a2b7b15,0x2d1f16758b32c59362c5,0xd1e2e3516fa8b6ac5ace,0xc45ef22f3b17838bb045,0x8c28460be302717f48be,0x8d88c5fc62863119186f,0xd519478c95c645e31f91,0x2342119d98cd94661e32,0x6b9a35731a958d32468d,0xd5c6de636b51b2d8d82c,0xb8e22470b238051bdd8d,0x1d128e72472f639231c6,0xc2d1ddf8ed3c75da3a7b,0xfa3d251e708f2a478d63,0x63c023e671f118f72c7a,0xe1700585d05608137830,0xb810197080e40d68505e,0x4022b08093c082b434e0,0x9983427c0e01e03e0501,0xe0285342027f05e104f0,0x810803583a05c0cc5119,0x3c4b285007a060a18c13,0xc0c8a0360f50cb007060,0x83e2282288510e91903e,0xa12ee070421e61542a42,0x1e85b41b8c05a61e4b60],#[0x39c321f239e160c8464,0x88b60ce080cc8fb0c070,0x502c60e62c0be1607846,0x1e81c614cb58890f05a0,0x415c148f500e0d602864,0x6a3302a2650ec0b4308b,0x210b82ac35090c148b20,0x9b8052ce1d45002d006,0xa846060ecc1893244612,0x362c86c02d08c0561945,0x388be4220e85707dc408,0xc200088790561c4610b4,0xd00282a2d41097d8a715,0x250b24d2218292413781,0x7a0e88a81e88b190018,0x84c4408be13427073460,0x6606829070860804e810,0x19017070001201a83222,0x40e0b03a0fc430850806,0x450d44e17c9382b405,0x1014a0e0dc8604240883,0x160b912180074c684ab0,0xc302484480a0d08da277,0x1c988ec0643241e0104b,0x2c0721e833c058be1426,0x93a3585185a078200a50,0x82363480687b2cc3d899,0x829240c0cc0867d05c2c,0x2809a150221040a81612,0x93c9c611c2e01293d17a,0xc04b270b60b912430208,0xe40d02d1584563208d08],#[0x338724ac8e33c8130ce1,0x11f07a9722a204535153,0x287e1863109f4b69372c,0x329f2580c11549b85466,0x956294514da9e93e8060,0x45187e4c901511470422,0xb694282a6c36c35c6d0d,0xcae858fc28d68933f1f2,0x450a8fe0d780286c41eb,0x727f981af0050e8d5fa0,0x41ce0050f0ff1c920028,0x4ae009a75d14f0a159fd,0x5fcc02520144065fffe8,0xae000ceefae605228604,0x35dd10beede604277af0,0x67d917470f0efc1094f1,0xff24104086af0ae000cc,0x2014153bb57e811429b,0x405e8ac4601d4df7f356,0x6ff0c508cf51e94d3623,0x87f61fa3a1845100e8aa,0x3500285108fff72a580e,0xfdd8d10901428947ff80,0x151a217fc6735ac224c3,0x21c3085120f7ffab451,0xa004c30c105520fffdb8,0x3a2cbdbaf16d333d1fd6,0xa43437b0fd1c06409063,0x20d0a2cd6751a155f514,0x4290ed6fa900ea557670,0xc051221ec8a3a333f383,0x162417ca148cb2f76589],#[0x284692f942919778e35a,0x9907084824567b7e2d05,0x8d58ff8ec39d0d2feda,0x9240050e5ffec3c2cc45,0xe7c7f062228d34433cbf,0x1490a1f9d9ffbb2bce87,0xa2b51946612271ffc5a1,0x97fff1eda04aa846a17f,0x31ce8a17fa75084c243,0x30d950c4ba7ff831004a,0xb80848bf9d0280a51f1e,0x1fd3816002b805433fb,0xc2a3433aefc5a671c044,0x9e5095fd74ae999859ba,0x54b9f2e19c81338b35,0x5ffa282e48c6885be035,0xd0faffd1412a1222227,0x764191a44413fe550c0,0x13fffb2950600d102fff,0x50445846bda2234bc225,0x7fab106d1a1f3fffdb10,0x5251acdffeca32b82872,0xf3982287127ba6392353,0xe31a317fce50acc2495f,0xdf84667affe8b9060181,0x9014c558c4370671b11,0x13f168254a0873217b7e,0xf2845a086e7f5422d043,0xa48244b71ff4b004cfaf,0x9374454246b671fdc528,0x3b57f06289234671ffbf,0x4d22c0135b17e1f6123],#[0x78204a749428c8ffdfc3,0xfde64780142c42be2a7f,0x8ce8a23bf96d49546777,0x170a667e5508ef97f7d1,0x2ffbe014c80911af573d,0xd583524357de39666ccf,0x52dbff7ab3680143ebf0,0xa6955cc9cc2e9e1647c1,0xdbf284232,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc47bb1820a971fa20a10,0xf905c1429189f704e054,0xa9a4c86b7ea88526432b,0x421bf77d4ede0d0e2fe4,0x152cdea6c0c352d3c566,0x283a7fc08508a73bec04,0x7f3700549e7502a327e8,0xf8d478815283c5885082,0x1743563e3b8ebcd21a5c,0x87a428ba5e146d2317b4,0x72c100688a7e42831e90,0xe691050a3fc24882fd5a,0x34910b6f9fa37322199f,0x46ddf022655e24376cff,0x46c43e989802a473e825,0x523383e910a105b3eab9,0x1e002a59b84885ff8135,0x34cf5a44ce05b2655bf1,0x6fc4c9a04143cf1f9732,0xfc4650a1d18fb381050d,0xb018517f1a800c2eb60b,0x3828517f1a8da8517fd8,0xad22c3fca5e0a149ff08],#[0xf549b28cf17f31228c5f,0xb054dcf9b8215811221b,0xb6f7623128867bf8c73d,0x48abf989130fe6e02054,0x8867bfe1582054a317eb,0xa1e77779c46f73716a0,0x1f3c4c20a195ffb38d02,0x42ef1e244e7fa7820a14,0x4524ffdc3511a9fb00a4,0x204cdde1f2c4656bb394,0xc850d6e480508dfe94,0xfeb0a177073bd237bf92,0x128da86a7e240290bee6,0xb349915fa102b42b3fd3,0xe8daf11acf1aed82a54f,0x33e3c8482a5831eb48b3,0xf232428560fefcf14967,0x4473f641084fcc00423b,0x1850c9cfd8993aab802a,0x42a7f504206657279f,0xc8285c542f70217593c8,0x4e3a70ca97ec028f5a5d,0x2a81ff40ca57370aaa44,0x40065d3f024eb210002a,0xa132f357f5c882866ffb,0xbf4a0426bf64142369f1,0xf66bb9810adf9ab10336,0x2846fe5a60654ff40064,0x73faa1946f980a3a5dc8,0x2d5ee4a2293dddef0425,0x58f484c79520eb1fa003,0x2fd300065dbde8c05232],#[0x3e2e0144086671e5484,0x21014775210ac1facab3,0x1b55214df948108ed775,0x91ca3c08737c4ea42734,0xdff4f4721192801124fe,0x273884617c734260021c,0xfd8a678a86a20f6c0a49,0x5269cdc9472a7c5072f,0xb7cdc84244408a53f110,0x55430991c823c0aa6964,0x2960fd6312e915fec53b,0x8cea2b25c3fbd6f0430,0x2042a7f856c00ccbb2f1,0xd000014d57b2151b3fa9,0x524747832698544179df,0x962841bf4c2a33be3000,0x812fcaa3db5300aa4a6a,0xcbb0a87349a88f60aa6,0x295aa190fc02a8d3eec0,0x1995fec56ae54363ff86,0xadfec9a69033d7aafd14,0xf3e2700b102f8116e054,0x14c2fdfff8a52890f,0xffc5cd00820442df7613,0xff667810bafc32292175,0xf431a59a2798dad25273,0xb8464fad8032c1e90e0c,0x66ea3146e646ea39f35d,0xb4788001490c48ffd221,0x6bf0c8a4854be6156514,0x5759c5076ffc7d380043,0x5fd6200052c1f610d80a],#[0xf4d4ea610d77a2571d24,0xa9628557fb14e2418617,0x16004344d67a0032ebd8,0x9c9fa3539d0fae8fb7f6,0x21a2f593c7c844f43d1,0x3d373a1e1ff305d60030,0x2161d10dd249d65c4d00,0xe4a31797c2508af2eedb,0x977db9c24bfbd2509152,0x549f92cc8587c80c0a16,0xe1a1ec399eae1dc106a5,0x35d92abfcf1baa0ccd31,0x4cd0aece08424fcf7306,0xcb8cc231a1cbe5c34e0d,0xd0430cd06f9546d421a5,0xe1b7f86184e199dbfc30,0x8f86ccb68063455482b2,0x6a17d421b0c3473a4a7f,0xe1c6834463c06e5c2237,0xcfdcec6232497cff0a63,0x8e5e5828843f81f78422,0x46a22a3e29354c08d48f,0x42152042371b017d86d9,0x9fda4003a1e3f964df0c,0x442ffe31b431804962fc,0x58581429a00fb8dc3528,0x1118d11172c1a148f796,0x99fde48308343589e9d1,0xde03fe3399bbfe983061,0x8058faa5e951a5e11d47,0xaa10a012261784961c7,0x5f4ac20d0e1e45affead],#[0xadfff644002670e91dbe,0xdc010e18d132fe6210d0,0xf9086852be208352585e,0x93a91be3f8b60099d5fd,0xfb71320b936f8e858b26,0x6a6645f499157124a2f7,0x1ce0005124fd0b284eff,0xcb4bbfb03842e3ffdb86,0xfe128393f4f446f4daa2,0xc334183c92830792507e,0xfd1bbb70190e95f99921,0x6d90e8f8f7a911319104,0x43719f3cdb21796c63de,0x31b928c190be3705bee7,0xd1eca83b2161cb7dc064,0xfae2632143fad38cb319,0xdfa1ac6858bef775948a,0xe4649211fabd2424121f,0xe7a720390d4ea860e779,0x2ce611367feaa02919e5,0x164d9824a472e59cb8a,0xf0853599e3eb21997b86,0x6e6c013427eb5992bf0,0x39a481ff84028319fbff,0x834233051a47952b691e,0xa46669717dc4f42d7fff,0xff64704478e69217ff20,0xf1fa8d075f87b654cccb,0xc6cc8cefb8108426aca0,0x7813109168459e692af8,0x2cc34621e47efda06844,0xede0ed0766cad461e452],#[0xeffdd22e019104f8b349,0xa179fbff748b806446bf,0x34287f9aeceb3430e40b,0xcc1fee91700c8886dc90,0x1c234b2e2fdf8259190f,0x8c82a40cbc432986f9d0,0x172ffd9d5b84d811680e,0xa1e1feefab0bb022d01d,0x2e7de0214bef982ae541,0xfdb0421f9f42bd3c686c,0x9ff2fee20a46887e2b5,0x7f2232113fedf5c4148d,0x4966cabe4a18be38e848,0xdfe8a508cf970a5469e7,0x190d2fedf94e1309119e,0x920e66840ca547f9b88c,0x2345059bc32150f73a32,0x979083c6421f34ec9294,0x1566e6125e420f19087,0x10842fc400596d968ca1,0x302cc5fe19566059e5c8,0x1c660f81430c662ff0fb,0xe5041f6d29199a3ff5d8,0xa0c5f0ca0f0c58c3521b,0xb1f0341bbe451a115e8c,0x457a32839b4d2a337ca0,0xb4311e4e02146ef904e8,0xc588d02f254cf428ff1a,0x859a4d68d465ffe1e1d,0xac36848a874b597bd3a8,0xe752c1c5945678a5072f,0xf7e1800919d1495ac0e0],#[0x402467458dd55ba343f7,0xc3e609ccc4fedeb983c,0xa1930860bacc986a5d65,0x7fe181433a241c1f6004,0xe84fabd5a9047446bf39,0x1c4122c1fe7904a17a1,0x44fefec46597df58202c,0xbbb6024e98488764f848,0xd9ff382682a5c8f79b27,0x8d468f16f5ac00a32b44,0x8ce8b1aad8c8853a9be,0x961797472f932f0db488,0xcba958e5987c26a83749,0x9ad6eb64cb82dd2d504,0x20233a28bfc7d61289a0,0x352e84294499de6ff6d2,0x7ed97c22a35811ac5fe2,0xf9ca50a2f9bae60a7438,0x15a1abe106f700134abd,0x797a7b519848717c5dad,0x38344146997b5b22a848,0x807e257d498290e5fe3e,0x2f4331f8947af0810ea,0xe6c8efabb4052195fe41,0xf7d8fc89a4e6dcd1b6cd,0x863cd96bf8a176349748,0x88023ac05a3f3bb04814,0xd5e5ba353e447675208e,0x5f04120521868c65ba38,0xfd05330f1262af7cc8a5,0x677458ff040599cccd43,0x3305a87d7dae16bd0daa],#[0xc2428d4cada47066fe4,0x85c88447d5db521a5fc4,0x75755311a5fc40c242ef,0xad46ad3ccc8afda004a1,0xb989a2efc56e111f66be,0x253a50bcffdda16090c3,0x18e39b68b6f8668317fe,0x42412206ededa341a5d5,0xcc4898595d235bfe003a,0xdd0232cbe65063e3c615,0x53808b3793b0df010d5e,0xd51cef5223f3794cb01d,0x850fad664dbf6598852e,0x66587568c842d2937ec6,0x981df49ad1ea04246dc8,0xd63811257a689d42964c,0xe261be0222d83a05ffe0,0x37ecda74d700a777cde0,0xdac029a83e12c90bd985,0x430bc36c98b086e3510f,0x7a9ada28529b4fb62c98,0xa528581a94712c720cbe,0xc0297deae3484bbd5710,0xfcd3a778480a7fbe229,0xbc64087aba5b67785299,0x9e093f7bb9043d3cdddb,0x379902935dbe6cd8d21a,0x837011077fd705aa52ec,0x526bc3c751486913478b,0x8503bfe6b452182d9e19,0xc3ece7835a19dff09e40,0xf273c523aefc5a66d043],#[0x88c525b824f0680921ca,0x8bb4a90bf214046693f6,0xb45468534df4f80854bc,0x4679ecd4e94a0a0452b8,0x626ef306e423f073c594,0x4767fd041085ee1bad66,0x142cd640e8522f1ddc8e,0x808713bdfaca4e64f8ad,0x65c7713e02151cfed40b,0xf501a36ced6d903c38d6,0xeba574cccdff926332c9,0xc1fe2320b375854686af,0xb0d252d877f0455e014f,0x1ace4e17aa085c32bf52,0x93081a941c1083a39435,0x28dca45039377010b67a,0x597abdd0042ebad144fb,0xa435ae30261cb985ca48,0x58eb38828330bfd0d68b,0x78810e6f53012822a381,0xc03280a533ec03280a5f,0x28567b71f9d08e87d3e,0x785090a23a00b101ee9b,0x70267cf970af4099c5f7,0x199fe19940061b3f9485,0x7e40908cecff4c4a36a,0x326467d3a1204600144d,0x181a8553e4281414bdac,0x17f151417246344fbffa,0xae82b20335d38b758685,0xc54504a848888a8ffe32,0x638028aa7e3fe752145f],#[0x6ffcd001a171afcfa1c2,0x9cd94911ffc80421110f,0xe8201088874fe1c81121,0x9894e3ffac60890dafff,0x801a1d3f66806668c3d7,0xf8502239b2927bff0080,0x2067edd22c7874cc83f9,0xf2246200428cdb7f2049,0x19197731e24607f5fe0e,0x28ae787202806875f5e5,0x8023373fd5a0892f000,0x4ec62407e7420ccddffd,0xee214ea9523ed7ccb352,0x1a1e3fff84c50e8685b,0x1360cf75e4537f11a50,0xc3a8d079f4ffa4546a00,0xd6195bc4491953b08c32,0x803441b29237c60a1eda,0x1432000d508fff023e48,0x3fd7a4002819a74f0be1,0x5fe7d3e38953990809b7,0x488ae48ac84edb307,0x43f3a1066687ffff20c8,0x1a28d1cc8caff05b6229,0x2fbeea93a9738618f677,0x7bba84ad10ce7c692691,0x3494f26b9e8a7e58889e,0xffc3b72c8008d30767c7,0x690bfff2db109c5666a8,0xfcb0e0a19339aa2f7146,0x176cb2d3fe51854862ff,0x146547fd8ec019e14461],#[0xc9ff4300a1490489ef40,0x746c85333517e2030119,0x52085fdda1ba86eff2ff,0xffe69660c424a9337941,0x8baae0125cee28047622,0x8a4da5e9cc2519a63fa,0xa8026a8e7ffe930f9039,0x3211a66363e45ef882ca,0x2c7bc23e65effffd80b2,0x81a212004d8b7f0a01c5,0x445977ec79133ffff1c5,0xfebd21892d122b8881e0,0x8cd265c28d7fb1888ad9,0x3a5021c5557116bf18aa,0x8548974b000a417d7f37,0x1cdfb8ff1c98111d71a2,0xc591688a5a9ae5fc2295,0x47a214b0627e1400296e,0xb60b1e66630e02a20daf,0xf79b208087f78736050a,0x8f800210bf4c401951ff,0x82c2f12271869c05170d,0xf320d6d46029d1f5f9a0,0x867a4429b69bb35a21b0,0x9f8bc04042975fa86467,0xa350bed1e123500b0226,0xe25d465149d2909ed1d9,0xd9b8c08557d1c89c486c,0x8c204427fc6c9b03373f,0xb10b9e7d5032a3f81302,0x4323e0472684353b7d39,0x5feb47835293eed1c645],#[0xd4ceddcb084e66f93420,0xdbc0888d0b07e351a010,0xc6cf15021968dfa84a52,0x1e9bf8b142969f898367,0x84259ac67a3ebac405e9,0x20198de057e8042dbdd7,0x87c6ea3f02010cdfa75c,0x57f760150daea93a8100,0x520f3615157d7a1408ee,0x2628d3fb16532e5e504c,0xcfa4c26afe1648066fbc,0x910982f88aa290782112,0xb02a1cdc5db0d00863fd,0x19fdfb8b00a8657ec9c1,0x1e9d3cdb2122bf87bc20,0x42014f6fff11080402,0x19e9f33a0804305f339c,0x104685a6c8f3ffc99090,0x93e06c4e7c8201217dfc,0xd2011b5f020d085c0e17,0xcf000d057958c15265ff,0x462be42c00854fef2cb,0x4088c60881ea9c9213a0,0x9e6c604021e9e2930e29,0xb84033f3fdecb2804340,0x2010fcd1e054227fb66,0xb93c9d408043cbe04f07,0x12cfff18547208400455,0xb3008ecffac8d8364101,0x809019f3f48c00cdbfe6,0x50100861eec2a2b7ff97,0x6827e0ee008808777fe2],#[0x7a8413814a5f1db48080,0xf207d0216d0fcb9c10b3,0x86131480f176ea804343,0xdac900ce52e9edc0cd66,0x40214dfd9404021abe3,0xd161c3028d0efc41ebe2,0x3e38fab02493b2e8b0e5,0xdca09dfb70c40a0c288c,0xae6e0009467e09440294,0x7a10010e4e1d4684de23,0xc26a4ff80738067e7cd0,0x3399ff1862041298a73c,0x4763e3a480cfd8f14e20,0xfd8bd00cddfe96286403,0x783243e30418fb80454f,0x4193900d25a65c190b49,0xd939ecd5c890a87afd39,0x4f99b0719d60c818343,0xc7d4684e7b356a4408d1,0x7e348044ab469cdb216d,0x10ec9edc699717753bb,0xcafa70a8497ff70a0d2,0xa8fec4da352325fae201,0xe040219397c8065d3e14,0x2f1fd1d383002a9e1c47,0x33f502010cb7c02b9005,0x6e010053a5d53300aa5e,0xffd8ed482202242fdc36,0x6466ffc783822010faa3,0x88087e66f2fc234353,0xb5fc099933f53193ff8a,0xdfab650100880fe0408c],#[0xa087e7b3572622a1e5ff,0x1a2f3eb652979f16c845,0x305ec6ca520bd1aaa902,0xcbcc5282115fc58d5204,0x210ab1886e0cf1e0f6e0,0x14194dff58b690b2d168,0x2042891faaa90218a1fd,0x42909b21fa1a1b1ffa15,0xd269a3cac0d4a6c3b202,0x1c653b3be98d269a3e98,0x518c085a62c5242369b6,0x61d0196f7684b6991ebf,0xc257af5f0f34501a7be,0x65252b679769b2aa9c4,0x46243128fa3a0361b6d5,0xa043538938a050d4e22f,0x3307fe49140cd8ffc2a4,0x6dfe05e10199bfd3b002,0x27f1664755e20e1f0370,0x3f4a7c303349f3354526,0xf5a814b97c011738618f,0x48fe54590bb145916fd5,0x7f4240c12405397f4516,0x185a710604615bca2c7b,0xa1ffc8a81019e983f08,0x71ff1a620334be4500d,0x88a6852e6152121f8a9,0x7dc118bfcb9a60669d6b,0x2ec81949f93d6810b3f7,0x38609202a1b97250654f,0x898d1a3362c4269fe011,0x3a086924e8b0728c61f5],#[0x3b45945f0c8108aeb8b3,0x854f77164364f710955f,0x61022421f5945c7b7644,0x87a69e20f9e3edfff124,0xcda075021f9ecd549854,0xe050822f5bb22608526e,0xd5a8a810f4c1c1103d53,0x37a066f6aec89821a9e6,0xa6f75f40e04021db978,0xbfa0702010dd7f19ec20,0xa220110c7ce2a0940536,0xf768441a9c088e7368ec,0x1008717f976511008767,0x2f8eda40403413f47670,0x100874bfb59380200a7,0xcf22a947014cafffa767,0x33375d1c2019edf2320f,0xcc1dbbe20668e9d27f0,0xce5f95428336690b62,0x1983b6342066a8fd72e7,0x19c7f303f10472fc6060,0x74fc6060198bfce50ae0,0xc6dc03363febc1d81008,0x802a0efec74a0294bdb,0x30a28202a20fc8d050a1,0x668fbf686019a2fc8d8,0x660f416f40cd1ffd1ca,0x882770314a0868f07917,0xfc992810bab3a49b0b40,0x3cf87a606626ef6e4263,0x7a6067abe85a4860299,0xeea2d993ae4e8a0cedd7],#[0xffdfdc1002c62222a3f0,0x4183111162c986858517,0xd3220e0967f7932fcc10,0x79f2c6672f4c3985b367,0x436346efee842187ee18,0xd6007962226dfe6c81c1,0x39848717358c8e155897,0xe0941fbeb8442639bee1,0x17142345bdde6c148547,0x747ff57d293090edff95,0xfd823128862fdb0b9426,0x71a9b08d3df84c664cd8,0xa42cbddca893090e18f8,0xd077c5e882910fcf8a80,0xda0150cfe7a027f4c114,0x997e395c24089139feb,0xd3faa624e114cecbcca1,0x82aaa4360786317d8883,0xf0a223fe082a979a24ef,0x547fc1196cb8ece16091,0x1638287efe18ea22c013,0xfc9042922c489e7fe8f0,0x97e440b585482aec88ff,0x7411a17ffe259464424b,0xcf09253cd44d09ded80c,0x21c8cf17248ce8a6229c,0xc223a1bbab9465eff856,0x31fe41a1ac008512aff2,0x308a5dd546d175b819a1,0x45acd8e01335855363cf,0xea6f55e40c0d0d1f876,0x5e6a8904122569dc9914],#[0xa9c3ff0554d80269a784,0x3aa7011527142f64103,0x5a72f89c60430b67fb16,0xe60757dc88527f244e88,0xff4b204797fbb5672810,0x56ce5021a5f12940851a,0x54c8687ae282ee10d2ff,0x3421add1bcd88547c08e,0xa5fee13286821d1f0239,0xe7aa25201f8bc26ae029,0x31cc170aaf50a2aa5289,0x49bf502a179f67832414,0xa0e9e2c41d7fe54100cd,0xfbb112a44bd34a8e9f51,0xa3e70d90a417070542d1,0x648e812262bfdb414cd0,0x5db0e2040654463e644d,0x3a017c1859be0b9711a0,0xfe585d8019c2f919c952,0xebd8ba6657e9030010d9,0xa0d32422be69800850f8,0x41ce48457fe96d042431,0xf465245f8b181ac91a77,0x14cb8c9f70726f68b8f4,0x802a950fe802a93bd3ae,0x1151297fe802a92cfe4e,0x81a9150feeafff90c05b,0xb0f476e1a9150eaffddb,0x383280200a707e1a9150,0x8951c0154c9e82993cf0,0xd64a676fd30784033d5f,0xa4e7b3572622a1d3cfe8],#[0x66cf4f5d1419a6f5a94a,0xa4291dcb2a525672d82f,0x294b973747122971a731,0xc57f19709014c27f901b,0xcd87810f76a62f956294,0x780a687aa1e042f3ff69,0x6cb54f5d1419a2f97bd0,0xc884effd33032a57ec1b,0x700089aff2d3303373b4,0xae5e2ea068f7d7f4a70e,0x3070c866bada511296bf,0x2280a6479b1f6c85d7a7,0x43257ff175033b5f2341,0xfd3a080014d8f175f720,0x502e71d19759aa26104f,0xa3c41936042a380183c8,0x78e0aaf528b14a533379,0xc7805e82a5e7926c085d,0x519b8f162106b3fca68d,0x6e7f3834209b1a2f3e30,0xfd19a00486378bc11068,0xd94c86d7daddbf7b0d8f,0x9b10b677c1b990b0db9f,0x9060edf057268434b965,0x836c0cb27f5cbf114b6f,0xbe111c2ebd31151c2c7f,0xc086f7f8ee501d043bbe,0x51fe2c018014cef8f08a,0xcd549854870fbf722833,0x429bf2a98e820892279e,0x14b4b3f6a02165c4a2f4,0xea3348ced5329f8daca0],#[0xe1b18bff0f68d3068713,0x9b48d0eacdfea1c68666,0xa7233f373a8517fe1ed,0x5efd3029804bc0b1c1a0,0x30de14ec7068029c0e19,0x23caadb442730fb55544,0x2043afd38d0465f67948,0xa157c67682373f4c5260,0x6d5a7b1e0c0544b150b8,0xbe8845a358f63c229a4d,0x18da5284fc280052c390,0x88032b47f8803295e6e5,0x5a05724217fd803217e9,0x42f98502a894a15f8132,0xdeefa932b2a1e9d7cc4e,0x734bb7c429cf484802a0,0x877f651ac23438d378ab,0x50252edf10a7365e200a,0x248577f6f284686a3c42,0x92179f0e24490b897f95,0x128c3b69b468cc0eccc8,0xd950d0f6784102182fcc,0x543111f586a8537bbeb8,0xfeb004584129ddf53616,0xcda662bfb1d0258aa66b,0xb57f10cb043531755fe,0xa9ade29aca85223b3f95,0x6aff9ca844bd6e21962,0xd29bef4b78d1687d7755,0x64520100a28ef1b0d09b,0xe58fd2a3a004d7627e54,0x2e3edf320d0100a273f6],#[0x9d31d3090332b97659c4,0x9f36c640cada78e98481,0x910810f14595ab88e22,0xff4bbb09108110affddb,0x6b8011b0d1f9041014d4,0x98234d6a5ff01581340d,0x90baf5489095b72a78ed,0xda32eb2b6de617d17480,0xa2c50cdf4952066ee5ed,0x17bbff94342043eb7700,0x6408eca9fe69661e84c5,0xd5b5edef401014e37ca9,0x4837ca96ef294cfa4251,0xab97649438d0f2617b09,0x3cb374a2a58e1ce11033,0x9484fbeb0429fc780279,0xfbb0070c68a99b1f28d1,0x30f84d09491f22d23466,0x3ab9797834361f292129,0x3e91a140fc2a811c3533,0x4412485b5bc706b0befe,0xc90d2ffd44c55b8697e,0x8253bcdc62a2a5d7a8b1,0x4585c1b877e542c3df9e,0x862ff8602b2067c43fc5,0x13febb2d8331bfaa5840,0x2888bf101dd22b26a5e1,0xa32585116cde4f15192c,0xfed684bad6a519bc9fa2,0x65a8b829944ff6b42289,0xa4d33a563252f0522952,0x290c4a6ad5e0c2156fc0],#[0x5f86455b078c45256db6,0xa63ccc8a06129e7114b3,0xee1890e2991f52a15321,0x9a445696fea883a5a24e,0xafa870c1852787d4a109,0x50ddc508560feda5394c,0x14d31007d195d5ca7293,0xa4fecc52da693fab7951,0x7d9624365866cae9aa64,0xe2de6766530323a3245d,0x490f9551296458a29d33,0x5f30ab28a5f43ecfe861,0xec5389061b5f8645242a,0xc1322941f8629c6e195f,0x4c8a523c68ac3ba59baa,0x12e27914e44f29e6eab0,0x4176a1e00c41b46fe61,0xcb3052b9fd4352c14a0f,0x18823c68ac3ba573faa,0xf2add168557c1f5e4734,0x7ccfb4226bdaa0fb1768,0x367770a2f316078b86c,0x91210ad2f18ed2f2985a,0x7779f88335decc4273ee,0xbfe88d0d1db53ff44686,0xa4166e0cd44e10fdb71,0x4c99112dc4f06122f84e,0x9d4d18b198a5178d02d5,0x62a041e10c9d6f0b7b05,0xe8e80d8647c08e4d0862,0x52fbf963c466009108e4,0xf265e4538914d75b4a22],#[0x8a31a4b71de0e1805eef,0xc0ccdcf66aa4c2a43edf,0x5f9d79f55c06d1da7f96,0xa9980d0cacb8552b2b0e,0xe5e1e719f4584369970,0xbe6c8c4a995649c15217,0x470a8e4f2f901f34a87e,0xbc7d4a28f2f3094ba492,0x8c2370acbe123e6fccec,0x75c2a443f475c054a3ba,0x99ff0422616ef0a89aec,0xb3f2592142c7cdf858d9,0x33c016c98857e5604b52,0x45086e7a7142517ceac8,0x6628d2b49efc528347da,0xecaafe3168403d1c7d49,0x16b43479e6f265e6fc18,0xb1aa5e6fc18ed989ece0,0xdbd029686a7141412bf2,0x401e0a95a7b606dbd2d3,0x6a8d52b3abf8c5a168fc,0x8ed994f1b4820a96ed5c,0xd9116b86047ee83e6fc1,0xf9d08e61d160c0488ec4,0x8950e2e4311c3751e1df,0x3ac1d4aaecbbdc0186c7,0x63b45279f115cea4b3e6,0x87e7603452a7262404ee,0x91019b7b0a8e77750587,0xc97464bfd2b0d8fa8eda,0xc391ebb085d11370897e,0x532bc3e3f3e8a339b4ea],#[0x5b5e5615af2b080782a3,0xf12b0b1c98b1ffa9a5a8,0x313f02836bc2aa8fde08,0x475f12633bf9584214e5,0x5a9a347c91b4a152b1f3,0xe5bd15142de8eb8d880d,0x6a1f8e899192a5b3a28a,0xd04f0a03c38fffd06326,0x160a67e90a3e13503f0b,0xc281673cbd248f8abc38,0x44386c7d4332a2952613,0x20ff063708870cda3fdb,0x55d11c1cda1d8abc2470,0x239f1f0a32c583b22af0,0x64952ec55e145e07165,0xf606f06c52124fa4cbbb,0x7781328d2639115e3f85,0xd1d5f3751aaf05308f84,0xa542c952cb93283420db,0x79820d38627d08fd0917,0xa1506b708ae56ca69319,0x19c4af8a292e17d01b96,0x63cae12d2a4d76a619f7,0xbe0a38d48e7cf255a43b,0x5315cac0a3a33b240a4e,0xdce5b840a6cb81a06920,0xfab8375d014e4e08233b,0x27014d6f67c096f0436d,0x42ad99a0e6052ede0d05,0x3725e5d9721a5fbbb6e0,0x93438a086692e374cc05,0x141bb028ded8fb8148cd],#[0x953c10b8c5c10c221e05,0xd4c0a3fad737c00a5c74,0x417f748d042e573028c2,0x7c391eed8149b44f6c0a,0xa38628288d0a7c305125,0xabe52264efc898ece842,0xa1e9ff8094ec286d68e0,0x555e2cef859fe2866290,0x33bc00f22bd2a7603c57,0xca8a52d55fdc36145eac,0x30767a1e431cd2b5f48c,0x6fe30054b641c2a3445a,0x61b602f381626bc50567,0xf36155aae43989b34e22,0x60509aff854cd3028797,0x148a7a16af786076273d,0x18b8a0ab3ec9920cedbd,0x1e2e3b0a3e44c6b29e15,0x8985c7530ca3e1934ead,0x215d0854905f1b1ed643,0x93c16205884fb2d0c50b,0xee110fe74c0521be1d06,0x753851e9b1751806b0f0,0xcd05a627c28c831ec7f,0x478cde24791c30090f07,0x3a1dacde0121e10cc6a3,0x43c1ba928520ede9034e,0x10e874686e11f92ad299,0x4e63661f1f3452e7b83e,0x74b751adc5751d0e4e13,0xf94f860f27068bf2c63,0x7e14ca9207a584528713],#[0xb2061484e04279c69863,0x21cd0785074343938427,0xdd49ef5412c201e94d25,0x42ca694972b530ccd5c6,0xebf2e7b843580e125f46,0x53a3836bd2f3472d7041,0xbcd1f8d00dc3f7b9783d,0x2530e5a8404ce5ab2a98,0x1190bb346ee582a2f893,0x11fa83000fe32a4c5c06,0x88f81b293c8ac18b4c14,0x713f3e77933437f4190b,0x5e5e5c9394e6874d7761,0x2ac0aea60fe3b006543a,0x8348247ff8d30286cbb1,0xb0d9f0ba93450de700e,0xe8854bcd1cdcc50b13d8,0x420014c1af4af0d0f2aa,0x49effc48b4314331f124,0x8362f7d4d0a974ea1985,0xa7e15241fc1b00a4e65a,0xd52749559f800f34a335,0x856955a060662f8693c2,0xaf8d88c0c5394fd60d98,0x4231853f57b30d88569a,0x8caadd422d953b9c6dad,0xe783ec7b138772e2270e,0xcc4829295d9bf7c84d1b,0xf6a7854bcfae590a15af,0x21b843c22bf789308334]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x40820000093870608301,0x1c000061c80000082810,0x4801000285022400000,0x28202340081408001081,0x8a0068a800c141000400,0x60c001040c6871a100,0x200003021d0020214b0,0x23058010100011014001,0x801030a2400000040120,0x4196020c807060008104,0x300240800004094121,0x4018060c1960000,0xe801c0a7320410032040,0x42010100005020c784a,0x48000220888000828a,0x493080401210100000,0x1010640301081448014,0x47e40000008006120,0x8a20893c1c66c82d6000,0x283000240c921000602,0x6d39488c85680020d400,0x4c87ca2d400101081397,0x1600a6df1e17a0931f6c,0x4558dbd3e50744de0004,0x67700000f327267df038,0x88c709f457ce3ca4,0x2be4867000588c00,0x60000a69175aa934b800,0xf9800000000000002783,0x61c8000a0f8,0x1002171a906228,0x392e000908800386e138],#[0xa806374d2549938fb000,0x8887b90b000422c0005e,0x9c00044cdbbb00e00050,0x28c00197f26aa0740000,0xa2c80024520000005,0x425b38e0000007225296,0x50aa3c0000001089000,0x800000180f000080800,0x192589dc7110fe18147,0x88f440cd04c400000,0x15e9000000214d1c30,0x8e4e8e69240000000000,0x22de00040d0001821119,0xb000000000199f000000,0x111fc02754b84d9c,0xa3074800141600000000,0x2bc000000ebcc5d80011,0xd0f8c564b400090c6426,0x325223a000000455108e,0x2000483800104b8ac000,0xc000000019e000000121,0xc94340004178001199cb,0x225e00087d18d52,0x2e01241181c01ce0000,0x28f26ad2e99900dc8000,0xeb2ec736e1f0985,0x48d80014320000a1800,0x694208ab8cb800000000,0xceec57e84600082594,0x454000000801e3b00000,0x20be8489e1c930003,0x27fe3cd6030ed8000000],#[0xdcd4819608b406000c36,0x25f2828123edfc795b7,0xfacef00001e74628ee47,0xf3c4b0001de528e80039,0x9ea00000000010c2d2ea,0x428800104c64f41a4,0x4590000000000,0x4d780010c441daea000,0x2b400062f800000000,0x2dc00081f00000,0x3da34e00000000000000,0xceb47782380000000004,0x66320d7c2a00014caba1,0xdaa00000030dfd1bc1b,0xfc54400183f8f6d07f12,0x421156e7000332200049,0x24715818b9e00e2c55c0,0x6101439c828,0x60d80020cb0b905d7804,0x117000070385c8000912,0x71980000000ba800,0x10529b30000003bd000,0xda000256289000000000,0x5e61f812442e24800010,0x8ce40c0002ae8000cb52,0x800030600000000000a1,0xb08f24361119d0000643,0x50a4be0000000000236,0xd882605b56eb10a00000,0x289c0010a300000013,0x830000000439a21e1f10,0x416f10e0060006135],#[0x550000190d,0xe000405800186383e01e,0xd5a89238000465000003,0x3bd03831344896ce01c7,0x2269622e027bfa1b8,0x90100068208ba0000000,0x28b61a0000ea70000001,0x618f318c2072b815e000,0xd6787c72511c30631813,0x2a114ea3f0e50aed0561,0xa0054926986ec5442533,0x8040c8e2d140625d888c,0x27be6f037d9a188162ab,0x108703960366c61c7019,0x1517a7d09da1dac6d922,0xc5280000e905,0x1e00065cc00000000000,0x48740d0a860,0xc95000201f46a000c818,0x255400120cca08000001,0x9314c30000000000ca2,0xc31880010d7000777800,0x1d092000687c0005038e,0x83b383dcf00028aaa,0x424cbeb16000006d0,0x46500000000cb00007c8,0xd26113e000631c0010dd,0xb100022f,0x6c0000000007000a3800,0x10f100048,0x1040011ea0000326ae20,0x8648d400000001d60004],#[0x0,0x98dce76478398000000,0x852140000008ab429000,0x5347fce8000000000041,0xb9a3f80019b400a00021,0x18a14a98000000d072,0xcae80000000004ef8000,0x243d02f10b0003210000,0xdedc873610805582346b,0x1344000000637809589,0xed27d87a400009a00000,0x56c4121d78b0b1900018,0x64a4000dfa0cd6,0x55f69fc0000004754000,0xcf10cb41f646400082a,0x3036129200089ce34b38,0x4c80000004e589,0x980f400080949165080,0xdd70007754a2c111e,0x5f411645d43c0618000,0x23f80000000002458000,0x100046d8001059000000,0x313b34a5000506927a83,0x1500033758bc0004b065,0x8,0xd120000000001875f058,0x185dc9580010f5,0x89191400001bfa3a000,0x6e5640000000fd0002a6,0x78000040000005000046,0xef000235400087827b92,0x26a21a000682a29e000c],#[0x47e90840010374ce0001,0xc00189f0005544001897,0x2614000322cc960f3e0c,0x32e0000005e28000122,0xe0576b4000000e1b00,0xc0bd46cfc00013240,0x48b00000000009284a68,0x2036461000000219e,0x400044aa2b80000e8000,0x271882b17aaa600021e,0xc4f2e0780021ff9d300,0xa587af461946e1965962,0x9ce00000000000000006,0xb4000632c3b8003,0x21999e4c4c634d004ce1,0x37ac39e00090221a,0x39f1233000000129400,0xad00005b4001a1400000,0x10000000000000000011,0x1fec712108000000204d,0x13d011acdfe29c1a8,0xc000274d508000c65913,0xd217fa1200050a800334,0xe000286000000000026,0x1a800000000000000023,0x10050004410000000c,0x5f835245c70c0000,0xabb8d4dc3f47c034a0b0,0x209905a034800000060a,0xb9056100e33904800150,0x8b280451f33bd04c6120,0xadbe80c10dc00000019],#[0x1bb4c042f4ae4481106d,0x93630ad11c806800242e,0x6600a04684c1adcf6c08,0x761980000f4c6e61ed8b,0xc60860a741c62c6a1d02,0x93e30000188200073b28,0x10b3c7500029c58528,0x162c0009ae0004020,0x2ce00000000019c0ccf,0x479000208,0x8000000000000032cc00,0xe200000022a142e20b51,0x1cfc00000000009,0x50800000000000,0x21efc11000115d442,0x4eecc480000014d3000,0xf8863a9044283b000000,0xd412590002bc40002e,0x3800326cd7000048040,0xf1d2514001969e,0x356a5e97781e6800,0x800000026b800037a9a0,0xa00075d6a8a000000063,0x44000000298e4ebc6710,0x4900024161778bcaf783,0x23f618485a00001c80,0xdf700008d80014ea0000,0x38f5182a8c0003221,0x10f58bde16a11a0002bc,0x1874400000051288d000,0x1d280987f409f8e58f,0x5103640011c200070640],#[0x46e000000266e3900006,0xd0280030e600069b8002,0x2375de38ea00032dc02c,0x70000001330000000000,0x9fe000c41800022e13]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0x50910505105011048510,0x58110551105491054510,0x5911058d105891058510,0x5d5105d1105c91059510,0xdd510dd110dc9105d910,0x501204c5201d120dd910,0x545205412050d2050520,0x58520581205512054d20,0x5c520595205912058d20,0x5d9205d5205d1205cd20,0x9d1209912098d2095120,0xdcd20dc520d0d20d0520,0x50930dd920dd520dd120,0xdd130dc9305913058930,0x549405454050940dd930,0x58540581405514054d40,0x595405914058d4058940,0x5d5405cd405c9405c540,0x9914098d40951405d940,0xdcd40dc940dc540d0940,0x5914158541dd940dd540,0x505505d9415d54159541,0x58550581505515054950,0x595505915058d5058950,0x5d9505d1505c9505c550,0xd05509d1509915098d50,0xdd950dd150dc950dc550,0x59551591515855155151,0x5915459153dcd515d951,0x5d9545c5545c15459554,0xdd954dc554dc15499154,0x54d6054560505604c560],#[0x59560591605896055160,0x5d1605cd605c9605c560,0xd05609d160951605d560,0xdd160dc960dc560d0d60,0x5916158d6155161dd560,0xdd561dd161dc1615c161,0x9516359563551631d163,0x5c5645c164dd163dc163,0xdc564dc1645d5645cd64,0x5d1655c5655c165dd564,0xdd165dc565dc1659d165,0x54b405c264552635c254,0x5934058f4058b4055340,0x59341547415cb4059740,0x9fe775c3435c34159741,0xcfeffbfafdbdeefb7ebf,0xe5f7fdfb7ddef77dbf5f,0xeebb7ed7afebbade7f9e,0xf7bddf6bd7f3fbfefbbd,0xfdbf5fbfeefb7eaf9fdf,0xc23ffffbfdff3fbfebf7,0x58879f5486a45085d758,0x91595752595695590f99,0x6640619c5459149758d4,0x54406d484040a1e6d159,0x6650806de0406d58406d,0x6958c04fdc804f5c80,0xdd804f5d806659006655,0xed4841c7e1804761804f,0x81db5881ed5441ed5041,0x5d01db5901cfdc81cf5c,0xdb5941c7e101cfdd01cf],#[0xc02858c00fdd41cf5d41,0x5d400edd000e5d002898,0x8edd800e5d800edd400e,0xa858c08edc808e5c80,0xdd808e5d80866140a559,0xedc810e5c810661808e,0x810e5d81205941205501,0xdc820e5c820661810edd,0xe5d021a590206e0820e,0x420e5d4206e1020edd02,0xe1c0c161c0c6e1420edd,0x4161c24161c147e00141,0xc34c58c34ee04346e043,0xe18341e14341e1034c98,0x4161044c98c44c58c441,0x28c5d02816184416144,0x61c18a5d418bdd018cdd,0x8161c2c95d82cb5d02c1,0x4381e0838ee04386e043,0x614481608481e18381e1,0xc161c30a5d4301618481,0x84c1e183c1e103c1e083,0xe084016184c16104c160,0x1608501e14401e10401,0x85cfdc45c16145016105,0xe085eb5885eb5485eb50,0xe65505e998c5e958c5eb,0x5e69905e65905e69505,0xe145c76145e6dd05e61d,0xc76185cfdd85cf5d85c7,0xc6a958c6ab588687e185,0x594687e106a15506a998],#[0x8fdd868f5d86a1dd46a1,0x78fdc4787e186876186,0xe1078fdd078f5d079b59,0x8fdd478f5d479b594787,0xb01a1c61bdd8787e147,0xe0c6c1a1cb0161cb0760,0xd858c7c1a1c6cadd46c5,0xcb8c58cb8560cb81a1c7,0x610b8ca0cb8c60cb8c98,0x47600b41618b81614b81,0x801a1cb4161cb43614b,0x5d481859480cdd080c5d,0x4cdd0a4c5d0a4cdd480c,0x746604bccdd4a4c5d4a,0xa1c74161c74a5d474b5d,0xb5d0a0560ca07600a01,0x884b5d0841a1ca0161ca,0x600a81a1c84161c8495d,0x41a1ca8161ca8b5d0a87,0x454b5d054560c5466045,0xe00941a1c54261854361,0x41e0494fe0094bdd0947,0xac7600ac1e18941e149,0x614c01604c0161cacbdd,0x895d888a5d4881618c01,0x498add4981a1c88161c8,0x604c41e18981e10981e0,0xc9dd89c1618c41610c41,0x4c81e149c1e109c1e049,0x610d81614c81610c8160,0x1618dc1608dc1618d81,0x4f8fdc4f81610e01608e],#[0x588fa6d08fa6508f87e0,0xa6550f87e08f8fdc8f9b,0x4f9b594f9b590fa6950f,0xdc4e9bdd8f8fdd4f8f5d,0xc1a1ce9d550e85e0ce8e,0x9341a1cfd6590fd858cf,0x61534b59134c58d34160,0x66e00e47e00e41619341,0x4e4b5d4e6398ce6358ce,0x58d30bdd8e4b5d8e4bdd,0x461530bdd530b5d5323,0xd30461930bdd930b5d93,0xa1ceca5d4edd550ec4a1,0x41a1d0095d9016591001,0xd38c58d381605384e111,0x59138b95138b55138c98,0x4161938161538b99138b,0x50585950639510635510,0x5d52a355128cdd504c5d,0x44e08f4add4f4cdd528c,0x8f4b5d8f5ddd4f5d594f,0x609244e18f44618f4bdd,0x8461924bdd924b5d9244,0x508b5d5084e09089dd90,0x6092d6dd9084e1508bdd,0xc46152cbdd52cb5d52c4,0x51c1a1d0c161d0ca5d50,0xe191c1e091c1e051cadd,0x1619401609401605401,0x5201e09201e05209dd92,0x615441609441605441e1,0x4161ebca5d6bdd552bc1],#[0xec495dac56592c4d5cac,0x592d4b552d4c58ed4161,0xa3552c81e1ad41e16d4b,0xac1d596c0c5d6c98596c,0x5d6d0b5d6cc461ac0b5d,0xa154968fdc568161ed0a,0x1687e0968fdc969b5896,0x6159cfdd169b5916a155,0xa551a01609a0161d9c3,0xd601619a0a595a01611a,0x5d960add161e98d61e58,0x495d971359570add960a,0xda4c58da41605a43e158,0x595a41611a4a551a4c98,0xcdd175e551741619a4a,0x1643e0964cdd191e5519,0xdd964a5d965d99165d59,0x43615943e1964361964a,0x5987601983e1588161d9,0x609a81605a8161d98361,0xc3e097c1619a8a595a81,0x18c1e098c1e058c3e117,0x611ac1609ac1605ac1e1,0xd65922c76022d6591f41,0x5f85e0df8161e2c261a2,0x61234959234160a35359,0x49dd6049dd2041616341,0x2389592381606382e1a1,0x60230161638959638161,0x161e30261a303616307,0x224261a0135960165920,0x61a25659224560e24760],#[0xc2e16082e0a08161e242,0xe28261a287602282e1a1,0x6163c160a3c16063c161,0x1606402e120c2e0a0c1,0x5486e0148161240160a4,0x61d50a5d550b5d54ce5d,0x81e01581e19541e01541,0xee41e0ae4e546e41e155,0xe1ae41e16e4b592e4c58,0xce5dada0596da5592d81,0x1b4161ee0a5d6e0b5d6d,0x591c5a591b60551b46e0,0x3619b0a5d9b1d591b0c,0x1c03e11bc6e05b83e19b,0x60a55858e501e11c01e0,0x81616541612549592541,0x258bdd24565924585d24,0x6125c16025c161658160,0x160a701e1ae81e0ae81,0x270560a7016027416127,0x6026056026c5e0264561,0x98612698602685602745,0x9e41605e45e02b58a126,0x619e4a595e4b591e4160,0x8a595e8b591e81601e81,0x1d04601e04e01cc1619e,0xe05dc1e01dc3e05d03e0,0x1e0ab01605ec1601ec1,0xa881606881e1ab0b592b,0x6168c16028c161688160,0x81606901602906e06801,0xaa41606a41e16b81e0ab],#[0x612a81602a81612a4160,0xc161ea0261aa03616a01,0x81486180c1606ac1602a,0x5d86105d46105d858861,0xd05d8b105d4b08618610,0x47d05d07d05d86d05d06,0x5d8b505d86505d48d05d,0x105d08105d87105d0710,0x8bd05d0bd05d89105d09,0x5d48505d8a105d87505d,0x506049505d85505d4a90,0x4950e0c95060c950e049,0x618950e1495061495059,0x905d8ad05d4ad0e18950,0x8990a109906109906049,0x60c9d0e049d06049d061,0xd06109d02109d0e0c9d0,0x49d06149d0e109d0a109,0x5d8ed05d8e88618cd0e1,0x10dcd1505cd148618ed0,0x52105d93d05d91905d8f,0xe09210609210e0521060,0x10615210e0d21060d210,0x95d05d95c861abd0e152,0x9d18505c98105d99c861,0xd0e058d06058d05d9990,0x18d02118d0e098d06098,0x5ce150e118d0a118d061,0x905d62905d21909d2150,0x806f5480509d29505ce7,0x61406f59406f60806f58,0xef5481ef5081ef61806f],#[0x41ef6101ef5501ef6081,0x5480ae59402e55002f61,0x2e50812e5940ae5880ae,0x22e54822e50822e5881,0x58c0ec5880ee6040ee55,0xd05d40e75900e75500ea,0x80c8e140c86140d0dd40,0x61c0c8e180d0dd80d05d,0x6c58816e604150a1c0d0,0x150dd01505d01625501,0xdd81505d8162594148e1,0x50a1c15061c148e18150,0x2505d025c59026e6042,0x5d425c594248e10250dd,0x5061c248e14250dd4250,0x4350550348e14350a1c2,0x590450550450e1435059,0x88e081ae604190594450,0x81905d81a25941a75901,0x61c188e18188618190dd,0x90594390dd42d0a1c190,0x308e0832e6043105944,0xe08410a1c31061c308e1,0xd0e14410e08408e14408,0x45ef5c45ef5845ef5445,0x54c5efe045ef6045efdc,0xefdcc5ef5cc5ef58c5ef,0x5ef5505efe0c5ef60c5,0x5d45ef5945efdd05ef59,0xefe145ef6145efdd45ef,0x85ef6185efdd85ef5d85,0x5846afd046af5046afe1],#[0xaf5906af6046af5c46af,0x6af9d06af5d06af9906,0x6186af5d86afa106af61,0xafd047af5047af4c47af,0x47afdc47af5c47af5447,0x54c7afd0c7af50c7af60,0xaf60c7afdcc7af5cc7af,0x7af1d07af9507af5507,0x6107afdd07af9d07af5d,0xafdd47af5d47afa107af,0x462e584610dd85af6147,0xdd462759062a58c62e5c,0x861c610dd8608614610,0x4b27590b2a58cb2e544b,0x618b10dd8b08614b10dd,0xee5c46ee5846c861cb08,0x46e25946d0dd06e25506,0x61c6c86186d0dd86e2dd,0xd0dd07dc5907ee5c47c8,0xc7c8e147d0dd47c8e107,0x98c8ea58c8c8e1c7c861,0xc8e108d0dd08d05d08ea,0x88d05d88c8e148d0dd48,0x5d0baa58cb88e188d0dd,0x88618b905d8b88610b90,0x8b50dd8650594b90550b,0xdd080861cb48618b50dd,0x2a550808e1c808e10810,0x82a5d082a1d082a9508,0xe1082a21082add082a9d,0x2a21c82add482a5d482a,0xbea5d0a6a550a6ae1c8],#[0xe0476f600748618bc861,0x675d0767990767590748,0x4750dd07679d07505d07,0x618750dd87625d476259,0x4861c75061c748e18748,0xa27590a08e1c750a1c7,0x61ca08618a10dd8a275d,0x675d0848e0486f600848,0x4850dd08679d08505d08,0x61c85c5d8848e14850dd,0x88e1c850a1c84861c850,0xca88614a90dd4aa75d0a,0xe0496fe0094861854861,0x50dd49505d4950dd0948,0x8950dd89505d8948e149,0xdd8ac8614ad0dd4ac8e1,0x8604c0861cac8618ad0,0x4c10604c08618c105d8c,0xe048af600890618c1059,0x9c5d88a25d4888e10888,0xc890a1c88861c89061c8,0x610c48604c505d8988e1,0x50604c48618c505d8c48,0x49d0618c50a10c50610c,0x604c88e149c8e109c8e0,0x90610c90604c88610c88,0x8ce7590cec588cd0a10c,0x590d10a1ccc8e18cd0dd,0x90a1cd08e10d10dd0d1c,0x4f90a1cd48e08d50590d,0x604fafdc4faf5c4faf54,0xaf5c8faf548faf508faf],#[0xcfaf54cfaf608fafdc8f,0x550faf60cfafdccfaf5c,0xaf614fafdd4faf5d4faf,0x8ea7508eaedc4eae584e,0xdd8ea2594ea7590e90dc,0xee5c4fc861ce88618e90,0xfc8e08fd0dc8fe7508f,0xe14fd0dd4fd05d4fe755,0x27509108e1cfc861cfc8,0x112755112a58d1105c91,0x5093505d91105d512759,0x6a58d3486093505c9367,0x53505d53675913675513,0x5493486193505d934861,0x50595350609350589350,0xe67550e6a58ce506153,0x5d8e50dd4e505d4e6759,0x6758ce6754ce50dd8e50,0x4e67594e67dcce675cce,0xdd8e675d8e67dd4e675d,0xe75d93275d5327595327,0xceea58ceec588ec8e04e,0x990ee7590ee2550eea98,0xc8e10ee7a10ee7610ee7,0x8ed0dd8ee25d4ee2594e,0xa1cec861ced061cec8e1,0x8e0502f601008e1ced0,0x102795102755102c5c90,0xe11027a1102761101c59,0x10dd50105d501c595008,0xd01061d01c5d9008e150,0xe01148e1d010a1d00861],#[0x6a98d16a58d148e0516f,0x11675911679511675511,0x5d5148e11167e1116799,0x505d9148e15150dd5150,0x13aa58d388e19150dd91,0x6153905d53a75913a755,0x9054d3886193905d9388,0x539059139055139058d3,0x590f1061939061539059,0x48e1d048e09050dd8f27,0x506ae1106a55106ae090,0xe1d06a21d06add506a5d,0xc86093e75911aa5d52aa,0x4f67590f486193e75913,0x618f50dd8f505d8f6259,0x675d8f67608f67604f48,0x50a75d9267618f67dd8f,0x6090a7605090dd50905d,0xa7dd50a75d50a760d0a7,0x90c8e050e75d52e76150,0xe110e7a110e76110c8e0,0xc861d0d061d0e25d50c8,0x91c8e051c8e1d0d0a1d0,0xe191d0dd91d05d91c8e0,0xd06091d0e051d06051c8,0x9410e191d06191d0e091,0x6094086194105d940860,0x8e09208e05210619410,0x9448615448609448e152,0x58ebec58abd061545060,0xe2596be7612be7592bea,0x2c5061ebc8e1abd05dab],#[0x5d6c5c596c67612c6755,0x50596d5061ec48e16c50,0x2d08e0ad1061ad50616d,0xd056af50569061ed2761,0xaf5c96af6056af5c56af,0x16af9d16af5d16af6096,0x5495ee5855efa116af61,0xe25955e75915d0dc95e2,0x99e25499c861d5d0dd95,0x5959e75919c86099d0dc,0xc861d9c86199d0dd99e2,0x96d0dc96e25496ee5c56,0xdd16dc5916e25516c8e0,0x8e1d6c861d6c8e116d0,0x58105d18225518225498,0x591610589a105d982259,0x229d16225d1622991622,0x9708e0572f6017225d96,0xdd171c59172255172c5c,0x1c5d9722615708e11710,0xd710a1d70861d71061d7,0x5d186255186a58d848e1,0x50591a505d9862595850,0x192a9d176a5d1750991a,0x59166260966260566a5d,0x88e057a26196625d9662,0x17a79d17a75d1788e097,0x61d79061d7a2615790dd,0x48609948e1d790a1d788,0x9888e0588861d9675d19,0x5d98a2e158a2595888e0,0xa2595988609988e19890],#[0x17e26097e26057c86199,0xe098c8e058e2a117e261,0x50dc9f1c589f08e118c8,0x5f50dc9f5c589f6e5c5f,0x61df48615f50dd5f5c59,0xd0dca2dc58a2ee5462c8,0x62d0dd62dc5962c860a2,0x589fae5c5f8861e2c861,0x9c591fa2551f90dc9f9c,0xa11c58a10861df90dd1f,0x5d211c592108e0a1105c,0x105d611c596108e12110,0xe05c50e050552348e161,0x55205c5ce05c54e05cd0,0x5c9d205c5d205c95205c,0x215c592148e0615c5d60,0x5d615c596148e121505d,0x9050e39ce1a148e16150,0x239055239054e390d0e3,0x591fc861e30860a31095,0x9c592188e0a190dd1fdc,0xa008e0602f602008e121,0x9d20275d201c592008e0,0x1c61a0225d6010dd2027,0xe010a1e00861e01061e0,0x61e2675d224860a248e1,0x9c60e09c60a09c606088,0xa1c8e061dc61609c5d60,0xe161d05d61dc5961c8e0,0x9c59628860a29ce1a1c8,0x20dc60a0dc6060c86162,0xe0a208e0621ca120dc61],#[0x276154e76014c8e12208,0x6e5060ae5061d508e015,0xe02e1061ae50616e5059,0xe2619b22601b1061ee08,0x6508e0a522611be2601b,0x606448e02450552548e1,0xdc6024d0a1e45061e46e,0x1c9061ae9060ae9c6164,0x5c5d6a602b6a602648e0,0x48e09d505c9d48e05d50,0x9d62e15d62595d67591d,0x595da7591d88e19d505d,0x27605ce7601cd05d9da2,0x5dc8e01de2605d22601d,0x605dd0e01dd0601dc8e0,0x9061ab1060ab10e05dd0,0x6788e0a7905ca7905c67,0x5d67dce1a788e167905d,0x50616b9060ab88e02850,0xa9505ca948e069505c69,0x5d2988e129505d2948e0,0xc8602a08e069c8e029d0,0x1705d01705901705940,0x5502706181705d817061,0xb06083306081b0614270,0x4b305d46305946305d85,0x5d86f05d06f05906f059,0xf0dd47f05d47f05507f0,0x86705948f05508f06147,0x5909305d08305907305d,0x30618cf060c870604770,0x8eb0588eb0608d70610d],#[0x54d030595370548ff05c,0xf05d8f3058d17060d030,0x95f05c95f05895f06050,0x5c96f05d99f05899f05d,0x306116f05d16f06096f0,0x5f705c9f306057b06057,0x5521305c9fb05d62f05d,0x306060305d1ff050e170,0x1cb0602470602e306015,0x10a0059001a00003060,0x5b80280011c0073802dc,0x3808f0042a01e900d580,0x18f00bb0058a028e013,0x3ed01e380e4806d00345,0x5c047c022e810d4082c0,0x40af4054202850138c09,0x19500c5c060b02e9016a,0x9b81c0c0dc006b203420,0x503e581e740ef2075803,0x87b042e020e4103407f,0x2ba092a047e8232c1154,0x78140209de04d7826081,0x82b00150a0a5b051b028,0x5d582df816a00b1d0579,0x740627030a017f80bca0,0xd35068403344194a0c,0x1c0c0dd706d8036001ac,0xb541d580e86072e038d8,0x3dcc1e920f2e078483,0x8220407c1ffa0fc807d,0xfa086e042e0212a106a,0x98119108b28450422401],#[0x424b6122a0903847c023,0x4d48263012ee095a04a0,0x904f90277a139c09bf0,0x30a6f052ac28fe14480a,0x15a20abf8554c2a68150,0xd28165c0b16857dc2b9e,0x4c2ec8172e0b7785afc2,0x860d0301417e80bdb05e,0xc8286360316018940c2e,0x40ce90669832e219360,0x81a960d3a8694034581a,0x36841b200d7b06b50356,0xb4380c1bd30dd586de8,0x78732039401c760e2987,0xed0075b43a701d160e7,0xeaf0f39078f43c241dd9,0x2c1f7a0fa387c683dc41,0x4407220080fed87ee43f,0x84a441ea20d6105a081f,0x9087604356218310ab8,0x9115708a0c44ca224311,0x2359119a88c3445e422d,0x7f023d911d888e3c46e8,0x3c4964247d1223890804,0x95304a5a25061272093,0x331098bc4be825bd12c0,0xf137989b104d48268b1,0xc27e413d609e104e8c27,0x51d828bd14460a160503,0x6c45312295d149d0a438,0x8a95854522a0314ec8a,0x15b00aca055ea2ab9154],#[0xc6e161a8afe457782b8e,0x742d1216718b2bc591c2,0xc5bf42dd316d50b5cc5a,0xbb285d342e7417248b88,0xd78bdfc5eac2f26177b8,0x418390c10460122fda17,0x3145188a0c3c8618a309,0x45231fb18ea0c67062ce,0x10659832ab19430c9806,0x8cf10671c336b19970cc,0xa638d25068d2342819f3,0x9f1ab88d50c6a3234f21,0x8363d1b078d7a86b8635,0x6e4036fb1b690da546cb,0xff06fac37a51bc10dd54,0x90e34c7150386d1c158d,0x1cd40e5dc72aa39271c7,0xa851d2e0e8e4743439df,0x2c3b541d8a8ebfc75843,0x478be3c221df30eeec77,0xf56c7a5e3d031e610f21,0x270f8587bd43dbe1ec90,0xe1f898fba07d6e3e871f,0x3fe21fdb8fe387ec43f3,0x1584084202c900c48014,0x1882ba413420829033c8,0x10968845e41fd20e1106,0x18910bb4859442a82142,0xe421d190e2086ca43362,0x4448b2236910fc881043,0x8ad04538228191364896,0x8f88c3245f922e89166c],#[0x691bac8d80468a232d11,0x23fa11f3c8f364762239,0x89a243912150906c4817,0xc84938248412354916c4,0x4946e4a0124e39265892,0x2c4895ca4abd25461297,0xf592f14971a4b62259d1,0x264c1319c987c4c1b25,0x4d7026a19343c99e24cc,0xcd04e332701937349b42,0x8c9e544eea276013a409,0x940189fc64fc027c613d,0x86014288a104505d2816,0x9328b3144d8a21450de2,0xc5248290894794a36c51,0xa64852f4296614a88a4e,0x20a7ba53b229c314d7c,0xe152e0a910545b2a1a95,0x2acf9559caa7455022a6,0x6622b1b9584cabd855c6,0x3a56fa2b6615aa0acfe5,0xaf7257972bbb95cf4ae,0x6270b0e258462c0615f7,0xc796590b25858f32c5f1,0x22d239685cb3da59bb2c,0x5b122d7396aecb53a5a7,0x7c85bb92dc296d54b660,0xb8b90e5c622e1c97034b,0x9761cbaac5d1f2e74172,0xf2e978a0bbfe5dd62ed8,0x562f9597bc0bd8c5e8d2,0xc60122ff197ee0bf105f],#[0xc20a60d43052181b8c07,0x794c376618b30ac984c4,0xa98a88c4e86238310898,0x31bb18d38c64862ff316,0x3e531ee98f54c79a63a6,0x1a640531fe98fd4c7da6,0x4c85a6425320e99054c8,0x9154c89a6445321e990d,0x3e991d4c8da6465322e9,0x5324e99254c91a648532,0x64c5325e992d4c95a64a,0x9da64e5326e99354c99a,0x54ca1a6505327e993d4c,0x994d4ca5a6525328e994,0x2ae99554ca9a6545329e,0x8532be995d4cada65653,0xa65a532ce99654cb1a65,0xcb9a65c532de996d4cb5,0x7d4cbda65e532ee99754,0xe99854cc1a660532fe99,0x331e998d4cc5a6625330,0x665332e99954cc9a6645,0x1a6685333e999d4ccda6,0xcce0266d1334e99a54cd,0x9fa4cf50678033a799ca,0x7d9a308d134685c34131,0x34de9a630d2a6692734,0x6ab635381a8e4d42a69e,0x7446b6e359f1ac38d5c4,0xc4d8fc6c3a36049af68d,0x9b600daac6d21367b9b2,0x7479b94cdc2c6ddd36d4],#[0xba37bf1bc9cddec6ec33,0xc7093382d9c0a8dfe26f,0xe3507172389c9c40ce17,0xaa0e4ee724239069c758,0x51cce0e62872f039661c,0x3a1d1d00ce7a673a339b,0x53d3a809d35ce93e7475,0x6e76013ae89d694eae47,0xcede276bc3b439d95cec,0xdf20ef3c77743ba49dc7,0x5c1e254f0a678273bf99,0x3caf9e4dcf21a78dd3c,0x7a163cf79e71cf34c798,0x5c07aaf3d459e960f47a,0x58f7487b713d981ec1cf,0x1f224f8c07c2f3dff1ef,0xec71f570fa4c7ced3e5f,0x753f229f83cfbc27db63,0x47f433f859fb60fd4c7e,0xbc802e3ffe9fefcff2,0x509022c80e3405d20221,0x82082d03c281b140bc20,0x417420ac50510825f411,0x3dd41d4a0dc50676831a,0xec84c44240a111908248,0x10b58857b42a62147109,0x1b050d1c866443112178,0xe421e710ec68737437ea,0x8445f221dd107487f943,0x89e744dda261d128c88f,0x61a8acd454a2295d144e,0xc117a08b9c45b422ce11],#[0x233fd19a28ca14634230,0x6f1236d11b0c8d594691,0xbb4747a39691c5c8e074,0x68f8347aba3c951de08e,0x216e90874825a40211f9,0x6c922f09146488ca439d,0xa496d2454920248eba4,0x49a7a4c8d25e892b5494,0x42c49ff24f25273c937f,0xb895344a79252b128b49,0xd2bf495d24ad1a55fd2a,0x5b652d3896744b262587,0xf5a5e792eba97374b83a,0x24c6e262a930ce98304b,0x99e24cd7a65d13282991,0x5649a8e4d34268f1341a,0xe1370a9b384d82a6b753,0x2718938729c1a4df826e,0xea0a744939c09cb04e49,0x224efba77113b449d624,0xa9f164f6827a653cc69e,0x40309fe04fcca7dc53e8,0x40d41c4a0b7503fa8111,0xa287094318a154509428,0x5153a8a1544b4a22d50f,0x38f51b128cad45f0a2c8,0xaa44e5210a8fad4782a,0x94a96a51d5275a92f949,0x99194c00a5d152cf295d,0xa829c794dd6a6ac533fa,0xc5405a9f494f48a77653,0xa9035469aa2bd50faa83],#[0x3aca99f54bcaa56d5268,0xcd5562aa73551e2a8155,0x2af015724ab6655952ab,0x6572b1fd5894ac2055fa,0x9956b5ab5115a10acd95,0xeae42570c2b7d15b94ad,0x5e3aaef857602ba555cc,0x255fdeafbd57ccabd4d,0xcac41161a6b08d5828ac,0x59022c745633ab168589,0x2f85963aca6564beb22a,0xc8b3bb59c72cd816654b,0xd692eb4765a1f2cff967,0xd6196ac4b5355a83ad31,0x5dad9d16c56b5f05ad82,0xc5bb42dd116e48b6ed5b,0xb87e5c242e01d6f9ab79,0x306b94b5c88ae395715a,0x71752cba685d112e7617,0xaee9576f0bb495d8a2eb,0xe512f1cd787ebc105de5,0x995eacaf4d57a16bce05,0xcbe6d5f1eaf7cd7b7abd,0x7ecebf385f86afb8d7d4,0xe9801cbfe45fdfafe29,0xc3043181c4c091603230,0x60fcb07258328c16b609,0x2e2615cb0a1984b6c227,0x6ac38d61b130ce18614c,0x988e4c4436201b0f6187,0x15d18a72c506626db12a,0x39318d18c16c5e362da3],#[0xa639831c218d92c6a363,0xc81d63f7b1f158f36c77,0x23ec8eb645b3222d90c6,0x3193e8c9c564cf325719,0x32b559562ca826518b28,0x5eab2e6596e6cb3a6588,0x916638b31359838cbfa6,0xecd40668d333a99982cc,0x9c00cdc866d4b36299ac,0xbd19d8ace8b672cb38bd,0xa33ef99f0ecf576792b3,0x685f34241a0bad02d67f,0x1aa68bfb4541a23ed0ee,0x60d2876923b4841a3b8d,0x9a708d34b698a34b85a5,0x51a5a876d40c69ed34eb,0xba35521aa1cd4d16a4e3,0x26b1d35815aba2d5a76a,0xd72f6b7fb5b39ad32d67,0x7cd8066bec35e91aecc,0x9b20cd8d76c53b61edb,0xb68b1b3ced9b66cbab65,0xd95b6bf1b590da946d34,0x406dfcb6f25b70cdb586,0xedd336e76372f5b8fadc,0xbc50ddfa6ee2b764dbab,0xd55be3cdece6f48b7971,0xbb7fd5bf88dfa06fbe37,0x7087b8369c144e061701,0x21b70f0386a1c310e15c,0x28e2e8715a38a35c4aae,0x5c756e37f71ac38cddc6],#[0x9279c8f6e451720438f9,0xd2b95bdca58e4fd726bb,0x27331398cdcc0ee5dd72,0xe753738cb9b9dcd68e69,0xbee82573f6b9ee5cf08,0x11d2a0e919746aba26dd,0xba8e5d410e9e074dc3a6,0x581bab51d55aea877534,0x2e75fe3af2dd72aeb3f7,0xeed32767dbb285d8c6ec,0xdc8eee0c76ec3b659dab,0xde5de74ef097762bba21,0xd3c201e08eeff277d6bb,0x78c8bc5ade286f10d785,0x2857927bc895e3c0f1b7,0xf4f34279853cb89e560f,0x5e8c2f41879f23cec9e6,0xd4bde9f4f4d27a583d21,0x103d7e1eba8f5937aac3,0x87b693da7decf6f6557b,0xf7e17bddbde41ee94f71,0x1eef8d27c53be149f026,0x59f326f95f7c9f3e455f,0x3ea85f4defa487d0b3e7,0xdcb3ed8df660fb037d6b,0x7d7e24bf085f7eafbbf7,0x8fd297e7cbf349f942fc,0xfc08fdd37ecc3f5ddfa9,0xc4dfdbafea67f393f8e5,0x3ff31ff3aff737fa43f,0x806b402ae00cd0041800,0x1e780de405e202ab0113],#[0xcf02b88138c090a04250,0x207b103a781b3c0cde05,0x13f609a7049882324108,0x14417860b65055f8293c,0xa8378c1aca0ce7064e83,0x80683d7c1e1e0e8b071,0x25508eb845d422121071,0xe613b109ae84c2c25621,0xc2aaa14f90a4e8513427,0x5c8c2d8216570b01856b,0x83862a430a217e10bbd8,0x70d3f86854339619730c,0x1c7b0e0d86ef436be1af,0xd321e350eed875ac39de,0xc401a1fa90fa887bcc3,0x8871c42d62115104f881,0x1b188c14457a2279110e,0x712588916c47f223ab1,0x6269b13258978c4b0625,0x50f2281513da89d4c4de,0x804540629a514a48a3ac,0x18f03c250b4130bc1f05,0x703417b081370ac1604,0xf028450321404815d08,0x84072c643445d064b306,0x8d13e0783f0513346045,0x4093c8a6090005a2130e,0xc3618c0c2d80d10c4139,0x81d0c43d15c004e85118,0xb4284988c1f3141560b,0x8b50e85c26c02330590c,0x440700e60f8303706614],#[0x41c104bd008f9368141e,0x899050ca0e0320687858,0x1a8268f3160bd1619814,0x393a1905c8607a03a38,0x240404c5261d8060210b,0x5a014b03a0800a82a0c,0x1e43c8b8429100585c38,0x40c36840002184ac9908,0x88a08930230c43f02c04,0x46c0d0bc4d0189222e26,0x80c0297b2d0823115853,0x4a12a224440c41cc6a36,0x13c080642b8d45e11934,0x1bb2e5344908a200a87f,0x1d08f44e1a200694da1a,0x8ed381b61e93a1d15120,0x490830933247628cf33e,0xe1f18cb2faa86c98010e,0xc03121c3e35d1a119db2,0x6906dcd8410287b49b3d,0x5c2de00cb5dff95ee802,0xb14c0144fbf4b3a4c50c,0x7928b992c428997cacc9,0x68f0a165ecc8858a1814,0x85c2664ff2fc458cd0f5,0xa165fc20b100014437a7,0x563f0e180d8d04fcc240,0xa9ff01b1943cbf11633,0xdf49d0c2934cbe6cdb05,0x1c6e009277aeb58247ce,0xb7af2560922fefa9136e,0x4bfe12211890f7f7d489],#[0x583c266b7f5c868c0144,0x234e8ff26bb11da25b7e,0xeb27e122467ff9a89913,0x1ab0134aea3e5609227f,0xc123ac1f582470ffd5a8,0x50dc01f02e2a4d1bc7ca,0x9fa4ef201343b67f88b0,0x3aa8f80808783fa70148,0x921fa991094ff8c08476,0x6f76e2f53221bef01c22,0x243ea611215bff900206,0xb60c99e9c1b1961e5204,0x98042173ff26000676fe,0x8099d3fb654000068a7d,0x8b9ff2a00003407f2ed5,0x67fca0228432fe40d611,0x3f3e0032e797a27c0067,0xfea032f3584197f50190,0x98111a5bfe1842066ee3,0xacfb74cc40d3df87f26e,0x9410001a33ff2600066a,0x3387f4e20804ce5cff,0x86143c7f580646f7f8b0,0xb496f6f200cfcf16236,0xd0f8e1fc6042e387f181,0x5e0c1c302191466c5b2e,0x2390dd5fdb8d40881a5,0xc0c9afe100472195e5c5,0x810bc279bf01010ddfec,0x3383e57798c08617df31,0xbcc2de0342d7fb7db110,0xb5ffe4143293f88f80d0],#[0x3f45c8011a29f957b110,0x1b1e3841f780f6c194bd,0x6f974b00086c6315d90a,0xdf64c000d1aee833410a,0xff784028dbeb0011f3fe,0xe28ac814343c5d2050b6,0xc89ff0a4ca9ff01b1961,0xe1098d9da2842ed6f048,0x2c00219471e0091e96b7,0x99f7db89350001aa9c1f,0x5bf0843ba1456d5f8a10,0x242851786de520a43dbb,0xd45e9facd4009a09c9b,0x71c4002417c76fb4c084,0x23317c76fa9c8000d5bc,0x7e109b5bc12337ff5595,0x8a118d05cb840b19a96b,0xd201c7cfd0006b4e7cf6,0x70b10c866e6c5feec48c,0xd332fbf049f010687a7e,0xe4ebc63b8490c4a0d397,0x26489f93df0a648bb815,0x968587f53840b430acc9,0xebe1863a044569e798dc,0xfed488cd31ff6b011159,0x466756eed928d0c904e9,0xe9f0e102466aafff7a02,0xd4d1fe54d2630234f6d4,0x2568666c6a49be914050,0x44d9aead48b1c7b1c486,0x49f37219d0abf718ac22,0xbe7088b9ff0c8209811a],#[0xf9ac30090c67fc1d4253,0xd0163487f596c0991a21,0xfce428402a213ffd1210,0xa802643d3cbc28654333,0xd12551cfe163253af262,0xc2c649c879ed125259b2,0x28da8bab9089f867321f,0xb9093dfb8514246fdc29,0x38bfdb1ca85004413e6e,0x7ea012085d03c9f05004,0xd10542cbeba930600870,0xf15c084860c7a4199907,0xd402410bb6e8988052d3,0xe381c085975173410a0f,0xfcbe1440d06feca8421b,0x1119f5b457e915a02b0,0xc57e9041a65fe546be14,0xa01a29ca87556c3573cb,0xffefc4b4034817ff7e25,0x44239bd78060087ef02,0x4f04c80437b0d9cd04c8,0xf541e7db32f40806867,0x7849e3aa100ac5f54202,0x7c890a0949e7eeba906,0x542fff97f7862521367e,0x7c21acb5f4e18121041a,0xdbd1428021eccc5793c3,0x4218489fd4620861249f,0x806817e85205859fd44,0x5be7d6ad4940d59d6294,0x3e41a650edffe204033a,0x4feab900848bbc92c9a2],#[0xc22ae8d5127f55c80424,0x710359b3f701a4199764,0xdc845d9c08abb261173d,0xfa35905349f25a159fa9,0x17a4010a29aafa190acd,0x101a2bf9ea4044106937,0xd963bbc5793074ff0f11,0xdc5e900429d9f8d84f5,0x1e29b7f9480d12e345a1,0x81a93f2fa95044840d6,0x605044840d59f80c820a,0x742f7fc3a0124468eff8,0x93a2d08a2784427cdc86,0xb2f3c25eff9658c08ce6,0x30103597c3c3a1041069,0x25927e19ccd5f2f0e861,0x40100d21597f9cac840d,0xafaa3112103557fbb7f8,0x2010edfed9cac840d15f,0x8dffd4b09119f5e19ec3,0x27a9271cf3436bc33b70,0x164eb78e79a18df1e27c,0x235db8676e175db8f13e,0x9d5f2410285d59c6be09,0xb8e1930533c7f394d829,0x1829a7bd3e3cbd09b1a1,0xec98823321ebfff0ac92,0xc4d05f3d43b44804d4cf,0x4dd5b0a54134371e8a18,0x3989a83ef2f96648124d,0x69490b989a43fd47c293,0xe7a8d0420fe0c522f7ff],#[0x985006707e8c95480087,0x200446b93a8d042c7ff0,0xcdf11bc004aa41f56794,0x806a0669f7ac400246ff,0xfac004747f928d042c7f,0xaf8008f5f82c14019e6f,0xe864347fce7d84633cfb,0x33a3f3e88080861480ab,0xdc7ab44824d37fc79020,0x4b204067efed82c22068,0x202237ea3fda102447f,0xff8ae509c1249afea422,0x37e0061810f5f987432a,0xfdf0332efebbdaac1239,0x9f16213907eca11810f5,0x440d51ede106422069e6,0x777e106110b1ecbc8218,0x81142302233f0eda2606,0xcc4b42f3e1c0110befe1,0xd1e0101106f8b488427e,0x2044d9f13200d4a4476f,0xb71f0e86537f8ec81304,0xbfc0ccb51ff326902034,0xd41fcbf0cc400c606b6e,0xd8019a3f97f2e0944080,0x8637e0a4330010e5c3f8,0x163b71b00331bd788400,0xbfbd7e6006737fa26002,0x97d7ea6528e95f9801a1,0x2bef09c14d7e42052668,0x4bf2569157af18e00049,0x226bfd170ac0000d],#[0x93bcdbe80154bcdfe068,0xd72d000481106fbbd002,0xd380b32f7a6e42401a39,0x6d4133720fb1140021eb,0x6b4f086a4540d15ed,0xa390001a43fffa10ca24,0xa45bf65e6180541fff94,0x68cf5fcf93040344f5d8,0x87afcc32996be0a1c600,0xba1b300097c9bf061800,0x317fcf8609400069df5f,0x410bbd525691f71b812,0x7fcfa75040141a899be4,0x4f430ff9f4ea08900350,0xd61ff3e181100141a95,0x60c52387fcfe0c010240,0x808044eaff58800480bd,0xeda8173003563cbca041,0x98201a77f4b102470ff9,0x86620630035c7f4ff0d8,0x6067eb71e5c60670fe5f,0x7fa611e5c6068eb71e5c,0xe593033a6014f840339,0x5930343610e593033b61,0x5fd48440404457fa605e,0x88c087e75ab930c087d7,0x8687e32ce010dceb262,0x33060dfc032fbe320c8,0x67c860dfc03377f65d78,0x3720f911042a7a64b200,0x9f907c888216bda8d803,0xcd97a3600ccda65f5801],#[0xe7ff514244688eb3404c,0x1714891bae5fd183124b,0x813135f4b5e12119d7eb,0xbc411f66135e17f679ac,0x672fb4bd26589a2bd9,0x108bf24616024172f0a5,0x6e042467f384cacfd9aa,0x7d0003337dff001955fc,0x4e19a135f013c0404354,0xd2bd400206a35ded074f,0x8440d2dff8c08cadff97,0x160d5fd8904a4ff40d7a,0x342d3b70120854fb5b99,0x86993044c01a95dc09e0,0x6f7d9190d185fcdf6e64,0x469ee3fd228008d05f,0x950b87d8019a3f5ef814,0xf541b603fe019721bd89,0x2524bf28241034020,0xd4fd016400cf3df5f8e3,0x889a4778f8fc5f6dc804,0x75ee3880025c371d7b35,0x80479afff1c6000499ad,0x195a45361e7a050bd46f,0x24185f7c4c65e5f136f,0xc68b426585451af044d6,0x2244d01ce7af40c89a25,0xd092f4e9040cf5fd5df,0xd12e882043a74b578f80,0x1a63f52c7a424206a87,0xe9607f4a85ef26963a58,0xefb12c4d09ff3cb09119],#[0xfae09267badf00120bed,0xe00244ddd7e002449cdd,0x2222afdae0024cddd7,0xa8d121c01989fdc6c73e,0xd7f28006599737f5d904,0xe6ff26004aaf78b00033,0x4a20890f097f80910bb2,0xcf9220684fc339929ff0,0x910e6e9f34048860fe96,0x6bfe4a90919f5cbca080,0x3cf2678fe7d40a9091a,0xcc6fd9221dc0087cfcd2,0x9f9f25e600cf9c3ee600,0x55ac000359979b798055,0xfc68405ce803547fb068,0x263f0010e1db5109267a,0x21dc047de43b808e6fd9,0xc548a819d7c84660246f,0xfe0c522867cc300a7bff,0x3458e79c4d67367130,0x33cfbf55e0024675ac0c,0x9fd70a612407eedf8436,0xf5d21b8033c19f05047d,0x21211a67a7f5380120b,0x338ff4780384915f2f0c,0xa0ed6e86143373bebb01,0xfb64492450e4e69bb050,0x4285cfbc8be412804d54,0x143067dfde993373003e,0xd2f693400a1a5db94c0,0x6afbc01b199df8573c85,0x6f9b4c04d18e9c63c428],#[0xfdeb0048f55fc0a4ca1f,0x6214348c0ff45a7e1446,0xd03fd16983828817d913,0xed8cbeb1336efd93c247,0x67ccc34f265ddfb27848,0x8285c8fe13221483f562,0xa44ced9de384cd4ff88d,0x709973bd8e133078687f,0x65c70cdcc68400a273bc,0x628a139a29e284cec7c2,0x18910efe4407d110c6f8,0x1c794c01431bf9081d53,0x93b7bc5090e3ca600a1a,0x410a288c7e5c48c59143,0xfe2849ce005108fec168,0xee18a286c6fc62c04ce4,0xa1bb9437f390268432,0x863321c0aaf48797b79c,0xd58270efa435990e39e6,0x867295e158f8612c64e8,0x370a258c9d1abdc1a6f4,0xa1cdfd54a688a1a9a585,0xd5d8563e199fe1542638,0x67b0c8a1b3ad6aea4cfa,0x14d4dc2879ccdbc99b5f,0xc4024234819643d18594,0xebcbc22c004d29fd797,0xb001346619fe11600269,0x99833af305267af2f80,0xc2476db9e5913306bc68,0xcbc658fa1004d2351eeb,0x9e5b689a79c59e0c30a1],#[0x5135da51b793337b611,0x11fe7024897a11963420,0xd2c4ce3fbeb11a8124ad,0x28787c60e8a90c19f7b7,0x83f183b0343736f68da8,0x7e842644434c5c8c0143,0x4939fe9301004d18f6c4,0x473ef9309226b8d77af0,0xab918109259ed23b8a14,0x454869790306802875ff,0x36141f0c590621bdc317,0xfc75e5c74908d286592f,0x3fae12574bb4b8f24ce1,0xb26680d170c099e765c8,0x1933c730b1464cf98681,0x42e7cea2e3c934467835,0xdead5c1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x281e1f0b19a40000000,0xc213199e76a8fb090d2a,0xd486ce496fee441652fb,0x8548d7bd792b049117ff,0x2c1cc191313ffe375664,0x43fbcc7b15362508ffce,0xac12457fff550648548d],#[0x6de3e631c153625ef5e4,0x717a98c086b717a98c08,0xa0d1afec8775308088b,0x810edfd2941943f92631,0xaa798f5a11b9ffe50113,0x575100d6d8fa4aa92201,0x4bd30c4033f7ebfd273a,0x1a3df03423a87c4a0432,0xb034b3f83bcc604307b5,0x7b723db3034d7839afdc,0xfc219e29c69fb3033878,0x551a9d136b036772d0ba,0x1b3b0d1a9ebe83467da,0xa16866af5dbdb03f1441,0x3377dbfcaee881a13dbc,0x1c1b2ffd18ccda7f2950,0xfb8b84128df62ddf3a02,0x7f2559afb860448c7fc1,0x868adaa3e9e490606ac,0x58edcd7d068adaa3e5f5,0xd040700c43d3e8203406,0x8335d7fcc204d3b7a0a0,0xb5d881035610279f8c48,0x3cbdb1716b325a203996,0xc3118408897362d468b4,0xb03628f0fbfb048141c5,0x940c887af5e39c67c208,0x7fe16caee881a51fc99b,0xecc0ce3fe2e772348256,0x881b99f8af04354635df,0xd931034cfae4d7793412,0xa1f70db5224680fd135],#[0xc0ca9fe2cc0cb0b70711,0x80d0edfc32c0ca9f8ec,0x75e0e9a0c22440bf214e,0xfb00086ce1cf60f06677,0x537dadca274506957e19,0xb43819fbd7c34cf05103,0x665ffdf34870104a0f6a,0x8226782881acbff21624,0x3427f544cc2881a53f8,0x3ecbef1499e35f2c32e0,0x84e9022038bfc561a1a2,0xb0008782bc508487d307,0x3996215dae206ac74e60,0xb9f0019d3f885661440d,0xf8361836f54d32668d7e,0x4a43599f855090dad99e,0x6874ff1f49c8cd4fca94,0x9ec8072e4a67e4e03214,0x5961f37ea3406088c8a5,0x51a1bbb70d4ccc9f8323,0x678b9131ce2971fe1c04,0xfc8fdc894765ee4493a6,0xde2e47ee4632b2e95c43,0x5724a40e57504b48df7a,0xe330201c96ba86d164c5,0x89564687e0f9db665d5a,0x824b47a5fc0a32554eed,0xbd355997440808d93c7f,0x208964f920d0231a1c,0xa343cf5ce393238c67f2,0x5e9d3895a668a7d34602,0xfe8d6a59a13a76074ccf],#[0xab932b9ff53b4b33d361,0xee7a9757258f3a5cdd4b,0x43428bed4488acd0e3e9,0x999d3e16e6b733db968f,0xcfe47a13844a2f97ba62,0xd32a1f7fa4f44e11297,0x991759ec33b2a5fbd5d0,0xc8520ca885e59bb2d6ca,0xf8b36182940446d37fd8,0xc56b03e1f8aee2407ffc,0x5506da9a3b4e560a44a4,0xc552ee398cb5b2a527fb,0x3d3fe34063550f172345,0xfd0a60b4568ab07920bb,0x80335349f2fc284495c7,0x7e687f9606c8965faf62,0xedf691226e6ede80912e,0xf500689455a27ce669cf,0x971253367f5acb471c53,0x941ffa7e40ea11a0f967,0xaa7f793426fd0e703218,0xac9281a52134f3aca406,0x9dfc9aa8a2021cbb7f78,0x2e340346fd1a9f535812,0x13f8ae585c0835437ffc,0xd0dfebca5d1432901ad,0xd2d9830042853b7f8494,0x809bc20d0afd1c151010,0xc20d1997ff03680676fb,0xba668bd480d7dfd72820,0xfb521e8137b0835b7f6d,0x92e52034cf7ee1450901],#[0x69b6ff48372241aa88bf,0x8a0a86aff8ae1822841a,0xd9fd7c9349a406935bab,0xa6f4150d0fa0793e5010,0x4927d679d6172901b01a,0x4206d97e958c9d89404,0x4fc58c2597ca17f09ac4,0x7b9751018d00db227e8d,0xf12dda942e1035a7dbff,0x610672dabf85c68069af,0x7d42e4ffc1104cace3e0,0x288089ae54fc4620689e,0x68c92790111027ed26aa,0x873f1ff9c09b2813110d,0xbf6942810edfdf849019,0x520d0da7afc9524cd129,0x33a08d4040e74dc7f36e,0x9d2040d49ff032a633b0,0xbc7cb1ee8040d39b7732,0xb049019ddfc9a8120218,0x7535c25a7f0890654edf,0x4341445bd541a34c6765,0x3fd0103810d2ff4580e0,0xc72187566687c079342f,0x6d15f48347672d7b0833,0x6008827f01532a86ae7d,0xeb12ac21c1116f3cba82,0x990086078be0264021f4,0xe3874c14f5e806c87cbd,0xd51f7f5d4b200806aecf,0x900892fc6dfb37968100,0xe7de99008767c6957468],#[0x450087623cf3ee008737,0x438b83f114021bdf7d1c,0x9e7dec01132d1e79f430,0xad00866c07fc032c3d3b,0xda03467ee0348336a0d2,0x41a0373cd19294db4f75,0x739b40841393f8ae5818,0x676f1c634040d1bf487,0xdf951882184a0e9cba6c,0x339f629d05434aec9846,0xed6b6033caf497b60681,0x4203847e2518c08d11b7,0x80d9dfb6a42d8e62ef0,0x1141035f7ed485a19761,0xadf974d80cd1fff046c2,0x686ffb6c0656ffbcdcc,0x2cfeba84c23b7c10f1c1,0xe5eb151c1068d62f1434,0x433f50068913faea1308,0x441263fa53c26f7840d,0x47dae2ab90084a9d7df4,0xdfd6e239a01ad7151e28,0x76fb9cd24533403757ae,0xdfb5216c55b60e06ccfd,0x6206b5e3ebaf5432095,0xbfe808824a65ffc06a52,0x82417fedca40c40d023e,0x5f8aae4021297ebfe00c,0x1049aede4deaacd00d43,0x27f55c804244d7fd4c7d,0xbeeaa190d12e9d60541a,0x7ae206b357f04940cc29],#[0x51af8999c3f527f1333e,0xb2c0a3cdd7c008b01a5b,0x315812d7fcc42a5d955b,0xabafc7e21020972946f5,0x1e5764c2357dbb7c4ccc,0x7fd3a8a5033a11fd4e79,0x29bf5d25010f7731e131,0xf8660340ca51bd4d7095,0x88a4b351b7725a131249,0x8944dfe3332a6bfff83c,0x79d60610675fc66a80a1,0x69efda90b635d87035e,0xc832081a93f2fa1c242,0xfef5e2a8905040d85c78,0x6b2119d67c77ca8824d7,0x73813b386f20819ebfc5,0x696120d2bfe6329640ea,0x9b2bf7c4690914de7c7,0xbadc104b98ca59d9568f,0x7329ace1c916865ebbf1,0xaf08912c5f956850fdd3,0x59c0458bcac40d53f91b,0x9541034c62a32fc0c40d,0xbe786dec2840d25d77c,0xc36f0a2334af9fa14212,0xcf2d1e0a840e9f0a9973,0x3d96e080d09f4e838e80,0x434242e5f19c06888fc,0x4453a087f68777aece24,0x5743c0888ce8b2dd819e,0x344473d9503e821a44e7,0xc195cd01a2212811527e],#[0xd628757eee2b204333eb,0x907ff0cc9421a122728f,0xed5ff2c1246d8e6b5824,0xc9829a03fbba6130134,0x1ff5ad71b6128a9a9847,0xa675fc9f8f4801225cf,0xee57f8a0048985fea9e6,0xd5439bfb540d3aa87dc7,0x43b7e6b714cd4fd98018,0x75c878c4d10ed66388a,0x287dff80ab18281262,0x5738c56a8869b4fed645,0x2a4a7c3b24a2021f7dc,0xa67ceb9ffe880671be23,0x5a7f093810ad1fa7f2a8,0x4069b7cf09421663c684,0xdaffe2e13387caffcc4a,0x100d4197e98341009a5b,0xbf6100a8a6aafa47c019,0xfe31214c3d9141adbff7,0x318265bc1d80c00c0880,0x7fe248433ce8feb11d5,0x1a0804d0dcfcb540833e,0x14cddfdc1ac04ce9ffdc,0x6d3f802241334d73fe19,0x3fe8843303e8f2158286,0x440c995f879498099dbc,0x7de7918868fb43fce3a9,0xfd80a099a2b1fa7828a6,0xc460548d87f80363336d,0xff2c123f7fe2b810cca7,0x81499ebf05a8006689b],#[0x8fbe75675ba2c2995f88,0x7c93c94c202226ffcb04,0x97b4affd76d3188506bd,0x37f049529021c3f95a81,0xf39b424402022c567a44,0xf3f7d578700101a9da75,0x491fde349af4270dc13,0x7d7e60190d1bf58ac627,0x440cd1bfadbdaac12539,0x5c84f6333021c3f6d7f7,0x989510a9ff9188c101a2,0x406a2d3fdb88f033413d,0x87dc29a0ae3fc770d0e0,0x6410570c9e140988873f,0x187fd076903345fd7fbe,0x2e10643457d601c080d1,0x2fb608bde9ada2867af8,0x40442e31bf74dfc63026,0x6806dbb34203193a7540,0x4c8660406ceb71e10c60,0x219b2f38e040680c7f5c,0x4336df44832c38be4660,0x91128ec080d94fb0c970,0xc1ff5fea18d1209750c7,0xd8dfe14feb858660406,0x98087efc82090b43f028,0xffe6d49a2412e1c50f01,0x9245ffcdccb6f3301093,0xe981d810e3e7aff90128,0x4d2dbe3d8001081aa1f2,0x2460943c7b9e9fe89090,0x378c7fb558240f8ee7ae],#[0x7c9819c9fc2080421022,0xb07b520a81b18224a50a,0xce060701bc4e2d6f8f04,0x80c0db9f0c714b72596c,0x7a0683667ebc73cc7981,0xff3c995055dfa41216a5,0x69b7c34e3f401110361e,0x4440d1bdf99fd801209,0xcdeebb41881a3bff1e2,0xb57e42122145351f0219,0x80cf5f2f8f9c30020406,0xfff70068904a8d7e71e8,0x1001035a60df000c8681,0x64c2bf440ccf9faf1b00,0x3db6f9035953dbf206e6,0x68191f72947e53024081,0x509fff9885a241287f8,0x3192a7ff94aa875b86c2,0x75fafb080412e657d48c,0x86617073d892440344ed,0xcf9fe1db4a19b3fdb1cc,0x56f54991470ff6c6200c,0x7ac1a147cf2b92c060c3,0xcc4a03433aefd8cd10a1,0xef450ce81d7b8643393e,0xfff0f223038101b7bb75,0x910dcfb618c44317d35,0x59780bb9d9010eef81db,0x740e3148111af66e7668,0x390218d773cea58a1d5e,0x627c101b9800873026ff,0xc4d44c0043dbcf3ee008],#[0x7977142b38fd130a149f,0xfcc4cfc355eee004333e,0x259a5a774393431474a,0x4244ce3d99f191b3d7c8,0xe3cee812082206ccf9ce,0xc8480354ff938c680488,0x7076ab7602143b7ee4cd,0xf978f620344ff9b9bc04,0x985fb7f89412081a635,0x72004cfbfff4ab911c00,0x92673bcdfd0029effa4,0x7fb72c1438c00d5de9b9,0xec9c085763ab6414143c,0xadfff03d4801881a8df,0x3c0c048000db6fe98d41,0xc02adec6612307ffe40,0x1067af82871899cfb373,0x90b62de1141b23e9c6a8,0xd00673bcdbcc029efd20,0xcc6a4349d708348529d7,0x8880006cbfef78fa4402,0xfc19b4b50009b1daf154,0x60001a0efcde60142f9f,0xdeae13253ab94895f8cb,0xcffb29550f2d14b0814c,0xeafd08a667ae53aa3256,0x850cde0ffc7141401a8d,0xff4aa2024103543d1244,0x71180001acde3c099296,0x209a31bc79d08a73c7a5,0x7091e5715a912a2943f1,0x81c00a1c7e144d177708],#[0xc1a24e9fc6c409221f77,0xa8fb9e4a21244febc70,0xb82a28789f9228dd73ee,0x7d9dea80d4363c09187f,0xc08647dd4701010d52a0,0x91792046c25a1fd361e0,0xfc5819ebd625f20f0406,0x21c8a9c18fe80d055db0,0x623f02206817920472a0,0x782557fe4c0bcba0680b,0x6c47e0440d30785d6b7c,0x5021da9c1cb7c41a13e9,0xe6b0cc2080d0af2402c5,0x9b0aa043abf8cf254043,0x8090d4e0878e506897f1,0x5369e51b00671ce7cf37,0xb790e2a97a2e3be158aa,0x6c68fc70b116c4d32bc3,0x72a448edbc2b43244b09,0x92875d97e341894bed4,0x8bd8a3088d3be63a5dd4,0x2cd2312821eb1434c0fd,0x3a65fd652033d7b575e1,0xfcaf514ce0a3ca6d0804,0x4101a47ca7d4d60498ef,0x31cb09a5a0cd2da739a7,0x4034f3d5c16730c90a24,0xd7f8df14cc5e09e5f38c,0xff1847efea83c44a0d19,0x9a6385c354c101a47816,0x15750835052dd093cc1,0x130a1d7e48c2d23e778a],#[0xe764a6d080438be8a3f8,0xaae2506a2d8be57a8a68,0xfe495d26806044c54649,0x9210d09e2c59a1420d3c,0xb7beab042e1035657cee,0x50267e76d3b9cc866144,0x6791bc183e0a86ae58af,0xf895400335c7a167da52,0x931b6d25ecd913457c8c,0x782843ef5c5efc0f3551,0xba438f4930406bd7f0d9,0x9e1c08cd6c90101125fc,0xcb649a50d0fdff1041b9,0x628923eff2fa2708940f,0xce982e25f30671d72fe2,0x3f21c2182647f49f8488,0xb072243fbec1287ff35f,0xc0d59faf1cc2a49e6421,0x35d0881abbfee1446af3,0x8bac1afec51273fc9fd0,0x448afe1f1a60f588440d,0xfd26531424699959ff2a,0x4f01a1ebffca4cf8467a,0xd31b5bf6b6033a2af81c,0xfc38c08d2d8e832e0080,0x8eb5c2c81d4e7933bb1e,0x27f923ffe4a3d08c8336,0x7d8019898f9a9ca20344,0x84f5f4cb98c3ec4cb5e0,0x12081adbf006ff880ced,0xb4e81b00676f2e96d794,0x25ef1e57e2fbb800137],#[0xabae1034cf7d7b8e300,0xdff70a415712e06c0fd9,0xd464cba275aea04929ff,0xd55c29fa09c170d205,0x27f62004b8ff00f62100,0xcbebc19ec9009aa7fe81,0x7c15e1004d3a27fb1091,0x79ec50b8f11b1109199,0x2e7e60a4cc6c3cf62726,0x41860026aefca1004e67,0xd440a1bd525691fb8ffc,0x8c70092173f321747921,0xb312034427e920965df5,0x9021cbb4ea326627f9c8,0xa6be64e9040d6ee0d7dc,0x2227bebdc702004acfcb,0xb17d4099c1f566d6dc90,0xfd50249cc2eb84846828,0xa4222d0f53b2043ccaeb,0x6884f974aac04d28fa9d,0xa624055225bf2a73ce20,0xd39ca94e122068b7572,0x6fd45041a031ca98a503,0x2213fd259135809a630f,0x328e206b47ce3966e680,0xcdb48ec4994894f8dd3b,0x2a3fa7911295e3881b2d,0xe8d430d23efe6cdf1a41,0x915f548b75840d214b74,0xe9f269784cd157ed704,0xacf145521d116cf00c81,0x7df5f5c0850ef970981a],#[0xf7bfa9784cf6c5f04c21,0x93512ee99ba6728e46be,0x1a77fadf5cc676575a02,0xdcc260269ef5962dd988,0x134caffc128b2897de3,0x6e81e41246befde3da93,0xb59d42ba1851454b34a6,0x7acb10e900069dff3f16,0xa084c08827e19114a437,0xb78520c520b035836d39,0x51112e82cfa309810e9f,0x152a42206b64c4fc2889,0xe69d7b1482c0d49fc7d2,0x1c30ffea585200891adb,0xcc9521235abe90c50112,0x734da38c8891a5bff386,0x828efaf103faf9012413,0x6b9faffe20a9547e90e4,0x7016289718a8fa310620,0x15617000910382ccd7fe,0xea3a172a081aa3f12846,0x9cd0428852c93f0ce662,0x94ae8c08a51cc6d8c51e,0x218dffe807094a208915,0xfcd20bf0506896acd682,0xe96b410ecf9e0ac8a1a3,0x720446bd9d2d8c2ab369,0x34e0ab1444473765279e,0x12573771f38d2004473b,0x96cb75840d23f1136702,0xbdbfd3d10f311c40d95e,0x1979ef300a86721f011d],#[0x597f1945c330ca8f808d,0xf3fcc029d8f8b7381002,0x4c1f8fc44dec4009662,0x7d8848ebfe7e842f1620,0x51c40d465f9f9805022,0x19a475f215269213d51f,0x3627c768e3a20685f21,0x68410f5fd3a278a90031,0xee0e671215236e3cf740,0xf82478c33e6180565ffc,0x46b9fd7ed50641287e52,0x5a8b0a8d7b7e9b4120e2,0xcc02a9fff3ea152ad3a,0xbf6c260bd60c523dfba7,0x50a3e023739d6282218b,0x348206bc72ec40724088,0x1101c0003547ff47d921,0x8e3d7bf74fa824c7ffe4,0x47f27170504ac3fb1a84,0x8420b448fe938388012e,0xad3bffa76c4348ef6cc,0x5bf954d3268ccc343e77,0x70898688ce77803633d5,0x92293e5081499c1d38a,0xb1216b639995a56bddae,0x9f5fd48739272b946c99,0xde5e08cd25b3bd8e1338,0xccf7c1b0d9dec7099a77,0xe5d3c9c8d36671cd84d6,0x50ede25a5a7856822fe9,0xd80fd2c9a55e4bb44314,0xb4a3fc24c0201438143e],#[0x8c6a105a4bfdb7852420,0xda6438151c14882ff79,0x8afa70e01a5f70ec5645,0x455c2c50f6fe961458a1,0x9a9afbe255000cd94fc1,0x654a110236430ef60a17,0x35efee9020c4920febef,0x60026c0ebef65883001,0x9bbd525691f308ffc416,0x804923c0fefbeb9a1008,0x133e3154dd8286dfdd23,0xdf332822843f76da1e9e,0xce9ff978ca85f42009af,0x5ec024026e8a37f11f48,0x5b130582874ffc13acef,0x68687cbc6ded24026a97,0x9e404804d85fa6cf5402,0x8cb1e04804d6d0f978ca,0xd2d55eda78784d0d0f97,0xf6009678fcbf4d11f404,0x168698e94d6a499f350,0xa24418c841700f5cbc82,0x7f9fd141a24a7b75f0aa,0x9007ee52a8e909c58542,0x16a0bd60c523ee792884,0x49001450797e8279da84,0x386b3ec9b19ed0e597c1,0x376b06aa1b031e0a1493,0x2971d7c3bd82854f8871,0x25471dbaf1542919b88b,0x9ea53ac2a332b5f82306,0x2b471d004d43d7e5a485],#[0x28a3702b2822843f75,0x3558891435a1cb4913c2,0x87cc21b9fc82a4450d4f,0xb1030963225da6c301d0,0x2dd052eb010db26e19db,0x9c2ce0f34b249dc37583,0x6662fa153ec33a063d2a,0x760fb1538d9810be1f5b,0x2b1360d18ff32328c808,0xd41a01fe7a0c021893f4,0x7f39ae468110dc9be716,0x8c6810e8d5f036810ca8,0x1adc1c770612088471db,0x3821d9282149f19b6d02,0x822b008937f37c021e04,0x17822f851a08717830f1,0x8d82f043507d338f4067,0x2022093f46f2dc19c10e,0x64424a0089971d7d8ae1,0x91e5ac9949802221d7f5,0xab1153443d3066f05ee1,0x9421a9833782f70d4c1,0x30e8d5ee01b90ca57abf,0xa21a3560b2409f98ac01,0xf943423cc08886e77d59,0x9119a1844f2c0b2c3035,0x2a43cdc0c0810a597e66,0xfb283fcf7909ee49685,0xe1592e1821ba43e7d9a,0x1830c4ead9ef21712655,0xddaf32164d9fcafd598,0x1a0d0f8c089a55aa1503],#[0x21d3b7c03346d9fcafd,0xf3e69b6c19b1fe646759,0x7e18ad021e25ce93c419,0x260439b969d134421d18,0x12fccd25ad043db4e54c,0xe89461a1d7f2624d3811,0x4c3009ffbda770c067f6,0xd47eec4d6e1996fe2f80]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x1000e05080809040200,0x2000000080c070a10,0x101003b000000030a02,0x1c0e02130300000301,0x6010c0a1b000b070a03,0x2020113160203090101,0x38100101030a0e190c01,0xc0818061f06081407,0x2040d0103053d0001,0x90105010d0f02010705,0x706000110011d00040a,0x2010e01030401040200,0x51200000d05060f00,0x3150304040000000c04,0xb000a261a0003000802,0x103010a03121909010b,0xd00030a000f0005,0x3010102010000000101,0xf000e00050901031a34,0x5020801121b20060510,0x120b0032000800050d,0x2731e010106050a00,0x130000030005050203,0x260502010001030007,0x119020006260d1410,0x130f0b061b00050802,0x40f04221d0b000c0003,0x1050f111d1e01010211,0x2240000040100070010,0x1b00110e210514040800,0x8130000000413004809,0xf0106013a0326080802],#[0x410020a074302020b05,0x19040700000139080000,0xe120e06010104060000,0x10e13001722000b082d,0x200030c0e110d090b05,0x3360a0604015f030302,0x150126000b3602050605,0x40f1b0302050401051b,0x80008000600012e1629,0xe030a0b070b02051d05,0x62a130b092513052229,0x70106020814091120,0xf020000002106170406,0x3040008020101080102,0x220a100909060b000102,0x53e18020c000409050d,0x110b0001144200050107,0x2060003141f00020000,0x901044d030000290413,0x8080004010903054303,0x70b00040002030302,0xe010405001a08011600,0x1010839013e020b0701,0x40d3137100149070300,0x50002030402030e2e03,0x20d0400140001020705,0x1000203170005013308,0x5020a150c190700040b,0x30821050347021f021d,0xf07000b042302000a10,0x1f01040002022d020601,0x2005f120d1400031911],#[0x10303160f000b021202,0x1f0006140103008c0201,0x1000002062a011d1c01,0x600090c0500050f0a06,0x3300011806062f07001f,0x2b0b05000c0908050103,0x10207122f150d121201,0xc13050303091f611615,0x4020a06142123040901,0x4a1e4d0b08030f100526,0x2090003000110020b1b,0x10301010604101e1702,0x1040203124201060001,0x52400103041b010016,0x1007080d08030300338b,0xb80004e3a54a1c1f02d8,0x71000033cfc2c60000c1,0x67b8a3a71c8e04600004,0x424a000000000001260,0x40f70b1c00,0xde416792c3000084980,0x22026e648e0f48e08000,0x2a88fc000000011d823b,0xe9f11c370ae00fb0001a,0x4a4c04763c9018a,0x27a22000000000946c00,0x273978c00000006cb71,0xbe33148d287bf2768000,0x73400060f1c7831cc01e,0xcff119f9ad3c4a463fe0,0xec635c18e96134710000,0xca8c81c128ac2e00012e],#[0x800720eb86000018,0xa816e20de00001d48000,0xd3c41566d000001a4e1a,0x30659c5a0c10000e8ad1,0xfa8f4844c041237b0000,0xebc81606acabe180043,0xcc84190629a000070c42,0x860050000d763147f19d,0x8c800026280e541ed134,0x61720000000000001649,0x8d8f5077c8f3a087284f,0x8c4000425e0000208b3f,0xaa1c8e911bd667b00011,0xaa186f1f09a7d05f8000,0x1605d14180a3a3,0x1c72a98a000000000,0x7458507000030640000,0x8000068d98c0321a400,0x673b00001,0xbe7cc4e46000000046f1,0x822a12800000001a5925,0x4c0417f5bea82dc00019,0xa0000064040d80006302,0x92e3069800d12613c0c3,0xc40e000000028530ddad,0x15d00000000,0x10b5c00,0xeaee925219986bb20c60,0x20ed293fcafdbc20000,0x378171000000018d2000,0xe0e60001051e03007988,0xc8000000000014490000],#[0x787e09fd6a3b0,0xc2fe00030c1800000000,0x6e682cb96a40000640,0xf35108416de9319e3400,0x51a1c628b82e0990a81d,0xc818500011759c21968d,0x13400010af100e000128,0xfd1c8851b3a74b88520,0xb4031caac00032fd0000,0x12f72009cac4000200,0x344e85f6c2fa0,0x78000000000000000000,0x32140b8000cba3d0a41c,0x624400005ce8b19a,0xf000091628948285e882,0x13000061258c9e98883f,0xcf0800000001131e,0xef756241322053c,0x89105743187e0000000,0x193e6c20045071ee9,0x609700008d980000000,0x120ce2e323a219f400,0xc8ab877ea420000d0360,0x476d889800000000000,0xdb3aeda722000141b400,0xed02cb170403da9,0xe8430e16cd184000287e,0x87d3b4c725eff801a337,0x51d785e611aa71800579,0x88598aff556c73b5b401,0xfa52d7018ba90b11cf13,0x517e000331b800000011],#[0xae66183620002c2122c5,0xd28ac440d18b240da939,0xc16b2287a36004e00011,0xd20d30708000000065c5,0xb96025800082498cca1f,0x5198000000022cb00260,0xba12eb1f69b66361c29f,0x3d198242600005137a4,0xd2c8000000027fae,0xcb66a193b9260fa,0xc085e3d000,0x49a00003394744700000,0x632b42568996a3e08c4,0x6ca02527e500005b7400,0x86b40000394c12910b49,0x3268d0702a3040f1d629,0x13e300000810117b04,0x243d0938000780ec2f80,0x14286ca417e63392425,0xb581f28000000011ac00,0x8009124000066af00010,0xcd84deca2e367075e569,0x6039097f58d531,0xa0f4e1239b0800000000,0xc8000000000000000000,0x294000446800000000c1,0x1886fb01800083720,0x22434ab1ee26400024d6,0x1384e262031391e486,0xd0152ed05048be60,0x4709a0001a0ff3c98887,0x33c6207e219400023b],#[0x1a096c82a5ef506a0,0x808c900000d491aba1fa,0xd9c0000000c78000000b,0x4358000000020b100001,0xab7ff000112d62b250cf,0x32ff8145c0c6000314,0xd1491ce0000026b00000,0x80000001c4bb3770000,0x9931a660800000838136,0xaffa00b23f0c6e000009,0x20000a05558abac38011,0x20d0055b0ee6a2,0xa406000310e80004bd60,0x414fe0d2499c0000000,0xa231d1a060e84855c400,0x366000000017e547000,0xd002f849fdf691b58000,0x3039a82c10958e7401,0xc078000000000db71f40,0x48000e79600000b10000,0x1bec80005208000007,0x18350154800047600,0x1bc007c369,0x15c00061d405ff212400,0xcd520000000480400011,0x1577988634f1c0000000,0x440bb6e0748f7806ab36,0xc1d023de410e68945f6d,0x4a5bc0001daed859f73b,0x3bb6368bc42582f832,0x85680000000452a10060,0xf341e0000d25400003e3],#[0xeb400021fb6ed64ba3b7,0x181da993a57d8b5b8,0x70000708f91bf2a9a4a8,0x42ac8000813709b5a4,0x98e29da05b00000a,0x7e39500018a94a2d0000,0xe553a085c2f08c60762a,0x8be8076d13fc5decac01,0x24561cc6cd3f3293f0a8,0x21fba650a9505c028b0f,0xca1922eb071b8c342a58,0x2a48c027e0a9800026dc,0x96f1f6627927f1627f8a,0xf1858cd800066500d5b8,0xe82dc4a988c31b4134d,0x24415708a3c5954bfec8,0x80d62225ae2207949670,0x484ab09261d1f44be44b,0x44f780c847b2a2,0x53da33aaefb49a4a580,0x20000a62c847c0002885,0x453ee20cd83609a6134,0x4e49cada1f217e4a6de,0x4f07fc4f600000006552,0x2d6367c1a66890000326,0x8f31e1410cc065db0a5e,0x93600000000,0x33c40774308000000,0xa5a93ae273000000000,0x789038ff2d4700002755,0xae46ae75444afc2f626,0x18b3408f71c2e],#[0x42f2a324e280006451,0x27000004d20000915800,0x1056000044c350e74,0x45c6c733083c0000658,0x343968c614e000,0xe4b7d6bd21b65bda8a80,0x30000ed8000033a98072,0x19dec13,0x91eb13340002458ccae0,0xc00008cee0a3408de361,0x37000036bf8a5e0478b9,0xcd9c0000000407aee128,0x2b085f400000006626,0xae000062dd00004f2000,0xcf820ac7b0dc38600001,0x9b489aa2617,0x92570a7c02e889000,0xcd2a219e24140be0,0x8d0d3c88c1ee614cf63f,0x89512e800000c39cfb1b,0x4dead2091e2182681df5,0xd1801467e891c3d166b1,0x2bc2b2e22103984c83c1,0xc192985a85e102d80ad0,0x9421fa80fcdc40e247fa,0x4344606a7eb93e035,0x4576000216311fd489a0,0xc13536a348b7d0818000,0x984000000087bc8f4a9b,0xca27a31e42b8307806a4,0x2396cc0a578b3b7234e,0x2af06f800000019e6400],#[0x8bb8000000048cd11f32,0x90000d0dc000284f0000,0xcb0168818703e6000200,0xe93d0284000684300008,0xc000001c551a4406e59a,0x3373c01c8f50000130,0x4c420003473a13500000,0x38000cc5a014d2088000,0x1a0b2867ccd5d02886,0x116b8ba328be593c0ba0,0x200002f36023b4010856,0xfadbe527aee0446036c2,0x1147b3af604c00018,0x4285000152ec0000000,0x3c0ca143ceca000000,0x8d6a0001426421800000,0x7342d0148a2439fc05c,0x1f3ab780000000e34400,0xa64254a52bb0000ca64a,0xf4150c4f820c04720000,0x44c170800042ed170f9a,0xa17ecd4800068d700010,0xb0000d01600000005747,0x3ee2bba65f00001b1b9f,0x91d71f4b70be086d,0x8a5fe000013cc0367441,0xfee10f253921910e992f,0x60f39d0909e636f0806c,0x5c3e887be95d533287d4,0xb90bcc665e0fc9d62804,0xc3a600022da9288c3100,0x489a00019c072ac05bb],#[0x3c000018368a60000000,0x83445013415b3d5ef5aa,0xe44c808429641bcf4414,0x13800043830c951a38b7,0x31a1d9905862f54e001,0x1a329287e8f86b5d22ea,0x2a4a40b4d0ee9388ae,0x685d95129d8c6c4e7a00,0x38ccb21cbe1620000,0x10fb01cb0fa296a000,0x37160873a4800000000,0x1e77f000000032b82208,0x30a0a39a8e5c911c81,0x88f991feb3de0cb0e620,0x58233482422edc5088a5,0xb243ace6f44c39087214,0x84891c7a21421c5884f4,0xa7b5603461041d7e533,0xd753840668c775121927,0x8a139f3825c800042101,0x2057ecb220001adcc62c,0xc4318e373e442da2dcc0,0x29cc03f23ae13f300001,0xae8f30000a0800006739,0x33780000e79a848f07,0x80b000000000,0x78000882600009ea6435,0x24c14316c70000000133,0x109b8de3344232700018,0xa81328f8f03e4000253a,0x2be200000000000116,0xab2d9418b04317300000],#[0x429d0001600eb66e645,0x336c3f42750fd80001c1,0x121ac000000000005,0x608270df55af8000376e,0xdf012000000000003b8,0x67c8ff80000000c0932,0xc03a80c7400032958000,0x1102f2800000005619ab,0x190b0000470403681,0xdc4c00000a252176849c,0x116470c3cf86eed37b3c,0x484817903f008ef11506,0x1986b274d7b1,0x805d108000011,0x4e0c8e2b0aa800085840,0x9559bcaa0564a38613d2,0xf54368000000056110b,0x8acf47a800028fd20ae0,0x327dd0cc4000034884c6,0xfd110d3640000141f023,0x49880c39254e6c9078c4,0x907cac91f1d840ddc633,0xa38000385ab09c0b02a1,0x67a965f1f8a19dea1f8,0x7e2c149a2205b44586a6,0xa4a1fee24003ae93b2a0,0x3059817a4805d,0x612cdc4ac9f4129de7a5,0xf2da617423419c000337,0x8a8db6d8000ea3f8,0xb800089fd974e2a18000,0x33f3e78000000102ad02],#[0x1a11f0a431e400006,0x638988b9200033a9346e,0x31badb1080e7ff04c02f,0x203b116800026d4e7c0e,0xda84680b10d342b7622c,0xc9908c75fa02e19d22c,0xc34f14633b80000cf718,0x2c6a80000000134d8000,0x383a800042b5842bc6,0x46dc00032a5064610460,0x8800081841a900000000,0xca22ea00000000000140,0x1cf8c0000000f1e15,0xf2850000022e411d8585,0xcbc00000006b1d056646,0x209e811110695,0x981222e5c19c13b78000,0x15bf86da000336,0x9bc00002a4924725c00,0xc240686ba03931f94833,0x69e18f32eea1a190f823,0x817462f51524248cc761,0x1d3d1e3a001953ef1490,0x11a841204c4e000291,0xc01a0002010000010a40,0x2232000162f00000000,0xef2ac993b900008cb800,0xa28583800028b02b3ac,0x527860000c1993de8000,0x43400000002b6e11b50e,0xcef400013e20000cf01d,0x15bcc25ba2d80000647],#[0xf58000607c0eb6000000,0xc872a2ce97eb7a000164,0xee3000001183d1978000,0x9810a4c010c71c007a21,0x404400031fe04c2c6731,0xcc4b40f4e00000000362,0x1c4b633aef3edc040e,0xc18a4f90000000000000,0xf202d00010ca00000000,0x4da3c5c14e217d9c69ad,0x18,0x9548c00000086a5420fd,0x7e4b6d07a6000000029d,0x41118028000007f0000c,0xe80006a4b12b40004449,0x7e000058ef00001ba323,0x911f9b213ead679c5361,0xd83b236d8666a2341d1,0x47f13d419f6de905330f,0x3b142dc23da2da057f9,0x891200023038000,0x7a8c73a57969a3222000,0xc26e8a580aa362344e90,0x3734505750dc80001305,0x296ec36404069b8700,0x6956d24e22e15e190c60,0xb464bee47d1f7a5d0785,0xcc43bc389ecc5cca56bd,0x45449c44a1be871b10ad,0xcc1c9ea581dc9c25e225,0x40034f6312e9d923fb1a,0x86a320010dac6cbce402],#[0xba3380c489284c52215f,0x39e1e60c510000020a,0x9d1b24d800000000,0xd01dc00005c0e2560000,0x19c00035d14fe400029d,0x11dd029800025d58b391,0x8220144425c48f2,0x3a6a6c00000116c00,0x180203efc7d710880,0xfb3de00000d700000000,0x7f2105e173cefc144b80,0xcd7ed773a250697ca994,0x21c0c03a00000000000,0x498000340925b7a22800,0x10adb0d2d7af50aad,0x569020000000218ca8a9,0x205c0000000188fa2d,0x11650000000000000,0x4800000001b7c0000000,0x7c00026ae000000009d,0x11,0x31af0c1200031280000,0x61900000000000,0x41cab2e218f50620,0xcb7fa3e0af18000,0x3400004e8cf428ee000,0x846f8e7c0cf0000d0ba9,0x5e7000061fc22a0000,0x20ff24a02a2a000000,0x12da41264884ec60,0x8a1b789aa00022bff5c1,0x10931a4325490e000229],#[0xc2ba000340c44a3abbb5,0x18000e39d870898f8000,0x20f4443fc57d98a9c5,0xc409193bbc3250dd1cc0,0x249948824f840000000,0x84c0007857cb6e805000,0xc6431189c1c18a04a2b1,0x5e4f200011f3400020dd,0xa73840a66300000003c5,0x4aa30eb330503dd0aaf8,0x6886c006099308a448b,0x30c67be000000,0xb10c0003ae3800001400,0xec5f7f20c09f73178788,0x403a2e01b00014141a1,0x50b00000000483c895d2,0x9800001ab1033815e26c,0x9373726078455513050a,0x70ac00021a1800049c60,0x87569054000479a,0x15b30000000000,0x8c918644000736988dc0,0xa97fb000087ff2800000,0xeb80000000ce589c4815,0x503c0002ad937f800000,0x3d2b60001800a841e231,0x63c8fd6000007,0x81b8000000000000,0xe00000a5000000002096,0x1c400070bb0000000342,0x24cb00010,0x6e59d0001632d246856d],#[0x4669000088b747,0x8a7ca1e800056d500000,0x6587c4921fdc00006fe,0x84d41f20c300011cb400,0x9ed8000278900018,0xd0000008600023f73565,0x7746425800031e,0xcb1685b10b0a31ac0aa0,0xb22de00000002314e085,0x9a0159083d3182000133,0x31e400000000000882d8,0xcd6c42de303,0xa4800000002f84000000,0x6070000328b34594f5f1,0x27260fc74ca40e94095,0x247d80006cacd6d000,0x15444000000083e00,0x78000870e10280000000,0x6a98d1c14aebc0506d1a,0x44019b742f8000000004,0xdf3b300001a9c000661d,0x8b44090000e9c6051a1a,0x17f213b227e00005,0x1ca0000,0x0,0x411a0b48000646445e60,0x7a3b700010e4a37e0000,0x5400061ab86c6085138,0xbea0fdb81764d4c4d4e,0x40000640b426c3c1c6f3,0x36ba65c6190000a1c042,0x86820000114800085251],#[0x403738830989400007c5,0xccc00000000000000215,0xb35000071ac9,0x75187000088a92cf8000,0x21400374103b2a,0x4df323010e4507000000,0x3a81d8fe0e39bc31c5c1,0xbf81f740acaffc1c9225,0x8c174cfcb3141f5c181c,0x46fc8ed71de88e3,0x980000457ccf678b3400,0x124160bae67900000,0x6437cc906a34c0000000,0xfaf8dde4ce05c10777be,0xf17c92c40003616c080d,0xe055d10ca0001beb08b4,0x3489ec27b782cd0bbda1,0x49b31a5000048a70001a,0x6381a8b5898f9a4e01e5,0xec63e48000e3379421c5,0x4ce000334545c0c6cb9,0xd44e770521b7a143c2af,0x1a400003eff07e8f8a23,0xae8a621c00027178dc50,0x8b1e00000004906,0x22bd00000000000000,0x131a00000,0xc0000858600030f58000,0xed2c722fd000055c146,0xe79952a41cd800051f40,0x148f00000000000422e,0xc3e2fdb4f200ea000000],#[0x1c52a3798ca78,0x46b02fd0000000045b8,0xf0a8000000,0x83f1d64008d20e600000,0xb0000ce3699481b87851,0x2f629242d34d0e528227,0xe15a00021e3827000019,0x6ee5969a326b466,0x33908480000000143d42,0x5136092e2cc8000702d4,0x6cd095ec000608a,0x639bce47030000000000,0xcee8960800000fecc1c0,0x988c34e1d18500002842,0xa17328e2f7499400033b,0xc42b890f2c543c3468a1,0x41d0855806512ad43bf,0x333e48c24fb0100400,0x574800000000fe60,0xa00000001537c0007204,0x380f454b91a250ed1a,0xe1840000000568e00000,0x3a5a30eec00002e7e595,0x79b84ee5ab004a9bdcb9,0x658ae08d13743d52c354,0xc07bf0000609c29171fe,0x5e3a5728954f1f1c2d13,0xab89626c4a21a800bd8,0xa83d02145903c860e796,0xff785d0253d096204f3f,0x2f2920a5c47c34943039,0x4554ce9106b93a82353],#[0xfab829b2ef0000031800,0xe7f200022b18000ca0b0,0x5e200000002901,0xcd749fd000,0x1cc78000000000000,0xca5b81985c8,0x45b2450000404e217c00,0x84b28559a368000e3ded,0xd62fe0001913d2f6c737,0x71b0d243d90bcc000106,0xc560000000403387160,0xb31de8a840f3439b0000,0x3bac0f000049994c9424,0x8b7285ec000423900000,0x50000000180dc000507e,0x2af65ea0000156d22,0x20881014000009d00000,0x780000acdcca11e98000,0x3800007fb0e64000013,0x11e118c4c4138,0xca6cc65f44315153c794,0xeb400000000000000135,0x815c1,0xd80000001c27f02a0000,0x368a0000000332,0x169585266ff03240,0x16c41c684e5,0xbc00026c70000e06c00,0x89600000000608249bfa,0xbe23f000000038c0f489,0xe4f07a000001b00002bf,0x4451873904207848ad60],#[0x42b32937cf3ab1e8000,0x37e12f800003198c9800,0x884a,0x265505e15940000613e,0x7c435000000000000000,0x635c15cc000416a00000,0xa963b02d6d1171a5c32d,0x28400011f30e42070c38,0x46098df6211e6f8cd7d5,0x374d94d9b94ff19a0000,0x2257a0f30000000234,0x4c3790e01c4c5a183360,0x4e16401ac15b20bba782,0x64c27072f17028000105,0x4a6a0001b6b102ccd6f0,0x8c6038e000004ff467,0xa771c280000000950400,0x918a1275b1e00006a241,0x52682e7bb1ace37d8000,0xc6c00000348b9b001c21,0x83d2052c2a800002d00,0x50000613303333cf0290,0x3291686681466e131707,0xc2d289198f48771b153a,0x4b42feb0a16d9205c4a6,0x3ef07bc6ace171999a18,0x43f81a671cf5266a1431,0x1e1976822020522fc481,0x536b0922079c13,0x56510ada41ab1ec0,0x940a866be00001c42581,0x302c8374000000002b],#[0xc7f00000000000000000,0xea7ffcb0011a932e71df,0x51d46784a200011690c2,0x93c400042426dfb0,0x80002910520400023f7,0xc285721a1c6c199b01d,0x453a31c6,0xe210b000091c2c29b082,0x43d8000c1fe891544,0xe8c4844b1ab0000cf800,0xcc43a8954a07046de8da,0xf47c120102cf2f9a5722,0xaa26807c000000000018,0x9549942e89eee0d7e219,0x1b6951a6208e339dd724,0x1170cd31335a13b80820,0x341cf0001049f06bd736,0xff112ac2cf47b70b6cae,0x81b384710279737485d9,0xeb412ca461dde17961b6,0xf6c0ed74a74645070726,0x90e594f409c486c45d31,0xc54e824a80b200005487,0xecba67b1f6012093d508,0x47adc52f8e054140bb39,0x2e2ee0ec507f61758000,0xaa898ec4bae9ad22ba25,0xb0b085bd01748e5072e1,0x8c3e760dd9740a01c19a,0x56da90b2192ef70bdb80,0xc468000000000006f57c,0x9a5c78e0522588f58000],#[0xc4f43026108b7c0001ae,0x91fba90209c00018,0x4a067ae5200000004019,0xa6205380000000000213,0x10ea00000000000ce3e8,0x3436e9ba8672c648000,0xc35ba18800,0xc340000227e000000000,0x6d3da000000013020000,0xbf0000000030b84ebea4,0xc17256eaacae316e2250,0x4442de01e824a2c6c51c,0x99e3a7661500018f2222,0xd08b9af721e240706031,0xc14d8bae04c4000050e,0x251275489e47b80003b6,0x8ad40a874561078862f8,0xe783510ed430f4140000,0x10d1a3f5d1d01bbd39,0x1c5000018936c120,0xa866000000022e6,0x6c19db0a370b6d36c00,0x628000125f0000413cc,0x897699d6c66642b,0x8470385522024cc88000,0x86e0d1d45125e800018,0x2073a2b4c00019ff64dc,0x22f3be93a84e0f9cf492,0xe6d5c09215c000000015,0xb0000437b131d219007d,0x1f4c1467ea8daaa13832,0x4bb00db2ad800001064a],#[0xd15c5893edbfe13986d6,0x52d42a6280511a000200,0x315403d8000023dc3d90,0xc84f4a7a614a400052ed,0x10d0eac1b6c0f,0x124c052ec2020,0xeb2e8dfd34e0346,0x3d846e4236cfcdcf8800,0x821d102346716ccaaaa,0x814642b1a000000043c5,0x3b9350e7910527cfc7a5,0x50a25e90000075a415a1,0x6a79c10f20603375d5a3,0x3c58060000044600038e,0x103860ea83760bb7a,0x57a30e800fec0000000,0xdf3a8c356dc57bcb9dad,0x6f2f0a4486032c6c82e1,0x61f4050710ed1afd690,0xaf3339800091bad88800,0x406d9e8341b2603d1321,0x7c7dac79421983fb0000,0x9e3202603e4763d2bd09,0xb09e520f3e4241b7055d,0x280000fb2984536565e1,0x3a182f40000000007,0x15c2b32a000000000,0xd639c840d1788ad28484,0xe7d05b2048d17a1aaf28,0x9013d49ea6e32fc090a9,0x2a1b2466a6061c6733bd,0xc0a1070222000193fe35],#[0xfad808eae100000001c,0xb80000000cc5c30928bc,0x12e600001010041736,0xc718000000054bd6a140,0xbc7a489a69f2f420e779,0x22b8a46c00010eef15,0xe25c00018348f1c0,0x680f0d0600014070000,0x85308348d4cb958fb400,0xc2f9f924970001c,0x9a39091d80002c19c5f2,0x4873f10891d01956871f,0x857b08b408300009,0x60000a3f4c6c43d1e85e,0x3b000000000000000308,0x4f219483457e51d2f078,0x80000a3bb9b6800067ba,0xc1711d373dcb45a2b531,0x88cbd7263118000cb741,0x5c2810611a3822218000,0x7523f3f2a40000805611,0xee798d7a4480000e4a25,0xaf368c2429ad9c747377,0x610006885e1508,0x1e3fd2b4433c00000,0x8a650b31c4c00000f0,0x6f4000413400011ba400,0x320006710000d,0x3650a4d8a00010b0269a,0x8df3d500000000000040,0x18a50000602a81945,0x306c5a80003440e54d],#[0x6d3bdc1021e8980a0800,0x1a32e27ee375a86a9,0x64450001e29d3d657b0,0x41c00000000000000000,0x1843ea40081f2a541,0x5563e618c00000000000,0x12ca2a80cf23e589df09,0x3304d700015,0xbe3f40001011f23b0000,0x7ef00c38fd40b70ef108,0x1978311e62d901774,0x88000000082a8000181f,0x5118850a02,0x8dca522a0838000b1120,0x631100000000c668000,0x17c36880000000000000,0xe88000037bc9b6e,0x4c34a692d47df1cc61e2,0x466e8c7ae3c7ac,0x8e083ba02900000,0xb8000cf03c5640000000,0x41c8000b1ba000081,0x32a0000000000043e40,0x10ffc18e8000,0x77800063a760401ef800,0x407147521678b068,0x904600001d27400042e7,0x51c000331ce3daa06696,0x15d0c1854201cd171,0x4275917638551ee,0x220c00,0xad8c0313022226100000],#[0xf288e64d017a420e2133,0x25434062b900000000a8,0x8f3b84643e9820200019,0x67ef000000030b8a7ed,0xb3806080000e8986f800,0x8f148f60000648e43790,0x4c1e92d279a8d38e020c,0x37246b03a0c40a089f3d,0x4a919a8aa6ba878c8ee6,0x161d60001190c0001676,0x1929467f8fa40c911c,0x85f20af131f800000000,0x2c4af1c7,0x1c701fe323e04f86fc00,0x6c5993bc000000000009,0x6340000000001db66b4,0x40800000006c0f193000,0x7f2d03400008be70629,0x65a000000000adae3b3,0x1142c422a083cd926800,0x32808000ccda8,0xc47c30000c8e8bb80000,0x5a8534000217,0x19d320d4a0bd40c40,0x1c75105080c561f2127b,0x118c486f48e9003137,0x497949d80000000061a0,0x576f000085440000000,0x128801f70af0c98800,0xa8bf21870a240a400000,0x58000709400000000000,0xbf0cb425c0685034bac],#[0xc7c064111d9461ea318c,0xa8000ceae00000000000,0x94612d52b727b60bb240,0xc592000086483c90a4b0,0x6583c6acddb33029083b,0x24400000b7e8ae914a9d,0xae9e42832e964b244b0d,0x58310041b8f522a36463,0x40bc24e409d0e9503315,0xecaea1aa9d584610b5fc,0x108b28b97227d9f3e098,0x2bd27234d546b18c15a5,0x4112a3f3ae64472ca07e,0xac8262f269ba92b7a67a,0x765240346a4f601515a0,0x70dd4bed92fc8ff8119d,0x481aead600009d7528b,0x1422e223e62af34f9ab8,0x89f408bc00020f88bbf0,0xdb000031d2a3aa,0x9f0000053700018a330f,0x598604d3d5b771463ec,0x7a09a000192080000000,0x7c200010a5e34,0x1789d630f742174e4e0,0x900004ed58a2832d1492,0x19cd207]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0x54d51541415013048110,0x98e545956458d6158154,0xfdbdfeef5fd0f41d0264,0x877337fffdfdfbfbfbfb,0x57371acab05d666b1a,0x882141042420958012a0,0xb180b72012e40858410a,0x4ba80b74012e80798c0e,0x32a004b76012ec02dd40,0xc2eb184b710cac019540,0xd424ba84b74092e81798,0xdd045b908b76092ec12d,0x650865b88e560196ec22,0x3798c6eb18cb721b6843,0xa369906cb20da541b2a8,0xe512dd864bb0cb75192e,0x2eb165922caa45d63892,0xaaa452dc4b2b01497689,0x2aaa85798caeb194b722,0x1496ec525d8aab294b74,0x744a2c892dc928b124b7,0xd63242c242dd528b2a4b,0x8970912ec425d48cb211,0x48975932c92758e50a8c,0xb1956532aa868584c4bb,0xbaa8b74522c8a2dc144b,0x5ba2cb70592ed325c265,0x6e3a2de545baa8b7dc16,0x105b8a0b7043aa8f7dd1,0xd904bb21565434c88659,0xdc184bb39964712e0e2d,0x25d604b840b75616e2c2],#[0xa50805ba34b71696e0d,0x80a55014b902962052a4,0xec0a5d414b282974052c,0x2a21ad0434a0869310d2,0xd2861adc434b8869610d,0xd2e61a58c34a986b430,0x40d2c81a95034aa06b73,0x740d4e81a5d0343a06a6,0x9760d6ea1a5d434b286b,0xe964152c42a50855bb06,0xeb711d2e23a58474a88,0x90e9721d2c43a54874a1,0xb98e9731d2c63a54c75b,0x4ba8e9651d2c83a55075,0x34a946b761d2ec3add47,0x4b5a0969412d2cb1a58a,0x90b4b9169622d2e25a58,0x5d8b53a169742d4c85a5,0xa54535a0a69414d2629a,0x9ad0d34a1a69724d2e29,0x89a95134aa269734d2a6,0xcb2a59494baa6a744d2e,0x2e8aa55154b82a964352,0x52e28a5c114b21e97555,0x652e2ca5c194bb229644,0x46d2e2da5c1b4bab2973,0x3a0094013800153a3697,0x1027608701bc05a01280,0x847210803e00de031a0b,0x66817f85b8154851a132,0x5820187941d106ec1aa8,0x628109a825108f022c08],#[0x2fa8ba02d60b0e2b18a6,0x698d5e3428cb631b0c32,0x80f003b08e7438d8de63,0x90f042f10604018fb23d,0x26c48591ca4601152447,0x84f093864cf92f64aa9,0xc562954853e149a51714,0x5c296d659f964458215c,0x3b98aa61b981e5ec1750,0x1a4868319c065c193e6,0x9bfc6f11b826cb9ae66a,0xdce7609d2e73a1ca4716,0x607c91edc7a41e4a7821,0xa830a08280c1fe07eb9f,0x8a4a22a8782194853210,0xe23d08e523608c622da,0x7a61a974256e94624a69,0xa8009ed276e9c6a6c499,0xa42a7d29a4a4a28b2a14,0x72b022bb2ad22af0aa72,0x2b8eadecb61ad34b30ac,0xc182fe8be52f3ebb42e8,0xa4321ec74b176c45b0b6,0x9344ecf7336ecc3b2d0c,0x362cd7ab59ed53b4f4d2,0x84edf7b794dc9b6bcd9d,0x58e8139b0e55b8fce27b,0x4f133bdeee3bb1ceb03a,0xf963e00f6dbd4cf42bca,0x29c046ffe3f8cfc3beb6,0xdc281086c1c305540ff0,0xc47310843cd0dec3270a],#[0x6c1199c603169c54b138,0xa921648051e747391bcc,0x4c2c0305270497724648,0x81e460583581c060d0b8,0xd048a0c83d09020502c2,0x4e181b41a200e1f8522,0x820ac100618c150e0c84,0x2d0ea045e244009a1693,0xc2a8984470180701450,0x50441787c1c380080c69,0x18093c104e258069f4cc,0x21ca6d2e481911408358,0x28d1f41876274c08c8c4,0xe2c3d170481a33160800,0x8a50336f83ef904786c6,0xf54a065af8c2d8819eb8,0xb75ddae104853f390462,0x4bcda49216bf44700812,0xa3dd01207f6b80023cff,0x6924bbf3ef2784054b1f,0x67bc6fc1271c73e5d3,0x919a6b0e800cf52f184,0x668095b5c208a27bb5d0,0x4026478ec2066df53ae4,0x8cb73be04279c7924700,0x191e7df88a29125beda0,0xcfc060606bc9337ff210,0x8c5294267d9f7ce7123e,0xb8b3710267dbf602462f,0xc502499fbf44514092f,0x1248fe639080492b7ff4,0x230f866be236ee3e63d9],#[0x40661f0cff0461e2be68,0x3c048a27afd008d15f60,0xb538f01240fa858091c6,0xf1f840234fefcbe008f2,0x31fff05e0145d662014a,0xb0133f03820122ff3901,0x80486fd23ae0006875d7,0x133cad4fe100913f7e60,0xa7fdfb6b00484ffa0280,0xd43e01317f406a1f009,0x7b8308f7dfe914282fe8,0xdce249f7f9e8a812429d,0x85fd67123337f0800cd6,0x205078f7c135f1666014,0xc509efa1fa4102bb9f38,0x492479f5ad67140936f9,0xf05008d3db09647dffd8,0x309cf715028d3f181177,0xe6a12ae31f401024dee2,0x4d214a068bf93008507,0x823eff7c1e080204bcf,0xe84c0cb3fcc822ee37eb,0x473a6c136fe7885023b7,0x11a7c718b047dfcf10a0,0x8178b04a0fcd42698e64,0x85024ee08f5023eff77,0x478a1149fdc884e3c1e,0xbc37140cc9f7a8cac81a,0x33ac57ca846cb0cfe11b,0x2287866940cd9da98338,0x3f508d001fa8465b1d4,0x75cd4411c3da25a0665e],#[0x135f79e8142998e64119,0x39d42a3ee53e5429a1ea,0x6f89a08f79f0284f5e65,0x1e0f842a11f7c21508c2,0x95bd710a047dc89fd81,0xc36785c08e3fc2f11001,0x6c255f0dd08479f09508,0xd4295002693a3fb09ade,0x9268f131bf536424bee9,0x38cd00367d496bf54d80,0x9ba029d3d798d9002557,0x81d180254f76bc08d4fc,0x40929e030c2159c571f,0x40099bbdc701330f1638,0xa204d13f7d7602470fdb,0xeb8af4b96024981872f1,0x91f7d7e27aa4b4024c1,0x8492bfe51d091d617c8f,0x496fa764c099a7d40c0e,0x24e0c9e02691ef194562,0x30424b9f3c69e84905f,0x2496bc54038490bf3e82,0xffd698491c7ee8f19fa4,0xfd8091f7e178a9b41254,0x311e04cd3eb6c048f87d,0x212428fd8e40c4224c2d,0x24c2f3e860099e7bf7c2,0xec7f22475ff6de3e4201,0xef124c7f32ec481342f9,0xcd3e7d4e3802461e3ad6,0xf55a98c04025f7e4e000,0x346d7e1045ddae10465f],#[0x8dd2cba125d7e3a02801,0x244f5e438fdb8492c7af,0x9f6b1f0f111d4ac78f01,0x81fdc5802437eb6a4001,0x11e713ea08cabfb9a823,0xc012e7e16a011e7f0980,0xf27cb2d0025afc6e02aa,0x7f304025b4b1d481997f,0x81346d63ef1023cfd4ad,0x42f7af5b849203ccb26a,0x7f3f9200479f8f0bb802,0xfd983004adff8e48011d,0x89377f7ed0ad048de79,0x4f7ef446238e0bebb745,0x4ec012267f9654898026,0x4f5fe10514001a67e3d,0x36fffc33c10c128ce3df,0xadfd59c480492eb30803,0x7e66720246f6247c4804,0x9297ffe68568e240266f,0xfee98c0475ff6fef6124,0xccd8033ef85035520256,0x50132778d35202497f7,0x3bf22a6c80923dfda095,0x5c7ce0264e1d5690400d,0x3c5823efff1ce482c02,0x2e2819aabea84c0cfbff,0x940d4371638a0492ff8,0xfdf0782140949f99682d,0x1e13033b7f412a940d1b,0x33f7d4b504840d35cbe,0xd0285348ec264fe90a31],#[0x2812a7eb7b3f06049333,0xace1dd1a819f7ff2a704,0xe5c33c1084b3e71840c2,0xe7614efff132e28485ff,0xe668fec2833a0]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x3410004050100900c15,0xb000020180706007,0x15c20074a30000103c15,0x8023004000fc0602401,0x45d02c060000707800,0x168050180b030020000d,0x540d040090000903032,0x140000800050a40000a,0x10807044031d40005807,0x400000100080700850,0x830002e0003200412,0x42c03022098000b409,0x460012ac0001404008f3,0x700d0040a0942b01017,0x3700c2c0480502000,0xc4901c490ec1000000,0xb80001c5e0940207433,0x81400417000110a808,0xf48a1f0040100d00409,0x1f00c0980712c0a11c15,0xc2901c060180007801,0x4410148c0042609c2b,0x4002000060042f10001,0x474010602e0080301c06,0x28c3201c7e098a902c04,0x540504c000282d0000f,0x20011141220c0002c02,0x18000400004c0000000,0x1b44d05c10000b712419,0x2140030d01405c3e,0x7074270cc0001000,0x71df01c05000000f468],#[0xa00804c3905c0004c1c,0x4970001a1583b05411,0xbc04010321c42800026,0x682c024303b40101811,0x2c802048000004a0dc22,0x182c0f45f0f00a0e027,0x680411c01030bb00c10,0x7800018d38540200c09,0x80001007004a512809,0x6406010ab05c0a06801,0x4823018020a40607409,0x247d300100000e0e400,0x11819068972d4031b804,0x10ae0601b01c6b0187b,0xa084d30980601002,0x370040b403000020e413,0x8060207a2e0a02d469,0x17025064b90a00019cc8,0xc00004c120181802c88,0x34519dc3101cc437c2a,0x13c31044030606503c12,0x81e000225ac0306529,0x78a02940a0000106f15,0x80a9a0b610c4345903,0x38c0006c332301d1bc01,0x106144080ac3402418,0xcc430040a1e80b008e8,0x320216d0106f21003,0x92018050040600402,0x2caa004560195154c17,0x880f0f0080045501057,0x2780001ad20146847c13],#[0x347e048051480105408,0xa8d360a084b801c404,0x4f01d5c8ef4e325fe33c,0x7932acb462c6a1013b99,0x22b200023fb000006993,0x1df177c1ae0ba04fa079,0xcc4d4609d59f3c08d83,0xb8b639e40001b24493a0,0x40705ce000014181f50f,0x338800028398fc93ba,0xa80004f4a221c5b40000,0x3213019eae3b853b0fac,0x883d604afe94501440f7,0x882c165b4935489ec598,0xc000343dd1d741d91ee1,0x5021027f62b0b982f8d7,0x6ee4d64c3e83d57e5531,0x67611855760f706d5325,0x21ba90f0000919a1b4d0,0x148c24d4cf0001a13cbc,0x42b5bd0ec6c9f561878d,0xe4d0690b453857050172,0x4640a2686341f0cb021f,0x1fb29ba17140e511f4ca,0xad9bd75149cf4ea24c4,0x1489a1773ae481f1a6ac,0x3ff12c4200067b58712f,0x6f0cec3cc4f6f432708a,0x4000111284db4bdc7e11,0xab04f6c05ccd0ca364c,0x5520e757f4364cb0c1d2,0xb55fe05c24f540c61ad8],#[0x75a352bfdab6b54147d2,0x10ab1ceabfce19178481,0xfb55261b942f60eacdc2,0x106f430b367a67ed,0xc8089ab8fbd272339000,0x709cf8c0900ed23f1aec,0x56ba40000a7a428b3171,0x9fc3a6546016136ec0,0x3fe88b0000f6ab477a5e,0x889820d484002ced54d,0xf936000009de54c8b7aa,0xd4a21aa449f37cabda00,0x6c051900029b642fc4f8,0xe699c320545300023094,0x8545582a8fb895959464,0x238d0c7487612717bce7,0x7e6685053857f0969637,0x4518b4cd4b3dc4403a23,0xa0ac0d9e1dd83468a291,0x85dbb9295919526d2b3,0x7842d8db430a274447fd,0x509c112e05957d3af580,0xa78a6f4999465108d2f5,0x894bdcdbf473d5335733,0x2418c306418130b8f4c9,0x4146859b09381ece5284,0x42d04158315d217b5286,0x2cad181d1368474e3aa3,0x145c9119474496520481,0x99ac5fc536ebec490a27,0x672303c4738ac8ce11,0x61373bd92acb5cb13000],#[0xf07185f104ae024ec135,0xfcf96e83c006e7764158,0x59d7e86333d549c50816,0xf88d489c439cdd61d04c,0x53d87014b5375b1248dd,0x4234e457401cf39c95c4,0x6097c3ab225b5dbd8491,0xe47e4678a523b8a00301,0xbe4e5c9cc3a831093b6,0x802d9246a52115f81e9b,0x65bf810800092ce31f04,0x180d5b22fa437f5dd71b,0xcb43e00ae00eb5270002,0x532c8e170d3145843329,0x67f80aa44ec5a2112b2e,0x8d83d6157abf4d20d503,0xab4418342604488ecf1c,0x2dde580a3e6d5b89ea47,0x9cdaac60b4a6aa416952,0x4e53412ed4b842bc318,0x20a9113c4f2516304d10,0xe0c440086179386b4a32,0xff74e7d06031b801e348,0xf0428232e52f413b019c,0xe21794e1344c30c32681,0x3ee501239b8e8658a6c6,0x9508f7595815517c55be,0x20001d8bc0ed4a258522,0xec89176763184a00012c,0x9215b54148068c3160fe,0x985928bae94be9f446b4,0x745905d080726d89],#[0x2fe4bb7284c5cb4fec2a,0x48f113dccb13b7808d,0x4d221287c3824d028580,0x9f80d7000359157f250,0x6ad566c0be860067f589,0x880002b3ec8653321e88,0x468420fc4bd5f212810,0xddf8214db92cb19a0544,0x9c000088a83da18e36d2,0x4c17c9116e31a200011,0xf374000e26f45b00032a,0x90e1d793c151308953f8,0xf90ba2208ab677f851a2,0x724411ca0ced2aaacd6a,0x1cc03215250dd24520b3,0x393b90d6e5392571159,0x5cc089b84e9fa7700016,0x4c5730d434e104c2,0xec6c950000000f4d0c34,0xa3afca48722d8b5a21b0,0xfdda8d4e52493915fb67,0x26fd48a9330824c9408d,0x82000341ca0b64455146,0x394ef44faf731710e274,0x94e987fcce5d15d6972a,0x37f1cd88234094043b14,0x9bb1f412994402b0c71d,0x2436ce5527fc6ff08a4d,0xa170542296e518000000,0x188e8252a0fdfc2ccfda,0x4cd8734fd7a4075d1b22,0x209bd4c1cba00000e],#[0x46943bd60da446427893,0x2a9f4c5ab2f6c47c936c,0x31edd7c00a7000283a57,0x2b45325550b2d,0xe2c5f800068512632f8c,0x9880fdc5889800060b25,0x8cdb55213fd2abb5b829,0x91d56494300775419308,0x153e5000000084175114,0xada2d8180b600001bbf8,0x1e0e1e8a9b4c522c9475,0xb91046afd6b972510ef0,0x13a6a32000161810344,0xc935b01d344000c42000,0xa9b89280605c10bd505b,0x2014942fcb6b0e40000,0x201271fe601c66806505,0x84ccdf0a948e89db000,0x605169352cefc12f1570,0x20b7c45741ca0af07c61,0xa482fb4a2638b407509,0x9baabc9583b1a10fa586,0x1806d50bf51694e5c8a8,0x824b472e86900013b2cf,0x3cf53865c5c349de1b7d,0xe6e01931c4f1418183ba,0x9c768000cb1cde2d44b2,0x4152605c76058c01b117,0x9734bbacfb05762c4,0x215b1c5676108f1d0ff0,0x720e984dace440ebb872,0x36a00000d8cd5c9b5a35],#[0xf200000007596b1c094a,0x511189175b43b32f5d1,0xc2452d4910a5b2d1e800,0x8b23ac30003243,0xe95dc48d0000cd469c70,0x82d5909c5ec43862400d,0x1a4c15998c90aa21c81a,0x28f02560b147d3c84fb7,0x8c87c86ae5e631ac069c,0xc9711dd000000057ae33,0xadf407400c1994af503f,0x740008de388fd5e7dc04,0x141be9e71e64008c7e53,0x3de93b44144007a8a966,0x3c838d2a90287cc4d1cc,0xc7367ddc31022becde4a,0xc6e3bfc16f5b13364629,0x50c48f8e01aacc6292a2,0xf4ab50b680b584641064,0xe4430f9f116e222c476f,0x4694d344ec42f169cc1,0x38468d297d184000259a,0xe71800096eb48500020,0x13080f16a254ae00031a,0xbbd08fcd0c4b0d08c000,0x6e8fd00035c948559c94,0x91d1b2311c4063f5fac0,0xdac3eb4ac206800015d,0x4cae96257859970002,0x886a058b832988055a80,0x179c585464488654b716,0xa033290a14340c985948],#[0xfaef95ce96f0411c308,0x32e0cc4d2d3739a9da8f,0x98ac0822dd811632d971,0x2ba8a8ab0135c37dc281,0x1f0ceb0dc3c95475622b,0xd2911ac0528000167e2e,0x4dc5f14208354c23ac35,0x432452ca4036b2d44ea1,0xb450cf09ac6d45459067,0x32838544bbd16430d0f2,0x3fa72b113ab7c20fc028,0x80003187cce82fcc46f1,0x52040004e8f941841c13,0xba49170087523a85510f,0xba24a8891385855c2d0c,0x7d934cc8000434646f87,0x1e7ebbb829973c000ccf,0xb1662ddd86ca105a9792,0xc81ffd4596721b1aa720,0x53ee3e34af0c92e80291,0x6fa31e650d42635d65d5,0x9b7c0ea5358f1f7af81,0x13211030254cfb31db06,0x3bd00000006b9929e4a3,0x30557c2465735d414e5d,0x785711c26ae31ef8a2d3,0x4c47331d70cac2689592,0x3db1cbe60c44e64000,0xdf811811033e47cf4030,0xd0c0d23a3cd000005057,0x1b5804c5eeb2e1392062,0x82b1102e11abc83334f],#[0x15e3492000220ca21f6,0x410c3af0002b30687400,0x5b71b3ec7a58fb24c20a,0x9b2fd8b8daa4a430abb1,0x545ea6f857a00015afe4,0x2db000149fc8b8000843,0x7a00015ad0000372d136,0xc803a14966df5b641e92,0xc70f0bc84390068c04dc,0x56037f6ab80000000db2,0xd448b16de04000014b21,0x5d0c33719d91b561687,0xadc4761014d7400007d,0xa405d136c025e91840d5,0x35f6064530f25536643,0xce3d3e292113f040a45e,0xd2c1294d3a381e44d935,0x214ce493ae092980008,0xd897c9a5555cfd14a300,0xb21087adcf89c20092c0,0xbe0aaa1e95d634640b6,0xa4a0da0ac5f55d98dbf2,0x4abf151097617a484059,0x4355a0399d8089a1535,0xcbc214e7c0a38fcd5ace,0x4114c81b00db0ad29370,0x17507254c8c304274845,0xadca2111e40c928acf7d,0xe40ced29c876a8bce443,0xd294547352e180f5285,0x25135a648ccbcce5b554,0xda076aae843a0d1714b0],#[0xf1222b87584000135cc6,0x47d7fe836e1e64f383c,0x5e0b29192c7f35a08c96,0x841ef197460c4308e420,0x2655da1153e3ebc7df5c,0x405ae2e601034955c393,0xef12d0cb92282fff3b41,0x64d995012496c1348695,0xe5ccd3433d0b0565528,0xef45de32f57d62ff131a,0xd000140bc2ac491cb8b0,0xaf882bfe66daab802d48,0x4b33e4cf87087d2df0fd,0x7c55dec96265c8375f80,0x74e6564c0bb505489041,0xe16a0ee3c4849735b0d9,0x16a60a5c4cd231d429,0x54188ab370e2186ecbc0,0xd25747c871b5f3a281a3,0x25209050d72d29102562,0xef81d0135aed82011535,0x8541343c23310fc5a889,0x1a744703d9145c3d048f,0xd78e359b24c391c72891,0x347675e602324b470758,0x17585b08424d1a846141,0x4f8011c8fc1b796994ab,0xc4bef02c0275c4fa250d,0x8000d38828f32f9cda25,0xdf8eb1e3f50723b0e496,0xeb91250860bceac1b49a,0x70b051110adb94293049],#[0x12671e5903c00021120c,0x61505180b26b58000,0x105c4ba14240000,0xb3a71a5e0cb41a00,0x39a4845d0d01c209a459,0xd30dcc00091b8291b36c,0x4370000550f89aa2305,0x8ae91ca307926782e000,0x25a46497aad5703df4eb,0x804e846602cb15650959,0xc00000000000be116e91,0xf54124000934dc2ec13,0x8cf389d794c740004ae6,0x9e30bb158d8800043d34,0x8b91568d3511eb501a0c,0x46e3daca0400013d0000,0x5013ae0ce48a00028952,0x3556c07c54d00014c788,0x12fb4b600031fa000,0xa64aaaa41456a25ed3f4,0xe4d65323cd7a0b3f7dc0,0x86f3c46552f3f94bc703,0x61f487e738ecf5,0xa435fca410a44ab52dc0,0xf82e4ae000094795f610,0xa2d80205a465485d12b9,0x8216034ef8f2d29811f5,0x517a0000d470a02cf05c,0x48d402664f250eac8c1c,0x2745ab877350712fe50f,0x4c84713b3dad4dec0008,0x83d74b17258b09ab1d46],#[0x3f184c4000440,0xae9674410b3c85b3aba8,0x5d69d19b48a529a00dc5,0xd414563048c1e1252533,0x93d2d788bdde00000dd3,0x845d753dc3a5527adfd8,0x6098449a59e581c80cca,0x27c51fa376f50841f515,0x88cdad3bb045c025cc63,0x70354845c3e60666c639,0x72cd315176359b875043,0x477cbbc7e69348187cfa,0x5e29d0e0f241e4f73639,0xe884d381c3eafec9df32,0x5292c421655130470f59,0x8953c9951c86b8988ba8,0x9929d47681e616224fd1,0xf6b03421348184956fc4,0x1c6212c9b3aa38227398,0xddc2748ac3fc14b23e81,0xe3be08832f412a0000c2,0x54a4e9933349e250817b,0xddc6bc2bb68422a79665,0x75096ab4686826bb1cb0,0x9028000cc029b44ac6cf,0x1ac582622e52015de5bc,0xac1f674cb3e944c90288,0x5a20456edf9b55400094,0x121b4f00000003039cc6,0x30832d3d158382390dc4,0xd84e527dc9930e240b21,0x8c10479c54a3acca9534],#[0xc0e4ce7559c8b577857f,0x3728e051708b179722a4,0x45aac4ad0fc2c2741e45,0x3ceb3cd463953a36912a,0x92cd4238700c19081544,0xb830000059c34948cab,0x926b4da540800003ac00,0x541bf67430000ebdf5c6,0x14d5222c0000b82ae0ba,0xa0578e08d96f0c42b5b1,0xd090d74d3e61ec898,0x1b8f835c740af2a8b440,0x46f9401128309e42655,0xac2aaca565baad636c00,0x72305c0658c2d165e497,0xfeaafac1a2534e761953,0xc00041e000014fe3ea4c,0x5694c30526478b2300d1,0x2254025dad78c38c90e2,0x86f4b4cbc0f750d06cb0,0xf6f6c4300038819120d2,0x49fc02853ecfd0000320,0xe42f205b199e0002ad33,0x35a178211ffc34f27996,0x42e120245fc85ad8d0ac,0x521f22ec17ca5440378,0x9136c0db0002c8fc7070,0xa7981de8e3800011a61a,0xa233a2c865276b4463b5,0x4d161a47b29fc5ac0002,0xb2e700019cf0001c6fd2,0x9d244431fb1800000d5c],#[0x3d51e0355d7032224558,0xe096e26a85cc3244e28c,0xc4dc00093f2b12c4312a,0x2774022adc04c84a8000,0x3c00095afbd30002d9d1,0xa4981460465cc9c000c3,0x9ce585ce011080000f69,0x888c4254206f74f14b31,0x4310715e47f457d00010,0xcf773d80c483fa8685cf,0x63a048517760dab2c000,0x5]]
def g251D11 := limbs80 #[#[0xa0530a4144131963fff7,0xd51e8350698d60aa1d02,0x4ca9552b1d53e8750eb0,0x8da278640c0015973256,0xa5a899fc749925512e3f,0x3f6f1b84d8326bdad2a4,0x1860285c242c04145b0d,0x830203c089c18504000,0xf0c868d8d0a01078c0b0,0x1e41273a8131fa8128f8,0xd320982a077a5bcc21be,0xe96d6097e2d7412b881a,0x77ff8019fe00afb8057,0x21a8063d85a0293fb78,0xd00528603dfce0098f4e,0x80c7e9e809deda01cfc6,0x1f846502978]]
def g251H11 := limbs80 #[#[0xa1c00022646803c1c481,0x2c01a3e0110000084002,0xc69c00240005a6448422,0x8300055801e38614662,0x81062249100000233a90,0x82600883043808200280,0x2a8000b26080a2236c38,0x10164f000a826832790d,0x329c5c400342c2552802,0x2f7c41992f4db0935d70,0xcf08d000000001a00003,0x6950b07ae13b885092ba,0x4c48c3a81d8f306e6486,0xd35a18e6a7ddd30811f2,0xcd159e0fc13000e5d9b8,0x70008613e800b44000e4,0x434004a925a000000d,0xaa25670ee2f93a2b8520,0xd5b077d8ceaf2e800cc0,0xe04c0614aed87ce6df2e,0x6c00051c006e50012433,0xbbc4fdde1340016ab14c,0xe0030495000182b08e38,0x7341e71c4910c65000b4,0x6586782a007518000008,0x9e0001c8004884c6053,0xa38a00000000ed000000,0x2c48500090f1fc3f42,0x3001a3353a8e0,0x5e6a3721326561f7a000,0xf05891a7120003b00110,0x4b0008a3bfc5c6633850],#[0xa33686ec0f037986af0,0xa000001490011d91c800,0x2a099e95e17c0037e15,0xb965b00002c000ae0000,0x5140000015a108373,0x20000003a8168219a21b,0xa0019e80043a380d036,0x1c0004b5c881144ae2f8,0x7648629800005ed29000,0xd83e8d20d536a9827d96,0x3e2cc1671362b929b,0x169204ea8de573f19200,0xa1ec0032a4a61413d623,0x4f2b2bc91791c006bf76,0x6c2b861f8b80023d44f0,0x6c117de076ac17772728,0x205acdb1009694533800,0x7fb4a508d616ea6d26e8,0x86a244190011a8003b8f,0xc21000857157dba041c6,0xb2a5da7352581bee6aaa,0x89000f0fbe2975240308,0xd859bf62fb6591a93190,0xc4466ce31eefb103a000,0xe40074200008be5fda14,0x358004cb3900029adbf1,0xecc164ebf03c46e58335,0x33e96b63]]
def g251D12 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g251H12 := limbs80 #[#[0x223000893d32a2820000,0x7eaa04814418043a7040,0x105a0c9e60102a506806,0x690b001280004a3,0x480720]]
def g251L : Nat → Packing
  | 6 => (11,6,7,458763,52,7,1032,g251D6)
  | 7 => (571,5,7,10355064,137,14,1315,g251D7)
  | 8 => (2311,4,7,11600748,138,17,1386,g251D8)
  | 9 => (1561,3,7,3211451,104,17,1249,g251D9)
  | 10 => (230,2,7,720916,69,14,1127,g251D10)
  | 11 => (23,1,7,131073,16,10,1053,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 3 23 4 7 4 1 g251H7
  | 8 => lookupShort 202 1301 7 13 10 1 g251H8
  | 9 => lookupShort 790 4327 8 15 12 1 g251H9
  | 10 => lookupShort 521 2251 10 14 11 1 g251H10
  | 11 => lookupShort 77 383 7 11 8 1 g251H11
  | 12 => lookupShort 7 41 5 8 5 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 10=true := by
  apply @block_merge g251 6 0 5 5
  · apply majorBlocks
    decide +kernel
  · apply cellsBlock (ar:=6) (rows:=0) (d:=1)
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_10 : block g251 6 10 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 11=true := (@block_merge g251 6 0 10 1 g251P6_0 g251P6_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_96 : block g251 7 96 96=true := by
  apply @block_merge g251 7 96 81 15
  · apply majorBlocks
    decide +kernel
  · apply cellsBlock (ar:=7) (rows:=0) (d:=4)
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_192 : block g251 7 192 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_288 : block g251 7 288 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_384 : block g251 7 384 67=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_451 : block g251 7 451 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_547 : block g251 7 547 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 571=true := (@block_merge g251 7 0 288 283 (@block_merge g251 7 0 96 192 g251P7_0 (@block_merge g251 7 96 96 96 g251P7_96 g251P7_192)) (@block_merge g251 7 288 163 120 (@block_merge g251 7 288 96 67 g251P7_288 g251P7_384) (@block_merge g251 7 451 96 24 g251P7_451 g251P7_547)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_96 : block g251 8 96 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_104 : block g251 8 104 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_200 : block g251 8 200 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_296 : block g251 8 296 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_392 : block g251 8 392 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_488 : block g251 8 488 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_584 : block g251 8 584 96=true := by
  apply majorBlocks
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_680 : block g251 8 680 96=true := by
  apply @block_merge g251 8 680 69 27
  · apply majorBlocks
    decide +kernel
  · apply cellsBlock (ar:=8) (rows:=0) (d:=4)
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_776 : block g251 8 776 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_872 : block g251 8 872 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_968 : block g251 8 968 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1064 : block g251 8 1064 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1160 : block g251 8 1160 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1256 : block g251 8 1256 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1352 : block g251 8 1352 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1448 : block g251 8 1448 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1544 : block g251 8 1544 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1640 : block g251 8 1640 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1736 : block g251 8 1736 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1832 : block g251 8 1832 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1928 : block g251 8 1928 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2024 : block g251 8 2024 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2025 : block g251 8 2025 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2121 : block g251 8 2121 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2217 : block g251 8 2217 94=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 2311=true := (@block_merge g251 8 0 1160 1151 (@block_merge g251 8 0 488 672 (@block_merge g251 8 0 200 288 (@block_merge g251 8 0 96 104 g251P8_0 (@block_merge g251 8 96 8 96 g251P8_96 g251P8_104)) (@block_merge g251 8 200 96 192 g251P8_200 (@block_merge g251 8 296 96 96 g251P8_296 g251P8_392))) (@block_merge g251 8 488 288 384 (@block_merge g251 8 488 96 192 g251P8_488 (@block_merge g251 8 584 96 96 g251P8_584 g251P8_680)) (@block_merge g251 8 776 192 192 (@block_merge g251 8 776 96 96 g251P8_776 g251P8_872) (@block_merge g251 8 968 96 96 g251P8_968 g251P8_1064)))) (@block_merge g251 8 1160 576 575 (@block_merge g251 8 1160 288 288 (@block_merge g251 8 1160 96 192 g251P8_1160 (@block_merge g251 8 1256 96 96 g251P8_1256 g251P8_1352)) (@block_merge g251 8 1448 96 192 g251P8_1448 (@block_merge g251 8 1544 96 96 g251P8_1544 g251P8_1640))) (@block_merge g251 8 1736 288 287 (@block_merge g251 8 1736 96 192 g251P8_1736 (@block_merge g251 8 1832 96 96 g251P8_1832 g251P8_1928)) (@block_merge g251 8 2024 97 190 (@block_merge g251 8 2024 1 96 g251P8_2024 g251P8_2025) (@block_merge g251 8 2121 96 94 g251P8_2121 g251P8_2217)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_12 : block g251 9 12 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_108 : block g251 9 108 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_204 : block g251 9 204 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_300 : block g251 9 300 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_396 : block g251 9 396 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_492 : block g251 9 492 87=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_579 : block g251 9 579 96=true := by
  apply @block_merge g251 9 579 90 6
  · apply majorBlocks
    decide +kernel
  · apply cellsBlock (ar:=9) (rows:=0) (d:=3)
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_675 : block g251 9 675 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_771 : block g251 9 771 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_867 : block g251 9 867 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_963 : block g251 9 963 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1059 : block g251 9 1059 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1155 : block g251 9 1155 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1251 : block g251 9 1251 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1347 : block g251 9 1347 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1443 : block g251 9 1443 54=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1497 : block g251 9 1497 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1561=true := (@block_merge g251 9 0 771 790 (@block_merge g251 9 0 300 471 (@block_merge g251 9 0 108 192 (@block_merge g251 9 0 12 96 g251P9_0 g251P9_12) (@block_merge g251 9 108 96 96 g251P9_108 g251P9_204)) (@block_merge g251 9 300 192 279 (@block_merge g251 9 300 96 96 g251P9_300 g251P9_396) (@block_merge g251 9 492 87 192 g251P9_492 (@block_merge g251 9 579 96 96 g251P9_579 g251P9_675)))) (@block_merge g251 9 771 384 406 (@block_merge g251 9 771 192 192 (@block_merge g251 9 771 96 96 g251P9_771 g251P9_867) (@block_merge g251 9 963 96 96 g251P9_963 g251P9_1059)) (@block_merge g251 9 1155 192 214 (@block_merge g251 9 1155 96 96 g251P9_1155 g251P9_1251) (@block_merge g251 9 1347 96 118 g251P9_1347 (@block_merge g251 9 1443 54 64 g251P9_1443 g251P9_1497)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_5 : block g251 10 5 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_101 : block g251 10 101 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_122 : block g251 10 122 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_218 : block g251 10 218 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 230=true := (@block_merge g251 10 0 101 129 (@block_merge g251 10 0 5 96 g251P10_0 g251P10_5) (@block_merge g251 10 101 21 108 g251P10_101 (@block_merge g251 10 122 96 12 g251P10_122 g251P10_218)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_2 : block g251 11 2 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 23=true := (@block_merge g251 11 0 2 21 g251P11_0 g251P11_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P12_0 : block g251 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B12 : block g251 12 0 1=true := g251P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K249 V249) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K249 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V249 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_33242

open PEqualNP.Outside.L_meta_33242 in
theorem PEqualNP.Outside.L_meta_33242 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

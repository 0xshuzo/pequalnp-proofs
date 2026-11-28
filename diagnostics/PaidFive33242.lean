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

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

namespace PatternFive
abbrev LocalSix := BitVec 7
private def localFun (x : LocalSix) : Wire (Fin 7) := fun i => x.getLsbD i.val
private def localWord (f : Wire (Fin 7)) : LocalSix :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem local_read (f : Wire (Fin 7)) (i : Fin 7) :
    (localWord f).getLsbD i.val = f i := by
  simp only [localWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
private theorem local_ext {a b : LocalSix} (eq : ∀ i : Fin 7, localFun a i = localFun b i) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j h => eq ⟨j,h⟩
private theorem local_back (x : LocalSix) : localWord (localFun x)=x := by
  apply local_ext
  intro i
  exact local_read _ _
private theorem local_inv (a : Wire (Fin 7)) : localWord (inv a) = ~~~localWord a := by
  apply local_ext
  intro i
  change (localWord (inv a)).getLsbD i.val = (~~~localWord a).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not, local_read] <;>
    simp [inv, i.isLt]
private theorem local_combine (op : Bool) (a b : Wire (Fin 7)) :
    localWord (combine op a b) = if op then localWord a ||| localWord b else localWord a &&& localWord b := by
  cases op <;> apply local_ext <;> intro i
  · change (localWord (combine false a b)).getLsbD i.val = (localWord a &&& localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_and, local_read, local_read] <;> rfl
  · change (localWord (combine true a b)).getLsbD i.val = (localWord a ||| localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_or, local_read, local_read] <;> rfl
private def localBag (B : List LocalSix) := 0 :: 127 :: (B ++ B.map (fun a => ~~~a))
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

private def majRoots : List LocalSix := [43,42,76,112]
private def majGoal : LocalSix := 22
private def permWord (p : Fin 7 → Fin 7) (w : LocalSix) := localWord fun i => localFun w (p i)
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
private def embeds (p : Fin 7 → Fin 7) (a b : List LocalSix) := (localBag a).all fun w => (localBag b).contains (permWord p w)
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

private def axisData : Array Nat := #[1754760,1682184]
private def axisOf (t : Nat) (j : Fin 7) : Fin 7 := Fin.ofNat 7 ((axisData[t % 2]?.getD 0 >>> (3*j.val)) % 8)
private def state0 (_ : Nat) := majRoots
private def extras1 : Array (List LocalSix) := #[[],[4],[8],[10],[12],[64],[68],[92],[110],[124],[126]]
private def state1 (i : Nat) := (extras1[i]?.getD []) ++ majRoots
private def extras2 : Array (List LocalSix) := #[[],[2,10],[2,124],[4],[4,8],[4,10],[4,12],[4,16],[4,32],[4,34],[4,46],[4,48],[4,64],[4,68],[4,72],[4,80],[4,92],[4,110],[4,116],[4,122],[4,124],[4,126],[8],[8,10],[8,12],[8,32],[8,34],[8,48],[8,64],[8,68],[8,80],[8,92],[8,110],[8,116],[8,120],[8,122],[8,124],[8,126],[10],[10,12],[10,34],[10,48],[10,64],[10,68],[10,78],[10,80],[10,92],[10,94],[10,110],[10,116],[10,122],[10,124],[10,126],[12],[12,46],[12,48],[12,64],[12,68],[12,80],[12,92],[12,110],[12,116],[12,122],[12,124],[12,126],[14,110],[14,126],[20,64],[40,124],[64],[64,68],[64,92],[64,106],[64,110],[64,124],[64,126],[68],[68,80],[68,92],[68,110],[68,116],[68,122],[68,124],[68,126],[72,122],[92],[92,110],[92,116],[92,122],[92,124],[92,126],[110],[110,122],[110,124],[110,126],[124],[124,126],[126]]
private def state2 (i : Nat) := (extras2[i]?.getD []) ++ majRoots
private def badData : Array Nat := #[(word80 [0x2000000,0x400000]),(word80 [0x3000000,0x0]),5242880,0,4456448,0,5570560,0,(word80 [0x2020000,0x0]),(word80 [0x3030000,0x0]),0,0,0,0,0,0,4194368,0,5242960,0,4456516,0,(word80 [0xc0c00000c0c0,0xc0c00000c0d50055]),(word80 [0x404000004040,0x4040000040400000]),0,0,0,0,0,0,(word80 [0xc0000000c0,0xc0000000c00000]),(word80 [0x4000000040,0x40000000400000]),(word80 [0x2000000,0x2000000000000000000]),(word80 [0x3000000,0x3000000000000000000]),0,0,0,0,0,0,(word80 [0x2020000,0x2020000000000000000]),(word80 [0x3030000,0x3030000000000000000]),0,0,0,0,0,0,0,0,0,0,0,0,(word80 [0xc0c0,0xc0c00000]),(word80 [0x4040,0x40400000]),0,0,0,0,0,0,(word80 [0xc0,0xc00000]),(word80 [0x40,0x400000]),(word80 [0x2000000,0x20000000000]),(word80 [0x3000000,0x30000000000]),0,0,0,0,0,0,(word80 [0x2020000,0x20200000000]),(word80 [0x3030000,0x30300000000]),0,0,0,0,0,0,0,0,0,0,0,0,(word80 [0x0,0xc0c00000c0c00000]),4629700418014806016,0,0,0,0,0,0,54043195541028864,18014398513676288,(word80 [0x2000000,0x2000000020000000200]),(word80 [0x3000000,0x3000000030000000300]),0,0,0,0,0,0,(word80 [0x2020000,0x2020000020200000202]),(word80 [0xaa00ab030000,0x3030000030300000303]),0,(word80 [0x220022000000,0x0]),0,(word80 [0xa000a000000,0x0]),0,(word80 [0x20002000000,0x0]),0,0,0,0,0,0,3233808384,1077936128,0,(word80 [0xaa000000,0x0]),0,(word80 [0x22000000,0x0]),0,(word80 [0xa000000,0x0]),12582912,(word80 [0x2000000,0x400000])]
private def badMask (w : LocalSix) := badData[w.toNat]?.getD 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem badMask_ok : ∀ a v : LocalSix, (badMask a).testBit v.toNat = !(missesPair majGoal a v) := by decide +kernel

private def allowsWord (cover : Nat) (w : LocalSix) := cover.testBit w.toNat
private def paidCell (B : List LocalSix) (cover : Nat) :=
  (!allowsWord cover majGoal) && (localBag B).all (allowsWord cover) &&
  (localBag B).all (fun w => (cover &&& badMask w) == 0) &&
  (genLocal B).all fun w => allowsWord cover w && allowsWord cover (~~~w)
private theorem antiPair : ∀ w : LocalSix, w ≠ majGoal → ~~~w ≠ majGoal →
    ∀ a b : Bool, missesPair majGoal (if a then w else ~~~w) (if b then w else ~~~w)=true := by decide +kernel
private theorem pairRev (a b : LocalSix) : missesPair majGoal a b=missesPair majGoal b a := by
  simp only [missesPair,BitVec.and_comm a b,BitVec.or_comm a b]
private theorem paidCell_sound {B K} (pass : paidCell B K=true) : localMiss majGoal 2 B=true := by
  simp only [paidCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,beq_iff_eq] at pass
  obtain ⟨⟨⟨off,old⟩,clean⟩,moves⟩ := pass
  have avoid {v} (on : allowsWord K v=true) : v≠majGoal := by
    intro eq
    subst v
    rw [off] at on
    contradiction
  have guard {a v} (ha : a∈localBag B) (hV : allowsWord K v=true) : missesPair majGoal a v=true := by
    have eq := congrArg (fun n : Nat => n.testBit v.toNat) (clean a ha)
    change K.testBit v.toNat=true at hV
    simpa [Nat.testBit_and,hV,badMask_ok] using eq
  have oldNo : !(localBag B).contains majGoal = true := by
    have no : majGoal ∉ localBag B := fun p => avoid (old _ p) rfl
    simpa using no
  apply fastTwo_sound
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true]
  refine ⟨oldNo,?_⟩
  intro w hw
  have win := moves w hw
  have membership {a} (ha : a∈localBag (w::B)) : allowsWord K a=true := by
    rcases (bag_cons a w B).mp ha with rfl | rfl | original
    · exact win.1
    · exact win.2
    · exact old _ original
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true]
  have no : majGoal ∉ localBag (w::B) := fun hx => avoid (membership hx) rfl
  refine ⟨by simpa using no,?_⟩
  intro a ha b hb
  by_cases origA : a ∈ localBag B
  · exact guard origA (membership hb)
  by_cases origB : b ∈ localBag B
  · rw [pairRev]
    exact guard origB (membership ha)
  have da := (bag_cons a w B).mp ha
  have db := (bag_cons b w B).mp hb
  have core := antiPair w (avoid win.1) (avoid win.2)
  rcases da with rfl | rfl | bad
  · rcases db with rfl | rfl | bad
    · exact core true true
    · exact core true false
    · contradiction
  · rcases db with rfl | rfl | bad
    · exact core false true
    · exact core false false
    · contradiction
  · contradiction

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end0 : localMiss majGoal 2 (state2 0)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end1 : localMiss majGoal 2 (state2 1)=true := by apply paidCell_sound (K:=(word80 [0xfcbdc000f0f1,0xd011880b8f0f0003bd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end2 : localMiss majGoal 2 (state2 2)=true := by apply paidCell_sound (K:=(word80 [0xfcbdc000b0f1,0xd011880b8f0d0003bd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end3 : localMiss majGoal 2 (state2 3)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end4 : localMiss majGoal 2 (state2 4)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b033,0x91118889cc0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end5 : localMiss majGoal 2 (state2 5)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xd111888bcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end6 : localMiss majGoal 2 (state2 6)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end7 : localMiss majGoal 2 (state2 7)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c801b033,0x91318c89cc0d80139d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end8 : localMiss majGoal 2 (state2 8)=true := by apply paidCell_sound (K:=(word80 [0xdcb9d000b833,0x91118889cc1d000b9d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end9 : localMiss majGoal 2 (state2 9)=true := by apply paidCell_sound (K:=(word80 [0xfcfdc000b233,0x91118889cc4d0003bf3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end10 : localMiss majGoal 2 (state2 10)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0x91118889cc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end11 : localMiss majGoal 2 (state2 11)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x99318c99cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end12 : localMiss majGoal 2 (state2 12)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b033,0x91118889cc0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end13 : localMiss majGoal 2 (state2 13)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end14 : localMiss majGoal 2 (state2 14)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b033,0x91118889cc0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end15 : localMiss majGoal 2 (state2 15)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end16 : localMiss majGoal 2 (state2 16)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b133,0x91118889cc8d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end17 : localMiss majGoal 2 (state2 17)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc401b033,0x91118889cc0d8023dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end18 : localMiss majGoal 2 (state2 18)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end19 : localMiss majGoal 2 (state2 19)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0xb111888dcc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end20 : localMiss majGoal 2 (state2 20)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b3,0x91118889cd0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end21 : localMiss majGoal 2 (state2 21)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0xb111888dcc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end22 : localMiss majGoal 2 (state2 22)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end23 : localMiss majGoal 2 (state2 23)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000f031,0xd011880b8c0f00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end24 : localMiss majGoal 2 (state2 24)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b033,0x90118809cc0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end25 : localMiss majGoal 2 (state2 25)=true := by apply paidCell_sound (K:=(word80 [0xddb9d000b0b1,0x901188098d0d000b9dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end26 : localMiss majGoal 2 (state2 26)=true := by apply paidCell_sound (K:=(word80 [0xfdfdc000b031,0x901188098c0d0003bfbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end27 : localMiss majGoal 2 (state2 27)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x90b18d098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end28 : localMiss majGoal 2 (state2 28)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b031,0x911188898c0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end29 : localMiss majGoal 2 (state2 29)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end30 : localMiss majGoal 2 (state2 30)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b131,0x901188098c8d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end31 : localMiss majGoal 2 (state2 31)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end32 : localMiss majGoal 2 (state2 32)=true := by apply paidCell_sound (K:=(word80 [0xddbbc041b031,0x901188098c0d8203ddbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end33 : localMiss majGoal 2 (state2 33)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end34 : localMiss majGoal 2 (state2 34)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b1,0x911188898d0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end35 : localMiss majGoal 2 (state2 35)=true := by apply paidCell_sound (K:=(word80 [0xddbdc000b031,0xb111888d8c0d0003bdbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end36 : localMiss majGoal 2 (state2 36)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b1,0x901188098d0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end37 : localMiss majGoal 2 (state2 37)=true := by apply paidCell_sound (K:=(word80 [0xddfbc000b031,0xb011880d8c0d0003dfbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end38 : localMiss majGoal 2 (state2 38)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end39 : localMiss majGoal 2 (state2 39)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xd011880bcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end40 : localMiss majGoal 2 (state2 40)=true := by apply paidCell_sound (K:=(word80 [0xfcfdc000f031,0xd011880b8c0f0003bf3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end41 : localMiss majGoal 2 (state2 41)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd0318c0b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end42 : localMiss majGoal 2 (state2 42)=true := by apply paidCell_sound (K:=(word80 [0xfcb9cc00f031,0xd411882b8c0f00339d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end43 : localMiss majGoal 2 (state2 43)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end44 : localMiss majGoal 2 (state2 44)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f031,0xd011880b8c0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end45 : localMiss majGoal 2 (state2 45)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f431,0xd011880b8c2f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end46 : localMiss majGoal 2 (state2 46)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end47 : localMiss majGoal 2 (state2 47)=true := by apply paidCell_sound (K:=(word80 [0xfcbbe000f031,0xd011880b8c0f0007dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end48 : localMiss majGoal 2 (state2 48)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc011f031,0xd011880b8c0f8803dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end49 : localMiss majGoal 2 (state2 49)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end50 : localMiss majGoal 2 (state2 50)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xf111888f8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end51 : localMiss majGoal 2 (state2 51)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f0b1,0xd011880b8d0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end52 : localMiss majGoal 2 (state2 52)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f031,0xf011880f8c0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end53 : localMiss majGoal 2 (state2 53)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end54 : localMiss majGoal 2 (state2 54)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0x90118809cc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end55 : localMiss majGoal 2 (state2 55)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90399c09cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end56 : localMiss majGoal 2 (state2 56)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b033,0x90118809cc0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end57 : localMiss majGoal 2 (state2 57)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end58 : localMiss majGoal 2 (state2 58)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end59 : localMiss majGoal 2 (state2 59)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end60 : localMiss majGoal 2 (state2 60)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc005b033,0x90118809cc0da003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end61 : localMiss majGoal 2 (state2 61)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end62 : localMiss majGoal 2 (state2 62)=true := by apply paidCell_sound (K:=(word80 [0xdcbdc000b033,0xb111888dcc0d0003bd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end63 : localMiss majGoal 2 (state2 63)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b3,0x90118809cd0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end64 : localMiss majGoal 2 (state2 64)=true := by apply paidCell_sound (K:=(word80 [0xdcbfc000b033,0xb011880dcc0d0003fd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end65 : localMiss majGoal 2 (state2 65)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc001f033,0xd011880bcc0f8003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end66 : localMiss majGoal 2 (state2 66)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xf011880fcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end67 : localMiss majGoal 2 (state2 67)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc01b031,0x9113c8898c0d80339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end68 : localMiss majGoal 2 (state2 68)=true := by apply paidCell_sound (K:=(word80 [0xfdb9d000b0b1,0x901188098d0d000b9dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end69 : localMiss majGoal 2 (state2 69)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b031,0x901188098c0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end70 : localMiss majGoal 2 (state2 70)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b031,0x901188098c0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end71 : localMiss majGoal 2 (state2 71)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc08b031,0x901188098c0d10339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end72 : localMiss majGoal 2 (state2 72)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc01b031,0x911188898c0d80339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end73 : localMiss majGoal 2 (state2 73)=true := by apply paidCell_sound (K:=(word80 [0xdcbbcc01b033,0x90118809cc0d8033dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end74 : localMiss majGoal 2 (state2 74)=true := by apply paidCell_sound (K:=(word80 [0xfcb9cc00b0b1,0x901998098d0d00339d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end75 : localMiss majGoal 2 (state2 75)=true := by apply paidCell_sound (K:=(word80 [0xdcbbcc00b031,0xb013c80d8c0d0033dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end76 : localMiss majGoal 2 (state2 76)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end77 : localMiss majGoal 2 (state2 77)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end78 : localMiss majGoal 2 (state2 78)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c080b031,0x901188098c0d01039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end79 : localMiss majGoal 2 (state2 79)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end80 : localMiss majGoal 2 (state2 80)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end81 : localMiss majGoal 2 (state2 81)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0xb1318c8d8c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end82 : localMiss majGoal 2 (state2 82)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x909189098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end83 : localMiss majGoal 2 (state2 83)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb0318c0d8c0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end84 : localMiss majGoal 2 (state2 84)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b031,0xb111888d8c0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end85 : localMiss majGoal 2 (state2 85)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end86 : localMiss majGoal 2 (state2 86)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end87 : localMiss majGoal 2 (state2 87)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end88 : localMiss majGoal 2 (state2 88)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b131,0xb111888d8c8d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end89 : localMiss majGoal 2 (state2 89)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x901188098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end90 : localMiss majGoal 2 (state2 90)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb011880d8c0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end91 : localMiss majGoal 2 (state2 91)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end92 : localMiss majGoal 2 (state2 92)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc401b031,0xb111888d8c0d8023dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end93 : localMiss majGoal 2 (state2 93)=true := by apply paidCell_sound (K:=(word80 [0xfcbbd001b0b1,0x901188098d0d800bdd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end94 : localMiss majGoal 2 (state2 94)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0xb011880d8c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end95 : localMiss majGoal 2 (state2 95)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x901188098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end96 : localMiss majGoal 2 (state2 96)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000b0b1,0xb011880d8d0d0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end97 : localMiss majGoal 2 (state2 97)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb011880d8c0d0003dd3b])); decide +kernel
private theorem stage2 : ∀ i : Nat, i < 98 → localMiss majGoal 2 (state2 i)=true
  | 0,_ => end0
  | 1,_ => end1
  | 2,_ => end2
  | 3,_ => end3
  | 4,_ => end4
  | 5,_ => end5
  | 6,_ => end6
  | 7,_ => end7
  | 8,_ => end8
  | 9,_ => end9
  | 10,_ => end10
  | 11,_ => end11
  | 12,_ => end12
  | 13,_ => end13
  | 14,_ => end14
  | 15,_ => end15
  | 16,_ => end16
  | 17,_ => end17
  | 18,_ => end18
  | 19,_ => end19
  | 20,_ => end20
  | 21,_ => end21
  | 22,_ => end22
  | 23,_ => end23
  | 24,_ => end24
  | 25,_ => end25
  | 26,_ => end26
  | 27,_ => end27
  | 28,_ => end28
  | 29,_ => end29
  | 30,_ => end30
  | 31,_ => end31
  | 32,_ => end32
  | 33,_ => end33
  | 34,_ => end34
  | 35,_ => end35
  | 36,_ => end36
  | 37,_ => end37
  | 38,_ => end38
  | 39,_ => end39
  | 40,_ => end40
  | 41,_ => end41
  | 42,_ => end42
  | 43,_ => end43
  | 44,_ => end44
  | 45,_ => end45
  | 46,_ => end46
  | 47,_ => end47
  | 48,_ => end48
  | 49,_ => end49
  | 50,_ => end50
  | 51,_ => end51
  | 52,_ => end52
  | 53,_ => end53
  | 54,_ => end54
  | 55,_ => end55
  | 56,_ => end56
  | 57,_ => end57
  | 58,_ => end58
  | 59,_ => end59
  | 60,_ => end60
  | 61,_ => end61
  | 62,_ => end62
  | 63,_ => end63
  | 64,_ => end64
  | 65,_ => end65
  | 66,_ => end66
  | 67,_ => end67
  | 68,_ => end68
  | 69,_ => end69
  | 70,_ => end70
  | 71,_ => end71
  | 72,_ => end72
  | 73,_ => end73
  | 74,_ => end74
  | 75,_ => end75
  | 76,_ => end76
  | 77,_ => end77
  | 78,_ => end78
  | 79,_ => end79
  | 80,_ => end80
  | 81,_ => end81
  | 82,_ => end82
  | 83,_ => end83
  | 84,_ => end84
  | 85,_ => end85
  | 86,_ => end86
  | 87,_ => end87
  | 88,_ => end88
  | 89,_ => end89
  | 90,_ => end90
  | 91,_ => end91
  | 92,_ => end92
  | 93,_ => end93
  | 94,_ => end94
  | 95,_ => end95
  | 96,_ => end96
  | 97,_ => end97
  | i+98,ht => by omega
private def map1 : Array (Array Nat) := #[#[0,194,0,190,6,183,0,0,44,0,76,171,106,0,0,0,7,182,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,77,170,0,0,0,0,0,0,0,0,0,0,0,153,107,0,0,0,0,0,0,0,0,0,0,152,0,0,0,138,138,0,0,0,152,0,0,0,0,0,0,0,0,0,0,107,153,0,0,0,0,0,0,0,0,0,0,0,170,77,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,182,7,0,0,0,106,171,76,0,44,0,0,183,6,190,0,194,0],#[6,42,0,40,6,38,0,0,8,0,10,36,12,0,0,6,14,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,18,32,0,0,0,0,0,0,6,6,0,0,20,30,22,0,0,6,0,0,0,28,0,0,0,26,0,0,0,24,24,0,0,0,26,0,0,0,28,0,0,0,6,0,0,22,30,20,0,0,6,6,0,0,0,0,0,0,32,18,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,14,6,0,0,12,36,10,0,8,0,0,38,6,40,0,42,6],#[44,74,0,72,8,70,0,68,44,0,46,66,48,0,0,44,17,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,0,52,62,0,0,0,0,0,0,44,44,0,0,0,60,54,0,0,44,0,0,0,0,0,0,0,58,0,0,0,56,56,0,0,0,58,0,0,0,0,0,0,0,44,0,0,54,60,0,0,0,44,44,0,0,0,0,0,0,62,52,0,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,17,44,0,0,48,66,46,0,44,68,0,70,8,72,0,74,44],#[76,104,2,102,10,100,0,0,46,0,76,98,78,0,0,76,19,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,94,80,92,0,0,0,0,0,0,76,76,0,0,0,90,82,88,0,76,0,0,0,0,0,0,0,86,0,0,0,84,84,0,0,0,86,0,0,0,0,0,0,0,76,0,88,82,90,0,0,0,76,76,0,0,0,0,0,0,92,80,94,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,19,76,0,0,78,98,76,0,46,0,0,100,10,102,2,104,76],#[106,128,0,126,12,124,0,0,48,0,78,122,106,0,0,106,23,120,0,0,0,0,0,0,0,0,0,0,0,0,0,0,55,0,83,118,0,0,0,0,0,0,106,106,0,0,108,116,110,0,0,106,0,0,0,0,0,0,0,114,0,0,0,112,112,0,0,0,114,0,0,0,0,0,0,0,106,0,0,110,116,108,0,0,106,106,0,0,0,0,0,0,118,83,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,120,23,106,0,0,106,122,78,0,48,0,0,124,12,126,0,128,106],#[138,150,0,148,24,147,0,0,56,0,84,143,112,0,0,138,25,146,0,0,134,144,0,0,0,0,0,0,0,0,0,0,57,0,85,142,0,0,0,0,0,0,138,138,0,0,0,141,113,0,0,138,0,0,0,0,0,0,0,140,0,0,0,138,138,0,0,0,140,0,0,0,0,0,0,0,138,0,0,113,141,0,0,0,138,138,0,0,0,0,0,0,142,85,0,57,0,0,0,0,0,0,0,0,0,0,144,134,0,0,146,25,138,0,0,112,143,84,0,56,0,0,147,24,148,0,150,138],#[152,166,0,164,26,162,0,0,58,0,86,160,114,0,0,152,31,158,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,0,91,156,0,0,0,0,0,0,152,152,0,0,0,154,117,0,0,152,0,0,0,0,0,0,0,152,0,0,0,140,140,0,0,0,152,0,0,0,0,0,0,0,152,0,0,117,154,0,0,0,152,152,0,0,0,0,0,0,156,91,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,158,31,152,0,0,114,160,86,0,58,0,0,162,26,164,0,166,152],#[170,180,0,178,32,176,0,0,62,0,92,174,118,0,0,170,37,172,0,0,0,0,0,0,0,0,0,0,0,0,0,0,67,0,99,170,0,0,0,0,0,0,170,170,0,0,0,161,123,0,0,170,0,0,0,0,0,0,0,156,0,0,0,142,142,0,0,0,156,0,0,0,0,0,0,0,170,0,0,123,161,0,0,0,170,170,0,0,0,0,0,0,170,99,0,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,172,37,170,0,0,118,174,92,0,62,0,0,176,32,178,0,180,170],#[182,188,0,186,34,184,0,0,64,0,96,177,120,0,130,182,39,182,0,0,0,0,0,0,0,0,0,0,0,0,0,169,71,0,101,172,0,0,0,0,0,0,182,182,0,0,0,163,125,0,0,182,0,0,0,0,0,0,0,158,0,0,0,146,146,0,0,0,158,0,0,0,0,0,0,0,182,0,0,125,163,0,0,0,182,182,0,0,0,0,0,0,172,101,0,71,169,0,0,0,0,0,0,0,0,0,0,0,0,0,182,39,182,130,0,120,177,96,0,64,0,0,184,34,186,0,188,182],#[190,192,4,190,40,187,0,0,72,0,102,179,126,0,0,190,41,186,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,103,178,0,0,0,0,136,0,190,190,0,0,0,165,127,0,0,190,0,0,0,0,0,0,0,164,0,0,0,148,148,0,0,0,164,0,0,0,0,0,0,0,190,0,0,127,165,0,0,0,190,190,0,136,0,0,0,0,178,103,0,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,186,41,190,0,0,126,179,102,0,72,0,0,187,40,190,4,192,190],#[194,194,0,192,42,189,0,0,74,0,104,181,128,0,132,194,43,188,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,0,105,180,0,0,0,0,0,0,194,194,0,0,0,167,129,0,133,194,0,0,0,0,0,0,0,166,0,0,0,150,150,0,0,0,166,0,0,0,0,0,0,0,194,133,0,129,167,0,0,0,194,194,0,0,0,0,0,0,180,105,0,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,188,43,194,132,0,128,181,104,0,74,0,0,189,42,192,0,194,194]]
private def tag1 (i : Nat) (w : LocalSix) := ((map1[i]?).getD #[])[w.toNat]?.getD 0
private def pass1 (i : Nat) := (genLocal (state1 i)).all (fun w =>
    let t := tag1 i w
    decide (t/2 < 98) && (permWord (axisOf t) majGoal == majGoal) &&
      embeds (axisOf t) (w::state1 i) (state2 (t/2)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_0 : pass1 0=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_1 : pass1 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_2 : pass1 2=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_3 : pass1 3=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_4 : pass1 4=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_5 : pass1 5=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_6 : pass1 6=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_7 : pass1 7=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_8 : pass1 8=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_9 : pass1 9=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_10 : pass1 10=true := by decide +kernel
private theorem selected1 : ∀ i : Nat, i < 11 → pass1 i=true
  | 0,_ => pass1_0
  | 1,_ => pass1_1
  | 2,_ => pass1_2
  | 3,_ => pass1_3
  | 4,_ => pass1_4
  | 5,_ => pass1_5
  | 6,_ => pass1_6
  | 7,_ => pass1_7
  | 8,_ => pass1_8
  | 9,_ => pass1_9
  | 10,_ => pass1_10
  | i+11, ht => by omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem old1 : ∀ i : Fin 11, !(localBag (state1 i.val)).contains majGoal = true := by decide +kernel
private theorem stage1 (i : Nat) (hi : i < 11) : localMiss majGoal 3 (state1 i)=true := by
  change (_ && _)=true
  rw [Bool.and_eq_true]
  refine ⟨old1 ⟨i,hi⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  have v := List.all_eq_true.mp (selected1 i hi) w hw
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  exact pullMiss v.1.2 2 v.2 (stage2 _ v.1.1)
private def map0 : Array (Array Nat) := #[#[0,20,0,18,2,17,0,0,4,0,6,15,8,0,0,0,3,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,7,14,0,0,0,0,0,0,0,0,0,0,0,13,9,0,0,0,0,0,0,0,0,0,0,12,0,0,0,10,10,0,0,0,12,0,0,0,0,0,0,0,0,0,0,9,13,0,0,0,0,0,0,0,0,0,0,0,14,7,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,3,0,0,0,8,15,6,0,4,0,0,17,2,18,0,20,0]]
private def tag0 (i : Nat) (w : LocalSix) := ((map0[i]?).getD #[])[w.toNat]?.getD 0
private def pass0 (i : Nat) := (genLocal (state0 i)).all (fun w =>
    let t := tag0 i w
    decide (t/2 < 11) && (permWord (axisOf t) majGoal == majGoal) &&
      embeds (axisOf t) (w::state0 i) (state1 (t/2)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass0_0 : pass0 0=true := by decide +kernel
private theorem selected0 : ∀ i : Nat, i < 1 → pass0 i=true
  | 0,_ => pass0_0
  | i+1, ht => by omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem old0 : ∀ i : Fin 1, !(localBag (state0 i.val)).contains majGoal = true := by decide +kernel
private theorem stage0 (i : Nat) (hi : i < 1) : localMiss majGoal 4 (state0 i)=true := by
  change (_ && _)=true
  rw [Bool.and_eq_true]
  refine ⟨old0 ⟨i,hi⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  have v := List.all_eq_true.mp (selected0 i hi) w hw
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  exact pullMiss v.1.2 3 v.2 (stage1 _ v.1.1)
private theorem local_miss_three : localMiss majGoal 4 majRoots=true := stage0 0 (by decide)
private theorem local_now {M n B} (h : localMiss M n B=true) : M ∉ localBag B := by
  cases n with
  | zero => simpa only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h
  | succ n =>
    simp only [localMiss,Bool.and_eq_true] at h
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h.1
theorem pattern_price {p bank} (reach : Reach true (majRoots.map localFun) p bank)
    (ok : Available true bank (localFun majGoal)) : 5 ≤ p := by
  by_contra small
  have le : p ≤ 4 := by omega
  have start : localMiss majGoal (p+(4-p)) ((majRoots.map localFun).map localWord)=true := by
    rw [show p+(4-p)=4 by omega]
    change localMiss majGoal 4 [localWord (localFun 43),localWord (localFun 42),localWord (localFun 76),localWord (localFun 112)] = true
    simpa only [majRoots,local_back] using local_miss_three
  have no := local_now (local_prefix reach _ _ start)
  have yes := local_available ok
  rw [local_back] at yes
  exact no yes


end PatternFive
end PEqualNP.Outside.L_meta_33242

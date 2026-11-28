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
      · simpa only [List.toFinset_card_of_nodup yes.2.2] using yes.1
      · simp only [enoughWeight,Bool.and_eq_true,decide_eq_true_eq] at valid
        have sumBound := fitsWeight_le t ws _ yes.2.2 valid.2
        rw [goalWeight_eq] at valid sumBound
        have positive := valid.1
        change (∑ w ∈ ws.toFinset, literalCost t w) < literalCost t T
        omega
    next => simp at h

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
    (List.range (offsetCode % 16)).map (fun j => atSix sixMenuWords (offsetCode / 16 + j))
  else []

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query ++ ((g.index k tag).bind (linkedSet g (k-1))).toList
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
    rcases List.mem_append.mp hx with extra | old
    · exact closeSix_sound extra g.mode
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using old
      obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) h



def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
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
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

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
    apply Bool.or_eq_true.mpr
    right
    simp only [Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
  let ls := fun tag query => closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query ++ ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) (query : List Sig) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag query, ys=xs.map BitVec.toNat := by
  suffices old : ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, ys=xs.map BitVec.toNat by
    obtain ⟨xs,mem,eq⟩ := old
    exact ⟨xs,List.mem_append_right _ mem,eq⟩
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
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

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

def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf0000ff00fe080106a,0x300fa047c6f3679fc7ab])),(BitVec.ofNat 152 (word80 [0x505050505060040022,0x10012402022303880208]))),((BitVec.ofNat 152 (word80 [0xff00ff001000093,0xc0300186090399f80000])),(BitVec.ofNat 152 (word80 [0x323232323221000012,0x40100186010288b88000]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000000fe000e31c,0x3c041f831fc1e1fe8cd])),(BitVec.ofNat 152 (word80 [0xa0a0a0a0a080084110,0x40488011401c10a000]))),((BitVec.ofNat 152 (word80 [0xff0020303e0,0xc007e003e001fe00e10])),(BitVec.ofNat 152 (word80 [0xc9c9c9c9c9c20303e0,0x24006e003e0017400e10]))),((BitVec.ofNat 152 (word80 [0xffffff0001c03fc00,0xfff80003fffe0000f10])),(BitVec.ofNat 152 (word80 [0x50505050510210000,0x8eaa00296c8000010c00]))),((BitVec.ofNat 152 (word80 [0xf0000000001ffc0000,0xfffffffc0000000301f])),(BitVec.ofNat 152 (word80 [0x60606060619300000,0xb3c1175800840020000]))),((BitVec.ofNat 152 (word80 [0x1fffffff,0xf0000000000000003fe0])),(BitVec.ofNat 152 (word80 [0x80808080802429acd,0x40000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,16,169,66,9),(32,0,219,0,9),(2,16,169,64,8),(18,0,233,0,8),(34,0,217,0,8),(48,0,203,0,8),(64,16,169,2,8),(80,0,171,0,8),(0,2,73,176,7),(3,0,248,0,7),(10,0,241,0,7),(17,0,234,0,7),(24,0,227,0,7),(50,0,201,0,7),(65,0,186,0,7),(66,0,169,0,7),(66,16,169,0,7),(72,0,179,0,7),(82,0,169,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,121,0,7),(136,0,115,0,7),(144,0,107,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,16,168,66,6),(8,16,161,66,6),(9,0,242,0,6),(16,2,73,160,6),(32,2,73,144,6),(32,16,137,66,6),(33,0,218,0,6),(40,0,211,0,6),(128,2,73,48,6),(128,16,41,66,6),(25,0,226,0,5),(35,0,216,0,5),(42,0,209,0,5),(49,0,202,0,5),(56,0,195,0,5),(73,0,178,0,5),(144,2,73,32,5),(160,2,73,16,5),(162,0,89,0,5),(11,0,240,0,4),(67,0,168,0,4),(67,16,168,0,4),(74,0,161,0,4),(74,16,161,0,4),(89,0,162,0,4),(97,0,154,0,4),(98,0,137,0,4),(98,16,137,0,4),(104,0,147,0,4),(131,0,120,0,4),(137,0,114,0,4),(138,0,113,0,4),(145,0,106,0,4),(152,0,99,0,4),(161,0,90,0,4),(168,0,83,0,4),(176,0,73,0,4),(176,2,73,0,4),(193,0,58,0,4),(194,0,41,0,4),(194,16,41,0,4),(200,0,51,0,4)]
def g251A : List (List Nat) := [[],[48]]
def g251D6 := limbs80 #[#[0x50940481a0619741d120,0x48185595425012059563,0x59152501205d95454940,0x58120549615055048185,0x59554dc960501741d162,0xdc960543a25538258140,0xc2ba2553825815059154,0xf88f41782b615a8ad155,0x4ad17646d31c5d8ab0a3,0x28765296581d9396881b,0x9521b25064780cb22a59,0x40270130070033d3664b,0x27b90a02220c9053a0,0x1bcc0c023844010f03b0,0x134100000000b09]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x55151501105894250110,0xdc951501106095150110,0x58952501105515250110,0x54961501105096150110,0xe496150110dc96150110,0x55372501105d96450110,0x58952505105937250110,0x59372505105d96450510,0x59562549105516254910,0x58b80549106456254910,0x54941581105892158110,0xdc941581105914158110,0x5895258110dc95158110,0x59154581106095258110,0x5c96258110dd15458110,0xdd56258110dd16258110,0xdd564581105d16458110,0x55372581105d56558110,0x59772581105937258110,0x5d164585105d16358510,0x58f7258510dd56458510,0x59382585105937258510,0x641861d120619741d120,0x65874501206547450120,0x58d42501205514250120,0x59542501205914250120,0x61542501205d94250120,0x98d42501206194250120,0xe154250120dcd4250120,0x5095150120e194250120,0x58551501205515150120,0x5c551501205895150120],#[0x58d52501205515250120,0x59552501205915250120,0x65152501206155250120,0x991525012098d5250120,0xe195250120a515250120,0x5955450120e595250120,0xe5954501205d95450120,0x1d162501205096150120,0x551625012054d6250120,0x59562501205916250120,0x61962501205cd6250120,0x651625012064d6250120,0xa5162501209516250120,0xe556250120e156250120,0x55163501201d16350120,0x95163501205956350120,0x61564501205d96450120,0xe556450120e156450120,0x25176501206156550120,0x64a54501205da5450120,0x50b715012064a6450120,0x58541541205494154120,0x5c541541205894154120,0x591525412058d5254120,0x61952541205d15254120,0x9d152541209915254120,0xe115254120a115254120,0x5915454120e195254120,0x5d954541205d15454120,0x9d154541209915454120,0x5496154120e595454120,0x55162541205c56154120],#[0x61962541205956254120,0xe1162541206456254120,0x5956354120e516254120,0xe516554120e116354120,0x58971541205497154120,0x54b41541205957154120,0x597845412058b4154120,0x55161545206415454520,0x55171545206416554520,0x66176551205957154520,0x58951581205d07458120,0x5c551581205955158120,0x59154581206055158120,0x5d154581205955458120,0x1d162581205d55458120,0x5d162581205516258120,0x95162581205d56258120,0xa1162581209d16258120,0xdcd6258120d0d6258120,0xdd56258120dd16258120,0xe156258120e116258120,0x9d164581205d16458120,0xe556458120dd56458120,0xe5165581205d56558120,0x5d254581205925458120,0x547415812064a5458120,0x593415812058b4158120,0x58b715812064b4158120,0x59774581205977158120,0x5955458d205d07458d20,0x65d5458d205d15458d20,0x6416558d205d56558d20],#[0xa5d6558d2065d6558d20,0xe597458d205957458d20,0x65e5458d205d25458d20,0x5977458d2065e7458d20,0x25176591206537558d20,0x610845d9206427459120,0xdd551d05205918095120,0x59180d052061d63d0520,0x59563509405916250930,0x59162549405516254940,0x58942581405956254940,0x5d542581405954258140,0x65942581406094258140,0xdd54258140dc94258140,0x5095158140e554258140,0x59551581405515158140,0x5515258140e4d5158140,0x59152581405895258140,0x59154581405d55258140,0x64554581405955458140,0xe4954581406595458140,0x95162581405c96258140,0xdd56258140a516258140,0x5d56458140e556258140,0xdd5645814064d6458140,0xe556458140e496458140,0xa5165581405d56558140,0x5518158140e496558140,0x5974258140e498358140,0xdd742581405d74258140,0x593715814058b7158140,0x64b71581405977158140],#[0x59372581405537258140,0x95372581405977258140,0x64b815814050b8158140,0x59382581405538258140,0x95382581405978258140,0xdd564589406438258540,0x64a5458940a118058940,0xe495458d406438158940,0x65d6558d405d56558d40,0xa5d6558d40a516558d40,0xe41875954064b7558d40,0x60962dc54059563d0940,0x59554dc94058d82dc540,0x59563dc94055163dc940,0x64164585415d56458541,0x64b80585415938058541,0x59161505505496150550,0x59141581505494158150,0x58952581506054158150,0xdd152581506595258150,0x5915458150e515258150,0x64554581506115458150,0xa1154581506595458150,0x5c96258150e495458150,0xe516258150dd16258150,0x9d164581505d16458150,0x6516558150e496458150,0xe496558150a516558150,0xe457458150e516558150,0x55181581505498158150,0xe4981581506118158150,0x5967458150e458458150],#[0x54b41581505968458150,0x59741581505934158150,0x58b715815064b4158150,0x553725815064b7158150,0x59772581505937258150,0x59774581506537258150,0x553825815064b7458150,0xdd382581505978258150,0x64b74589506455458550,0x6516558d506496558d50,0x5967458d50a516558d50,0x64b7458d506427458d50,0x610845d95065f8159150,0x66176d055060962d0550,0x59154dc95060962dc550,0x641545855161163dc950,0x64154545605538058551,0x6427455160e497154560,0x64382551606438155160,0x60951d0560e498095160,0x59180d056054580d0560,0xe4980d0560dc980d0560,0x64254dc960e4954dc960,0x64b80551636416555163,0x5516254b406195454b40,0x5956254b405916254b40,0x5517258b405956354b40,0x551635cb405917258b40,0xae99e96793787e87b86f,0xea9ea5da379ea9da9ba9,0xb17b0faeaadaaceabaaa,0x33b2eb2db2bb27b1eb1b],#[0x7b6eb5ab4eb4bb3ab35b,0xba6b9eb9ab96b8eb8bb8,0xcabc6bb8bb2baebacbaa,0xfc37beabe8be2bdabceb,0xcbacaecadc9ec97c7ac4,0x2bd27d1ed1bd17ceacda,0xad4ed47d3ad35d2ed2dd,0xda6d9ed9dd96d8ed87d6,0xcadbadb2daedaddacdaa,0xbe27e1ee1be17de2ddad,0xe8de87e6ae5ae2ee2de2,0xaae9ee9de9ce9ae96e8e,0xaed2eceecaeaeeaceabe,0xf1bf1af0ef0bf07ee2ed,0x2ef2cf2bf2af1ef1df1c,0xdf4cf4af3cf3af38f34f,0xf8bf8af86f6cf5af4ef4,0xa2f9cf9af99f92f8ef8d,0xafc2fb8facfaafa9fa4f,0x22a803fe8fe2fd8fccfc,0xd59010feb18224d63034,0x8cb031a9860028ac8097,0x5640bc06ea1419e88148,0x7281e1ce943af0b2861f,0x6544a88ca09071a20fa2,0xd288067a2103aaca1c40,0x96078af4422196904233,0x282a456505231d10390d,0x884e37d1099797415a1b,0x284c61a4140c74a2718e,0x334c92c64e58e4c76ccb,0xc327b5d864ddc28c1619],#[0x462e4c28c6496518b570,0x8e1cb851bb930a3772e1,0x19bdaec336e6146664d0,0x356ee146a23540cc45a8,0x6a7acb0d587761ab0aec,0xe585761c88f4c353de58,0xc9ef2c393d65872c3bb0,0x66ae186cf7bb0d045a61,0x330aa10445a51d08f4a3,0xa6154233830a418e5948,0x41eec40835d880e0c291,0x5665880ddc3101b98620,0x5dd3100b9a6202b72c40,0xb98523bdaec426e61484,0x774a45096a48e5cd291d,0x65d88612d4920b9a5241,0x1bb11181762208350437,0x3a6221e72c443c65888c,0x2ca51096909420d29244,0x618b050d3145a98628c5,0xc294825a92c1434c586a,0xa5279474a526ae14a4d4,0x4c5928e98ae50d313cb9,0xa0a6ccc294c25a92c943,0x295425a42d8734c5a0e6,0x52e18b445f89594ba1dd,0xc4b65614bc4ed3170b5a,0x8ce12d11351196263aae,0x19cf58633a4eec67495d,0x30a232c6609e98ce7bc3,0x6309688c6bebb1897d76,0xd07ac29a110a930222ec],#[0xbd21761704f4a683de14,0x2adaec644f68c5ea0d10,0xf70e10dc78cc22c79a53,0x820d41cc41a8393b2ec6,0x581763a88350741f69ce,0x87487110698ea78cb1d,0x66618ff14b21fc41a43b,0x1cd320d99654192b4c7f,0x3ba44092f48800869508,0xaaec778e6890acab2a18,0xe688f65dd11e0b9a23d3,0x6bb23421a23e2032c792,0x9975a202ec87086890eb,0x2c8b63b661688d4bad11,0xdd52aa9c9a5511975aa8,0xcaae119955baa326b776,0xa7520e34ea4256954880,0xe89e2c6854a1cd429072,0x9d3c38d3a79d9754f3da,0x3a85ed745095b46a11ca,0x14e87350a11ca9d4238d,0xa9d7b5d13a56d1a74b1a,0x53ef7ba27c72a74e92b4,0xa9839a8510e34ea21ce9,0x5407350a31c69d4638d2,0xa71ce9140edbaa8039a5,0x32eabaa6439a4548e348,0x6911964dbaaca9b4465d,0x8282c8b2406593880cba,0xa28e895488cb2c511975,0x633d2aa91395553df44a,0x465a4560cb4eab286895],#[0xa232c9448655280ed12b,0x405d55e0ed12bd01955c,0x16d43357d76678af48ae,0x5ba65e39acabc0ae999c,0xb74cc403e997a7ccbaec,0x1659748ecaae80fa6628,0x6d2b0c0ea96102752ba4,0x1925f9f32ac703e998c0,0xb4ac113e958027d22f95,0x5d99805d024c0fa66409,0xd2b2461a164a22ecca5f,0x9216ae3462c5f6805824,0xc8e000ea5966acab2ced,0x91fe8cc93f08da66f27a,0x941101957f2232afd445,0x56abdac8da3a5920a7ac,0xad628e99b0f7bab55ed7,0x9ae0cd4b592d956b3aae,0xb6419a66e2232cdb4465,0x7ca5b2af9755d5f20dd2,0xe244659f688cb3e819a9,0xc296cb385d97571452a8,0x91129771baaeae323699,0x594344eb28e91d480cb3,0xd066a5d850d13b019a97,0xeab2c0019a4770e344e,0x51195808cb4d031969a0,0x2032b021ce8a0433d2c0,0xd69a0cc8b2c1847a283,0xbfbac1d7d758386b4d09,0xd77572adaeb080de960e,0x1f44e606699d296b2ba5],#[0x4dd5e488babc81ba2741,0xbbabbca7a1780334af24,0x9a2798cb44f119e89dee,0xb4af5405d5ec0cd23d81,0x592142bd13d019a97a91,0xbab44d3968c2eac9173a,0x76693130b16735d62ce6,0x4ed4745d5a644d3349d1,0x921c1ad343045a2860a3,0x2c685da285a12ed0d3a5,0x5878ef45195961636e6b,0x51113e8a2042d2c49296,0xa2826d2c4c4fa5888d74,0x5c5d176b89b1251503e9,0xb9aeb0f72745d6e444d3,0x705961ee828d3dcd6987,0xec2ed35d5d165ba87f41,0x92d95a139acb7742e56,0x282b53434065e8688cbd,0x776dd24a80b2d191992a,0xe0bd249815a6942032d2,0xc15a5988e3453025e965,0xe745481569a8eeab251,0x15e929280b2d291194a4,0x18d35359164a6887454d,0x2d6497067494e5b5969e,0x1f4d2a23e8a520ad34b9,0x5696680bd14b08da6969,0x2d3ccc8da59991f4b320,0x5a99f9c3313f4065e7e3,0x32f4015e8a9680b2d301,0x68a700ad4cd815a49ba0],#[0xb2d456965ae00f455b05,0x65ab0ef455d59596bc7e,0xcb5737a62aa7ccbd5531,0x82a849d054c93a0a91f2,0x4d6407a2ac09b4f54246,0x4b533acb686c592d001d,0x96c3ae56d274b25ad7d6,0x2c888b25b4fd65b6212c,0xd94e964b29c2cb643a59,0x8f9d2c9664b596c670b2,0x6018e8238bcbac78e564,0x443d25b8dd65b7b1ac9,0x22695403cd344019a550,0x2482ca05995500b10aa0,0xb2fe98090dbb01269a10,0xb2ec285083a605c32ca0,0xa09650bc8aca15965902,0xc82a81997684332cc285,0x716143520b286a41850c,0x1ac286df96411c0b0a1d,0x3d650947aca0d945901b,0xbd2e117765c2316b2042,0x65907b34aa0f675421eb,0x2b28ee69541fcea843f9,0x1651f4aac83e995507d3,0x748312fe987932d10f24,0x590a139d38c4cfa718ce,0xd194a55642b4aac85495,0x5236cb2c86b9b548d72a,0xc88b90594d932b21aa6d,0x48fd20b2a315d9645cca,0xb2221d7444482c87d9b5],#[0x645482ca8957e59110eb,0x4b3905950461d09c1e97,0x9312eb125d55655b4bac,0xa5641544ac8aca989758,0x48c62c88f906892d21ba,0x90576491cf2bb24a1574,0xbd2ab1375f297682bb24,0xddf9857ec6b48df8d699,0xc4ab06d59554daa54d33,0x49659248a6cb39d4d647,0x31ad2c8e41629148acb2,0xd3965a229ac9449058a8,0xa72cb3d9058a749ccc50,0x2669a76dec24ee35649d,0x9ccb4ae356495b4acb3c,0x39659c95743328d68652,0x62c92026e866a9cb2cf9,0xc592a0d6b256a31a590c,0xab2d89a165b3b6aeb698,0x9958ea732d618d592c29,0x80250026000118b257d4,0xe8035405a008b00f0019,0x16a02a204fc096811101,0xf901d9038206840c40,0x4209f812c023c0458084,0x329061c0bcc16882b905,0x81f283c107340da41a20,0x64125823784440852102,0x5690a82147827e04db09,0x42f485d40b7e167c2c48,0xd6194432086260c2617f,0x6e20d961abc34b067b0c],#[0xc3c4075d0e661c8837b0,0x66204c3fe07e50fa41ed,0x8c011502200433884e10,0x84a7092f122c24004728,0xf427544e009ac132c25b,0xa6914b829045158a1913,0x858c0af715ac2aa854a8,0x442e085b78b5816802cb,0xc3a183e30245f90bce17,0x66c8cab191431ac62a0,0x1835b46ab0d321a2a33f,0xe2f1c0a37886e30da71b,0x7608e9b1d0039987270,0xf63d3079b0f0b1dde3b6,0x2c20043f6c7d78f991e,0x486710b7212841c48269,0xd644e8899111f221043b,0x1ec23b246cc8c8917e22,0x4938925b247c48649031,0x484c1c97512d225644a3,0x3c127544e149b1133f26,0xca32944b2856502c9ec9,0x6e5464a7814ce294851d,0x5f52b8e56b4ac395632a,0xb4796772cb258e8b0d9,0x645c60b7f16e62d9c5ad,0x7c12f445e18bb617502e,0x4c1698162ff85f90bec1,0xf26328c54188f30fc616,0x97c32c66544c9c991d31,0xcd0499ee339c66b8cca1,0x8a6a84d3f1a523478687],#[0xb6536846cb0d831ada35,0x4dff1be237986ec0dc29,0x7e72a0e479c7038a270b,0xd6f3aa674f0e8d1cea39,0xf0a9ddf3b747660ec49,0xce7b60f569e8f3cbc792,0xf8a3ed67d44f999f0d3d,0x900a1ffe3fbc7f00fd11,0xa282a90422066406c809,0x1634290846108220f341,0x50f621d4438e86e10c6a,0x668a99144a267447a883,0x34446548c1d17022bf45,0xd1eb23ba47348dd51aba,0x29175220242947f88fa,0x51749f49371263a4a949,0x92d7a58b4ae6954929ca,0xd698e531025fe4bd0974,0x6ee4da69ae135026854c,0x13d0a7814ec49cfd388a,0x4a19541928064fc09f1,0x92b520aa39d45fa8a251,0x94e6a9b0533ca5b54a12,0x26a9c5527aa325430a7b,0xb36562cabd55642aa755,0x15f02bc8575eae215afa,0xb2b2d9648ac6d5876b04,0xd515a66b47d686acfb59,0xd6f3adc55b30b6056b82,0x76ba65740ae545c78b84,0xf425e4ebc3d777aed25d,0x17f42fc05f40bde17ada],#[0x6cc249835304b6072c03,0x15c626cc469880b0e261,0x18e8b1bc635ac6498ba3,0x42c9d1926b22a6430c7e,0x34a6640cc0597432c965,0x19e133a86710cda19acb,0xe8d141a18341767fccf9,0x5396a14d39da5eb48c68,0x1afab5cb6b44d611aaeb,0x60da61b4136696c7cd83,0x72b6e24dc09b7936da6d,0xdbd4b79a6f02dda5b9fb,0x90e0a1c09b7fe6fcedf1,0x8d57162e281c41387570,0x5cb4394c7266e415c79b,0x20e7e5ceeb9b87316e5f,0xa7874bee93dd1c3a2774,0x9d70bacf757cead9d4bb,0xdced81da4bb2a7630ebe,0xbe877a2eeb5dcb3b7d76,0xde413c6a789af0b5e033,0x20f3d1e663cc4794af24,0xdb87b14f5e1eadbd2e7a,0xdf2c3e3f7c40f7d9eeeb,0x92fb05f4f3e8e7cfef99,0xf527e6cfc81f7e3edb7d,0x5fd7bf8a7f04fdb1fad3,0x9700be00bbffa7faafef,0xe981a702ea048407280,0x60be416282a304aa0874,0xd906fa0d841a88335062,0x1007009806a120421f83],#[0x8bc0007b6080640bee,0x27b803c0809de140c405,0x3807de1360740b612e14,0x64380e580006c10ae08c,0x46427c05f61605085321,0xf9438e2906b60d051e08,0x4e300ac62aa142662280,0x800e1c868867a08c2ba1,0x6ae0fa04a280a003fc06,0xd064093a0c0f0e2186a0,0x4bf25961fa1065810d05,0x1503c83a09162887b068,0xbc0e258a2c45ea1fe0c0,0xc0942945887fc1045320,0x808bc1250981180b5632,0xa23a65a62800e61c0840,0xe04610c01c12428c6507,0x5825f05a829c0e03c899,0x108b21ce14e596168096,0x258468491c08e2de0e61,0x2a078a7ee0523043a231,0xd831493050a79c2a6158,0xcc04303860909106c0e,0x5a83e6080e8a116040f4,0xde1922b6180a961903a8,0x490c93017e0721209a0b,0x2b22b072c02a5849c49a,0xa27e86a631a1741c02b4,0xc6866703207d07c67e03,0x42844309380488b600,0x1810c08255808258e1b0,0x2720ad04d804c16430c1],#[0xbf01e22e81f4030280d5,0xd22c4700b2a280baa2d0,0x65681462da12a3162c01,0x11070a31a31a2e21ce11,0xf82b07827261ae1a09fe,0xc2983863085ec1c47a60,0x1121985340d60960f01a,0xa87c830076452832a0ac,0x6c828a5722ea56a20a1,0x1625ca5cc5845b404456,0xc811c1e20aa108920178,0x42213808110104094a1,0x750441000a60552040fe,0x1c032070100c94126050,0x86e83ae00e0280629029,0x3c3b5770a403a5ca2a90,0x10adc98abe62b8af0a,0x5fd132057e20995dfeb9,0x3da11b37741dbf8120d2,0x8c2bf406431cb611f047,0x1d9eb5149f9405197e81,0xa3f9019121fc0644a7a3,0x43d0c03a938c9428c710,0xde85156de31c1dd98ca4,0x6e8307ac9060670f8426,0x301cae996938683c1838,0x14c1fe856747dbc44f4,0x5d3fc0c15211ac074520,0x9c67a963f42326fe6504,0xb462a387e4910b0be602,0x2d0730b091f3b4c8b66b,0x42afea4724617e1dca1],#[0x6dd12fbc5a3422bfa802,0x277a18df860bcf821509,0x7e06643c247b8f21c709,0x1a4883c854f0341e8a16,0xb16c71db80c93e90445f,0xde1c6d100dc5869c2438,0x40cc62c3374ce9916cd7,0xf810c9b7f3c9028a9b1d,0x5095a498c318b19c323c,0xc61e856397d0507c97d0,0xbfa094bfcb2189983d0a,0x3091bf713217f9358994,0x88497ad1108e388c2b7,0x152f4327f530408537e8,0x4afdb28132f7a18ce449,0xc221ee4495c91ab9bd88,0x92007ff710033ed07703,0xca226573f586082a53ae,0x7c4299f10d3b698ccadf,0xc3dc4871d098ccebc92,0x84663beb40700a581c10,0x883df21c5fc434f56e,0xc32c918c18e7e44449fd,0x25a2a170d1d1376654eb,0x32561e58e2b9570520bf,0x97cc24dfe90e5464c70d,0x2b348bde121917ebb822,0x42afc44c0462f492649f,0xf6635f8d088a2fe6c4c9,0xb1149bfb19117c4e4448,0x348bbde90e1393195f72,0xaf9024e2879a7114bbd8],#[0x16af1c88a002b67ed061,0x88b0a679d263054b6edc,0xbc9171d3f884085862fa,0xff841421dfb881526ff5,0x7164cfd0c7cfe020a101,0xd8861f158d7d05a2057b,0x96505a6cf110480a6009,0xdc609486fce094247462,0x287962f76120e59411df,0x2764898e1a64d239b824,0xa65e3ff204522bc9941d,0x4694979646f89634e386,0xe5f1a4ca911e5906f629,0x4aebf8d132d7fd220656,0x7dbc44f432ced224ac84,0x6aecd2508a7b1d146af4,0xfc95a9bd0c7a11cbf2d0,0xb59f20650af2d279d9b1,0xcf1a2f2b25796abb7998,0xcc16dd891491c386d444,0x358d0d7f6412b794260c,0x5a48a3f1e3092363f91b,0xc6bfbc922efea104598f,0x1e38910b49a5bacc92f0,0x9478e24406f863497863,0x6735e91263f6a45af9e0,0xfed40459cd7a44af9e09,0xb20967a4110c87728222,0x3701f7584443674063bf,0x96d1de4bd9626dbb62c3,0x2e3fc82a04e866d9b961,0x4f312c74d1324bc68c04],#[0x1170ec510779689d2b14,0x9fc2cb459fe618455332,0x23c284c861e921e76425,0xa08413fd88400a527989,0x5de0a1a1e27845273f30,0xacf4b290a433a5b9584a,0x8ea8420bfb9508495be0,0xbebb928f1f535aa8436b,0xc0127b8602ee4a3b3928,0x93dc20047db052011f,0x29e8a54a78447ca428e,0x72ac86ca6ebd0ec5214a,0xd47c6b68b1d1fce84eae,0x6592105c0e3aa107e68d,0x75aa10ebdfa11846d7c,0x935f903ad44543ebebf2,0x114686019b3da0a62798,0x4926850e47461952d1fc,0x1475ffe35532e9fa062d,0x297e42b081f51b1edf48,0x53a3c28cafea8a3d980c,0x39f10a67c43e7bc5a84,0xd7a064a7f9b300c2866e,0xbf3100485264f021a16b,0x1a7a50e9a46cc1e43421,0xccd5e001929feec0020a,0xe6f80008152d7fe4004,0xbf140a10a5d18f682d4,0xb7b0313323ff61900543,0x38bfc122efcc0808c9f,0xf09802907ff04c8a806c,0xc12fee0251f9d4e88c77],#[0x4679e0434299e40546ec,0x3a7943dff8244eff4226,0x2b5d113ff4c800218d78,0x13334b97a332b3c5b20c,0x34f2869e89e3227497a1,0xf35509dd2bc64e4be321,0x4c7df416a65b6d0c1b19,0x3813114967c88254845e,0x1fe17e841d2d0c45f43a,0xaa7ceb530025329c5513,0x1165e1117e27225fec04,0xfee8b5461bc6689270fd,0x3c801949efddeb0e2430,0xb28ad4c86190796164a,0xe5814692081468d308f3,0x410aa6c3f41a110a553,0x72030840edd23205f1b5,0x465c135e40cc1df2064d,0xc6c88cfb240742f9a9a3,0x9f45885375b3ccb50a59,0x50b28dd6c28c634203ca,0x6ac20c2e249e10a5ee6b,0x8427b37f2109170aea3c,0x9432e054cb85705ebbf2,0x6524f8423295f8b0022a,0x950a027fa08a85af8480,0x96c6e57d71c2159c5f00,0x212ffc08999c631512b1,0x89f8d214c9fffa02119a,0xfacb132c7fd8e0328087,0x75fc71532b72f962652f,0xcc8186de8c596b11e84],#[0x96b0831db08def8c651f,0x4b4fcc204219f2361202,0xa4ea339194b1758af919,0xa222b8bfa650218093e8,0xc830ad745678e46524fd,0x610f8c74ca2d908cf16,0x16db6a9096da183d61d9,0x259a19b682125cdd145a,0x402950b5dcb2913f12dd,0x64c67a0cb94b131fce21,0xa50f6f862658fe7088a6,0x6a203d52a84b3e05af02,0x2efbdd42a4774038315e,0xcfb58449f3a95156d611,0x114ff40075267218c5c0,0x4bf53e08418d0a5a3892,0x1a7dee95af9c33dd2,0x88ec0f851cbeba017428,0x2d16c215ed0d2d1cc417,0xc040ee70e4d0c9a1e7f,0xc3a0065360860c074eb3,0x2603841301c26f6ad8e3,0x28a8ee4aa290a23a7994,0xc252b3e6c9e02121b6fd,0x8008697c9c050967f4c8,0xe7d255a3c875273e0e0a,0xcde8a852383028c073d4,0xaa1bd17b77ef8c10b627,0x7a177a6601ce6ea52ea9,0xe30f0b223a2e5dd6177f,0x3a1906fa201af864de96,0x14bced054d88e283a12],#[0x1eddd6158dd6179ea254,0x45fbae0987f7d1551eda,0x2b370e1c1050e082d3cb,0xa3da0c989f702aa9417,0x518159bff4234f0762bc,0x781c7d29d7c207dc2,0xd3d60b9e2b60e57ed840,0x947692af91a416d4bac0,0x3b0b0676129bb0d1bda1,0x5bc50742dc8d8e43c383,0x8d013b871a02770eba,0x1f6a3c1e8e1247c333c1,0x5786111daf6a34cf878d,0x237763afb4b1e1a1f606,0xaf868e578614552af4d2,0xe2e154618ee108f0c400,0x7c32de1138fa2e3a9451,0x8b932d614016ccfb51a9,0x28a663c3d28cefed28f9,0x5c8d88013c3477458a09,0x2df511429007bc473d0a,0x6e8fdfae6ad78519c861,0x816ec6ee061ba1c5d665,0x8063eae16848dc13702,0x40b89da90018e1786b5f,0xb23620057bed83c7ee0b,0x5c4557c8594a400aa068,0xd68a3e5dd52a42a1f451,0xfed49cd5a3076b9184a7,0x3589da97242fcc303aec,0x85b5271dd45ebd1c2933,0x9fe339ea49b0b6a32373],#[0x159e0d584068fc2d1e0f,0x82f079574aa5a6040336,0x44aaf86279b69c95d69,0x9155f10]]
def g251H7 := limbs80 #[#[0xd402909cc02800880,0x682604280008b1844ec5]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0x485105d1214415448510,0x4412150110dd52144176,0x54940441515011050940,0x50110585404415450110,0x44172501105914044162,0xdc94044182501105d940,0x50510549414438150110,0x44176505105914144162,0xdc941441865051061541,0x50910589424415450910,0x44185509105d94244164,0xdd542442875091061d42,0x54510509514438750910,0x44165545105895144154,0xdc95144186545105d951,0x54910589524415454910,0x44186549106115244176,0xe0152442875491061d52,0x551105d5544416455110,0x442875511061d5444176,0x505604412158110dd154,0x58110545604414258110,0x44162581105516044152,0x5c960441655811059160,0x581105d5604417458110,0x44372581106116044182,0x509614437558110dd160,0x58510551614415258510,0x44172585105916144163,0xdc96144175585105d161,0x58510e09614437558510,0x44164589105516244385],#[0x61d62441815891059562,0x58910dd1624428758910,0x44174591105d16344375,0xdd56444187591105d964,0x5951061d654417559510,0x441655c9105517244287,0xe0974443815d110e1572,0x5d910e0975443855d110,0x44154dc910e157644382,0x5977244164dc91058f72,0xdd11060b7444186dc910,0x44186dd51060b7544186,0x5d874481741d12060b76,0x1d12060c74481811d120,0x482871d1206187448185,0x5454048142501201d140,0x5012054d404815250120,0x48162501205854048154,0x59540481645012058d40,0x501205cd404817150120,0x48185501206054048176,0x98d40482545012061940,0x50120dc5404826450120,0x4838150120dd14048373,0xe19404838550120e0940,0x50d20591414816150520,0x48152541205055048176,0x58950481615412055150,0x54120591504816354120,0x48174541205c55048165,0x6115048181541205d950,0x5412098d504818654120],#[0x48284541209d15048264,0xe11504837554120d0550,0x54520551514838654120,0x48171545205955148161,0xdd55148176545205d151,0x55120591544838354520,0x48175551205d15448165,0x6195448180551205d954,0x55120991544818755120,0x4837455120a1d5448274,0xe19544838155120dd954,0x581201d1604838755120,0x48151581205056048131,0x58960481545812054d60,0x58120595604816458120,0x48174581205cd6048171,0x60d6048181581205d560,0x58120615604818458120,0x48284581209d16048254,0xdc5604834358120d0560,0x58120dd1604837358120,0x4838458120dd96048375,0x58d614815458520e1560,0x585205c5614816458520,0x4838558520dd16148187,0x211634807458d20e1d61,0x58d20595634815458d20,0x4825458d205d56348174,0xdd5634837458d209d163,0x591205d9644817459120,0x482745912061d6448180,0xdd5644837459120a1d64],#[0x59120e15644838159120,0x48176595205d56548387,0xa1d65481875952060165,0x59520e11654838159520,0x481655c5205517148387,0x5d971481755c5205d171,0x5d1205d574481655d120,0x481865d1206157448176,0xe0574483805d120dd174,0x5d520e1974483855d120,0x481865d5206117548176,0xe1175483755d520a1175,0x5d92021176483865d520,0x481845d92060d7648181,0xdd976482845d92061576,0x5d920e1176483815d920,0x48174951205925448385,0x60e5448180951205da54,0x95120a1e544818795120,0x4817498d205526348376,0x5d6644817499120dd663,0x9912061e644818099120,0x481769d1205d67448375,0xdd274481879d12060274,0xd0520dda74483759d120,0x48164d052058f4148151,0x6034148176d05205d741,0xd0520a1f4148187d0520,0x48176d0d20ddb4148375,0x61f4348185d0d2060343,0xdc520ddb4348287d0d20,0x48165dc52058f7148154],#[0xa0f7148263dc52060f71,0xdd1205977448181dcd20,0x48184dd52061b7448181,0x6137648181dd92061b75,0x50930589424c284dd920,0x4c186dc930591624c186,0x58d42501545094061b74,0x50940595425016450940,0x50263509405d94250175,0xe01425037650940dd542,0x54540551515014254540,0x50165545405895150161,0xdc55150287545405c951,0x54940e0d515037254540,0x50163549405895250154,0x5d552501655494059152,0x54940611525017654940,0x502635494061d5250186,0xa1d52502845494099152,0x54940e05525037654940,0x5038754940e195250384,0x5d954501655514059154,0x55140609545018155140,0x5037655140dd55450186,0x509605038655140e0954,0x58140549605015158140,0x50162581405516050153,0x5c560501655814059160,0x581405cd605017258140,0x50182581406056050175,0x95160501855814060d60,0x58140dc5605034258140],#[0x5037558140dcd6050372,0xe09605038158140dd960,0x58540549615014258540,0x50171585405916150154,0xdc961502875854061d61,0x58540e15615038258540,0x501545894054d6250387,0x5c962501655894059162,0x589405d9625017558940,0x501845894060d6250180,0xa1162502545894061d62,0x58940dd5625028758940,0x5038558940e116250381,0x595635015458d40e1d62,0x58d40951635017558d40,0x50182591405d56450375,0xdd564501855914060d64,0x59140e09645037659140,0x50187595405d56550385,0xe05655028759540a1165,0x59540e11655038259540,0x501635c9405517250387,0x5d972501755c94059172,0x5c940e0172502645c940,0x501765d540e117250381,0xdd575501865d54060975,0x5d540e0975503815d540,0x501825d9406057650386,0xdd976501855d94060d76,0x5d940e0976503815d940,0x50182951405da5450385,0x5d6635015498d40dda54],#[0x991405d6645037598d40,0x50163d0940dd66450182,0x5db4250175d094059742,0xd0940a1f4250185d0940,0x50152dc540ddb4250375,0x5937150162dc54055371,0xdc54060b7150165dc540,0x50163dc9405537250185,0x6177250165dc94059372,0xdc9409537250186dc940,0x50182dd5409937250263,0x6177650182dd94061b75,0x585415d5615056458541,0x50580591415d56450780,0x61d6550580595415d565,0x5d941e0176507805d541,0x54161505505494154385,0x58d52541645055058941,0x549505d9525417454950,0x54374549509d15254264,0x5d9545416455150dd952,0x55150609545418155150,0x54376551509915454186,0x505605438655150e0954,0x58150551605415258150,0x54165581505916054162,0x5d16054172581505c560,0x58150609605418158150,0x54284581509d16054184,0xdc9605437158150d0560,0x58550e09605437458150,0x54164585505516154152],#[0xe096154187585505c961,0x58950551625438758550,0x54176589505c96254165,0x61d62541815895060162,0x58950dd1625428758950,0x5438758950e116254381,0x5d1635416558d5055163,0x59150dd1635427458d50,0x542745915061d6454174,0xe05645437459150a1d64,0x59550e1d645438259150,0x54284595506116554182,0x5c9715438459550e0965,0x5c9509d172541635c950,0x541765d1505957454385,0x21176543855d150e0574,0x5d95060976541815d950,0x543815d950a117654184,0x55263543845d950e0976,0x9d150596745418799150,0x541859d1506027454176,0x58b4154152d055061e74,0xd05505974154164d0550,0x54185d055060b4154176,0xddb4154372d055061f41,0xdc95060b7154162dc550,0x54164dc95058f7254154,0x61b7254184dc95059772,0xdd1509937254263dc950,0x54186dd15060b7454165,0x60154545765515161376,0x58551551615458655151],#[0x5458059551e056454780,0x60164553805d95161165,0x59554601655538059154,0x551645c154e056555380,0x60176551765c15459570,0x99154e0576553805d954,0x55165dc1545937055180,0x5977155186dc15460b70,0x505606037655180dc554,0x58171505605954158164,0x589515815454560dc941,0x545605c5515816554560,0x5838354560dc95158172,0x5d154581655516059154,0x55160605545818055160,0x582745516061d5458186,0xe05545837455160a1d54,0x58960e1d545838255160,0x58175589605d16258173,0xd0d62582745896095162,0x59160dd5625837458960,0x58183591606096458175,0xe1564583825916061564,0x59560611655818259560,0x5838459560e096558284,0x59171581625c56055171,0x5c5605d171581655c560,0x581655c9605917258382,0x59173583865c9609d172,0x5d16059574583825cd60,0x5818095160e197458381,0x59674581879516060a54],#[0x9d16060274581759d160,0x58162d05605474158187,0x5d74158165d056059341,0xd056060b4158180d0560,0x58375d0560dcb4158187,0x5537158187d0d6060343,0xdc9606177158182dc560,0x58165dc9605937258154,0x6177258184dc96060772,0xdd160d0f7258254dc960,0x58185dd16060b7458181,0x6137558182dd56060775,0x55161601545856455161,0x5877455161a1d5458581,0xe09705858059161e0154,0xdd16160b7058554dc161,0x58d801d1636037558580,0xe015458d805516359554,0x595636116558d8059563,0x58d82dc1636025458e84,0x60b70591735c16460374,0xdc5646037159185dc164,0x596745c1656037559185,0x6137059582dc16561e74,0x5c2546037459580dc565,0x9938055263e197095382,0x55152d03855c264e0970,0x54b4058d52d016254b40,0xd017554b4059552d0164,0x61d52d018654b405d952,0x5534059554d038654b40,0xd016458b4055162d0186],#[0x61d62d017258b4059562,0x58f4055163d038558b40,0xd03825974061d65d0165,0x59172d01635cb4055172,0x54741e1972d03855cb40,0xd07805974161d65d0565,0xe0970d05645c34154570,0x5c343e1970d07855c341,0xff1ee3bc6fe1970d0f82,0x3fa7ecfb9ef3be6fcbf8,0xabed7baef5beafd3fa6f,0xbdafb5d67ecf597aff5f,0xd7b9f73adfdbeb7b6eed,0xbdb7aef55e7bbf77aedd,0xd7f6fe5fabed7d6f7dee,0xdf3ae6fcbf93f1fe2fbf,0x4fe9ed2f9ff3f67dcf79,0x6bdd77aeb5beafd5dab7,0xfdbdb776d6d7d9faff5f,0xf5bdb77eeeddbbab73ed,0xc7f8f717dfdbf77e6fbd,0xf9d737e6bcbf9772de57,0xdf5aeafd3f9ff3ee7bce,0x6ded7dabb3f5febdd77a,0xef9defbd776eebdbfb77,0xfe5bc7f8ef1be1fbf77d,0x9fcff9ef3be73cdf9af2,0xda7aff5deb7d67abf55e,0x7bdf79eefdd7b8f6ded7,0xff9df37e67cbf95f1fdf,0xc5f7beefdbfb5f5be97c,0xfb7f67ebfd5fa3f3fe6f],#[0x4027fcff5fe7fb7f2fdd,0x4c6ac604ccaa8035328,0xb2eaec05b72e402c4ac8,0x412ca1cc4ac81bc82c41,0xcaea1f2eae81eb0ae41e,0xac627afac6262e2ec09a,0xe825afee8252fae8252f,0x63f3728448807282bae2,0x3f2730a3f51cc63f51ac,0xf376ec3f372ec3f2770a,0x4baa8402770c3f2730c3,0x130c4243ac84224b0a40,0xb24482eaec4312b24472,0xc64e0bb2c3e8f32a3e92,0xc4e24f084e4ecc64e4ea,0x4e24b0c4e346ec4e342e,0x2130c4fc02ca4fa4f0c,0xb0ac46facaec513f2ca5,0x170867b0ee867b0ae867,0x70a67b0eea67b0aea67a,0x30ab2caea68aeae86821,0xa7885f2c791ab02ab80b,0x3b1830c3b1930a3b2c2e,0xb9fac8d72eac8d480730,0xbb2cd40bb2ccbc3ac4c,0xe2cacd9fac8d7aeac8d5,0xf24ce8bb2cd38bb2ccdb,0x2aceaeeeaceaeaeace8b,0xae7bd2cae72caeacf0bf,0xacadac9ab01724ee2c2e,0x2cacb272c2ebad3d2cb,0xacacb278ab2d20402c52],#[0xab2d20be2c9209e2cb28,0xf29220af25222cacb280,0xc9842c2cb34ac2cb4d8a,0xb101f2c9111fac97e1fa,0x991dacb97bdac954ae2e,0x316f2a0254aa8020a32b,0xd4a8404bbee40354a840,0x4aa80496f2404bbee404,0xb240854a840816f2a04d,0x220296b2a0854aa80816,0xa02d22c602d3ac402d4b,0x2b8aec029472a029432,0x2a870c02a830c02b8eec,0x4daa8039472c029432c0,0x8aa80622b0c0545ac805,0xac807b8aa807ba2c607b,0x28070932c079cb0c07b8,0xa04147240454b2204147,0x438eec0438aec044dac,0x41432c042870c042830c,0x49aca1b09724069472c0,0x9ac41b96f2a1b3beea1b,0xac41cc9aca1bbbee41bc,0xc81c48ac41c3bee41cc9,0xa1d48ac41d0e32c1c45a,0x1e49b221e0e32c1d422c,0xe22f081e326e81e322e8,0x326ea1e322ea1e0e7281,0x972a1fb22ca1f8e72a1e,0x328221cf0822322c8220,0x2c210932a22322ca2209,0xa1db8ee81dc5ac81d8e7],#[0x20326ea1e8e32c1dc22c,0x28972a20322ca2009724,0xe7241f49b221f322ca2,0x93242309724208e7281f,0xf2a00b86e80009328230,0xc019c30c0188b280188,0x888f2a0108b2c019c7,0xbb9ac60bc52c80916f2,0xb9c30c0b9c30a0bb82c8,0x8f240a04f240a88b2c0,0xd2a81084f2a0b04f240b,0x2ca13b52a813c1aca11c,0x241288b2c139c30c13b5,0x823c72c62384f241308f,0x261c70a2616f2024452c,0x79c70827b1ac82788f2a,0x88b2a279c70a2788b282,0xc6e8289c2e828a22c828,0x6ea289c2ea2884b28289,0xe824c52c82484b2a289c,0x426b1eea25a7f0824b86,0x2808f242708f2a2688f2,0x904b242908b282808b24,0x332ea0c442c80c84b282,0x1b300f883240faf2ec0d,0x7280e81f300d857200e0,0x2a10073280f01f2a0e87,0x817a5aa817a9ac41781b,0x148532c17a5aca178532,0x601f3015336e81440aca,0x83241706f2a16857201,0xa7082caf2e82a06b2a17],#[0xb302d083242d2d2ea2a9,0x2c2b877282b887242b81,0x8318632c2c01f2a2b867,0x3281d303201d30319a70,0x61b3083681b2c3281b28,0x1a3083701b303619b0a3,0x9b0a3781b303718b0c37,0xf2a3801f283801b30379,0x241aaf2ec1807f242d81,0x4188732c1ab32ca1a873,0x1981f3019077281906f2,0xe077242e073281a01f24,0x8632c2f873282f8772a2,0x1f242f067242e81b302f,0xb2a3304b243301f2a2f0,0x2c3381b2a3388b243304,0xa3881b2c3401b243401b,0x3001f2a3901f243901f2,0x101f243086f2a3086f24,0x81b2c3481b28348632c3,0x1f243a01f2c3981f2839,0xb2a3501b283501f283a0,0x2a3a81b283581b243581,0x83f95f263fd3a843f81f,0x41c7ac641d3a8441cdaa,0x438ee84453a844445ac8,0x95b2648d3a8448947284,0x3a844a53a8445b8aa848,0xac83f53aa83f562c63f5,0xa3f29b0a3f53ee83f53,0xc3f3aeec3f3aaec3f29f,0x3f53aa63f29f0c3f29b0],#[0xf53ee63f53ae63f53ac6,0x53aca3f53f063f53b063,0x3b0a3f53eea3f53aea3f,0xeec3f53aec3f53f0a3f5,0xc64053f0c3f53b0c3f53,0x8404faa840564c640562,0x4053b284053cc84053ac,0x4faca40167284053d28,0x3aaec404fb0a404feea4,0x9f0c4029b0c403aeec40,0xaa8421672c401632c402,0xe84248ac84253ca84253,0x84253b284253ee842538,0x4248aca42167284253d2,0x21672a4229f0a4229b0a,0xd62c64ac8b0c4248eec4,0x3ee84ad3ac84ad3aa84a,0xb0c4a9632a4aa9b0a4ad,0xa842d22a8429632c4aa9,0xa42d26e842d20e842d24,0x47a970a42a930a42c7ac,0x92970a47a930a47d22a8,0x53b244125f0a4116b224,0xdf0a414daea414daca41,0x30c4138eec4138aec414,0x2c411432c412870c4128,0xc4738eec4738aec47147,0x431432c472870c472830,0x353b244322f0c43322ec,0x1472a432870a432830a4,0x830a4845f0c4345aec43,0xaec3e9432a482870a482],#[0xec49945303e9432c3eb8,0xc43a5b0a439432c49b8a,0x4605530438533043b22e,0x629f244625f0a4616724,0x572c461ceec461caec4,0x532c4b1ceec4b1caec4b,0x92845326ec4514728450,0xc469672446b8f284538,0xa4b8572a46a9f2446a2f,0x56cfaa456cfaa44d8532,0xf05330569132a5696324,0x1172a51cfaa451cfaa44,0xfcc84e4fac84e4faa453,0xb084e4fce84e4fae84e4,0xc4e4faec4e4fd084e4f,0x84fc8ac84fcfaa84fcfb,0x4fcfeea4f967284fa9f0,0x4f2a85048b0c4fcfb2a,0xcf2a854cf6ea50297085,0xdcc84ecdac84ecfb244e,0xaec4ecdce84ecdae84ec,0xc4ea5b0c4eb5eec4eb5,0xc509172c4e9132c4ea5f,0x551132a551632455322e,0x59172a52167245205330,0x85330559132a55963245,0x6324561172a539672453,0x330560932e561132a561,0x2c579caec57a5aca5785,0xc5111728514fb2451053,0x5735aec571132857422e,0x435f2a529172a529132c],#[0x57285429f2454167245,0x8ac465c8ac4650532858,0x3246ec8ac46ec5ac865c,0x2e6e8e32c6ec5ac86e96,0x466053306e8952e6e893,0x66422ca6615f266648ac,0x9326ec6948ac46935eea,0x95b266fc8ac46f8e72c6,0x8ac46b0932a6fb22ca6f,0xe8667c8a8667967246b4,0xe667c8ae667c8aa667c8,0x867c8aa867c8b0667c8e,0x67c8ae867c88e867c8ca,0x7c8b0867c8ee867c8ce8,0xc8eea67c8aea67c8d086,0x132a6f163246f48b0a67,0x52e6f0932e6f0e32c6f1,0x246b96b2270053306f09,0xa6738ae86745ac867167,0x670e32c6735aea67422c,0xd163246d0952e670932e,0x38ae86d45ac86d15b266,0x952e6d0932e6d0e32c6d,0xae86848b2468053306d0,0xe86845ce868322e86845,0xa68326ea68322ea68326,0x6495b266496b22648e72,0x48e32c649132a64b8ae8,0x38ee86a167246a0952e6,0xaf246a0e72c6a326ec6a,0x72c6a0972a6a322ca6a3,0x2e6d8e32c6d963246db2],#[0xa70b22ca70853306d893,0x6e0e72c6c167246c0932,0xe0932e6e0e32c6e16324,0xc8b24688532a72053306,0x5eea6ac22ea688e72868,0x7246c8932871097286ab,0xc64c0e32871853287296,0x2a3af2ec4cc52c84c472,0xa3a82c8a3a92c6a3aaaa,0x39ceeca39caeca38572a,0x9c30ea1356eaa10572ca,0xf2eca21b50ea19b30ea1,0xb30a299b0aa29a30ea22,0x30a318b0ca301b30a501,0xaa401b30a581f30a301b,0x5901b2ca481f2ca401f2,0xc1b2e85c356ea5a356ea,0x1b6ec5c1b2ec5c1b6e85,0x6d2e58b32e85883b2c5c,0xd2e59ad2ec5986f2a5a8,0x285bb53225b99b0e5b86,0x67486f2a5b06b2c5b86b,0x74306e873b02e873c72c,0x501b2e761a70875af2e8,0x85320768372875057207,0x8f0c8799f0a871a70886,0x2ecaa9b2e8aa83f30a99,0x30a919b0aa91a308a91b,0xaa18b0caa19b0aaa01b,0xa69caeca6877284d01b3,0x719aeca70572ca69ceec,0x18b0ca607728a619eeca],#[0x1b30a881f30a601b30a6,0x72c7901b2ca801f2ca78,0xea783faca7836ae87806,0x7a07d2e7807b2e7833a,0x7a07b2e7a36ae87a15b2,0x7153227703d307a07d2e,0xcb2c771032a7736ae87,0x5f207903d307707d2e77,0x720790cf2c7936ee8791,0x2c7907f2a79302ca793a,0xe7ab6ee87a95b207ab07,0x7787b2a7b302ca7b07b2,0x887d2e7787b2e7795b20,0xb032e78bfaea78c7b207,0x7f2879b3eea79b052e78,0xaea99b6ae89987b287b8,0x289a87f2a9a07b2e99b3,0x45f1c2ecac1c2e8ac07b,0x5c81b2e63053206329b0,0xc9a30e5caf2ec5cb32ea,0xb32ea6094320608732e5,0x47205d8732e609a30e60,0xf205d86f2a5db32ea5d9,0xc5db372a5db32ca5db8,0x610772c5d9a70c5d9a3,0x620732e61332ea611432,0xd2d2ec5d01b306206b2a,0x19b0c5e06b2e5d19b0e5,0x8b0c5e86f2c5e19f0c5e,0x3286281f305e81b305e9,0x2e5f81b306286b2a6287,0x6001b2e63853206381f],#[0x6019f2a601cf20600572,0x181b2861873286181f2c,0x282c897053206401b2c6,0x572c971ceec971caec97,0x2ec959b6ec979b2ec978,0xc960732e959a30e95af,0x9698b0c968772c961a3,0x99073289901f309681b3,0xd01b2c9881f2c9801b30,0x1b2e80053208029b047,0x672c7c2f2ec7c147207c,0x72a7c1a70a7c38f207c0,0xec7e143207e2f72c7c07,0x7f0632c7f0732e7e2f2,0x7f8632c7f873287f81b3,0x98aec80853208081b30,0xaf7287caf1287c81b2e8,0x57207d877287d989307c,0xf287d9a7287d9cf207d8,0x287e98f2c7d81f2a7d81,0xa9c053208101b287e873,0x9b0772a9b1a30a9b0572,0xd01b309b99b0a9b9a730,0x1f2a9c81b309d073289,0xa30c3b1b2ec3c9c2ec3c,0xf303b99aec3d1a7303b1,0x2c3e20b263da2b203d81,0xa8b38ee88b29f048b01b,0x888732c8a8532c8b0532,0xb18f0c89077288919f0a,0x1b2a8b8932c8b3af048,0x1b2c8c097208981d3088],#[0x72a9e81b2a8c897208a0,0x2c9e9ceec9e9caec9e85,0xa019b0a9d8732c9f857,0xa098b0c9e077289e01b3,0xd01f2c9f01f2a9f01b30,0x98b0cac99b0aac81f2aa,0x9b048281f2aad81b30ac,0x3208481b2e8405320842,0x2e8498aec8499aea8485,0xa8206f2881ad2ec8181b,0x83057208306f2a832d72,0x399f2a8301f28831cf20,0x81b30838632c8386b2a8,0x6b288f053208501b2883,0x7208d86f2a8d06b2c8f0,0x208e01b2c8f893208e89,0x8ae81f2cae01b2890097,0x910972091063289381f2,0x407b2694077289107128,0x86f2a91897209181b2a9,0xa3089087b269088b2290,0x32093097209206b2a909,0x209281b2a949a7089309,0xaaf81f2aaf01b2895097,0xb1442c8b089320b001f2,0xc01f24b281f28b205720,0x45ac8cc4daa8cc15f26c,0x5ac8d4c5ac8cfc22cacc,0x2cad489324d4b22c4d4c,0x28d1c5ac8d18932ad4b2,0x8d705324d728284d7147,0xcbbaee4cbc8ac4cba82a],#[0xbd3ee4cb8e32ccbc5ac8,0xb8aeacbc5acacbd3b04c,0x472acb9432acbb8eeacb,0xacad445b2ccbc5eeccb9,0x2ad438eead438aead445,0x8ccc8ac4cc9452ed4143,0xccc22caccc5ac8cccdaa,0xe0952ecc8e32cccb5aea,0x45ca8ce45aa8ce48ae4c,0xe728ce45d28ce45b28ce,0x72ace326eace322eace0,0xecd014728d045ac8d00e,0x8d545ac8d50e72cd0326,0xd5322c8d538ca8d538aa,0x245ac8d20932ad5322ca,0xa82a8d78e72cd214728d,0x2acad7a2ac8d7a84a8d7,0xac8cd1ceead79caead7a,0xc8d2c5ac8d5c5ac8d0c5,0xacdc5ac8cd94728d2c5a,0xcd8e32ccdb5eeacdc22c,0xdcdb0acdcdeeacd94724,0x94324d3c5b2ccdc5eecc,0x5b22ceb26eaceb22eace,0xaeacec5b26cec5b24cec,0x2acec5b0acec5eeacec5,0x8cf45b28cf0e724cf45b,0xd1422eacf0e728cf45d2,0x10e72cd1326ecd135eea,0x9324d63272cd109724d,0xe32ad68e324d694728d3,0x2a8bbc52c8b94d2a8b90],#[0x6bc26f06b808b24bbcd,0xcbca6ac8bcb32a8bc1b7,0xb883b2cbc9b6ecbc9b2e,0x8a3b0cb8b36ecb8b32ec,0x1b24bb0ff2cb88fb2cb,0x32c6d8452c8da472c6da,0x320dc2f2c8dbb02c6dbc,0xead981b2edc202c8dc05,0xedc85320dcaf6ead9af2,0xdb01b24db03728da81b2,0x619b0b0603328dd01b2a,0x2f2c9071bb050701b310,0xb2c70881b310718b0d07,0xf2d0881f2b089a2c9089,0x310819b0b081a30b0781,0x6b781f2d0901f250901b,0xb7a82c8b7a82a8b7a92c,0x52f6ecb4336eab30532c,0xd3ee4b788724b588724b,0x830cb7a830ab7d22c6b7,0xaeab3c32cab39432cb7a,0xeab636aeab636eeab3b6,0xeb48732eb4b32eab4b6e,0xb5336eab513724b50752,0x51a70cb51a30cb537f24,0x9a70cb69a30cb68772cb,0xf6ecb593724b58732cb6,0x32ab70772ab5b7f24b5a,0xeb0236aeb02432cb0207,0xb02a6d0f0226b0b0236e,0x28732f02a3b0b02b32e,0x50772d031a30d0303331],#[0x1a2ed040732d051a30d0,0x772b0383731039a6ed04,0x32d048732b059a731038,0x2ec483328c4a3aa8c483,0xabdc42c8bdcc2a8bd81b,0xbe312ecbdb4aeabdc0ac,0xe33aeabe3facabe4b2a8,0x33aeac24b2a8c21b50eb,0x3b0cbd336ecbd332ecbd,0xf2cbd0fb2cbd23f0cbd2,0xeac29a50ebeb32eabe8f,0xac083330c28fb2ac2b32,0xc30fb2ac313324c30ff2,0xf86b2ebf05320c503330,0x99f0cbf99b0cbfb4f24b,0x6b2ac401f30c006f2cbf,0x328c581f2ec101b30c40,0x2ac188724c181b2ec583,0xcc386b2ac388324c386f,0xe145ac8e103328c601b2,0x50e72ce128508e128308,0x3328e5202c8e505320e,0x3728dfc42c8df81b2ee5,0x2ecde3eacade312ecdf9,0x24e31a50ede0c32cde2f,0xe30c32ce32f2ece3133,0xdeaf6eadeaf2eade8333,0x393324e38c72ce20c72a,0x5320e583330e38c32ce,0x1f30e00632edf2d2eadf,0xb30e48632ce488324e48,0x2ee603328e605320e601],#[0x4e28672ae0b1724e081b,0xe403728e28672ce28872,0x681b2ae40632ce408324,0x26f08f228708f483328e,0x3f0af1b36eaf1a0f0cf2,0x530f42070cf2af6ecf2a,0xcf399f0af30332cf583,0xb0a36ca90a36aa90a18f,0xd36aa90d1b30b0a302c,0x99a30d09b32cb099b30b,0x9a30d0c8772d098732d0,0x772b0a9a30b0a8732d0c,0x7250b0732b0d9a30b0d8,0x2d0b81b310b19b0b0b08,0xae73facae701f2b0c01f,0xe8cb6eae712724e733ee,0x7c3528e7c3328e792324,0x3052ee7b032ee7bfaeae,0x7b24e907f24e833eeae8,0xb250007f24ff92724ff0,0x24c9af6ecc6b36eac687,0xc906f2ac786b2cc986b,0xcaa3acaca94720c88572,0x70332cca9a6ecca9a2ec,0x8fb24c98ff24c70ff22c,0xff2ac78fb2cc9b32ecc9,0x72ac787724c7af6ecc78,0x20c914720c907324ca33,0xcfe03324cb03724c9287,0xfd8372cfe1a6ecfe1a2e,0xe9a730fd87724fd83730,0x6324ec0672ce987324f],#[0xa6eaec9a2eaec94720ea,0x6eae993f22ea8332aec9,0x24e98c72ce9af6ece9b3,0xeb07324ebaf72ce9877,0x10c324ec03324ed1472,0x8372b011a6eb011a2eb,0x9a731008772500837310,0x1b2eef83328ef8732501,0xb2ef019aeaf003328f00,0x30ee8c32cee8fb2aee81,0x4ed81b2ef085320f0833,0xee08724ee2d72ced86f2,0xe04724ee0672cee06f2a,0x1b924ee1cf20ee03728e,0xa728ee01f24ee1bf24ee,0xf2cee19f2aee01f28ee1,0x24ef0632cef06b2aef18,0xcf786b24f783328f101b,0xf818f0cf606f2af606b2,0x701b2cf889720f681b24,0x7728f708724f709720f,0x1f250e81f2d0e01b24f9,0xb24fc07728f986324fb8,0x28fa09720fa01b2afc01,0x8fa88f22fa81b2afc877,0xfb08724fb09720fb0772,0xf81f2b0f01b24fd07728,0x442c9a44c2a9a401f250,0x12eda434aeba440acba4,0xacba4cb2a9a49bb0fa43,0xeda39b30fa4b3aeba4bf,0xda3a3f0da3a3b0da3b32],#[0xa59a30fa5332eba50fb2,0x619b0da606b2fa599b0f,0x5721a701b31a699f0da,0x1b2fa803329a801f2fa7,0x2cbab37aa9ab01f2da78,0xeda9beacba98872bab31,0xbaa1a30fa98c32da9af2,0xac0632faaad2ebaaaf2e,0xf01f2bab81b2fac03329,0x9b70baf302cbaf36aa9a,0x732dae9a70daeb32cbae,0xb2bb081b2db01a70baf8,0x25a8b032fad43329ad01,0x9ae1a72fa903725a90ff,0xad81b2fae19aebae0332,0x6c22cb1fc5ac91f81f25,0x9132b26c22cb26c5ac92,0x22cb228932f268e32d26,0x2cb240932527322c5274,0xc9204fb05201172b2442,0xd20117292035ee920422,0x21422a92148ae5214232,0x34232b210e72921326e9,0xb5aa9279172b23422cb2,0x22cb248932927b22c927,0xac928a5aa9289172b24c,0xc92091725209cee928a2,0xd20cdd0920cdb0920c22,0x21c5ae9218e72521c232,0x3c232b21b26e921c5ce9,0x8e72d239172b23c22cb2,0xe32d259132b25c22cb25],#[0x3252805331258932f258,0x2d251172b25422cb2509,0xd261132b26422cb260e7,0x2242323220932f260e32,0x64252922423292242325,0x19b0b4b19b0f47452c91,0xa30f4823b0b4801b314b,0xaed4a02b314899b0f489,0x314901b314919eed4a19,0xd4a81f254a81b314b81f,0x29beac92981b2f2b81f2,0xc053212c02f2b2b23f09,0x1bb054c06f2b3b82b2b2,0x1b314c18b0d4c2d2cb4c,0xee91799acb4c99aa94c8,0x211990f251806b2f1933,0x11986b2f1990b2519913,0x1886b2d1a19b0d1a02b3,0xa86f2918b4f251890f25,0x25b0b2ec22cb2e86b291,0x1b2f3102b2b310532131,0x2ed2d90f2b2dc0acb2d8,0x2d2cad2ed2cbeac92cb1,0xd30ad2cb3088325308b3,0x31853213181b31308632,0xe0b7292d01b2f3182b2b,0x887252f867292e317252,0x83253002f2b2f857212f,0xb2b3205321320632d300,0x213ca470b3c3facb3c02,0xd3d02b293d06b2b3c893,0x501b3094db3aa94d82b2],#[0xd332c94d1b3095033aa9,0x6b2d4d19b0d4d334c94,0xa3094e087254e06f2d4d,0xb2b509a3095081b314e1,0x2d4f19acb4f01b315086,0x53281f294f86f294e81f,0x341072b33bfacb339072,0x41032b343facb3415b21,0x7b253483d313407b2f3,0xfd29333fb29333fb2533,0xac91e917211c9072543b,0x2d1e99eed1e99aed1ea3,0x91b8fb251d8ff251b02b,0x1bb31291b86f251b8ff2,0xd117211d06b251e33729,0x82b251f02f251d25f211,0x2b2b3801b2f3782b2b37,0x321360ff2b3501b2f380,0x2d370732f360fb2b3614,0x13587729358872535863,0x3682f2b3584725358572,0x402b2b38853213887329,0x2b253f1ef0d3d81f254,0x57254598f0d3e02b2d3f,0x72d459caed45a5acb458,0x314499b0f449eb0d4485,0xd45077294519aed4602b,0x5181f2d4681f254698b0,0x901f255206f255119acb,0x117213982b293a917213,0x6b2f3a0b32d3a113213a,0xf2b4002b253b02b313a0],#[0x2b40897214081b254206,0x1411a3093f81b294286f,0x4186f2b4108725410972,0x306b2b419a7094189321,0xc52c96201f255281b254,0xeb0b61a030b612f2c962,0xee58422ac5842aaa3841,0x2b8422acb8405725841c,0xd81c1acb81c52c981857,0x8598b0f821c30f81a230,0x481b318598b0d85af2c9,0x1eb0b832030b82a02c98,0x1f258501b31860233183,0xf0763c1acb6481f2b850,0xc9662d2cb659b70765a0,0xd633eac9631b6e96620a,0x77a1f05770b729640b32,0x818ac9881ef0b7820709,0xaf2c98781f2b8801f298,0x1b318799b0b879a30987,0x3216f81f298881f25888,0x256d0632f6f8b32b6f8e,0xf6e8cb276e8e3216e8d7,0x6f0e3216f0d7256d8632,0x23316f0632f6f0d325,0x86329708d7256e0632b7,0xa7097a893217aa070979,0x3297b1ef0b7a0632d7a9,0x2b8c893218c81f2b8a82,0x58901b318c8632d8c86b,0x891a309892f2c9890872,0x90632d8919b0b892d2cb],#[0x7b278c093218c01b318,0x632d8c1a3098c2f2c98c,0xf2b8b0672b8981b318c0,0x258681f298b867298a01,0x968207097b81f2587057,0x6ba2b0d68422cb6845ac,0xb9eacb6ba02c96b85321,0x53216c01b2f6b8232d6,0x232d6c1eacb6c202c96c,0xaeb668c7256681b2f6c0,0x2d67b32eb67beacb67be,0xb6a3eacb6a143216a0c7,0x6b0732f6a0c32d6a332e,0x922f21690b7256706b2b,0x87729698872569827256,0x272d6984725698572169,0x32d6c853216c873296a8,0x257f202c97e857257e02,0x3720232b730e7217181f,0x738e721728c729710df2,0xd823257d9ef0b7c82325,0xa2acb8085725808232b7,0x23317f9eb0b7f8572b80,0xf2b8101f258107729800,0x2b8d81f2b8d01f258d01,0x9758e7217401f258e01f,0x750e321750e721748232,0x602331750632f750b32b,0x81f298f01f258e823257,0xc2eb1104b251101f258f,0xf2110c532b1045321101,0x211386f2112877211188],#[0x51481b2d1401b251401f,0xb281b211501b2b1481b2,0x2b52cbb2b82c9b29c705,0x9a2c9b39b2c7b39c70db,0xa70bb301b2db381b2bb3,0xb25b481b2db401b25b41,0x2fb219aebb201b2bb481,0x95504b255501f21b181b,0x5586f2153222c955252a,0x381b295701b255704b21,0x81f299498ac994a0ac79,0x9b0b942f2c99401f2b94,0x2c991202c99281b31941,0x25950732991873219245,0x99581f259581f2b9501f,0x9a01b25b581b2db501f2,0x703f299a01f259a81f29,0xbfb219683b2597bfacb9,0x3f259a83f259603f2599,0xb09980cf259820b05980,0x21990cf21988cf299820,0xd5aa070d5a03b25a20cb,0x5e9a2c95e98f0d5b1ef0,0xe077255d81f2d5e99acb,0x1f256001f255f06f255,0x1f2d6019acb601a2c960,0x7255d03325580ff2b578,0x215982b25590ff295883,0xb5b877295b887255b82b,0x6081b215c81b255c06f2,0x181b2da11a2c9a101f25,0x1f2b9b88f239b01b25a],#[0x1f2b9c81f259c81f259c,0xb2ba281f259d81f219d0,0x2b9e1a7099e01b25a301,0x59f81f299f0632d9e06b,0x9e81f29a001f25a001f2,0x4d83040301f25a081f21,0xd7ac403d5aca02d82a40,0x12ca03d5b2803d5ac803,0xaca0555aa8053ceec03d,0x240455aa8073caca07ca,0x41bd830a1b55b0c0455b,0x1c55aa81c5830a1bd82a,0xd512a81d57b041d4aaca,0x4ab2c1d5130a1d4aac81,0xab2a1e4ab0a1e4aaa81e,0xaca213caa8223cb0a1fc,0xa1dd5b081dabb0a214a,0x41f4aaca21cab0a1ed13,0x8d52c808d72c408cab2,0xbca2ca093c6ec08d0aca,0xd0b241250b24113c2ca0,0xc2a827d0aa824552a823,0x3220c492ca0cd42a80cb,0x2c0c396ec0c4e2ca0c55,0x814d02a814d73221494f,0x143b52e14bb32e14c92c,0x4366ec144e2c81450b22,0x17f201617f201591f2c1,0x2b0e2ac62c829ca2ca2b,0x2ca36392c83632d0e2ab,0xe23fd82c23f89f2c3636,0xa3fd5ac83fd7ac43fd82],#[0x4455aa841d7aa441d12c,0x257aa64255aa84457aa4,0xd5ac840d7b264257ae64,0x6f2e42d6f284297f2e42,0xb264355b224155ac844d,0xc44dd82e24dd82c24dd5,0x456d12ca4dd5ac84dd7a,0x56d12ca56d5ac856d7ac,0x1caac84f582e24f17b2c,0xd12ca51bcae851d7ac45,0x7b224f97f2c51bcaec51,0x2a26ecaaca6597f22525,0x266582e2664aaca6ed8,0xa664aac866512a866583,0x66caaca6b4aaca69516e,0x84aac86bcaac869caac8,0x50acaa12bacaa3cab266,0xa2c85950aa8592b30ca1,0x2e85a50aa85a50eea594,0x2c5a3c2ec5a50aca5a3c,0x858ce2c858d132058977,0x5a977225a91f2c58ce2e,0xbc2aec59d13205991f2a,0x11f2a5b11b2c5bb62ec5,0x2aec86392e885c62c873,0xa84cc32d0eb1bb52eb0b,0xcad4d5aa8d4caac4cc55,0xad1d5aa8d1bcb0ad4caa,0xce55b06cbd5aa6cbcaac,0x2cab26ce4ab06ce4aaa6,0x4ab22cf55b22cd97f24d,0xe2a8b9ce2cab855284b9],#[0x2a8bac2acab9c62c8b9c,0x28ba4e32cb8ce324b8ce,0x2d9462c8d8ce2a8d8ce3,0x6ce2cb06c632ad9d532,0xd52f28b3a8b0d06b92ed,0xc62c8e1c62c8ddce322b,0xe2cac828aa8f546326de,0xf22c7ce322c728b0cc84,0xa51fd83031f94f22c914,0x526d12a526caac51fd12,0x2417b312697b2526caac,0x417f25244aac524512a5,0x2bb09244aac924512a92,0xab2321d132320cab2321,0xaa51617f232517f2323c,0xcb16c62c916ce2c915d0,0xd474e2c9474e32b1742a,0x47c62c947aa30547a630,0x9a8ac949a330d47c2acb,0x91f2b2ac2ac929262cb4,0x2b2b2a462e92a50b2329,0x30d1c4e2c91c42acb2f4,0x231d11f231bce3231b26,0xd3ea62cb3e94f233511f,0x6211f233989f233e1d2e,0x44632b61462eb614a2cb,0xab30581ca2c581abaeb8,0x330f83462eb82a32cb84,0x72564ca2c564a330d83a,0x216342acb6542aa96397,0x96442b256442b2d63513,0x76c62c976a32cb7942b2],#[0xc32acb788eb2d76b92e9,0xa330d68c62c968a32c97,0x32cb7d42b23674632366,0x2eb1328b0b120ef2374a,0x553d0b2154d0b21b136,0xd53a630d53ce2c953a63,0x56263055611f215411f2,0x91f215691f295626309,0xa330b934632190462c99,0x340000363215f91f235a,0xe4005d8023400c800,0x3c601a700c000530023,0xb1005360278012400870,0x380d78065c0306017380,0x2298109007e603c201c,0x56f029c813f4098c0493,0x5006640319817b40b5a0,0x40ea40724037e01b500d,0x20680fe207d003cc01de,0x8b82354114e086f041d8,0x504fb826f8130e094904,0xb2f057b02ab414f00a3,0x8440bf605df02df416b4,0x1c19980ca10638831381,0x837cc1b6c0d7a06a3834,0x78803b441d360e680710,0x1e07f883f2c1ef00f440,0xa10e5085a8421420a210,0x23fe11d008ce04550222,0xcf0260012d1094a04918,0xd04fb0277a138709af04,0xa6d0529828fe14520a0],#[0x5af0ac0855602a4e14fc,0x2216630b1b058502bb81,0x82e3016f00b6905ad42d,0x5fcc2fa417a40bb485ce,0x4006190306818220c028,0xd0c8e863cc31aa18ba0c,0x19c90cd38663432f0194,0x5201a600d1f0683033d0,0x20365a1b0b0d6f86aa43,0x7010379c1b9f0db606d,0xe69072a839021c580e17,0x9f0eb3874f03a241cf30,0x81e690f1d878383bb41d,0x3e4a1f000f6a07a943d0,0xfac3f8c1fab0fc087d60,0x48822040ba2038100987,0x10a50849441fc20d8105,0x20c10f3886ec43382178,0x9a22aa11428895844562,0x846ac2336118908bc045,0x906c47ea23cd11d308df,0x6a892c04918246112210,0xd12c40952c4a4424f912,0x264f1316898084bba25a,0xe1e26e0136009a604ce2,0x44f3c278013af89ce44,0xa128505a280913f209f,0x47f0a360516e28931433,0xbc14ce0a5cc528a29231,0x82a4915130a7fc53b829,0x56842b2015770aaa454f,0xc57ce2bbc15c98ad94],#[0x20b25c58e02c4c16168b,0x16c08b4f85a182ceb166,0xe6c171e8b8545bb82db4,0x402efb17678bab85d1a2,0xc5f802faa17ba8bd605e,0xc1886082302117fe8bf7,0x968c3f461ba30b918458,0x818d98c64c62c8314218,0x32a6193b0c92c644631f,0x734336319990cbe865a6,0xf0684a340b19f38cef46,0x8d314693e34741a290d0,0xabc0d5946a8e352a1a7e,0x411b0e0d7d46b9835a11,0xa36d61b5d0da286cce36,0x6f5037811ba50dc786de,0x21470a2381e1bfd8df48,0xb0e50071fa38e81c5c0e,0x1d250e8a473ea39ab1cb,0xb0a1d730eb0c754c3a83,0xd03bb11dc28ed6876643,0x879443c741e218f08077,0xf5d87aac3d2a1e7d8f34,0x388f8c87c1c3de01ede0,0x71f9f8fc147d9a3eac1f,0x4071201c8fff87f8e3f7,0x2a04124207e103248146,0xb8839e41b620cb905ec8,0x10a2884c242522117907,0x1a590ca085f842ec2160,0x1e21ff10f48874e43812,0x2449a223e91184888444],#[0x8ad64546228e1136c897,0x7dc8bba45c122d291620,0xf91ad48d004647230991,0x23c511d848e68470d236,0x85c2414120108fbc47b6,0x5e490524689228c910e4,0xc936e499624b91257892,0x29a494724a1924fb1276,0x9592c5895d84ab6254d1,0xf25ed12ecc97124b4c25,0x4c8d26381311098324be,0xa304d022672933089946,0x9c9b0a4d6326a1934c89,0x138189bee4dda26dd936,0x74e139f49cc24e4c2719,0x3e278e13bd09da24eb92,0x8500727ee93ee09ef84f,0xa1ee50c7284e94198a05,0x89ca3f051cc28cb94528,0x614bb0a5965295292f94,0x29c894d8ca68e5323298,0x4682a2195078a7e653c2,0x7e551e2a7e1532ca9345,0xab9655ae2ac4155a0aa,0x5a5cacd856452b14157f,0x9795c4cadee56d42b5f1,0xb2bcf95e08aed857502b,0x58332c0d95ff8afba57b,0x1ec58d92c50161e0b0a2,0x5cb30259602ca01647cb,0x16888b3ea59d72cdc966,0xd8d96be8b5a85a882d33],#[0xfd2ddd16e50b6d85b402,0x5cec2e52171bcb8725b,0xbb6c5d862eb4974c0ba2,0xa88bcae5e252f041772c,0xf17d68be345ee62f6117,0x304b9818cc0445fe42fc,0x18730aa9848cc1e660be,0x386265311c987e4c3846,0x8c66e6318317e18b1cc5,0x9018c7be63a831c198d5,0x6e992ecc8fc645b32199,0x832c199568ca5a650832,0x665c331e99810cba065a,0xe7a6715337819afccd12,0xc4cf9867ac33c219da4c,0x9a1b0d0886820340499f,0x4939a424d1ce68b73441,0xf034e61a688d30869583,0x66a6d35251a8b4d41a69,0xd6586b0935681aac8d52,0xf40d7706b8c35b41ad68,0x39b244d8926c1a35fa1a,0x36ad9b4ccda2e6cec366,0xe1c36f61b714db4a6d82,0x26ec937501b998dc8c6,0xdf6a6f8237ab1bcc0de,0xc260e0e2703b38099bf8,0xcc9c54ce25e70ec38639,0x2392e9c8fce41071c438,0x733439879cb80e568728,0x8a8741039e91ce60e6c0,0x34ea6a74f13a619d234e],#[0x9d7f0ebae75aa3ac69d5,0xb631da9ced0a76533b10,0x523b9e9dc78ee0876e53,0x478093bed1deb8eefc77,0xf20c78cf3c4c1e1c0f08,0x7b0f388799c3cb79e4f4,0xb9ea6cf4e47a383d0b9e,0x3db51ed24f63a7ae03d5,0xc743e1e1f00cf7a27b95,0x9e7d173e7c9f32cf94a7,0x8fbf87dc73ecf1f5c4fa,0xfb70fd667e903f251f89,0xe59fe5cfed47f413f859,0x403520135004680013f,0x8161409ba04010198809,0x488822040f7a07350326,0x85064882f2415e209d90,0xa10a907d683c741c420d,0x27d212fd092c846d4227,0xda42d9a15d90a9485264,0x486794323218990bf485,0xf288756438721b5d0d5,0x2011086881943f8a1f01,0x92248d121088d1445722,0x44ea2267d131e896e44a,0xa84452f22909143a89f2,0xc08b3c458322b8515728,0x5184e8bee45dda2e3516,0x340d19b28cb74645a315,0xe1a36891af48d5846972,0x14738239211c268df246,0x8f2d4784a3ba11d7a8e9],#[0x128fdd47d723e351ed2,0x852162907f482ea40c52,0xa45e922bc912e4887a43,0x90b247ad239291b048ca,0xa549402498d248092234,0x49356498ea4bdd25ae92,0x286093f949ea24ea5270,0x46129ea94be4a4925199,0xa256dd2b16956b4a9a25,0x4b18258652c1495f34ae,0x6d94b5aa5a892d0e9656,0x7897874bb425cf52e389,0x1308298154bfea5f612f,0x63bd318a98a34c3ea617,0xdaa664532d2993d4c892,0x24d3ea6901342099e04c,0x9b584d9526bdd35ae9aa,0x8489bff4defa6efd372e,0x539429c8b4e2ca71053,0xa75913a8e9d224e75273,0xeefa770d3b4e9d8d4ebd,0x924f34a78d53c249e024,0xc9f6a4f9127b6d3d6c9e,0x4084a0224fee27ed93f1,0x3ad419aa0ad50472818d,0xa2865942d4a143508728,0x5132288e543eca1de50d,0x341518d28bcd457aa290,0x36a3f251e1a8e4d46c8a,0x5499ca4b15239a912548,0x96d14b18a54f5292293e,0x6829a954cc0a63652fa2],#[0xf53bfa9d194e36a70653,0xa845541829fe94faaa7a,0x25ea8dd5459aa24550e2,0x5d53a8a9a854ba2a5455,0x2aad95524aa6955212a8,0x5d6aada1568eab165570,0x4056152b01957c8abc35,0x2ad08566aab25158aaac,0x5bf0add156c82b5d55ab,0xa715cdeae5a571c2b895,0x8abd5d5e64aeef57602b,0x5830ac0d95feaafd257c,0x147588dac375617ab083,0x7cb21658eeac6e56314b,0x1665ab2f45951ac9e964,0xd08d67b2b3ae59c52cd3,0x64ad2a168eab45c5a1e2,0x35aae2d4f56a28b4f85a,0xb63a5afe2d7696b6eb59,0xe5cb7025b5e2da416ccc,0x496fe0b7bb5bc8addb96,0xae2f970fcb84f5c182e0,0xcc9ae5a17294b9255c7b,0x6c5d1fae88573f4b9c05,0xabafc5d722eaf5751aba,0x7780bba15dbb2ed4d764,0x25178c8bc3b5e08aefa9,0x5af5117a36bced5e652f,0x5f052f7a57b90bd9c5eb,0xed55f5d2fa397cc8be3d,0x18bf635fa12fc997e02b,0x5808ec0195ff32fee17f],#[0x40581b8c0b8604db01b,0xdfb065d82f0c14f608fb,0xb611bb087983f6c1d260,0xc309616bb0aa58512c25,0x7f2c3c061c530d99866a,0x58932c485622a3109d8,0xb15598a5ec508626a313,0x2f93172d8b52c59862b5,0xd863473199d8c62c6176,0x6c7a163b931d018e18c6,0x9158c862641731fd98fa,0x7199344c97b649f323c9,0x2329d59482ca1164fab2,0x65a9b2c9195f4cacf655,0xc1165f4b2ed59724cb71,0xecccc1664b331ad987cc,0x19b02cd6366a3b346d99,0x38799bdacdd766d7b366,0x6f33acd9d22ce7c672c3,0x367c6b3dad9e6ccf0367,0xd066681ab40559fe8cfc,0x288d10f6872342e1a124,0x99a38ed1a768c5b45bda,0xb4a1da4c4d2296905b47,0x9aab4c91a5f2d2df6956,0x1669fcb4f45a75ad37a6,0xcd4966a3cb5141a868d4,0xaad6d52a6a813537da97,0x8d9ac24d5e66ae235641,0x535b41ad46d6776b2ab5,0x6be435e3daec8d7376b8,0x8cc6c4cb6215b0a8d80c],#[0xcd9616ca1b64b9b1f8d,0x1b464da0c6cefb6681b3,0x6c0db5bedab66d463696,0xe436e81b6e6db4f6d98b,0x76e2d370c5b81edbe76d,0xdd396e89b739db962dc8,0xbd8ddcd6ed5b761dbac6,0x41bcd8de516f1eb7849b,0x37cedbe24deed6f6637a,0x17b7fc5bf96df866fb5,0x11706eb82d5c10ee05b7,0xce1b170c3385a5c27ae1,0xc4a2e2327109387e1c39,0xbcdc5b6e2ae7149389f5,0x738e1dc6dae3337189b8,0x7224b9069c7e6e3d471d,0x4e9726c392e5c938e470,0x40e57a72a7b947dca0ee,0x9cc78e61872fa39729cb,0x9c91cdd6e6ca7345b996,0xe8b9ee5cf44e75d739fb,0x974433a1c9d05ee80073,0xe922747f3a349d17ae8a,0x3a2e9b274c8ba5add292,0x31d4d8ea3f750cba7cdd,0xbad3dd62eeaec7568baa,0x612bafddd78ceba575be,0x137674bb299d8dcec4e7,0x6edcc76d0bb619da82ed,0xdd98ee82772dbb8a5dc0,0xed9df0aef5177943bbf5,0x43c245e0a0f01777f33b],#[0x78cc3c57de260f0fc786,0x2957934bc8e5e414f1d1,0xaaf32c79823cb65e578f,0x9e7f2f3d179d03cde9e6,0xd395e97cf48d7a313d07,0xe43d671eacaf53c7a883,0x47b4cbd9b9ec68f5f47a,0xf7667b9d3dc4deddaf6c,0x8cf8147bf4bdf1def3c,0xa9f212f8be7c4dbe1c5f,0xbe7d9f392f9a57cbb3e4,0xd6fbeae5f4f6fa5b7d16,0xb37dbebed4df66cfb147,0xefc697e223f05df7d0fb,0xfac4fd2d7e7cbf345f93,0x8e9fc42fded7ee5bf635,0x6bfb9dfd5cfe7d7f293f,0x7fed3fef9fefeff497f8,0xae804bc01d200830003,0x23015e809ac045601cb0,0x20467021480f9c06d603,0xc0e05a302a981434098,0xf40fce075f0378819fc,0x982614126608d3044382,0x5b182bd415360a2904e,0xd1f064e8313c18060bb5,0x6a0e8307178379c1b020,0x41f860f85079683c3c1d,0x444c217e106d081683fb,0x2c8483c2382118508a58,0x909cf84d3c25fa12b309,0x15870a90852d4287613e],#[0xe6a16eb0b598593c2bbe,0x6c310618510bfb85e5c2,0x868bc33a2197d0c8e863,0xddb86df436761af50d52,0x190e628722438ae1c150,0xe1e5d0f128776c3ade1d,0x3f361f530f8287b343d3,0x704427620cb102187fd4,0xe88c6c45522277111288,0x1265891ac483223b311b,0x65112ff896a44ac62517,0xea2793139c89b8c4d322,0x452a22903144f8a16c4f,0xabc455322a4f15028a6e,0x618b1b458062b8315988,0xf17188b7645b1a2d4916,0x2ffd17cf8bd145dc22e8,0x33a315718898c30460ae,0x7465ce327319188c7ac6,0x8d12c680e33db19b88cc,0xae18d6146a8234fd1a54,0x111b628d9cc6c6635f11,0xe38791c178df446ede37,0x73fa39b11cb28e40c71a,0xe7c76a63afb1d468e954,0xa8f444796a3c471df98e,0x1f598f9947c263dc11eb,0xb120088ff1c7ef23efd,0x5a41d120b79050c81e64,0x4870a43372175909e484,0x14f489c644b3222190f7,0xa691b6c8ce245fd22d69],#[0x5243f921048fca47a523,0x4a0b24e29258c923a48d,0x78a4b45257d92abc94ae,0x6c9a2a4cc32636930a49,0x9395c9c324ddb26cf935,0x7f093e449e7e4ef12752,0xa328ae94434a15250412,0xe5331296c94a0ca41251,0xaa1a54af2a2d95044a72,0xa3cac7a56032ad895584,0xb95e7caeb257252b6b95,0x2c9c9636cb116584b2bf,0xadd2d36968ecb3ba5987,0x1e5cab2e2b96f1cb6c65,0xcbcce5e0f2ee1975d4ba,0x7facbf625f652f9197b2,0xde984e4c1be609930189,0x931ac98c2cc572624930,0x652932609915cc7f663b,0xe12669d332f997e4cb32,0x6cd122684b340699df4c,0x9a9d4d43669b734b89a3,0x62c9b014d71e6b1d355e,0x3136ee9b5d4da6e6cc13,0xa6f83379b9bb84dcfa6e,0xe23e70b738379c07cdfb,0xb34e4de722338eb9c604,0x29d064e7a2738339989c,0x3abe9d4c4e9ba74913a2,0x7313b659da44ec7e75d1,0xfe78a93c279df9cef067,0xcf48279fd3cd09e53cf1],#[0xefccf75a7b713d829ea2,0xe79f5f4fa0e7ca53e1c9,0x53f8a9fae4fce27e1f3e,0x8091401ea0004ff6a7f6,0x43681c540bca048d01ce,0xe5074e83334166a099d0,0xa154d09d684a1422ea0f,0x3a4a1b9d0d0e864b42e5,0xfd4454a2115100a87a94,0x68a6d4510a276512d288,0x180e8bb345aaa2c15156,0x7051afa8d0b465aa3175,0x9a3d151dda8e91471aa3,0x4886a42c520d6900147d,0x2854926a4825238a915f,0x7293f549d8a4d3525ca9,0x52b5695554a7ba528d28,0x5ead2eaa96e54b2aa57e,0xd6a659d326298994c14a,0x34d97a6b5d35169a1d4c,0x9d0f4e51a7105379e9b8,0xd869e734f0ba76cd3ace,0x6d40069fa34f9fa7c4d3,0xa870d42c2a11b5065a81,0x1c0a8cd545eea29b5118,0xdf5242a914d481aa3c15,0x6a60352d7a95754a5aa4,0x4ef6a733537ca9aa54ca,0x32d510ea84153fca9ef5,0x3aa83d5376a963548baa,0x55cdaad0d55daaa93553,0xd235674ab255587eabe9],#[0xb6ae2156edab6bd5ac2a,0xd5f62af635786abad55c,0xc33d611ab0355806abfd,0xf6ac6b562dab1235886a,0x75972aca9564c6b22f58,0xb40359d6acded6692b32,0xabab4f55a5ead1fd6856,0xdd6c9eb6155ae6ad6456,0xadd9d6e22b6e35b59ad9,0xc40ae1757052b7f75bea,0xe15cc5ae55d7216b8cd5,0x2bac15d51ae9757442b9,0x773ebb655da1aec3d75e,0x3d5795abc575e13aef75,0xeaf7ed7b92bd7f5e95af,0x5f90afb2d7d2abe595f0,0x7f601cb001d7f82bf67,0xd6c19f60a2b041581a2c,0x58642c2bf6140b08ed83,0x13ad890ec42561d9b0e2,0x50b19358bd6c59562a0b,0x563cdb1d5d8e4ec6ed63,0xc909645bb21ed9086c7e,0x48aca1b64edb266d92a6,0xf59632caf1655ab2a059,0xb31cd987ecc0d65f4b2d,0x6fcb368d9a9ecd0d6666,0x396775b3afd9ccace2b6,0xad0a56834b3fed9f1ecf,0xa396d1a168b3b446da1e,0xb35a552d26b691cb4825,0x5b4edda6ded33d6985b4],#[0x6a91b5375a91ed4576a0,0x6196aedb56a5aadad533,0x92d70b6b68b59c5ac76d,0x5b10ad8276befb5e55ae,0x665db2ced9276c7cb630,0x4ab6975b47ada0b6ce7b,0xd6dc7b6d35b60adad36d,0xdc796e22b7095b7eadba,0xbd6dd8f6ea7b741db982,0x45bdaede9b6f31b786db,0xb8005bf7edf856fa3b7c,0x8ab838dc14ee07b7020,0x3b70fab86f5c32ee15f7,0xae38f718fb8b45c4f6e2,0xca82e4e3724cb90ddc7a,0xb45ccdae62d72e8b95fd,0x7ba005cfa2e77b739ab9,0x74cfba50dd1eae89d742,0xbad759dbab2dd4d2e9f7,0xfaeca57630bb0a5d7d6e,0x7c02edeb76d3bb53dd9,0xe1417e8204dc0b42831f,0x1c201a00601ac2582b0a,0x121a085e074203970580,0x1e0500501203e0560641,0x4e27c4c81c03e278070,0x5a060d214e0262bc2046,0x3a8118c003c0c8cc8af0,0xc089c50b60e0a48c6004,0xfa14e0e4b70407a25a,0x9d0661c8a00223406f05,0x158204b91c90ea284521],#[0x5d43f0507903c8521e6,0xd0b21f90a01e0c903086,0x638170ce3016e0c9160c,0x8cf0a0e10782c24462f4,0xac1d86004b0047d45a,0xd038c4500c2c47ac440a,0x2cc2c1e41445b0d04982,0x40296e0cc0815196a182,0x48842e4bec3226d0da23,0x6065091c060570ec0d07,0x74590e284126a08c110,0x61d17c1324c490c26071,0x8c1c9343742080886c27,0x1917e1180a0f887076c5,0x8a9090ad8250b634e228,0x137c1e4128311963085d,0x88a8241c71500182820,0xfe4321300141d0360b40,0x1311013023b8618120e0,0x81d10a1004e8100680d6,0x850c89e8991305d41680,0x2a0e940b010426190104,0x2a0db1c457a1c8142f8,0x989a934486004a847c28,0x449580a49c8db8bb17c2,0x83c0280412e1c2001114,0x419e01c9999a3580c864,0x304014a0585b05e0390f,0x130f61933e82d85a0708,0x16596430c3e87993d178,0x51440667a4fc2c823635,0x102a0584089414920606],#[0x38c2385c02d1404d0a81,0xa908c04b26448411979,0x58c92c454a6e4da95047,0xc88491d87e4f20481611,0x9372d83d4b91514d4564,0x3306554e61863109f4b6,0xcc794fa2e45a41018037,0x35c6d0d4514718a29e80,0x4878bf13690684a6c36c,0xc36e93e20a577d25202a,0x727e99242f3fab4c8050,0x68028777f985a640287b,0x87d5a8134028717f2415,0x42674014493f0d1a485,0x6f77788424601447bd3f,0x4fa8f00067a3bc4c1648,0x7c692fa42e1a3480a4af,0x19bf5156e1c4371c0a40,0x65ff4482002193ea3c00,0x18127142539393f4c921,0x1341dc1424ce4299eff6,0x53fe10ea267087fdcc75,0x84397ff5cf8c8a2a0b50,0x66494e512205f0e4a28e,0xd34f459a2107289134ff,0x39b0455417f0ce5824c4,0xe9b320ca1091375dfca0,0xbfffe9b33c2810913eff,0xd84586bccbebcbb1533f,0x7362b4ca862ffeb9f050,0x727804a856459bc4a858,0xb63742916eafad390a58],#[0xfa2b014288db018f46a7,0xbad854905ed0a265e7ee,0x9ee60d13497b4289964e,0x43074f9e82165135774f,0x2fac58884d54fc551b64,0x10efde0ab40143e7fffb,0xd31053c3f1f8b984e755,0xfff43890b121d0faf09c,0x514afd82fa821ca144db,0x31428757e0eed2886068,0xe61208a659114affde80,0xcffe6646e1c892e1ffe2,0x1f7c0602936cde40c052,0x302200fd1de20ca03015,0x916af512a19593ab477d,0xc8b37ba121d5a2112a19,0x5356094adfeb41b604ce,0x44e3ff00a2e2a8a88c3e,0xac8543e3ff00a26394aa,0xffb7420c6a5222dfdb83,0x9253bfff02298642a22d,0x906b89a0a4d7310d75a7,0x3dbf57c7514a87cffff2,0x8862a4d7efff0608dc24,0xff20cd411269af95f220,0x5a8a8ccff2581110269c,0xbfc237393ffa641098c0,0x4029ab4c482de0cf1687,0xfe1244cd410fe70f9b78,0xa06c10defe28a06c10d6,0x5121c3fceaa04cfefc58,0x32a028b441e9e4062370],#[0xc288a1268441e9e45682,0x145c6dfd74c12678c3f,0x4ad12315faf70b1211b4,0xe02998857c43ebdc2b02,0xd7da5827850e4fa7a20f,0x36c848737ebe42972488,0x43b13443c0ccbae17caf,0x68753bca6950f9ffd840,0x27a6000a9dd8326a5628,0x8dc2d9ed61291297cf22,0x10033f9040416985003c,0x4365bdd4104a567fc712,0x8ff72a048577bbfe5dc2,0x2c64e9431bfe2273a50d,0x2849b0b6051358aa797f,0x25289e475142a951f8bd,0x90747ac2094937b3eb08,0xf83b04a49bde128f5ff8,0x2d2b1c13141e6c8484ab,0x18695ba2ac724aa9131b,0xa3165a9d0d1a56eed5d8,0xbe5c486cd18b79ed88b9,0xea290a88b7ec48367e0f,0xff0c88b9e111905f07b6,0xe0c21214ccff834e242c,0xb3ec430b6780d294aa76,0xf11d4709fc2232c13d88,0xf364005878399b04a4c3,0x4114c267c7f5212115af,0xfa8480050eb8c2444ffe,0xb0a32bdfb4800152fbff,0x76ea5e6a66a8da8c81eb],#[0xc9d0e2431bfba5621c48,0x585a64b7fc00b121dd17,0x8597e037616169f9b620,0x15df8b47090b4fcdb19e,0x6229713b51975f933e12,0x25267cf8b99f919e67fb,0x2bf568632d0144461b71,0x21129b3f1e0e2a900935,0x293d5c104d21b6fe314e,0x4659fed88957ff409c25,0x486abfe85c7094a5c4ed,0x90fd922f526687ef0251,0x49ff06e466d7fba8c438,0x9967ef62213fd7b3890b,0x35227e9c8093307fa5b1,0x50d5dbfca265e3a398,0xad890defc0028417d248,0xc1214bc80e146647fb10,0xc67a183ff912ccb0fded,0x30484c73481c8557ff4c,0x13e93315f1a842252ebb,0xb9e22c252e456d465cca,0x424090b9ebb0feb999f8,0xfb43c0148cfe6102101f,0x2123f4ca81959f1b2484,0x198b5cfe19198d2f31,0x810ac3ac8ab7123f2d2,0xee242e36d3b810a0eaf7,0xbd87014b47f8028ed065,0x50f896a48847a6965030,0xd0f07e410b16fac20caa,0x2b85c204443c1f500215],#[0x3890d4f2b8408547ff4a,0x29529fe7c8ca6f2fb7d,0x4233bbb8908271b90e,0xbe40858ff8bc00cdaf8b,0x4640c6a5affe206487a4,0x7880cbaf3783204291fc,0x62fd00a3065ee24237f8,0x6a46bfbe0148d4fe7199,0xb0d46d2ffc40cb77e530,0xa1fa779021bdee9a0c2f,0xa4a41ed34247ed6a032b,0x34247f8400194efdd480,0xf4363e8fe90010c2fbdd,0x2a6840feab664d605c96,0xc40fa3428bf748084f75,0xc20755010e2fc4a9a121,0xe881130f47f48008607e,0x16261021f5fecffa6189,0x7dfb0293088fa846369f,0xc1f3642c29a2cf2590c8,0xb5f241c7e5f50ac6684b,0x43bc1e5478fd5b2a042c,0xd2d3560d82855bec280a,0x211e0257ba43a47e8f3d,0xbdd3c420d8287a7ccf84,0x194c0d2bf56c01ad0022,0x8ce5fa0ac660b4391a3c,0x3cf7492a3fd95911028,0x33dc315e25239018a87e,0x7691e130e549f508c626,0xcfebf2032dbe2b4c2043,0x7a44a3d3fefdf803204a],#[0xeb12896f6bc8800014de,0x101481d0f8325f366027,0x9f04890867f58947978c,0xf80431033fbcbe610214,0xca55f9947442e219489f,0x81977928697153b72194,0x651c7eded044c676d3d8,0xff26da00088a04549f88,0xf90563307b7df0ac6607,0x82c019ddf04f4404367a,0x26271e04cdc1296bff84,0x6fe710850c0a9c77ed00,0x11000447be8fd9c1021b,0x410a12fca49941ff4e9,0xd5f2261d5a59525bfe42,0xeb84819571c43197e863,0xe7163c230f7fec01c476,0xd00902ff6bb46910111b,0x7a9251c5d9ea8e6ffde0,0xa10cc37b7f948562ec48,0xacd0a76fb858587ec010,0x310a57ce080a40fb3401,0x2029825f94932a38bd0,0x8cf809c5d3920fef4e07,0xe738202941ff906c10b7,0xf492fff5004e1021c6e,0x459983ff40c1662bc6a0,0x101a03df02a32e72f930,0xdb2e405880d21edf7c0b,0x1a8049cedf6c01c80d39,0x8cc619512578251ef5e7,0xef5ffaa18887e7d7bbfc],#[0x46545f3649fb848a21d5,0xfad910e6ff6e42646620,0xcc06213c1470ca6c5223,0xa8f899c475263fb871d8,0x18ce691ec5cc7527133c,0x7fa14a171f80d112168d,0xccf82cfc62f0862a951e,0x6a0ffdd49b9c94d31f18,0x393c0e842e98d603805a,0x70e2a676d7e2b0f15344,0x859abf19059505a1a9fd,0x9ebf181eaa53427f81cc,0xa29e4b6c70ebf1905d29,0xc6ba4e7cdf378d698e22,0xb3690df5163f90868226,0x67a0a6b1b7442aa26c07,0x1f08426f8d6b818888d7,0x4d4ad5e0c9e6b210ea85,0xbdcb2f44043f0e6580ac,0x2ed8481315613732647c,0xedfb3fb19c0743c7ff30,0xa06110bfff72b5b64092,0x5b28e4d4a14d4f3d1a6d,0xfd4c254d0b7106e8521,0x944a676f6ed44a6620f,0xf07418479fd983666f6e,0x476197c398e1674761f3,0x33fe5c129b0230a26b7f,0x381502cc5c887ef906a3,0x4a8647f460b2422a1e3e,0xfa22402672b23f64f200,0xdb81c4d34c7fa22a65ef],#[0x1045528df84115481e41,0x2061039e9b54099eaed6,0x9ffa11908bf4c0d9442f,0xf8a9927aa4a8bbc55a8b,0x954080144fbc1a5d099f,0x616d6ff8a708557ff4d8,0x788ea32e455b27b94482,0xf95060fd1d060fd1d06d,0xf9e25d88443d7c0d3243,0x7287d7179baa5484442b,0x2bf7f3ce50aadd00bcde,0x7f41a110a8b484ff6443,0x1083e50a472bfb10886b,0xea42214b3ee9ea219c1e,0xe700885bbee74ba9359b,0x8144827e5fc3414287d7,0x780d44343d98c1af3cfd,0x4cebffc253824495cf79,0x87fff526412467d13a14,0x72e511e0e4665121b241,0x51bb587326fd3820a3ec,0x50110f3fe4028a3f5c80,0x913fc82084b0d10f4e16,0x70fff826b5409a2a9c21,0x9f893dd0c903f6e0a886,0xb4ff40a045488289a75,0x913fa5304337347e8451,0x721d4bdedab02133dd0c,0x8aa387a62b04a8613a01,0x51b3fa8732527cc7c70,0x2538cc92639228abfa7c,0x54233e5a4424f50afd43],#[0x32c6a1ad4e0828f6fe58,0x19cb9169c1051957330a,0xb9d43c7b720d3ff11102,0x31ca3c72439088fdb907,0x86627f641509a5628927,0xc4aa2ef3743274ffa088,0x7d4319288cb93f6f8830,0xa70cd0e5858185549ffb,0x19288878f00442b7cbc6,0x57ea2713a1c9fefb7d43,0x78475361fa2a2534a807,0xc18770ca18e84609761e,0xbc3b8650c7422c1ffec4,0x52786a07e24543e3ffb9,0xe087f38a86c207df00ea,0x51346100c03ee80753d3,0xf8e354144d19ffdbad50,0x3cfd9036497e8274267f,0xdc875197e48cdb2872e6,0xe35944d1de3f160d133c,0x4528bff4283422183a72,0x942bdf1014a918fa0090,0x1f3f0cb2c1a26836aaf4,0xd66d264439306b369322,0x89f6ba1140f11b84260,0x67aecd0e65dfa4b620a4,0x8644397b4399238eaa68,0x4517cdb70c88617c905b,0x908864f08530acd38cc1,0xb3a8a3f00b043373ecb6,0x74193f5741c5db50aa4d,0x297f0a8357e8254223ed],#[0x223ed741fc073a8f6cea,0x3a0d5f141d080e2e044,0x548eb19f0a2e5c6a22bf,0x428817c9c128855e97c3,0x219ee29546cff145a531,0xdc8406e81cb2eb2700d4,0x42779cc66f921c8437fa,0xb188a2cf96228a2fe5ae,0x98225a294e5ddbbc14aa,0x8bdd92bc51b1b3f9d542,0x66617ff41b722b460896,0x5c3327a52e19635c649,0xc66662e35f7006674f42,0xc1722635fd006662e31f,0xa68600d11ce4ff7eaa14,0x2bc5f90cc1510eac7e6f,0x533828bbbe0f41a80353,0xb75f14285b59e4e110b2,0xb72524254288d6da2284,0xffd488212943da76c8cf,0xd049c24964b449cc8906,0x9737044c14c56475a3c7,0x1e4c1cde01a3000e4588,0x61e08933ae90c4b6c70f,0x11ac1172a09f311b5647,0xfc34a3003409acee644c,0x43c3ff00d180072283f0,0x89ac9f81d8ea4818e892,0xd80f43f7f8bed2aa325,0x9a758fd587429bf763,0xbf478360e4317edc6d05,0x446850e0ec87a1ca1439],#[0x3f0fc35d80893483cbc8,0xc00d50afec4ea9ba1a1c,0xf16001510c87e349a82a,0x28686674f2757580d0f0,0x4a793ab882034393ab4c,0x39412361d1c9a3aed3b6,0x5d6ea23a7d7230089a17,0x2a24785faaec1006885b,0x33340787d90199f78627,0x1a2364fcdb23d7c70a7,0xfbab9c8a313f989ddd0c,0xfba31391479febfc80c8,0x7e18539998bf42f400cc,0xb1afdbf229d9eb503239,0x389086a2fd8a029d4269,0x5a8869a39e28b1fd00a0,0xfa1f82dc711110ce2e47,0x31ecd447f43fc31d4443,0x756934d0ccf8330850a3,0x667c19842855fd2c8862,0x6a885f97c6665d5ecaa4,0x2470ecb41e66aeccc6a4,0x31c4443f726635fe1662,0x32d7c7c00283342bfe66,0x10815345c73c8a5e5821,0x6452fd2b8d0667c3e725,0xc666557fccce3a167ee0,0x750a4b0cb2778aa3afaf,0xccbaa97ac51b8c4434,0x9f42c51678a58a297e9e,0xe7a88c8ffb05a3414288,0x65b4893f99dd1a268191],#[0x63af8e14c0667afafc66,0x6f262654ffc4c8652e7e,0x2981170ff7d4b30218bf,0xad56c0d0efe19958ad0b,0x188a58343c645247f873,0x13e0442b53843241f123,0xf5ada1978394bb433438,0x6a1f7060188b5fc028a1,0xecdd552a5cbf1ee9180a,0x3a115530221d57802132,0x498111bf3bfc304767f0,0xa2f5c7eac0cecf77486c,0x21da14d819d5ee9cc085,0x62e350c1c93f9f0215a0,0x42a74fe70486068969a,0x5e3c3f3c33034226e3e6,0xf713a0c0860fce0c1ccc,0xfc3f0c0898276378d21b,0x452df69b1d22b8bb7b4,0xc6a14a4e5149ddf0d0c6,0x67975f0506180a95b24e,0x7ed193825db244c0886b,0xe5ad81a0695e30148469,0x4ea5e3e4a4252a54e1a4,0xa51ba2378d225e271f4,0xe4a4346180a7a3d2e918,0x2236fc8f0248180a7e3,0x469180a967e1eeddd4b3,0xac0c69180a7aa17ab01c,0x5287ebfb6e46c0d177e,0x3c800c01011547ddfa0c,0x800400150f3d584effc8],#[0xaf4a183de0cc9e7c8eb5,0xa2985c38da275213c81e,0x85375c8f7f9c014c2c15,0x3279a51694955afa6a6a,0x3e4094667c8128d3f910,0x332489fc881923f84633,0xee1b2c21d1ebee830218,0xb2429a92ecbaac21a92e,0xcf89923b1aa14f348ec9,0xafa0c085d3e476354296,0xc953e1f62040cd6ea747,0x8d7d206029f0fa026a6a,0x604361f635903014d87d,0x8547989e5d8547b3acc,0x328385380808646ac7cc,0x9570fa3b8080888a7bb0,0x42cbb734183f4e020217,0xd16783c5c688e7fa3603,0x48cd09e6e76888d4a8f2,0x222014f67f830602949f,0x9d0660488d4d67e20d81,0xf80a7bb883604888053f,0x666076406a633c0211ce,0xffa68a352b99dce81491,0x7c527c604419958d4647,0xbb89810c23c54361b0d3,0x7c60438347e02021540f,0xa13bb716f06664737c52,0xff01d8e00402a59e0d19,0xfc040429507705a42bf0,0x92353932f145c0686068,0x1a5e2939010be7229e62],#[0x7568e9b04383f0895922,0x23482c91e117a60442b2,0x68d478f17487342ed474,0xf6008088974e0202160f,0x76b0f27808087779ba9d,0x4042d3cf1c36008088,0x853d1fd66002014dcffd,0x89b7b6948049e67c3e38,0x7f8f4884649f66f09143,0xc9181b21fd571e8c087e,0x210cf004a426ffc3c842,0x8957cbc8443021c63fe,0x2ec084cc0e3c9d924100,0x42a107ffb61724606aef,0xf5f182b02003533a4109,0xa57076d1e9e86b3a933f,0x69e8fbaba971c9e59810,0xe302191ff5e2284c6044,0x59819e0fa7ed0a3debb7,0xbe547450c400224bf0f1,0x189e96ba121ddda25429,0x1a09e96ba121ddd89302,0xaf5adbe092db73d38558,0x9a982563f8c443021873,0x92043386302296ff4bf5,0xb81e6d0010602a3dfc1f,0xb469f0496f26ecd0e67f,0x164ccbf6a20e09031ff,0x49fee692080044f7fc5,0xbd788b518b2afee92e67,0x6188649ffeeb6a20e094,0xb2ae8dbead18042b40],#[0x54023034b701bbaf50a1,0xfc3021bca18da3eff48,0xacc4368d7ee51868ea27,0x66dca0088884fd8d4219,0xe79c028eaffca81d0bcf,0x8d0a4e315047954429d6,0x860901ceb5996068a08c,0x4107d9dc52943affccd7,0xc604307faf88b48181a,0x387964785b2c0d32fd7d,0xa4c5d86c2473f2a042b,0x83fd0243033824fd789d,0x167f28c3464fd3a59819,0x1438fc7849151f3e9a92,0x43826f576121a70c202,0x37e92cc085255f8b00a6,0xe1fd35c8c0ce09bd5d84,0xcadf7060650f5e52080c,0x7fd4002981109f09610,0xd356ec0ca9f0a6c0ca2f,0x1db8080cf0d385c081a1,0x70244093de5f38c0cc9f,0xa1886043ef35ca88cbc4,0x72cfde1817801ad1cff2,0xba191dd6e4227c7c153,0xf4ee0dbaa8d929f260e9,0x8bd3089ea36337a77066,0x32380978ce684024909,0x8db923267f0866656dbb,0xfce6b0100930f9000685,0x1cfd15c542cff31022af,0x3999c12fd1ec901011],#[0x8080ce5fe701019825fe,0xa01d4f3fa1a2047cfe01,0xd9a3d9e79087e3364622,0xaf512a1a1d5a2112a1b1,0xccbc66c8c45403a9d916,0x9af80a76d3a264cfe085,0x57528ff186a2d4c7918,0x4c855c3e04e75195feab,0xb4a4d963845c880e5d15,0xc1d91e14d53021f6e078,0x1507e0301498c20b5ed2,0xd428437f4c5748424181,0xf14ec35e238136092eeb,0xc4a834fcbe93123034de,0x14b5e1cc79b699686697,0xdae844781d0627ca8801,0x54c5a52289a3dad0a4e1,0x3f8217329647d56c0cf5,0x7f5ecc0cc693f343021b,0xfe189d08ef8309810a1a,0x11042e68a3ee183014a0,0xc68a6ff2e12892674f97,0x34f2044cda8689f7696b,0x3c83329787c69e0489a2,0x530218967eac486043e5,0xa7d38da0e0406ba7f918,0x1579b332cbf3f8c04297,0x2a397f4a1142dbdd6e42,0xa4282080d17c944b6728,0x810b2fec5d093d521f7f,0xbd3e9c6d0059a41fa3e9,0xea22fc83322fdca0791c],#[0x1655d1f325d069f317dc,0xb88d7af186a37b837418,0x97cd50cc0d2bd788b51a,0xf8243a93bfe282aacd5f,0x49804004551f206b293c,0x2404c020022a9feee783,0x8811c4f42ed2929feeb7,0x8089abe8f6b2937f5c6,0xdc18a6135e02ff343f58,0x1a1a7e5b3349aaed293,0x78c8a2f833309efaa7a1,0x4104101a59f8074c22f9,0x420124df9b8a142c7fc5,0xa1a2049bf2e109978ae2,0x9fa10da82283d998d7ee,0xa54305be2194a6e89cc,0xe87e233400a553e23340,0xc815242fbc7d707438d0,0x7f434909c747d512935f,0x1698133b7fad57302674,0x65995ff943102c337fad,0x8eaffe998cf43076f681,0xa2a86c01448fbfc09a4,0xca58e8a9639e68c9af36,0x8041ea5b3de80c0d4ba7,0x587f600517154544e9f8,0x93952408a6b97edf4468,0xfffe01659d5496a6fe9f,0x4080028acb575aa1a943,0xcbe6104154a84737f458,0x399d490dffcce0218687,0x600018c1a9ebf3803633],#[0x9f149bffed0d014369fd,0x211a1d3f90854cd1b7ad,0xd0444ce67524d7ff2208,0x4ba428cb1fe654c8de1e,0x880410918b27f5142241,0xb6bef6236be8ff1025d0,0xf2b6a908a685fcb8ac8c,0xe10028aafaf40826676f,0x1f6a10614333f27c3081,0x7ca57a74915e09e2299a,0xfbd8910b6973c8650d96,0x4842a1e1f81c8a111488,0x84026c2c372d32c3f823,0x4b2cf4a869d3f965546a,0x46a5214bc1a12652ce8d,0xa5215106752433a896df,0x18c30820aa8c7ff82582,0x6dafeca80d04cd337eaf,0x475fe9cbfa7144626e02,0x208182a82fb9cc99625d,0xa5af04f114cc37fde28a,0xc833461a686d7e962514,0x468cff543052a8cd0c0f,0xc3f5c04e948643992e5a,0x26935f2461e4b7966a44,0xdfdbc3a934313491ee83,0xaa921fdd214094551514,0xfdd682942522d15878b2,0x438256cbef7500d1a1a1,0xa24ca8ffe89a428d2445,0x383fe2b11c2370513df1,0xc80be02d3517fa251113],#[0x49a87f35d57a1bbf0ff6,0xe9961502a04d5e21ed09,0x7f05c092e97049a83113,0xa36e7edb55499a57ff51,0x26a82fff937d74909206,0x98c4db4cb1f9068ac110,0x9b0d949ff1314a31b828,0x2804d9f7024184696be0,0x5983aa267ffa7e0b399b,0xa15ccd0b87a44cf91936,0x944cd11cb162658fafec,0x655d266d7cb183af8f48,0x4062400a79e48f48a5f9,0xaca25215f88405245e9b,0xfc10480a86717882134d,0x29483a87d052948f099e,0x90bf7e0080a53bfb05c5,0x4296ce1728246f54380a,0xccef5418602a02a9d1d4,0x5605490a5afcc8195ac1,0x206567fc832488043b3f,0x317c7064cfac8192b86b,0x5584e8a24d8b16ef35c3,0xc6b506e52029d5ffbc36,0xa9f290a2fa77a73a4345,0x9cec8200a5a4ff19925e,0x27899069668fec02a434,0xccc80ebd397a143aff1a,0xbb26527e1ec00b43517f,0x244cd9f6f2c0280cfd2c,0xfe5ba4085c3c0a22e5e8,0xcaf00521babe374810d8],#[0xaf4ca0c96f92099021ae,0xa87a7702179abf02c086,0x51a7f2042fb7784c810d,0x4ae0068979abf124087e,0x1309185f0841973ffd97,0x1669b55881152c5ff988,0x503d912e84653172f00c,0x9cf1faa84f3ec91f8aa,0xba7fd7d8802a999f5c61,0xa2e1c1706a537cce8150,0x14baf6960f92ff728021,0xe8d4ef515749671f96ea,0x8fea042f9d97c211e832,0x914086b7f41914086b49,0xc4f87d0645021c1a63f,0xcbfa780423a3acdf5119,0xa4daea4a2dbfd2222810,0x49472f02acc8503c42a4,0x503307bf41a150340de5,0xa150336f3128460ffe21,0x247fd0820198d612667f,0xfc42420e9e513ae21555,0xe0108d2f87a88a04333f,0xe646439bf706da810db8,0x10f4fa4351190d09bd94,0x1d5c3f9ca130ceec3228,0x100200a757ff54040502,0x4363fc9022810de7a1dc,0xfd52101008727ea002a0,0x1648afe410150ab52870,0xc285effc2580600683,0x2a8e50fcf33d05526bf1],#[0x95084b23f3c4e35055,0xf8461292b5f8210336bf,0x7f80fef840d1dfc231c5,0x9819c81b35d9822042d1,0x7aef42008808fcd07fdf,0x4087ee9a63c832068f74,0x268eee8a029886fd1391,0xeae46421bf428322810f,0x5021d1f21bc1e45021f9,0x241e0461022ed9bfd064,0x709d62010408a57fc49c,0x53db5f014c8201b09ff2,0x3c3ebb2bd124402243fa,0x19d7fdd641187c7bac82,0x810c2ab928a5ffb65020,0xfe9f8402010e2ffd5022,0x8aec0a52afc4b0940d16,0x6e02949c3cdcf042d9c6,0x751cbf17be140865b8d6,0x58ca92903da940cb87ca,0xcbc0ccded322e4100d36,0xb319cbcb94a540cedee3,0x1245f9408a04357e594a,0xf8f14505810ebf604452,0x96582173397f95281955,0x6385156e0518197251b7,0xd12fda8c82a462b1c2bd,0x1223b4e355cc04d3655,0x2af0db4665a7ddb385a4,0xa890052875b68cca4ee8,0x885233455fa041a926fb,0x26f85fbc9e001283faf0],#[0x3fc24c120810f2f92254,0xf26502734bea46aa0438,0xf811081054d1471508d7,0x9628198ade5e89019ea,0x838a0672a7d38080674f,0x864ffe30940d03457f0,0x97041ce3c822fbe8d414,0x1961b75042428a30427b,0x5b40d2dcfa332547fd10,0x23a7ff228196bffb4942,0xbbfc6ca11010ebc710b3,0x6865e23a06c092727612,0xa6bff0880cb6fe2fe208,0xcff658909de5c4402119,0x192a25d6c89ff41d40cc,0xf1348085cb2a8a302fcc,0x17ee82859213fd40c8ef,0xca17127e254213e42021,0x316d6f93a50226196df9,0xd66940876fbd69e32c39,0x915021b5c192c84f7f90,0x7e43a8d6f8682a9284fc,0x24fef8a043771db40cb5,0x84a10ca723b1fc8a0433,0x4369e271ca0297cff8e0,0xd1b5cb10ca575be0c8a0,0x100898b32411e214053,0x82018008a371fffa2331,0x1ff6f42a067c767f27c8,0x6e237e2040154cb52874,0xd0201008767a377a00a8,0xc4cbdfa053228e50c1ff],#[0x2811408881e0308bfe80,0x79cae08914256bfc1fab,0x875eb541651d78e23294,0x1bc4b46a5f7f74850360,0x3fc5b3424bf6ba2021b6,0xa7aae0c82fe28f440434,0xad3120b7833a7e937832,0x429616f06487c2236085,0x10bd5faa032ebf4c5b3,0x42e3cbeba2021ade5db9,0x503fc371010eeffa9c40,0x3c26142a316d7c954313,0x976b55241978ab154b4e,0x952f2c432bdd36b55241,0x819d5fd09c085f659450,0x50feb84ba86861effb8b,0xc5d109590089cfde7806,0x44f932b0ae17b858457a,0x6f9a808c34d91e06aa96,0xf109ce00224741e9141e,0xd3ae9805242b3f9bc5,0x728ae143065ffff05ccc,0x9d004333562e4c243335,0xc00d11ff12020cd4ff30,0xc4fe0221850ddff84830,0xa956e14d460f8b422010,0x32a156e14d4626af0828,0x517b2a124cc983059ff2,0x6ee8f423010c6fd2b612,0x621c5029647d41154668,0x9b207fd89b20927a259e,0x6e7f0a014708053e7e94],#[0xf5a157c755502387d26c,0xbd9c2c2c7ecf82666ae5,0x408d0b5ffeba09019d1b,0xf868307d5908808667e8,0xf44cc93e420fc2acc9cf,0xcfe7aa07024eef02277,0xef45f141989fd4184043,0x7fcece821673b50a6049,0x42febd4065cfd470065b,0x40effd01038125a5fd66,0x6a26130fe15c900d0805,0xaa353f1c981100053db0,0x5a1001120733251e5f2,0x5facc6d6668a9fe3e4f8,0x55200674ffc0aa400ce,0x1f07b2801684004527fe,0x5eab054f61062178ce0b,0xd0293dcbf9d682189930,0xf10108bf6b0959200f40,0xd8b21309cdf1e05b283f,0x5213fb21309de344d90,0xb4253b4dd0450a97e948,0x8008993e06b459cec084,0x936693070c5ff27c0273,0x5f352170352fd8111484,0x30b0b5f965226ab3a53e,0x805019fade604cacf8a6,0x54a2bff740702407e5e5,0x101abbf808d914e2c005,0xd0f44b202253f4e16893,0x34311ee83e934b2e7e9c,0x9f914e100112cfec824e],#[0x3a06c0936c1560c9f83e,0xf23cffd7eea0a604a5e2,0x2a9dc4807c010ebc7180,0x3bbd001822d9b2cc904,0xdae243b860087e7547c5,0xcdf2ca1066ef99e7a60c,0xf45014defdd80f22810e,0x29bdfb01e45021bcbd63,0x475784a04459e64cc500,0xf4e7a913689408a67e8,0x940878797d4b9f38111,0xb7e8eae11408787f26af,0xb8214053957e2584a068,0xd7f24a704280a74bf1b0,0xe702189ff588a5128110,0x4acdb7e08940d04ffa87,0x3c66f05810af7fc24219,0x66aff408940cf4fc4e8,0xccde52f200666dbf06e,0x4087dfc9fb811b2362f2,0xccde1f7000cc6778b4d5,0xad820508002293ea3140,0xa810edf16ee0019d5fd5,0x10c9fd462819adc5d056,0x66ff0084406797f88210,0xceec322810fd97e40d06,0x1400a5f7041a5408667e,0x3f83190782280a823f02,0xe819a1f07f182300088d,0x6707d9c54010ddffea2,0x83357ec1020cd5fb004e,0x2219e9155a82193f4aab],#[0xfc4e802155abec4d9808,0x793061010d4fb950c273,0xb1019f8fb159a480a6d,0x999b32ffeb01c08f5fe8,0xfb3f9d9302c23522abdc,0xca2c23522d13d2e6ca6f,0xf4022da1a1f9f241edc8,0x2a07e24cce89eb566cd6,0x7090d27a23c0520e29cb,0x66a44dbd882427bfa364,0xa3a30aa70b2241c9c249,0xe0ed4845793fb0b0a143,0x10d5f874342f5c61a8f5,0x670a143a7ff82498344d,0x4327fc0565e46797f27c,0xd2c58c9746687e07209a,0x8bb0a143a7af900c5b24,0x930d0e0fe8850d0a8f2f,0xcfc8c702b294c483b3ee,0xd462285135fd959b199e,0x9294c4f549742128f0ea,0x3ba58fd9a907b7e76054,0x28e2d06d1a77bb5d1a18,0xb2abf9e6c042692203fe,0xfe26a49aa04d41ff6179,0x9144d3ffe914e7090f5f,0x140b83d925ffd8812718,0x10e66a8135c3f009c0e,0xa842fe520fb2c4d15fe4,0xc0da2529f0f92203fb3c,0x4cbafb2daa0850f07066,0x10a1cbf694a2ccd9e2c6],#[0x8d35f5f8ccca4ffc27c2,0x7a3e54277ff7e9d96d08,0x13118f8ca52ef93a7458,0xcd5ee6ae59a1cc014385,0x1a3a3720414cdd34ae34,0x813483f53e1c101c1449,0x63f1e020a7affc9a0d6a,0x3d50762b42ca604515ed,0x91263d2174cfa9d20437,0x9b4ae4010e6563eea42f,0xd5080217b6e82d00cf6f,0xd7ae069f7f4ae4010c8f,0x29c0e6d26e10dcde36d3,0xf41c22cc3f57cfc11061,0xdcf00b0a5cbc02159832,0xe40261a24b978060b35a,0xb7c04b229043ebffa801,0x73da1527dfdb024d80a6,0x96263b844fc5843342b9,0x9d71218c912dcdd213e2,0x30c33249cdfc8192d57b,0x83232169c74121367101,0x654947dffa0a50331a4f,0xea49a073a8c1f895073,0xc4c86275e45642edfab5,0x5ca1656e68990a4e817c,0xa042b3f3a118c28be74f,0x605132b79408c86973c8,0x7852021a21de8b382645,0x435bfd02834868746d2,0xd740f8852334b1df8484,0xf1d3071d5708f8d13417],#[0xe4a61021f0e76e1d496,0xc204337ffc7575033a3e,0x4686590d1f666337f014,0xc2c2199a213ef40cbcd9,0x908086b7e6cd21a153e9,0xbebc4b8885233563d31f,0xb572247290dfd2610214,0x821435563c993b66f40c,0xfb331dbc708a109f8bcc,0x527e2f321a1613fa0648,0x744f2be9c3bbed83c868,0x3dc1ba0d6eac0a5498f5,0xaf8d28deeed143b01ba1,0xb570221948afe8323215,0xdbc00833136ffe022194,0x90fecbff06b71a489913,0x8c6b099134fff5b99e89,0xbf32fecf2c67d7ff5cfc,0xa7d9cbe103f73313217,0x8e2245095c7d1ad40428,0x84f382194d585319079c,0x290990ebf3f1228472bf,0x826522f1c46528f007d5,0xae880869caf0b28cc7e1,0x86c6a40cea52afb32bbb,0xbb38a94b48b8466852bb,0x22014cd7f718446a5b3f,0x9c49a3e4111a9a0fd3c2,0xc809f0f810438babe8d0,0x807de800a6b7c1c0410a,0x3eab8d94bbaf540664b9,0xffbd2e06797e84e042c6],#[0x5fed52e06607f4508440,0x20d04cdfd94fdce08113,0x37b86910a943fd785b38,0x184f7ff72bd0a4740113,0x92e670681d18a1519b15,0x4283ec07569286eaf6ec,0xcf0378e400a6d7c95db9,0xfe5a4043443fb670419e,0x40536ee3fd038120df0,0x83c2f425848dbfc9d47,0xe86158b8f3932b3e432b,0xaf70658d7a960cb0e666,0x9c181d3c3d2c80014f09,0x82a627e2ba59a149e9,0x6ea5832f5d544074c4fe,0xd9ea48527e2a3a8050c5,0x8bb2a4a4df8c07919df6,0x9349847bd544778b8a8e,0x3f2eb494cd2d5d95094f,0xfc1590c28682f8ad8599,0xca1286c380268b00d313,0xb6167268f3c942dbe4fd,0x3baee0d104cd1469cbe2,0xc166b13da0161413f3,0x958a8e08f8851421bb6f,0xf294a4fffa33460621f0,0x29c283d02c810a4783bb,0x43d3c9e82870a0fb15d,0xfbf9428218dffeec01ad,0x8082176ffd304e80a6a7,0x81c08e1e9b65726607a2,0x68450bbf6fb9491e6feb],#[0x6cffe29c2c0b101a8dcd,0x8b1f36f3f23143e99406,0x84a7c5f3860f964d0800,0x6705bd2de7a48e6e6055,0x80e049cfc1127900340b,0xb72695e38c0791c79caf,0x2cb5329e90bdff2833a2,0x9af9371a0295c8ff9a04,0x940b154fa7365d4337a9,0xe924150d9b16c607e760,0xa140fcec148922a9e9f2,0x9b89e0cd4029edc3d957,0xa014e03d4aa7bdc0a673,0x6e36d8b0295ab543f066,0x57c58746d21971cd6116,0x1ebff3e024b362117484,0x10e31dc7011a677c301,0xaccba8eb011ad37c11c0,0xb37be814c6d4317cf801,0x2a2103a5c90a5f3a208,0xfc10529bcce9177f0412,0x8020296dc34f4843b80d,0xac8197283b70cd4b915f,0x95f39032570d640ca5cf,0xb7142e27f0264932dc50,0x5f1a85f62fe90216db6c,0x8a9685ef969208b34aac,0x40a687fa7f48008647ef,0xdf26a00906923f54e9c5,0x5dc384597bf51b0459bb,0x2d280a8a793abeb7990f,0x5879b0e2810d37b06935],#[0xd56a200a87080c6a1c9a,0x479bd8349e241405433f,0x4303fc0e3450ab1ac440,0x203f9198a159fea35c05,0x1f97b80066d7e4b1cc85,0x32c3fa0d68a174f1b28a,0xb1915f4121142a7fe246,0x7eace64333f00e984ab7,0x7e50547afe412114333f,0x3ab6f990c9ff35000cdc,0xdbeee33189d5b6c85a79,0x7fb851f5ed37e819d3fa,0x2272fe32142080a9d2,0xb04d194cac787f07c908,0xfecea376174a04505feb,0xc1540d2ea79e8864373c,0x14eff12840055347a70b,0x52fbc5a2190a627c7432,0x7bdc4a1065371cbe9106,0x1f6c19095f4e01140cf7,0x28c8f46c835eb541651f,0x437b78328c9c879caf0b,0xa2211dd273d2ed811a2a,0xa2fdf470ec98e14028,0xe4b026987fd0bb263b84,0xcd4f774809854c2d4ed,0x50e9fdc710067cfb8e20,0x3ef8f5811b0903d6bc04,0x44c00087e5da79382ea4,0x6f74e9d44c0008867fcd,0xa30045069d2bff0c0008,0xe505c09a26a7002347d5],#[0x3dfa193a884c2896c3e5,0x991bcc5bfab80dbb481b,0x9a1b85a2faec4cadfc0c,0xf8275510c650d0154485,0x3bd1a0043d17c4726533,0x74019b1e8ee84c10c6fa,0x21c1c5f4160921a38a,0xc017200053e327ffe85e,0x68d87804e0910a94ad2f,0x5f93022000a767b7fceb,0x93e8d0021e8fc015195a,0xa142a4b3b6f443694137,0x67a7bba44482a1c2f0,0x594a4f08842c2c7d30c1,0x70429fcb7009cafabb2b,0xa8b5337e19b93290d0f1,0x4fe49a08003405e3315b,0xa7e73c15257f6c39b266,0xd3dde3654329f9900548,0xb64a85fbf8980102a9bd,0xa6526501306e370a4fe4,0x664ff0b62d96099a20f8,0x6647e7050621bb0f4411,0x878cb84a2499c39ca692,0xb641965293ffe8cd2282,0x26e3dd6330f3f0c04583,0x9148010e365d88aca534,0x43422ff281a004383f40,0x63fe2600086d7ec83200,0xeff8a0aab327fea06833,0x7601be12bf2ca44d567,0xcff73160911578307ea4],#[0xa310357ee62c1220dfc4,0xee3949965dc72922fd86,0x8a995f37566404288cb2,0x9915c99414419bd186fb,0xe0c42b301bf062179fe,0x71e2a427e1c00b42bba7,0xf0c2156ff426193a56b1,0xc24292b6e85643119a73,0x489ce52967bd45455257,0x39d72a2c3cd7005486eb,0x3b7c00d66d74cdfd950b,0x7ce010acd0fb40432a1a,0xd0059a30c6cc81208d34,0x3cbf32aa040d1089f8f5,0xe21b130a6c273193152c,0x7b7130a4763179210881,0x40d1088330bc1b4d0f2,0x8e27a040d130ff47546d,0xacda435cc2df470fff6,0x88687c20cde0c4343e5f,0x593efe2428687f3c7881,0x3b447840629bcd2c2e8c,0xe6462da9e9cea951b860,0x44389a700e882a7da0d5,0x9951c5e8188500af882a,0x459b397c9822cc12fca4,0x4a6fdc5f55d219212fd0,0x4dfd94afa428dfb119a5,0xfeca57d2172f7162a0e9,0xe6e11cf571010521b4e6,0x971f2ab1794785887524,0xfeb15e62a5b3fac7788a],#[0xf11d2da32f7162a0e96c,0xb88071689390a1f1d5f,0x860b27739498bb996284,0x5c351ca8696d01b0b7eb,0x7e008a13cccfa15606d3,0x421ceeb928e8db0a4a4c,0xd71e46142238cf1e461,0x12e2a4573628a03421f9,0xba3009288d284b8a924e,0xb2843fb313f00b0bee58,0x2cd4169053c21a98d42c,0x2ade1f35011862e5e018,0xa231ff0eed3e8a9c00a,0x7b86910a94dddd5b2c21,0x2a767278e03e0620b133,0xcb268428a5b03faaf508,0x55238db38307053d5f93,0x229fc4bab0059a4ae6a3,0xc603c8e0fa09c8a081a2,0x11253393fd34445432f1,0x7db643c07e08d4cd01f8,0x2eec5f081887d7fc0868,0x4de143401f1746002d10,0x2d0e5f3a208b37be81,0xcd5f965226ab383c957d,0x49d7e0154cc9d7e0514,0x330e2f95021205c38b67,0x38c78a28310c4fbdc48a,0x8e124cd1ff71e955822d,0xc0f41887aee1c22cbdfa,0xa627ffd19a30310e0f77,0x4e844d18b6753e30948e],#[0xa3d135ee90acee251ae8,0xe9014ab51b8513f236a3,0x20811294776d8540905e,0x6d613092e761e25205fb,0x9ebeb9bb34bfe842761,0xbe9680394b2ffea5890a,0x498953e841dec8468c42,0xc3a8d9f62c908405c589,0x1b2681a4d33d5cb843bc,0x2da8828470b8ff1ae426,0xccfa7606b90ccca0b324,0x92be968f52b78c38caec,0xe95dc5f654390d162512,0xb47e2288094aa7d388b3,0xa5bddd61ea5d63fc6b90,0xf187195d9aefb6908252,0xa0c4ed05d38662de0a36,0x3baec414967f5168c656,0x19ddaa0760b0c142faa3,0x77a98548295516dd7e16,0xb5a9876a4e3fc5bc149,0x30cccad491da94bd1898,0x4d48c06ed0e251b6fea1,0x720f70c86534b0f2f0ae,0x387a3dd6133ecb36108,0x8644378e06b6db0c7782,0xa95f7a584fbd2c261e0c,0x2712d4a1e8c5978521a7,0x9a4ea128cafc4b51b9cc,0xa396a920f6ffcc6084c2,0xf7868e32c7db995ac5d1,0xa19f45b4467d1e36c119],#[0xf53c1ea4938ea553ed44,0x91de14a7876fad85c72c,0x2b349fa458f8663afc20,0x10055cf7748f3768f0c0,0x99c323ea3566d4b2b1de,0x17ca89a92099f1a30dba,0xce29c1f1a185a3c2a703,0x3cddfc51873d1d934782,0xac752c2d1e16de511ba9,0x771e0f042af3e934c0dc,0x3fa336d260855a0df4b6,0x32303ea8f47822947c29,0x6231d4b2f8ba0e062cfa,0xf8243c37985d48a4dbd2,0x51519e145a4f61a4f6b5,0xe247ca2e1bc2da1d75e8,0xe95136965673c30cfba4,0x41315894386500e25dbd,0x61e2c0a38b37681499b0,0xcf46c0a6d3c5096da053,0x804544814f6e0822ba39,0x53759b8087c029a4fd0,0xeb374be014b27e8ba69c,0xe6c7c6861bafd65380a5,0x57082192c3b96ba014d4,0x9fc028f0dca1c0a407b2,0x9c10b0fd518c225e0512,0xc10646579d810296982b,0x7fb3a904281a181472f9,0x7909fd8149178fec0a4d,0x5c9056972af8612d5af8,0x951192bf446333d5128d],#[0xc4fd812d604a66cf626f,0x78b9be117f9444e0b121,0xee72668f4aa594f16660,0x52b288b6f0fd3cc070ee,0x3a3e655a934bc7c8d59b,0xef6c1295ebb8947296d8,0x6fc3be00988cf2417d8b,0x9321009853fa0f758a58,0x46477fe6c2905490f87b,0x845d8b87c02883113b6b,0xe4820a73a32198d17ed4,0x3a0c2cf4463480f89472,0xa67c30d63e17a0e0747d,0x7aa2522a5b60f4b99c5e,0x1b289498708092252bd8,0x22fe86805253e80c1e5f,0x28e0ec75460136354869,0x253cbf1464c5383c303e,0xcf8980d3866456f07da6,0x966b5056f0986475a3f6,0x7d5228f11b3e91899b6f,0x670d4fc4bca81d2b9e68,0x561c2e8c2e644783ad92,0x51b5d5d51e8f4e134f3b,0xde28fa70606c307b74bd,0x1692a7cd8413b72b0c2e,0x2915c09ef50f30f6fc20,0x2f0bee8747a708efd48e,0xbfa13984abc4932a41de,0xd282f87861b897f5d525,0x4a348d6b74417d5c412a,0x1f4e2d1871668146b6e4],#[0x4653ae1ca08f831a2d4d,0x5e84ce075eb2d953468f,0xad1ab170416eb46447af,0xb057cc1692770185464e,0x966e05a8c35b14bd9f41,0x2c90c41f860c8485ed2d,0xd85383a60ef58527a559,0x9abcb39032b5f2e370f0,0xfcc85425361e250506ea,0x41c090c3799031a40b2,0xe8acb242e2fa04c317eb,0xe06fe8e0f210f244a5f7,0x1244a623f20534202982,0xa894b254c312928f8810,0xf43e00a4eebd634257d3,0x3eb794695a500fe25275,0x7da9df0de7e56666936d,0x9853e598a7312d2aa65,0x695126625a6bbf266300,0xe0b4f67f8e6318c714f9,0xb87030b970e6ea09c630,0xa23db0a43b8d1a35da9c,0xc5e9b12172fca382ca97,0x87eb2c234a7d03e25293,0x218e5af094]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x40820000093870608301,0x1c000061c80000082810,0x4801000285022400000,0x28202340081408001081,0x8a0068a800c141000400,0x60c001040c6871a100,0x200003021d0020214b0,0x23058010100011014001,0x801030a2400000040120,0x4196020c807060008104,0x300240800004094121,0x4018060c1960000,0xe801c0a7320410032040,0x42010100005020c784a,0x48000220888000828a,0x493080401210100000,0x1010640301081448014,0x47e40000008006120,0xc916958c5366c8294000,0x23b000240c8ae00060d,0x6d3949338d100021d800,0xc9831201000104584017,0x3541a0df1e4921f70c8c,0x4d28dbd1891504380004,0xe77000005922167df0d8,0x84e7203457c41c8e,0x2be48e9000588c00,0x60000a13175aa3d40800,0xf9800000000000005c03,0x63dc000a0f8,0x1018152a5664b0,0x3ab80009088003948104],#[0xa81d374d18498a8fb000,0xe495b88300044b40005e,0x6700043c9bbb03c00051,0x5f800196c214a1b40001,0xa6b00024520000005,0x456f38e00000074ad240,0x482a7f000000112b000,0xf8000001843000080800,0x18b7883c71121c16e41,0x88f440c244bb00000,0x15e900000023091c30,0x8e4e8e6aaa0000000000,0x229c000434800188b09e,0xb0000000001996000000,0x10aac11f4ab8ff9c,0x9c025000141600000000,0x6a0000000eb145780011,0xc8a8bc631400088468ce,0x356614600000044bd17c,0x600043c00010fd9a1000,0x800000019500000010f,0x8349b0004374001190cb,0x21b600083198d52,0xba04c43e03d40900000,0x252a6a92ad9860dc8000,0x4d2ec70ce0c0973,0x4508001432000089800,0x7d4209a08c7000000000,0xceec4f28f800086412,0x25800000080f61380000,0x22ee8488a5d580003,0x27fe3cd6030ed8000000],#[0xdc2884be1e7406000c77,0xf25a68a80b3edfc795b7,0xccc5100003ff46285041,0xf3c310001de525180038,0x8b600000000011c2cd8a,0x45f40010c96b843ac,0x4008000000000,0x4d780011c446daea000,0x26e00066f000000000,0x1c00087400000,0x17234a00000000000000,0xc4d42885200000000004,0x65fe1dbc880001392ba1,0xda900000031e3ca1c50,0x6c4a00018b18f6d1d32a,0xee0966e7000330e00048,0x60734c02d9e00e2c4c80,0x62c9439d178,0x63580021cf0090057804,0x1010000703854c00088e,0x73a00000000ab800,0x110a9b30000003bd000,0x3100024d298000000000,0x58a0ca0b546d22b00010,0x82142f8002aac000ca3a,0x2e2000000000019b,0xb14929162e5892000693,0x5214be0000000000236,0xd887f00356eb23400000,0x289c00117e00000013,0x8be000000411a1141f10,0x436724c02d0006329],#[0x80000000005440001886,0xf000415c0018e588103f,0xd5a29238000462c0000a,0xa9d03805744894be0f47,0x12093f2e027bf90d8,0x86f00068209b80000000,0x28b6048000e920000001,0xa185318c45b27213b000,0x46787c7248dc70605c2c,0x18095e8e729d1a8c7365,0x8804a91e78f0ccc45673,0x83201ae6b91be1b1929c,0x22f66f037d999838667f,0x51710a7616e6c6083061,0xe517a7d089e1dac1994a,0xcc080001f50c,0x6e000655000000000000,0x443c26ca260,0xd5a00020c346a000c388,0x24c000120cc888000001,0x8e34ba0000000000c8a,0xc338800102b000777800,0xf155000687c0004718e,0x83b383dcf00028aa9,0x47dcb533540000ef0,0x40e000000001d00007c8,0x11bf10c0006060001036,0x204,0x6c000000000701494400,0x105600048,0x2d00011ea000006eaa40,0x8e68d300000001d60004],#[0x0,0x982ce76294398000000,0x9d468000000898c60000,0x3550ece8000000000044,0xaa219c0019b402a00023,0x197c4970000000c782,0xc9d00000000004ef8000,0xe43d09210b00030f4000,0x8edc87362320d285ec6a,0x133600000060e018f96,0x4f23207a400016400000,0x4e04121d789f33980018,0x6304000dfa0c8e,0xd5aa8ce0000004754000,0xc560c6c42a464000868,0xd80b923c000882e09b38,0xb0000000044485,0x2982b400083545864480,0xdd7000775493008de,0x7c2ea45d4ab00a0000,0x23f80000000002458000,0x400046d80010d6000000,0x853b358100051a521289,0x5500030d99ba00049ee4,0x8,0xc8e00000000018fbf058,0x18dcc618001201,0xe951914000007ba3a000,0x64d80000000fd00029b,0x10000087800010200041,0xef000235200082927b92,0x1e821a000682a24a000c],#[0x43311dc0010a44c98001,0x800197900054a000195c,0x26408003130d5b0f3e26,0x329e00001ce5e800122,0xe1bf6b0000000e5000,0xc0bd1bcfc00013120,0x52d00000000008bf4918,0x20d64e10000002044,0x4ad2690000049000,0x27188ab163a9080020b,0xec458e2180020d19d300,0x9007af46191be4be50a0,0x89000000000000000006,0x23c000632c7e8003,0xa03f9e4caee09d032c3f,0x37ac39e00090223a,0x38c1233000000123e00,0xac0000530001a1400000,0x2c800000000000000011,0x1fec2022d800000021ad,0x13d009fcdfe620050,0x60002255448000ce7913,0x8a37b8f600050a800334,0xea000242000000000021,0x4e800000000000000022,0x102c00041c8000000c,0x5ac34e4da70c0000,0x2bb8d23c85c7c033c1ad,0x72051433a000000622,0x4511206ae74913000147,0x7b2354473329c72c09a2,0x225be80120dc00000019],#[0x1bb4b6c038aa6516106d,0x90bb1a70a281d800242e,0x2600a19684c055c5cc23,0x5e3a000a05ac1a64059b,0xca12209243da280a1d06,0x5e6044001917000713a9,0x1002c2580028818cf8,0x15ec0009ae00040c8,0x4288000000000187cc22,0x4ff00021d,0x80000000000000328600,0xe2000000224f49122bd3,0x1c6500000000009,0x51d40000000000,0x20bdc470001351442,0x450cbb8000001427000,0xf8863a3a4b687e000000,0xd112008002bc40002e,0x1800031f2d4f00048040,0xf1d2454001946e,0xa69b695f855e800,0xc000000215800037a997,0x2000755ea2a000000060,0x94000000271e41bc6708,0xc600021ce01780daf780,0x23f617280180000840,0xdf700008d800144b0000,0x8003a0116fa4e0003117,0x105b8b3635e26a0002b0,0x1874400000051288d000,0x1d282987f41998448f,0xbe80bc0011c200071840],#[0x46e000000264a3900006,0xd0280031f00006818002,0x2375de38ea000329a08c,0x3000000131e000000000,0x8d0000c8c000013210]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0x50910505105011048510,0x58110551105491054510,0x5911058d105891058510,0x5d5105d1105c91059510,0xdd510dd110dc9105d910,0x501204c5201d120dd910,0x545205412050d2050520,0x58520581205512054d20,0x5c520595205912058d20,0x5d9205d5205d1205cd20,0x9d1209912098d2095120,0xdcd20dc520d0d20d0520,0x50930dd920dd520dd120,0xdd130dc9305913058930,0x549405454050940dd930,0x58540581405514054d40,0x595405914058d4058940,0x5d5405cd405c9405c540,0x9914098d40951405d940,0xdcd40dc940dc540d0940,0x5914158541dd940dd540,0x505505d9415d54159541,0x58550581505515054950,0x595505915058d5058950,0x5d9505d1505c9505c550,0xd05509d1509915098d50,0xdd950dd150dc950dc550,0x59551591515855155151,0x5915459153dcd515d951,0x5d9545c5545c15459554,0xdd954dc554dc15499154,0x54d6054560505604c560],#[0x59560591605896055160,0x5d1605cd605c9605c560,0xd05609d160951605d560,0xdd160dc960dc560d0d60,0x5916158d6155161dd560,0xdd561dd161dc1615c161,0x9516359563551631d163,0x5c5645c164dd163dc163,0xdc564dc1645d5645cd64,0x5d1655c5655c165dd564,0xdd165dc565dc1659d165,0x54b405c264552635c254,0x5934058f4058b4055340,0x59341547415cb4059740,0x9fe775c3435c34159741,0xcfeffbfafdbdeefb7ebf,0xe5f7fdfb7ddef77dbf5f,0xeebb7ed7afebbade7f9e,0xf7bddf6bd7f3fbfefbbd,0xfdbf5fbfeefb7eaf9fdf,0xc23ffffbfdff3fbfebf7,0x58879f5486a45085d758,0x91595752595695590f99,0x6640619c5459149758d4,0x54406d484040a1e6d159,0x6650806de0406d58406d,0x6958c04fdc804f5c80,0xdd804f5d806659006655,0xed4841c7e1804761804f,0x81db5881ed5441ed5041,0x5d01db5901cfdc81cf5c,0xdb5941c7e101cfdd01cf],#[0xc02858c00fdd41cf5d41,0x5d400edd000e5d002898,0x8edd800e5d800edd400e,0xa858c08edc808e5c80,0xdd808e5d80866140a559,0xedc810e5c810661808e,0x810e5d81205941205501,0xdc820e5c820661810edd,0xe5d021a590206e0820e,0x420e5d4206e1020edd02,0xe1c0c161c0c6e1420edd,0x4161c24161c147e00141,0xc34c58c34ee04346e043,0xe18341e14341e1034c98,0x4161044c98c44c58c441,0x28c5d02816184416144,0x61c18a5d418bdd018cdd,0x8161c2c95d82cb5d02c1,0x4381e0838ee04386e043,0x614481608481e18381e1,0xc161c30a5d4301618481,0x84c1e183c1e103c1e083,0xe084016184c16104c160,0x1608501e14401e10401,0x85cfdc45c16145016105,0xe085eb5885eb5485eb50,0xe65505e998c5e958c5eb,0x5e69905e65905e69505,0xe145c76145e6dd05e61d,0xc76185cfdd85cf5d85c7,0xc6a958c6ab588687e185,0x594687e106a15506a998],#[0x8fdd868f5d86a1dd46a1,0x78fdc4787e186876186,0xe1078fdd078f5d079b59,0x8fdd478f5d479b594787,0xb01a1c61bdd8787e147,0xe0c6c1a1cb0161cb0760,0xd858c7c1a1c6cadd46c5,0xcb8c58cb8560cb81a1c7,0x610b8ca0cb8c60cb8c98,0x47600b41618b81614b81,0x801a1cb4161cb43614b,0x5d481859480cdd080c5d,0x4cdd0a4c5d0a4cdd480c,0x746604bccdd4a4c5d4a,0xa1c74161c74a5d474b5d,0xb5d0a0560ca07600a01,0x884b5d0841a1ca0161ca,0x600a81a1c84161c8495d,0x41a1ca8161ca8b5d0a87,0x454b5d054560c5466045,0xe00941a1c54261854361,0x41e0494fe0094bdd0947,0xac7600ac1e18941e149,0x614c01604c0161cacbdd,0x895d888a5d4881618c01,0x498add4981a1c88161c8,0x604c41e18981e10981e0,0xc9dd89c1618c41610c41,0x4c81e149c1e109c1e049,0x610d81614c81610c8160,0x1618dc1608dc1618d81,0x4f8fdc4f81610e01608e],#[0x588fa6d08fa6508f87e0,0xa6550f87e08f8fdc8f9b,0x4f9b594f9b590fa6950f,0xdc4e9bdd8f8fdd4f8f5d,0xc1a1ce9d550e85e0ce8e,0x9341a1cfd6590fd858cf,0x61534b59134c58d34160,0x66e00e47e00e41619341,0x4e4b5d4e6398ce6358ce,0x58d30bdd8e4b5d8e4bdd,0x461530bdd530b5d5323,0xd30461930bdd930b5d93,0xa1ceca5d4edd550ec4a1,0x41a1d0095d9016591001,0xd38c58d381605384e111,0x59138b95138b55138c98,0x4161938161538b99138b,0x50585950639510635510,0x5d52a355128cdd504c5d,0x44e08f4add4f4cdd528c,0x8f4b5d8f5ddd4f5d594f,0x609244e18f44618f4bdd,0x8461924bdd924b5d9244,0x508b5d5084e09089dd90,0x6092d6dd9084e1508bdd,0xc46152cbdd52cb5d52c4,0x51c1a1d0c161d0ca5d50,0xe191c1e091c1e051cadd,0x1619401609401605401,0x5201e09201e05209dd92,0x615441609441605441e1,0x4161ebca5d6bdd552bc1],#[0xec495dac56592c4d5cac,0x592d4b552d4c58ed4161,0xa3552c81e1ad41e16d4b,0xac1d596c0c5d6c98596c,0x5d6d0b5d6cc461ac0b5d,0xa154968fdc568161ed0a,0x1687e0968fdc969b5896,0x6159cfdd169b5916a155,0xa551a01609a0161d9c3,0xd601619a0a595a01611a,0x5d960add161e98d61e58,0x495d971359570add960a,0xda4c58da41605a43e158,0x595a41611a4a551a4c98,0xcdd175e551741619a4a,0x1643e0964cdd191e5519,0xdd964a5d965d99165d59,0x43615943e1964361964a,0x5987601983e1588161d9,0x609a81605a8161d98361,0xc3e097c1619a8a595a81,0x18c1e098c1e058c3e117,0x611ac1609ac1605ac1e1,0xd65922c76022d6591f41,0x5f85e0df8161e2c261a2,0x61234959234160a35359,0x49dd6049dd2041616341,0x2389592381606382e1a1,0x60230161638959638161,0x161e30261a303616307,0x224261a0135960165920,0x61a25659224560e24760],#[0xc2e16082e0a08161e242,0xe28261a287602282e1a1,0x6163c160a3c16063c161,0x1606402e120c2e0a0c1,0x5486e0148161240160a4,0x61d50a5d550b5d54ce5d,0x81e01581e19541e01541,0xee41e0ae4e546e41e155,0xe1ae41e16e4b592e4c58,0xce5dada0596da5592d81,0x1b4161ee0a5d6e0b5d6d,0x591c5a591b60551b46e0,0x3619b0a5d9b1d591b0c,0x1c03e11bc6e05b83e19b,0x60a55858e501e11c01e0,0x81616541612549592541,0x258bdd24565924585d24,0x6125c16025c161658160,0x160a701e1ae81e0ae81,0x270560a7016027416127,0x6026056026c5e0264561,0x98612698602685602745,0x9e41605e45e02b58a126,0x619e4a595e4b591e4160,0x8a595e8b591e81601e81,0x1d04601e04e01cc1619e,0xe05dc1e01dc3e05d03e0,0x1e0ab01605ec1601ec1,0xa881606881e1ab0b592b,0x6168c16028c161688160,0x81606901602906e06801,0xaa41606a41e16b81e0ab],#[0x612a81602a81612a4160,0xc161ea0261aa03616a01,0x806f548041606ac1602a,0x61406f59406f60806f58,0xef5481ef5081ef61806f,0x41ef6101ef5501ef6081,0x5480ae59402e55002f61,0x2e50812e5940ae5880ae,0x22e54822e50822e5881,0x58c0ec5880ee6040ee55,0xd05d40e75900e75500ea,0x80c8e140c86140d0dd40,0xe180c86180d0dd80d05d,0x6e604150a1c0d061c0c8,0x1505d016255016c5881,0x5d8162594148e10150dd,0x48e18148618150dd8150,0x26e604250a1c15061c1,0xe10250dd02505d025c59,0x50dd42505d425c594248,0x4350a1c25061c248e142,0xe14350594350550348e1,0x90594450590450550450,0x41a7590188e081ae6041,0x618190dd81905d81a259,0xd0a1c19061c188e18188,0x4310594490594390dd42,0x61c308e10308e0832e60,0x8e14408e08410a1c310,0x45ef5445d0e14410e084,0x6045efdc45ef5c45ef58,0xef58c5ef54c5efe045ef],#[0xc5ef60c5efdcc5ef5cc5,0xdd05ef5905ef5505efe0,0xefdd45ef5d45ef5945ef,0x85ef5d85efe145ef6145,0x5046afe185ef6185efdd,0xaf5c46af5846afd046af,0x6af9906af5906af6046,0xa106af6106af9d06af5d,0xaf4c47af6186af5d86af,0x47af5447afd047af5047,0x50c7af6047afdc47af5c,0xaf5cc7af54c7afd0c7af,0x7af5507af60c7afdcc7,0x9d07af5d07af1d07af95,0xafa107af6107afdd07af,0x85af6147afdd47af5d47,0x5c462e584610dd85905d,0x105d462759062a58c62e,0x86105d8608614610dd46,0x544b0861c608618610dd,0x105d4b27590b2a58cb2e,0x8b105d8b08614b10dd4b,0x5846c861cb08618b10dd,0xd05d06e25506ee5c46ee,0x86e2dd46e25946d0dd06,0x61c6c86186d0dd86d05d,0xd05d07dc5907ee5c47c8,0x47d05d47c8e107d0dd07,0xe1c7c861c7c8e147d0dd,0xd05d08ea98c8ea58c8c8,0x48d05d48c8e108d0dd08,0xdd88d05d88c8e148d0dd],#[0x905d0baa58cb88e188d0,0xb88618b905d8b88610b,0xdd86505d8650594b9055,0x48618b50dd8b505d8b50,0x8105d87105d070861cb,0xe1c808e10810dd08105d,0x2a1d082a95082a550808,0x82add082a9d082a5d08,0xdd482a5d482ae1082a21,0x6a550a6ae1c82a21c82a,0xbd05d89105d092a5d0a,0x618bd05d8bc8610bd05d,0x67590748e0476f600748,0x7505d07675d07679907,0x5d4762594750dd07679d,0x48618750dd87505d8762,0xc74861c75061c748e187,0x5d0a27590a08e1c750a1,0x8618a10dd8a105d8a27,0x848e0486f60084861ca,0xdd08679d08505d08675d,0x48e14850dd48505d4850,0xc84861c85061c85c5d88,0x5d4aa75d0a88e1c850a1,0x4861ca88614a90dd4a90,0x496fe009486185505d85,0xdd49505d4950dd0948e0,0x50dd89505d8948e14950,0xc950e04950604948e189,0x614950594950e0c95060,0xd0e18950618950e14950,0x8ac8614ad0dd4ad05d4a],#[0x61cac8618ad0dd8ad05d,0x8618c105d8c08604c08,0x890618c10594c10604c,0x5d4888e10888e048af60,0x8861c89061c89c5d88a2,0x49905d8988e1c890a1c8,0x618990a1099061099060,0x505d8c48610c48604c50,0xc50610c50604c48618c,0xe109c8e049d0618c50a1,0xd0e049d06049c8e149c8,0x9d02109d0e0c9d060c9,0x6149d0e109d0a109d061,0x88610c88604c90e149d0,0x8cd0a10c90610c90604c,0x618cd0dd8ce7590cec58,0x1c590d10a1ccc8e18cc8,0xd90a1cd08e10d10dd0d,0x544f90a1cd48e08d5059,0xaf604fafdc4faf5c4faf,0x8faf5c8faf548faf508f,0x5ccfaf54cfaf608fafdc,0xaf550faf60cfafdccfaf,0x4eaf614fafdd4faf5d4f,0xdc8ea7508eaedc4eae58,0x905d8ea2594ea7590e90,0x4fc861ce88618e90dd8e,0xe08fd0dc8fe7508fee5c,0xd0dd4fd05d4fe7550fc8,0x9108e1cfc861cfc8e14f,0x55112a58d1105c912750,0x505d91105d5127591127],#[0xd3486093505c93675093,0x5d536759136755136a58,0x486193505d9348615350,0x53506093505893505493,0x550e6a58ce5061535059,0x50dd4e505d4e67590e67,0xce6754ce50dd8e505d8e,0x594e67dcce675cce6758,0x675d8e67dd4e675d4e67,0x93275d5327595327dd8e,0x58ceec588ec8e04ee75d,0xe7590ee2550eea98ceea,0xee7a10ee7610ee7990e,0x5d8ee25d4ee2594ec8e1,0xc8e18ec8618ed0dd8ed0,0xced0a1cec861ced061ce,0x5c9008e0502f601008e1,0x1c59102795102755102c,0x5008e11027a110276110,0xe15010dd50105d501c59,0x861d01061d01c5d9008,0x516fe01148e1d010a1d0,0x5cd16a98d16a58d148e0,0x67951167551150dcd150,0x1167e111679911675911,0xe15150dd51505d5148e1,0x88e19150dd91505d9148,0x53a75913a75513aa58d3,0x6193905d93886153905d,0x9055139058d39054d388,0x93906153905953905913,0xdd8f105d8f27590f1061],#[0x6ae09048e1d048e09050,0x506a5d506ae1106a5510,0x5d52aae1d06a21d06add,0xc86093d05d91a75911aa,0xf486193d05d93e75913,0xdd8f505d8f62594f6759,0x67608f67604f48618f50,0x9267618f67dd8f675d8f,0x605090dd50905d50a75d,0xa75d50a760d0a76090a7,0x50e75d52e76150a7dd50,0xa110e76110c8e090c8e0,0xd061d0e25d50c8e110e7,0x51c8e1d0d0a1d0c861d0,0xdd91d05d91c8e091c8e0,0xd0e051d06051c8e191d0,0x91d06191d0e091d06091,0x6194105d9408609410e1,0x8e05210619410609408,0x5210605208e15208e092,0x60d210e09210609210e0,0x50e15210615210e0d210,0x54506094486154486094,0x592bea58ebec58abd061,0xd05dabe2596be7612be7,0x2c5061ebc8e1abc861ab,0x5d6c5c596c67612c6755,0x50596d5061ec48e16c50,0x2d08e0ad1061ad50616d,0xd056af50569061ed2761,0xaf5c96af6056af5c56af,0x16af9d16af5d16af6096],#[0x5495ee5855efa116af61,0xe25955e75915d0dc95e2,0xd5c86195d0dd95d05d95,0x6099d0dc99e25499c861,0xd05d99e25959e75919c8,0x56c861d9c86199d0dd99,0xe096d0dc96e25496ee5c,0xd0dd16dc5916e25516c8,0x9808e1d6c861d6c8e116,0x5d18225518105c982254,0x10589a105d9822595810,0x16225d16229916225916,0xe0572f6017225d96229d,0x1c59172255172c5c9708,0x9722615708e11710dd17,0xa1d70861d71061d71c5d,0x6255186a58d848e1d710,0x98625958509d18505d18,0x5d1750991a50591a505d,0x6260566a5d192a9d176a,0x96625d96625916626096,0x5d1788e09788e057a261,0xa2615790dd17a79d17a7,0xd790a1d78861d79061d7,0x61d9675d1948609948e1,0xa2595888e09888e05888,0x9988e198905d98a2e158,0x6199905d99a259598860,0xe26117e26097e26057c8,0x18c8e098c8e058e2a117,0x6098d0e058d06058c8e1,0xd06118d02118d0e098d0],#[0x9f1c589f10e118d0a118,0xdc9f5c589f6e5c5f50dc,0x48615f50dd5f5c595f50,0xa2dc58a2ee5462c861df,0xdd62dc5962c860a2d0dc,0xae5c5f8861e2c86162d0,0x1fa2551f90dc9f9c589f,0x58a10861df90dd1f9c59,0x1c592108e0a1105ca11c,0x611c596108e121105d21,0x50e050552348e161105d,0x5c5ce05c54e05cd0e05c,0x205c5d205c95205c5520,0x5ce148e0615c5d605c9d,0x509d21505d215c592150,0x61505d615c596148e121,0xd0e39050e39ce1a148e1,0x1095239055239054e390,0x1fdc591fc861e30860a3,0x5d219c592188e0a190dd,0x8e0602f602008e12190,0x20275d201c592008e0a0,0x61a0225d6010dd20279d,0x10a1e00861e01061e01c,0xe2675d224860a248e1e0,0x60e09c60a09c60608861,0xc8e061dc61609c5d609c,0x61d05d61dc5961c8e0a1,0x59628860a29ce1a1c8e1,0xdc6060c86162905d629c,0x621ca120dc6120dc60a0,0x6014c8e12208e0a208e0],#[0x5061d508e015276154e7,0xae50616e50596e5060ae,0x601b1061ee08e02e1061,0x22611be2601be2619b22,0x2450552548e16508e0a5,0xa1e45061e46e606448e0,0x9060ae9c6164dc6024d0,0x2b6a602648e01c9061ae,0x5c9d48e05d505c5d6a60,0x62595d67591d48e09d50,0x1d88e19d505d9d62e15d,0x601cd05d9da2595da759,0xe2605d22601d27605ce7,0x1dd0601dc8e05dc8e01d,0x60ab10e05dd0605dd0e0,0x905ca7905c679061ab10,0x67905d67905ce788e0a7,0xe028505d67dce1a788e1,0x505c6950616b9060ab88,0x2948e0a9505ca948e069,0x5d2988e129509d29505d,0xc8602a08e069c8e029d0,0x1705d01705901705940,0x5502706181705d817061,0xb06083306081b0614270,0x4b305d46305946305d85,0x5d86f05d06f05906f059,0xf0dd47f05d47f05507f0,0x86705948f05508f06147,0x5909305d08305907305d,0x30618cf060c870604770,0x8eb0588eb0608d70610d],#[0x54d030595370548ff05c,0xf05d8f3058d17060d030,0x95f05c95f05895f06050,0x5c96f05d99f05899f05d,0x306116f05d16f06096f0,0x5f705c9f306057b06057,0x5521305c9fb05d62f05d,0x306060305d1ff050e170,0x1cb0602470602e306015,0x1080058001980003060,0x5b80280011d0072802d8,0x1808e0042401e700d580,0x18e00ba40584028a013,0x3ec01e280e3c06cc0343,0x62047f0230010dc08300,0x80b00054802870139c09,0x19680c66060f02eb816b,0x9f81c2c0dce06b803450,0xf03ea01e980f04076003,0x887043402110104a07f,0x2d60937048502360116e,0xb4142009ed04df026441,0x2b40152a0a6a0523028,0x5df82e4416c60b2f0582,0x880631030f0181e0bde0,0xa0d49068e8339419720c,0x1c340dec06e2836541ae,0xba41d800e9a07388392c,0xa03e1c1eba0f41078e83,0x830840e020240fdc07d,0x118087c8435421641087,0xde11b308c384588227e1],#[0x82500124e09150484c23,0x4df026801315096d04a9,0x200504427d413c709d40,0x20a870536c295c14760a,0x15d30ad9056142ac8153,0xd86168c0b2e858a02c00,0x2f22175e0b8f85bbc2,0x86184306c18140bf185f,0xc980640831b418be0c44,0x2d0cfe06740333419600,0x61abe0d4f869e834ac1a,0x36da1b4b0d8f86bf035b,0x16438641bff0deb86e94,0xe073d039981ca20e3f87,0xee7076643ac81d430e8,0xede0f50879b03c821e08,0x841fa70fbb07d243e221,0xc40ce2035100387f943f,0x8558424421011070082a,0x1f0881443b021b010c20,0x5116d08abc4522226f11,0x238b11b288cec463e230,0x856240d11f288f0c474e,0xc49c824af123d0914c4,0x96004ac2253a128c894,0x34b0998c4c5025f112da,0x42139309bdc4db026be1,0xe281413ed89ed04eec27,0x524228f1145f8a228509,0x7a05380299314b88a510,0xe0aa4854c62a3d15088a,0x15cf0ad9056622af4155],#[0xcaf163a8b0dc57f22bcc,0xf02d5016908b3b859982,0xc5c742e1216f48b6c45a,0xbc245db22eb317440b98,0xf78bef85f2a2f65179a8,0x518590c2046092301a17,0x318718ab0c4cc620c30d,0x4dc3240190c0c7806354,0x2c662632f219668ca986,0xd03467ac33b319bb0cd,0xa888d374696634721a18,0xec1ade8d6346ac6353c1,0x6368d1b2f0d8e06c2035,0x6ee8374d1b910db986d5,0x148705837fb1bec0dea8,0x8e49071f638c11c400e,0x1cfd0e724734c39781ca,0xad61d570ea3074d83a31,0xd23ba61db38ed4076263,0x4796a3c761e1c8f03077,0xf6c87b0a3d581e8b0f36,0x4f0f99c7c7a3e131ef40,0x11fb30fcec7e123ed81f,0x403520050ff847f6a3f9,0x1fc40d720561021080ba,0x60835c418420a99047c8,0x90aac85004250210a907,0x1b290d00863a42fb216b,0x3721fa90f68876e43882,0xa44dd22601124488b644,0x8b74458a22ab114b08a0,0xa488cda464c2312117b4],#[0x11cf48e2446dd235691,0x2422920808fda47b623c,0x8ee246292298910e4869,0x6e498c24ad924a492144,0x495144a55250d127a093,0x2d94966c4b11257012ac,0x1d9305c97be4bb525c69,0x72677932f099224c6e26,0x4dc626cc935909a8e4d1,0xd7e4e8b272d938909bf0,0xec9f064f45278d13ba49,0x14168a072501827f213e,0x886943c0a1a650b02840,0xe128da94614a2ae512a2,0x45295292f948c8a40a51,0xa6e45341298d14bbca58,0x164a85c540329eb94ebc,0x695424a9b454ad2a4315,0x2af9956e8ab1a55552a9,0x6ba2b48159b0ac86561c,0xf457552b9395c08adb05,0x4b03457f72beb15e6cae,0x63ecb1a058a52c36160f,0xf696708b31459522c8e9,0x42d54169e0b49a5a192c,0x5b742da496c74b6005ad,0x8925c1c2df316ed8b722,0x50b9da5cc82e50171ccb,0x177acbb765d842ea7174,0xf6317a3cbcc85e3b2f0b,0xc22fcb17d6cbe605ef72,0xa6080302818090bfe65f],#[0xc2ec6145308a18370c15,0x960c45861fc30e51868c,0x398c48c5cc62ac314298,0x31f598f08c730637231a,0x4d13253191d8c884641b,0x9e659232a799498c9ea6,0x8cd54666f33231981ccb,0x9e3cced8673b338119b5,0x491a198d04067e933e21,0xd34ab1a480d1e068bf34,0x6a6535189a7acd376698,0x6f26b4f358c9ab4cd554,0x1cd8966c0c35ea9ae88d,0x9b5d0da3a6ced365d1b2,0x7529b9d0dc786e0436d8,0xbc37c11bd34de126edd3,0x4708d382b9c07cdfe26f,0xe2ba713a388b1c3c8e18,0x928e43471eb38d91c604,0x39cc74e5cc72bc39411c,0x3a0c9cfb0e774738439a,0x5083a689d280e900744a,0xd675c13acb1d5b4ea7e7,0x4ed4676753b209d858eb,0xde20eebc772e3b841db9,0x1f1e05cefea77d03bd79,0x43c6f9e2acf11e78673c,0x79c73cc49e57cf268790,0x56a7a843d291e8a4f3f2,0xd0f6f87b423d899eb7cf,0x9f190f8707c0d3df29ee,0xeb21f4bcf9f67cc93e4c],#[0x823f289f850fbd27d9c3,0xa7f333f869fb68fd607e,0x5a7ffa3fe09fe34fec,0x3e901a880ab403e20161,0x206a9031081624098a0,0x415da0a010498821940f,0x40041da20dcd065682ef,0xd484b442432115d08648,0x50bac859542a72146909,0x1bad0d6286744320a185,0xfe21ee90f1a87534393a,0xb4479222ad10dc882c43,0x8a3d45002270112e4892,0x6948b0e456f22a7514e2,0x9d183e8bee45e1a2e091,0x235ad1a648cd0464da31,0x72ea38911c028dd346d2,0x344787a3b991d708e8a4,0x48ff747e123e591ee28f,0x221890d64855241b9206,0x8a923d691a248ba24509,0xfa4c2d25b292a7493624,0x4a00a4f712740936c499,0x4f34a64a524d28b2942b,0xe695b44ac02555d2a4c9,0x52d3e967e4b27258892b,0x5e792ee2972e4b8025b2,0x61a628130f098364bf8a,0xf4cbd264fd322a98e74c,0x9a5d4d10267d93398999,0x6f49b244d7226af5351a,0xd539069c424e0626f1d3],#[0xa76353a949d1a4e75a72,0xf4d279b13c4c9dfb4ee4,0x674f9fa7c4d3dda9ec74,0xea04e500ca7f993f369f,0x42c4a1185072282c140f,0x88543f8a1cb50d22860d,0x328b5d4560a26c5125a8,0x51d9a8e1546a8a324518,0x48f5232290cd4826a3d4,0x62a582529e2941949a0a,0x14cf8a64a5303a97794b,0x9d254e3aa6e45362a9a7,0x162a0214fd0a7be53c22,0x8547b2a30d5118a85554,0xa9f854e32a68952c6a93,0x62caae45550aa9bd5470,0x99578caba655be2ad415,0xab2f958f8ac455609aaf,0x6d5ab5f55a8cad1c5675,0xa9573dab9215c34ade15,0x8af5e57982bbf15da8ae,0x60f6b0485804abf755f4,0x5b16264b104586aac2b9,0x1ac8cd641eb1dd58ceac,0x59842cb616574b293593,0x40759e7ace5d66ceb32f,0x42b4f55a5d2d2116886b,0x16bb6b5b05ac1ad53d6a,0xdb556d30b6685b1f2d84,0xd42de116eb4b7295b7d2,0xb5c28ae0996ff0b7d35b,0xb9525c972e39d7160b88],#[0x4deba255cf3ae6797306,0xc5767abb075d6baea857,0xaf0e177fabbc85dd1aed,0xe95af3f1798cbc965e32,0x145eee2f6757b02bd585,0x2bed45f53af99d7c6cbe,0x7f98bf915fa8afc957e0,0x4c181fcc0b96031b0071,0x83077d8358c18860b430,0x617730b058516c24a610,0x41461e030e2586a0c325,0x9ec5156268b129188bec,0x18c0cc5e062d9b16118a,0x1c4d8dbcc6a9633db193,0xfcb1f558f56c78063a13,0xc646eb224d90bac83b63,0xc9d964d73260d928cc90,0x55cca846530328a99410,0xb59702cb31658232b699,0x331c99890cc0c65ecb2e,0x6b3b34e99a0eccd96654,0x43670c337ad9b84cd996,0x6ceeb6765b3a859ce0ce,0x9fe4cfb967c533d259e3,0x3f9a17ad0826826b408d,0x8346fda302d157689734,0x6963349f5a4aad21668f,0x3b069b5b4cf5a626d2e8,0x54d46d6a1c35011a7b2d,0x5aab8d5436a89b53b1a9,0x5995ac50d6036aea3560,0xa935cb1added6c96b47b],#[0x56bf2b5f1daf44d7726b,0xd8cf6c4a361b9b07ad81,0x382d9a36cb1364ddb1ea,0x59b4f2da556d16b681db,0xb6d21b63edaf06d5bb6a,0xe2cb70a5b7c0dbb26dbc,0x5c6e92373bdb972dc8a6,0x6de1a6ef5376f5bb16dd,0xbe0aded36f54b79edbc9,0x21bfb6dfb26fb8b7ce9,0xb8351c158e073701e38,0x70e1b8641c2c2e132708,0x2f1715d389f5c46ae203,0xd6e3aa71bc38d3dc638e,0x1c968e47f722b39079c7,0x96f1cb14e54c728a3939,0x5f39a3dccc6e62572f63,0x573cb39d91ce4ee6f973,0xe8b37443ba12dd00ce7d,0x342e97374a33a46dd1cc,0x61d530ea5a750a3a78dd,0x3aeb5d6f2eb4d7583bab,0x650bb1cdd87eec1175ef,0xc176ccbb589da24ecd77,0xee7e771dbb829dbcaed,0xdf4aef587791bbbb1dd5,0x271e0c2f02777f83bf45,0x13c575e262f0fd786b3c,0x79193c7dde396f1a478c,0x3237975bcb21e53cf254,0x56f3f679d9bce0de6baf,0x1e9d0f4b97a463d18de8],#[0xd7ddeb96f59c7aaabd4b,0x873dbb1ed78f6867b20b,0xd7bedbdeb1eee4f7427b,0xf8ee7c59be1e5f084f80,0x410f9d47cd0be5b1f24e,0x51f56cfa867d2b3e8bdf,0xbee41f6a4fb217d7dbeb,0xe5cbf20df8a2fc207df4,0xeb7eda3f61dfaa0fcf57,0xcfed57f4b3f96dfc50fd,0xffe6ffbf7fc13fd49fe1,0x4c201ef00b98035c00a5,0xb4084603d501b580b440,0x8177c0b1a05030258811,0x3e581d640e0e06a30325,0xdf04ba82444113e083d0,0xa0b55058882aec14e609,0x1aa60cd1062f8302c174,0xb9c1d420e5706f58366c,0x18432420760fd707a683,0x97a8492c239e1169089,0x4950a0f84f342722134b,0x5e16490ae38550c29ae1,0x4304a17c90baf85bec2d,0x6844334e19530c768620,0xe686dac36461ab90d338,0x30e908732c39021c1f0d,0x1f110f50878e43bae1d6,0x22220b9102787f8c3eee,0xfc4566222b10e1885944,0x8938448ba23e311c588b,0x35b899644c0225a91292],#[0x514528a00c4f4a27171,0x62afb153a8a79c530629,0x59d62c7f16158af5456c,0xcbc5dc62e5716f98b644,0xb8c30c60e22ff317ba8b,0x197e8ca6463d23199188,0x55f1a718d20468223391,0xf636bb1b328d8446b723,0x470b237ff1bd28dd4c6d,0xe884738239571c818e2c,0x28ee94769a3add1d3b8,0xf1ebc8f43c798a3c711e,0x3f691f848fabc7ca63de,0x30e41232064901647fb6,0xcc85f64297211f907848,0x912d488b6440721c890c,0x326917b48b4a45632284,0xf123ce91d148dc646972,0xa4985249a9232c90de47,0x96ca4b012550928f493b,0x80499e24c93261a92f5c,0x81703c250542b0bc1707,0xd01c17b081370ac1063,0x45506c18321404815d08,0x115184592c0f3190d028,0x2131016d101cb0f84234,0x40c15822280793e4c83e,0x80e181f13d003024e30d,0x2304e463154342c15515,0xa12782d0f8190fc0214,0x9a2cc02328582d0590d,0x81071838380de0d06615],#[0x4412f07d004da0641a3e,0x8785c83d170431616238,0x89c320b86a1980c4123c,0x4ec381e80e1902686014,0x220c8b9314990b03a0a,0x800a100901dd2c0183a,0x120821e164243c05a00,0x10212b270f87810a44,0x288a08c3024c3701210,0x823080e2688c069351b,0x97b2d158530342f00c4d,0x4a12a224440c41cc6a36,0x13c080642b8d45e11934,0xcb94d124228802a1b87f,0x23d13868801a4254da1a,0x4e06d87a4e8745448074,0x49082cc91d8a33ccfa3b,0x61f8c6547e50b718810e,0x2050e5cb5e8d44ce1a,0x9a696eeda46243e2ad1f,0x5db3c8196b5fd3d08600,0xb54c0144f3f08138c90d,0xbe5e4a54c048917e3c2a,0x2d9c242eb83a066486c0,0xec1c466cfe5fc098cdcf,0x242a3f060b100014427a,0xc1d7c3c301b1a19f9086,0x42d7fc06c656e5fc098c,0xd3f166181469e7e9a6c2,0xce3700492bfb8e6091db,0xbfba998248dc73048c23,0x1fcbe0110287dc73048c],#[0xd1c46677f12ab4600a21,0xd310f545ab534135a72e,0xbac484d19ff62fba0904,0x560269dad7ccc1244797,0x2475e8f98247aff897d5,0x34493c336aa342faf998,0x2f442404d1e93f282c24,0x30f888087e78be00848f,0x3c999509cff10084b23a,0xf1f92665437de0345523,0xf4f662650ffea4400cd6,0x8de1e0d8cb6f290213b,0x848a7ff4600067b69341,0x3c7fdc280000d1cfb300,0xfe140000688fd3bab013,0x23804a1b7fc0358468c7,0x8197bf3907e10338bfe,0x32f09ca0fbfa80c9dcbf,0x9a43ff0d2003367bfea0,0xf0d000d39fc7e91e1890,0x684ffe8c000cd458fe,0xbf0f12202678c7fe1220,0xf7f96064e87fc580019f,0x7ef12067f7da4c682243,0xdf88042fbb7e2010a50b,0xa40218d070d2beed0fee,0x931febcd41001a59ecc1,0xf54404721b9f5ba04721,0x67a7e22021abfda0192d,0x2af32010de67e6402149,0xc4685effac3b30033d3e,0x542d98b0c21a96de4b],#[0x889a25ed57a950bafb1,0xca0f3acf6c1963e3cadc,0xb04086a630798121b18b,0xd1ee8b33410b6eac1,0x9038fe60023e7feb0e8c,0x6667bba3121479e34800,0x196bfe03632e7ff64d64,0x58250abade091823fe05,0xe3c0123a2217f284f66c,0x120006ab7f45b040865c,0x2a2f64fc1284cd3faf25,0xbc060a43fb10bf9420dd,0xa8013423c364090a0f4a,0xc3d69c312003547c7943,0x824000d4bf38e9001223,0x8c6fc9d03850d1e1eb4c,0x8163322217f2845d6f04,0x1ad21d35d34231a132f0,0x7f7a223348639ebc400,0x10687f7173588643270a,0x525743ebc332abfa35c0,0x922ef009e4f3ae71c281,0x686aef6c6942f1be7c29,0xd20fe2d92d0b2fea9081,0xb012059dbf05cc40902,0x686c6da5fe9c48cd25ff,0xcff8fc024667462c5d10,0x1134b74edcfb6102466a,0x279aca081a9a3f1d7263,0x6b1f3902a4ae0acd8d49,0x7af9a8c92461ca2ad480,0x40a81889a75fb6433a16],#[0xfbf2b2d148f9c92297fd,0x860504d00fe0b0c21435,0x477ff06d9b8058d39f18,0xeab1910cafd255584244,0xcb8a79f57cc00990faf8,0x613148f7cf368557e7e0,0x42f967321f832e2732ce,0x28485ebc4528c6c9d5c8,0x702219f17dc849d7af11,0xdf68a47021c5ffd0e544,0xed45c08747f001208534,0x7a4199977d12442bbf24,0x8d880529bf360084600c,0x273410a8fe002410bc6a,0xff1128487d703810a29b,0x6a05a0a3aff6e1800d1e,0xf8a19d88e04457c7864f,0x7619b5f1e33da9c0d24f,0x9bfebd1acc0d0cf146b0,0xe043e311bd592c630224,0xd87f226302211d1d3d22,0x9130345387a26302185d,0x8c9f442789e883ef16eb,0xbeb85a906766daba2100,0x40c06d1fcd79205012a0,0x52044e069c0e7c643a84,0x9cc13c9c3bc99acadf2f,0x213424d3e2fc288e043d,0xb0a3fd6444d0903fd66,0x1a978fef696090cfc4a6,0xfe113033e77ef1c538a8,0xbbf68c980be058650dbf],#[0xfaef258240ff5de4b048,0x6906655c984555ac5107,0xc98450fa2903598beb92,0xa161faa5c8455ce04555,0xd0c85c5b25a105a0df25,0x27034c393d9c08516867,0xa7fc3c2440686fd76801,0xe6b09e8b963bbe09e4c1,0xacb35a121c9ece042d67,0x8800d61b61f9f9080d1,0xfdae1285012bbe997154,0x268affea41408800d4bf,0x6bf6c86742c7fe152e44,0xc622679759ad08313c22,0x93270348c4f422d7ffd0,0xfeb0a960310035d7c70a,0xb696400694ed5e59ccd9,0x2fc7f9f8004c0d251b7f,0x2003467f4ed28044006a,0x59aef618c0878ffb5b4b,0xc5b6ce10bffb4311099e,0xb15da692d8822f3cd0da,0xa8aed34ae55b179e6868,0xd55809a29ea2db670aa7,0xfd62867d7c5231216318,0x199109cfa93143387e92,0x916454c50d32d5931661,0x4d58fe890c23321e3fff,0xf1b1aa24070e1c234840,0x151aa63efef2e89139f,0xe01181246a2cbf5e554a,0x8fff8e1120491a5bfb17],#[0x20439bf034109bd2f445,0x5fff2604819d1fcbaaa0,0x718b488111ee4f03410b,0x237ff318c6f00129d27e,0x287fb0350332d7c69001,0xcf3dfcc0047a7e2c0d04,0x1d63d7c00476fe558240,0xd219f4321b9e9e260432,0xc09019d1cdf82220218d,0x345ff77ad40a5a1ffd,0x467e2b0240676ff0c153,0xd4022202217fdefd8502,0x532cfe73ca0a21265efc,0x34436fc00a4021d39786,0x43a74fc26654f8ded040,0x4c24fc5884851ff28080,0x214c00d41e1f08313003,0xce0fcd05950b54e3d8,0xfab63280804457fafb41,0xb76625a165f370044293,0xa7e2e088088b7c585425,0x8c0044f3e5e0c4685063,0x34a5bf0ca65c7c5e0812,0x98ff0999713fcb268120,0x3537f8f848a401500d6,0x8840862fe9ffd825012,0x2181f9018621021e1f7,0x85efd0e440cc8e9ea91,0x2bf3c3848819d1ff0884,0xe970c110a9df0384881a,0xd2fbc360529cb84028cc,0xa1f2471167af8c700024],#[0x44d7fc9125600006,0x6f93dbe801533fbf00d0,0xfad000481107799f400a,0xe02ccb3f9dcc56824422,0x4c8cd0a3f444840874f5,0xd7dfcc5825034274fb,0x48001a6bff974194840,0x88b7cafd8c02aefffe14,0x901cbf4fc98981a16bde,0x1d39787432cfe738f520,0xf86ea0025c36fc1c2102,0xd9fcbfa9248001a67cf5,0x1042a9e92388e7e1fc44,0xff1f8ae26028357b6f90,0x9e86dfe3f15c4d0206a6,0x35b7f2fea40400506a1a,0x4bd11dbf87c350040810,0x8981a57fbe348009096b,0x290209103517f4ffec21,0x2302247e0d2091dbf87e,0x2290711035cbd3c1208c,0x19d34b7cb500cedfe3e1,0xa0a5c9480442696f96a0,0xeb080674945be4c0cecf,0xb080684e6bac2019d39a,0xdf9a8044404417fa493e,0x4021e11797252010e0f,0x4363d3c2f0086845c9aa,0x219a85fd81955e9eb640,0x3a5a85fd819a5924c310,0xa147d8882153b5658103,0xf0a3ec4410a9d3c4c819],#[0x263f1320664d7586440c,0xf7fe194442681c6f2123,0x57244903c70f8d62a496,0x4848d6186bd251338fe0,0x415187311af35f425c3a,0x40cf5f51c23a48d09d34,0x849f518c0d048af90942,0x292abfdc46517f8d12,0xfc8011aa5ff840cb4715,0x3046a4f7c84f11010c3d,0xee2c88801aa517b41f51,0x600696ffc622650ffe1f,0x3861f8d6012bbfc374b2,0xa149e9c0482143eadcc8,0x34e3172788d0b4d84f11,0x2692b553466beb7d7315,0x889a43f7f8891113457d,0xa55c3e440cd1f86b9788,0x4419693fd8196a5ce48c,0x128a9f9412801a3c4f,0x4bf48581033ae7effb58,0x8d2b9e3fdf7560f0413,0xdefda800259530fde9ac,0x208eb9fffb580012573e,0x647116ec9f7a0a27583d,0x1204458e2308d81c461e,0x66b42518d451ad440e34,0xd04688b7bf780c11a359,0x682e7ce9400cf1f855ca,0x61bc20010e1952df7c20,0x1a63f0873c22200350bf,0x113bfc442a7a5073a488],#[0x495248d15ffbc311099d,0xf5c124d3b7fd00a2be93,0x1227857f001224f9e1,0x4088d83dd7001267857f,0xadf74fd04627f2621cf0,0xbfa310328f166be38404,0xd7d4c00941e5c580019e,0xa26267d59fc80a85591c,0xeac00d05f2ce646ffe94,0x43db57c9202a18bfa6d6,0xfd2944c4cf2c9ee82005,0xf24878fe3d20544c4d35,0xb7e5222dc40875729118,0x6ada51021cbe3c172066,0x60001acf89ede60152b1,0x4389139206a4ff190e6d,0x7e0810f1e959054676fe,0x67411e2d33a08f6fca41,0xba0940cf7d4e77c1445a,0xbd2f44503fb18053dffc,0xbc8242dabd119772e88d,0x19e7f9c63c00485fd6ba,0x57f9853092038febc21b,0x7b658ec819d63bc5011e,0x84a2699fbdea700245,0x1338f8d700709233fe75,0x2ab813d04486ed670fb0,0x71e1cf32d19ddf10ec24,0x485cc3e19c324901356,0x2861330f58a48637113e,0x185fd46801432bb76980,0x8b6f8036335bf48e7812],#[0xbaed3013473c756f0121,0xd7d60091e2bf8051963e,0x121a5007e3207e12217,0x41f8c81c582440be0cbb,0xe758648cc5aeb1302672,0x49b63e8ca5aeb1302670,0xb85fe23217067f248cf,0x672caf6e2334bf351b09,0x2e16db7119b3c073fd04,0xc7c9bce920269caf6e23,0x21b92de484c2fbe232f7,0x10fe08e7a2a189fcc124,0xa600a18dfc09cdd32051,0x9e484669ed30050ccd3d,0x2447be2e05732921dddb,0xae078014473f603a6081,0x921a9bf98b0133ebf03,0x8bd11be1e409a08cc3e6,0x2a2ea5e90e2fe83c00a1,0x2bbe90d2b2a2f3cd0c0b,0xc45373e1b09b27468b02,0x9b27468c45e43d2195c,0xf99dad52435aea034e17,0xb9f0c4fc533880f243a3,0x486ac1749d519d165429,0xa1ec379e8cdafb05c4a,0x4d226750f4616513ada7,0x8b00134d7f5e5f4c094,0x88d9bfc22c004d2daf2f,0x79c6c1467af2fae60026,0xc7cb04668fd6e013312,0xd32802699e063d7848f5],#[0x69849c3c1c224387e612,0x8779e8cd5e38247d6d84,0x2427fa661ce9202696f0,0xf9f3aec412489f3bf341,0x58a90c266193d044879,0xd0d09bcc5f4890f8f48,0x19d7fd858099d5f4805c,0xc5004d0c93d03c501191,0x246cfcc5f1e09243fc2a,0x4d3d4d6e485d3d6bea61,0x7aca204cebfe393d4212,0x58310cae66498a90c5fa,0x944d246752f36155e664,0x77aa978a33e7f75f52f0,0xe3c247d591a1af8e1255,0x3568ce1d3489a336de35,0xf146866e1355a33e0749,0x33493e5c30485ceb8552,0x57c6105a50541387e16,0xf790159436f8426333ed,0x4cc12409ffcf21b39253,0x7ffb32437440e26b5fdd,0x1a4a0bffb18d598b1263,0x14b440e26a5ff53c2fa4,0x1a4b5fdd4cc12477ffb7,0xf24cc80432ffa3e063a4,0xa18404463f24cc804363,0xb1fa56588506897fa45b,0xfff11c020087b6994810,0xc1292981ab31c4020cd2,0xc7943981a8518117def8,0x7c8a043073870d3033e3],#[0x10d5db4cd0e10684418,0xd90b7ceb00d22ff8af32,0xa019f3aed2b43b403486,0xc0fb0e97f08672dbdafd,0x223b0e99009724e5806,0x7b134901b211410971e,0x6c6fc7d7353375bdba3,0xe002208be5fa62287660,0x98bafe14a066966e2942,0x6fd66af4043d171ffa31,0x201121af5daa54801ab5,0x3e850606a57e09a8b59d,0x404aa3fdf5086809547c,0xf9e4901a280c34e63c04,0x935c6b02d114901c029e,0x54d7e7fce4dac969ffa8,0xfc29a6a80219148801bd,0x92d1039f3dae7ed00951,0xe1a56d9ad0f2fef5a571,0xc2120137170c88002211,0x4dc47a103601b24fb63f,0x34fbfb68d4e32a1fadf,0x6b9cc00d49ffcb1143f0,0x86a2eaabfda019ebd60,0x5573d6c04a24d753d25e,0x13457ea8a1d2001a67cd,0x32f29c1a542e79fb5a83,0x60196bfbb403297f6b40,0x1447b1792fe11a1d3f85,0xd7d572667275f8cd98c6,0x82834f3832fd8204337c,0xebc1f06003527ca9c927],#[0xda40257708da1c0ce1f7,0x6baff0f99899b7f5f1d2,0xe1800d25fb40383e0c00,0xe5f70fb0e103417ed2e0,0xbf4959a9a3b8c3cf828c,0x25094ff54889d2044452,0x1281e08f860810fc478,0x10e1800d33e7b039e23,0x2d198befd2fc20672fda,0xa195b79df86c3675f73,0x4323e92289486b3bf8ab,0xf9b80ca41a1d1faa8901,0x6104c8a1e7540223929d,0xccdf8323595df474db00,0xe3fcb80c8343272f110c,0x9e364f1c8f177a01de52,0x5976154dfc8e98723765,0x41a44f1c9f0e474c1298,0x1b451bd2ef29485ed568,0xb6659c6f8e8100e4b55a,0xc55efab218c8d0e5965e,0x307fdf828347b3cfc025,0xc687dfa1c47efa0449,0x9f0f7f4004492f5f4335,0xf34d2228343c7aa94919,0x48e199d3b6da3070cd18,0x687a03ef057286886c34,0x12f2608c7267b98b0468,0xd0f398e0f98231c973de,0xd9d5f3a1a149eed01ef4,0xe19fd50cce9e5a4d5b99,0x4e492a7f9f970a724951],#[0xba7d508053221e7d728d,0xb960e14c918f2b948e14,0xb6ff8184a519111b8de8,0x23bffcf97232a9a4484d,0xe43469202d73363d28e9,0xa507ea2d02da1a0bf61,0x3c5deb15114b3f68cb07,0xbd0467d1cdf936018544,0x14098aebfa6dd15c1689,0x892ebd3da8821a1a6e5f,0x8abc05125cfd6a7f2a03,0xc79ccdb1ea38e8922717,0x90167107bf2001494c41,0xd51345c0f964c538d4f4,0xfeecd010a928bffd348a,0x50be9b4d094b3845ec28,0xc68540d2dddaeb0e4203,0x56ff6c2c82021dbc7a76,0xa14cc0d53cfa2fed8c09,0x40ffe95c66068246fff6,0x8406d0b7e0dca95ce06a,0x2c8406bafd17a06c5a2c,0xe57839080dedf97b701a,0x53c7f88540d1df65858c,0xf768a08086e61a2e0429,0x34cc0d39cb0157f0347b,0x4371fe91b3033c37dff7,0x5a0c2036c7edca411f03,0x980d06101aebf55e692c,0xfc2c660abdf035b7f5c6,0x572101a675ebc44a120b,0x21f7fcc005120d5441fd],#[0x6606a2ff8378f12781a5,0xbbb8248862e69e3f40a,0xa021a9e98ad0b2080899,0xbe632f05420361a6fb45,0x80d9883d6e050d0f1e1,0x6f094044f07d27da52b9,0x7dbc1c224006d47f804f,0xdd13cfa2f8cf425b76b7,0x36c7f333f10802c6606,0xd69fdbfccfc7051633,0xa14cc0d7df0953d7a138,0xbcc7a571981a7b2f3df6,0x8fe940132934f48f819c,0xa7b75e1400346e3f5c59,0xe4044625e8ed85904044,0xfd7090e10262314f964d,0xa043a38790080865cfe7,0xfd96b25066cb51d20d0,0x80f3cbeaa906682f8075,0x510400e74049f1c16808,0x3537f4a070d40448324,0xe67420069ef214d63490,0x67b7fb6009010cdd3f8,0x96dfc2241953c7ec504,0x29bd541a271a881f6357,0x3810caff7580e043641,0xa6856cf8d8bbb34bfd8d,0x7f3c3f2d518c0994d155,0x370c7df033a63aad599b,0x2be069b2bc506e740445,0xcf8d83c2034f7971f6c3,0x3178fb61415b303527f8],#[0x2fae55f03433d1502544,0x43db44a059a5c1115fb,0x3e04731810c6f96a44c6,0xaaeffbe5a016e50b0361,0x46045076fe1db9002606,0x6de2181128e1a7023e08,0x1c1c5d3498c08777f6d8,0xe4a84c087442e8b57702,0x4c10f0e8ea84c0861707,0xa745d34b81128e1745d2,0x3cbd8198b49fec0ca6ed,0x569a223ed85027667ef4,0x2840017066997ecd1108,0x49377682fae49a419b3f,0x2982feac2da03467c79a,0xf8372a47c0d16767c92e,0x689fc4a579da05009cd,0x361c3d3603397e17d820,0xdaae4c230fed66213425,0x9e360681339f654a4886,0x4027671f0ead80ceb3c0,0xd0ce49237f38fa5a5146,0x2c350a05cf0420382ffa,0xfc2c36a5cc2101b23f7c,0xcc1fffa86c22050035c7,0x658fe7cdccb1f0f4d80,0x11f3960f81e0688fe76c,0xa465a4a8406b1feab426,0x5581e068b62e14342b77,0x8005240ff55a1308edc6,0x43f95b28af7800d43efc,0x97792c12971fdf014012],#[0x82cc0d63e9774a11d63e,0x70d010cc0e1d6fcf91c2,0x43543303767827d616a0,0x48d360e06ccf6fac2deb,0x708fbc01000d51ff0b0d,0x49c97fe3d148040035e,0x97a402001a2781ffc050,0x258256fdff80040482ff,0x3a36b084330360d7d2ef,0x25bf3a070961981a813f,0xf5de4b0485cfebddf401,0x19f3fa212007084cb60f,0x817a2864335bceb8aa0d,0xfa290359bbf642a06616,0xa3f8c6476fa89e106670,0x460512e8bf0040c06998,0xaa3025efd4ac42703038,0x659ff7e022012e5203f1,0x4642a0684f1fa3215034,0xd31f4c393a9c0d29e3f,0x5411080db1f4c393a9c,0x283f225814677ffe96b,0x8804a1ff811008e7e44b,0x1a1add3900d0ab8fdf80,0x8c09db55c9846b709300,0xbf1b3c8e3ff20ee06070,0xb9342357fe75d2a0679a,0xe3570956a3a7525010ea,0x684ea5abcb301a142407,0xefffd2d60a92cd48e1c9,0xfb5d0942a4a6efc6665c,0xa730e06b4fb4a47c0ce3],#[0xd32d388800d31ff0b0d8,0x400d93fcf6b852a02577,0x7cc8024d7f5f1b528941,0x33a7f6a6b2899c79ec,0x6b101d2c6ce04eeda1e5,0x6dcc88ff7bf784b43efc,0x7ce491a3c33f91accdff,0xd212121e7c3cd5920d38,0x5884ac1811e13467d788,0x6b432f1d7c2e07900963,0xe2ad0b9974dcca0f3f74,0xe31012a7c0baf2490af1,0xa8f3e78c080943f7337b,0x1200361714e94aa0069d,0x9b1f2314905ff11b14e1,0xcc2b61f4da0c186606b9,0xd75ef123d26634e3e590,0x44c0d21ff15096004800,0x3c553a1082696ebf1b96,0x4d21fe9f0342011001b3,0x1c072a0034e74d212954,0x1050c33e3e866090df3e,0xe72442671e2432f35619,0xc7240688e9c773a033ab,0x70a337749711a213e249,0x4043773e3a649d8e480d,0xf421bda5bf68767f68f2,0x78c19e04444649d8f00c,0xc6a8817d14785821a843,0xb155ed911a22146229f7,0xc9c90ecfc44bb204313e,0x269fe531a128685086f1],#[0x3313f930491223e8e609,0xea4c50d09cbc6588c04d,0x97f43b0608104436a4a3,0x8a19e7d79f5d0414496d,0xff80ff50828933bfb7b9,0xa88757eee0165510fbe,0x21dbc1a1d43333f82803,0x2625ebc48d16d1829455,0x50e3ff181b11441260,0x87ddd45902d37dfe208a,0x4a4d7b3ca882021f75f,0x887e87dffea606723e63,0x2dbf4420085943d72214,0xb4d9e4884010fbde342,0xd8fe5c684069a60f4425,0x220269649c7a4184874f,0xd35600ca606a0dbf0e0d,0x6b6ff33f58028a86a2f,0x8018111df2c2c4605e45,0xafe87338b18266bfdc81,0xb0db819db3f4a14219f4,0x267cff960d220268ac7c,0x90fbfe1950cd9f960d60,0x8a6b090c5d7f0224a066,0x8c04ceafdd3004437bf9,0x9bf8e670440c98dff4c2,0xfa7c15433ef3c302d1d7,0x3633179fd80a819a03a,0x7810ccb7cc609485b7f8,0xcd131fc98247cffe0,0x9531bf9c100a33b7f2b1,0x31fc98247df98d1e0741],#[0x12408b17d49f48610111,0x7f2b5032930d79b14226,0xc8d7c44a7eab4252043b,0x6a85907678a1f0044045,0xe12213c3a7f0be1c0040,0x38c288495fe71938bc40,0x694ede9cbc02a9a27e87,0xa74fa026684f991da080,0x1a1dc9f70034021dbf4,0xd1ee0a2aa85efe0980c9,0x430901a8bfbfb60b84c,0xa1cf3eee16a0569fdbdc,0x73bf985015cb87350252,0x54090da7fb5b6813341e,0xce9d39c20aa689f8ff02,0x901b07cc21153e37b414,0x1dd11011190a65b41dfa,0x854034420e4cd082e66e,0xffe3e0a8cca04c4d2df0,0x233010c9efd8c240688b,0x807821929fa24196dc5f,0x212eaa25dd8901b2d254,0x480de3fd7f3c3196012f,0x480d8df6c553fd85d5cc,0x8c24071efd34f87d508c,0x501b23bf8642c36b3b2,0x780cc043f7f0c8586c7e,0x8bffc76a4cb00976e09,0x649209ffcdccb6f3301,0x6b364c2ec087dff2ff94,0x88026b6df5e8404800d5,0xbeb12304a9ea3f6cff44],#[0x342735f68201a178ce,0x94b37c2019dbffd71803,0xfa212cbfc2c265abe0d2,0xa06299c0c0e127dcb2b7,0xe98180c0db9f19eb836,0xb0dacf40d06ccf6fa0ed,0x1b17bde10300951fd90,0x4012f21feed5fa0018,0xffaf100600681e7d63fb,0xf810c868e79da1000d11,0x12035ebf020150a2d0a,0xdbee880ce1f97c7a7890,0x19a63e9826b08670c7,0xffe38032c02547d36c17,0x4024025a483f000aa685,0x64927f404cce3ffeff7c,0x3d29f903595bedf206e6,0xa06471e343638d024081,0x509fffe88596012b7e1,0xd59287ff1a1b2b0384ca,0xb9fc7d8090096b0bf186,0xa663711bc94f8023448e,0x9f1e236c054367fc8bca,0x529e92aa8fdfe45c4019,0xf7d7964e3f98c78c36aa,0xa2a23434587000954b5,0xdf414ce098f785533cbe,0xfff2d60b030901b63a63,0x2a1a5f10ac52a1bbf9d,0x2ee4f700b2021f9f11b6,0x2cd0bdf8756f06ae80d,0xf2baad85c5204443c5c],#[0xdf379021bda745ba6c9,0xee04323f624b88408726,0x151ff7d0884087d5d16a,0x696e8bb7242c36fe1112,0xef81c248cf0f3bedc408,0x31478cd00c9e055a6864,0xbd6462fcf480259b3b78,0x10467cf2fd2a38a678ba,0xd31e04891801b0beb0d2,0x1481aa7f97c63082457c,0x51d24e00243c7a7cc84c,0x72fb101a13b671320679,0x1bfefe528250034871f9,0x133e7fe12262180001b,0x67dc95f0002487ff11c8,0xe41c878881a93e353054,0x10a2e7a458244870ff4,0xff84658104003563d184,0x908001b6dfe2948215b,0x5438c6612357ff086b81,0xd3a721e24673f977b180,0x8f784506c0fd750db819,0x9f7272c400931fd90b0d,0x2c2569fc0d2908cbe481,0x801327ccf0e2880099dc,0xed2e20026a5f1fdce088,0x68dce2c40091be7ff30,0xdc5331cc444fb5ad800,0x343745811432814ceed7,0x2299e88e368ac94a3ff6,0x40ffe2518240d4776bf4,0x404a006ab7b34681219b],#[0x6b3ba781b8a53ff154,0xdd3ce84539edf15c4600,0xf40f1848aa56f1209a31,0xa1f785134518e02e123c,0x77bc6d209239f8601c00,0xec8a21240ffd8e2c0292,0x82470ff6c7828c000d43,0xfe1af40809001ae617f9,0x15910350f7f2080a492f,0x1b06c77c454ffc3b412,0xc842484fff8845009080,0x9bf88a03d5798a19c79c,0x6a18d741236fdc8514fa,0x8711010d96944b0ef540,0x612d0f8d3dd9008697c9,0x7cd6bc9bc901a59f414b,0x5da480db11d3df6c033e,0xba03fd01a23fc6174178,0x2003433e82972a021e30,0x8785044d5502229b19f8,0xe0800d287d5cadfe884a,0x7c2e82e3e20d05fe6c67,0x5dfea81205f411355408,0xaa043c3e9e9654043cf7,0x8c2e80e1e506837d3c4a,0xd79c4c819d211e713206,0x26d452f4cf23e4b514a4,0x3be1960859234e1e3386,0x124176d8382868d525b2,0x94369cf5a2a4ade31399,0xc11b484d2bf37585f104,0xd87400aaf550b4c8fc0b],#[0x34fc39080cf4d39aaa90,0x6bc5433907f5d3e9819c,0x80d33c8c7db181252bfd,0x6372f56a04ea96d6e324,0x13933b7abc52669437e6,0x812256ba5f9e47b03918,0x5dbcd3034bbf1eda80ac,0x4a0d06cbd135221ba12f,0xd39820c7e0678ff1a3c6,0x6e5af502756bb6eb6480,0x2271a754b26694278ee8,0x8c0e23f6bcc105a1f035,0xceaf83ecd3444879f51,0xe4b5af150d09fd769f4c,0x18112b2f03e3dceb0945,0x3184f034e3f8b5451a0,0x800d4c1eb184a10d1de7,0xd02b4311226b5f0b4213,0x48864f6f5710267e6ea3,0x69c0b4640344c99eed9e,0x80066bee4d5fa8519f90,0x52fb93608d09e293cb48,0xa1dbc8c4722f44133637,0xf4a8192035ebf04f9604,0xa5343668880898fedcb1,0xaba86874fd2c106e67c7,0x95f3eab1a9c92553eae1,0xc6861c38338d97f52b24,0xb690c1333f86fc442676,0xa65f3f084a1ff1cfef4,0x567b7d178d4ad3210d9b,0x4c00d51feb684347d083],#[0x8e1f8d64925f66ff0c5e,0x2bfcf83317ac26006c18,0x1ec4989a60c77fcc892,0x2343d3ec842b50a1f3f1,0xccadfd5b019fd6fb09ee,0xfc506675afe6e7f02049,0x4c68db6fa71889a735f9,0xa4a9336ef11e83a58d9e,0x482234467cb13ffc655c,0x9194ba87c8819a14fd2d,0x840439683cbe1963e87c,0x284be504a006b872031d,0xc0009a9e74899033c7b7,0xfdac000963fcf27f7463,0x191f946543c00695cfde,0x9251f8ead802623c0401,0x74d3d9aad19568e75e20,0x36d280006a6f46f9d181,0x43fd4811fd88012e3ff3,0xf6212397c25c18e8404d,0xc12032cb9bca009a56af,0xa23d984fbc4a07ee2175,0x4e67e4f8d828ccab07a,0x78fd2c1860026a4ff210,0xb9a86c540a0a7a48e238,0xcb3e718e01242fafc1e9,0x7edefa21446882fd4412,0xad19a57ceefa86c564c8,0x6b97223c5a408704f3a,0xa1002557db96b0d074a0,0x7e9a1a4da40885cfdefd,0x71fac549117bdf1c247a],#[0x2440d707be78e209260d,0xf7be3848e5fdd7ca27a5,0x2dff84290b5911001b22,0x4c98f44861aeab1ac549,0xbffc10a43d4420006db6,0x4417e53f265b62c881b1,0x7f28ca0cfcf81a4c1001,0x16ab0134d3e2469089df,0x4b4f7b6ddc0803437bd2,0xb37cc00d0df97b6c5a28,0xb81a133b6c5e2ea69eed,0xec1626b0134974f2f85b,0x4b57e8bf30e8702233f,0x2c5ac4b4ef71f9edc28c,0xa88d92af41006c6feb8d,0xa9a778fcedbf700941fc,0x5d447d800d289c696297,0xa59bc466d83dd70490df,0x9c8a438bb4dcb12043f7,0x6ec010b75f2e13620cdc,0xf66f119e9b3cb5285b75,0x1a1731a5b0a0935f6987,0x340e1a808b42000912e3,0x4d25e9e389da001a63e,0x8fd40906c92fbf23d88c,0x3989acbfbf2394602699,0x5ec2850554bb88cc698d,0xed2000d23ffbe3bc74c4,0x1104fcb22294862f4f1c,0x6a4e806b866dbd808a0,0x9161fbf08a010e5f5f6e,0x130035a797bfedd149a6],#[0xd3da93a01a8bcbfe02a5,0x7ebfc2d6b4003135b75e,0xa51313597f687a731338,0xeb6c43406269cfd36ae4,0x60134bf4a6dd149a690,0x3e26d8051debe557f794,0x5c2013a9ad79ff25621b,0xb51e7cd8e0404b2fe150,0x3700a1b79e7f34156497,0x2a801a97fde396203cf4,0xaa153b5796733171ae33,0x14154bb461eaa3dbd808,0xffb8081294230a2aec9b,0x35aa4088af4f60f53353,0x821d58b56d292185e522,0x10f2731398577e37989a,0x1aa2a239e36a059bc811,0x4ff0a0ad45341bdd37a8,0xd08495cf1062fdb44088,0x6f4c299f60034efd625d,0x1e3dbfca95ad6d41006c,0x8d1e27ef300a87165f41,0x25d7c2949d330e2afa0,0x2f13ff300a56f1bbba10,0xc40098bf7eb16f62004b,0x6b7b1091d7febea54e2,0x9ff90a301286a6388012,0xad22b88eb5a465c485c9,0x40036770f6c43e00685,0xba032a0870ff5d632e81,0xfe91a6a90510389b75d7,0xacbe091c3f03fb18057d],#[0xc626b1ffbdd50080943,0x11e16419547b87f9a094,0x8738660152fff5f98684,0x335afed84c96b4bd11ef,0x4dcbe164154c6f70fa75,0xe919a5068de4be8230ff,0xfe56fd34752801ac3f0f,0x935fff81509380006a8,0xb638f642471f1be7db18,0x88e2004b93eb515c5012,0x2b4678b5a100ad127d72,0x2850e14f02d39e2d0e40,0x1b19fad5fcee65a3474,0xcfee3a5788986884e37c,0x3baaeeb82488afc84028,0xb9c4d19badc56c425c2d,0x7ee623a9f3f3c8739273,0x88cd582e8b0d496952bf,0x9b08adbcefc361b0b6db,0x8063dbce1c480a26d4db,0x33730490f5d72434f816,0xf496f2b779868d3ce4d,0xdb4880569e7eebb80805,0x88afaf38d0a015a6beba,0x59769490d6b2a2ea1c14,0x80bb2430df6c24134a2c,0x9b1df89d698d921e5fba,0xf61214b24e36f2d22001,0xf8c34f29440226c174a,0xf6b0092e7cd6408a9263,0xffe7871601266c7c7cf9,0x6124926a9e92388e3f87],#[0x3e6b2380493bc3c7cf9e,0x853d3090e083f43b090d,0x8026ba7424de01287a7a,0xf2bf13397fc3f30d3532,0xdb573e87090809b9083f,0x1352a6e16f0c24397fc2,0xde4809a02dc3f36f6a10,0x87e616f0242026c8fe5a,0x2dc3f30c7921013585b,0x95f009a43b1f16fc711a,0x19d3d02f004b3c7c7f31,0xf2f480e6a694e14de95,0xfe1fe34376a01d02d433,0x8aa1c7f8fcca014923f,0xd0dda8070655017cbc50,0xd2f4471f645109236c78,0xa99d3405b4c08094525a,0xe4d8ce16e1f9f6916009,0x88a6c6cd3909519db3a9,0xfa57b090bdf5c488e16c,0xb469016428a0a0352e2c,0x32a8c18c7c72c54955e3,0x1b14d9bdc5483d267836,0x4e583004d51c7c809e50,0x9a99c029bc0250f1c21,0x4b30a4860b70feca7c60,0xcbcaccaff7ca5490c8fc,0x27a1010043166c35365b,0xe2fa169a89ab34e199f3,0xe56737833532dc353e99,0xcc1cfaccf34ce5d5f5c1,0x70b787338d9a933eb9b6],#[0xac3360d1afd18a1d4808,0x3506847db906010c01f6,0x5e6fa991a04407847dd7,0xca1a04383a7a0da0432b,0xdce6a13c4890440ba68,0x876efd238328be7ee681,0xa85601126fe0fa63380,0x9edf44fa81a087b7d6b5,0x77f792e08668f20f5d01,0xb4901101a7c9beae0cf4,0xf9a28894702255093fe5,0xf0ccece6aa2ab81112c3,0x7358c931aa1f1cde7084,0x2f44250d8e6f3842786c,0x987074f300dc8652bf,0xc1aa1aa1a1593116ed99,0x7becb6437a01104eed64,0x3551a9a181c70a799860,0x1b152cf37f2630952bbe,0xcb585c2a3edcf2133e85,0x3697b2c30a01413a43c2,0x1c09fa18583d73c856e1,0xf4364ba85b49b3828fc,0x1fc301a5e20112e83563,0x599021fbcfc08e1b6705,0x833f76b62d8336bf4628,0x8bf79115a043b709b5b8,0x39c700ce8dda49266943,0x443be35504d410ed87c,0xfabe65186961fe948b10,0x929802fd547adc3019,0x8abf443c670c655e0b]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x1000e05080809040200,0x2000000080c070a10,0x101003b000000030a02,0x1c0e02130300000301,0x6010c0a1b000b070a03,0x2020113160203090101,0x38100101030a0e190c01,0xc0818061f06081407,0x2040d0103053d0001,0x90105010d0f02010705,0x706000110011d00040a,0x2010e01030401040200,0x51200000d05060f00,0x3150304040000000c04,0xb000a261a0003000802,0x103010a03121909010b,0xd00030a000f0005,0x3010102010000000101,0xf000e00050901031a34,0x5020801121b20060510,0x120b0032000800050d,0x2731e010106050a00,0x130000030005050203,0x260502010001030007,0x119020006260d1410,0x130f0b061b00050802,0x40f04221d0b000c0003,0x1050f111d1e01010211,0x2240000040100070010,0x1b00110e210514040800,0x8130000000413004809,0xf0106013a0326080802],#[0x410020a074302020b05,0x19040700000139080000,0xe120e06010104060000,0x10e13001722000b082d,0x200030c0e110d090b05,0x3360a0604015f030302,0x150126000b3602050605,0x40f1b0302050401051b,0x80008000600012e1629,0xe030a0b070b02051d05,0x62a130b092513052229,0x70106020814091120,0xf020000002106170406,0x3040008020101080102,0x220a100909060b000102,0x53e18020c000409050d,0x110b0001144200050107,0x2060003141f00020000,0x901044d030000290413,0x8080004010903054303,0x70b00040002030302,0xe010405001a08011600,0x1010839013e020b0701,0x40d3137100149070300,0x50002030402030e2e03,0x20d0400140001020705,0x1000203170005013308,0x5020a150c190700040b,0x30821050347021f021d,0xf07000b042302000a10,0x1f01040002022d020601,0x2005f120d1400031911],#[0x10303160f000b021202,0x1f0006140103008c0201,0x1000002062a011d1c01,0x600090c0500050f0a06,0x3300011806062f07001f,0x2b0b05000c0908050103,0x10207122f150d121201,0xc13050303091f611615,0x4020a06142123040901,0x4a1e4d0b08030f100526,0x2090003000110020b1b,0x10301010604101e1702,0x1040203124201060001,0x52400103041b010016,0x1007080d08030300338b,0xb80004d665019c1f07aa,0xf44000317bc6ba0000c1,0x6316a3a7097e04600004,0x45cb00000000000164a,0x41f71dd000,0xcf2124923b00008b9a0,0x5a026e14ce0f49e70000,0x2a8a70000000011c9239,0xe75d1a771aa82cb0001a,0x48080c123b4038e,0x9d6100000000008fe000,0x64d93d400000006b670,0x1e0b3446a932f1c00000,0x13000062bdc2db1b600c,0xcff1177da4fc28269ec1,0x6c567c4f491d34710000,0x2b0c81c311aa7c000127],#[0x80070eb386000018,0xf836a218800000aa0000,0xc18415663e000017d606,0x30659aaa1c30000e4391,0xfa8f48afe0b5e33f0000,0xebc816082c87a148443,0xcaf215e2209000070c42,0x960050000d397366f3a6,0x58800025580d961e712f,0x64740000000000004329,0x8d8f502d485ea171284f,0x58400046450000208b3f,0xa7d6852d089e5dc00011,0x1238af1f098051300000,0x1529d14180a392,0x1d00284a000000000,0x721e5070000313e8000,0x78000068d98a4721a400,0x66e600000,0x8e7b84d7c00000004678,0x4b28f28000000017e115,0x4a4a1479be087d100019,0xa0000014440d8000607f,0x6422991800d1260e14c3,0xc9fe000000028530ce6d,0x115c0000000,0x11ea400,0xe8b489a605a861f20c60,0x22b824eddd6dbab0000,0xa983ed00000001833000,0xe1a400010e6e03002f08,0x8000000000014490000],#[0x759e09fd283aa,0xc6fc00031c3800000000,0x66a86bf92840000575,0xee52934369e4dd9d8000,0x51a1ce38b47e184083dd,0xb03890001138dc2195ef,0x1340001208100e00011f,0xfcfd5c907a26fc83d20,0xb4031c868000328d0000,0x12862009c882000200,0x344e8515c6f40,0x68000000000000000000,0x32140b8000c9b5c7a409,0x624400004d588f9a,0xf0000916298a01f46882,0x130000630e8b4c95383f,0xc5b800000001131e,0xef4762412be041a,0x78928371f1833e000000,0x18f2ec20021371ee8,0x6150000083cc0000000,0x10e867db28c0177800,0xc437923e9290000d0360,0x4736841e00000000000,0xcd7a74a6bc0001427800,0x57c243168e09909,0x301f0e45ac8a8000287e,0x51d39946c0eff801f334,0x51d78dda2cba6ac00579,0x78489aff552bb39a31b1,0xfa5255038fa4a9090333,0x517e00032b4800000011],#[0xee5ba877a0002c212770,0xbe0a3c428f890403e136,0xc449228791c004e00011,0x4a2980240000000064c5,0xf7e0258000861782d20d,0x51980000000278000261,0x6a31ab1f6993a31546fe,0x3d05921e60000484393,0xca6400000002358e,0xc960a193b5fe2ca,0xc085e3d000,0x45fa0003361f20a00000,0x60ad462a995692488c4,0x2be02527dc0000596400,0x81c80000362431210b49,0xb25ef023aa30424ad559,0x13d900000378089f08,0x2acb17a4000780ec6f20,0x11e86b5214622e921e5,0xe900ca0000000008dc00,0x80090994000661300011,0x5d84deb50e36715b6449,0x603905ad559d2b,0xa1ece123877000000000,0xc8000000000000000000,0x754000423400000000c1,0x19557a938000878a0,0xba1f4a8fee2640002313,0x134be650071b891893,0xc6dd27403df8a240,0x8f1860001a0ff3b58887,0x33afa1022500000239],#[0x1a096c82a50d506a0,0x608c900000369070a4e6,0xcc00000000c2d800001b,0x47700000000221800001,0xb7ff00010aba221d28c,0x32900335c0c6000337,0xd1491b80000065f00000,0x280000001cc6b33a8000,0x703069e10400008aa131,0xaffa00b23e8465e00009,0x30000a055556ba3b8011,0x228d0e39059290,0xa9f600032b180004a120,0x4344e0fc595c0000000,0xb170a52060e3c8514c00,0x77e000000017dc42341,0xd002f8c23df1907c8000,0x3069282c1095850801,0xc078000000002a371f40,0xa0000e2ee00001ae0000,0x1be280005208000015,0x18a6c389000042b60,0x310007c0f7,0x874000646600f5212400,0xcc160000000480400010,0x3d74883e345cc0000000,0xfb4b9b60d78f4c0edb31,0xc56623de410e5eb40ecc,0x624bc0001d87d910f6e6,0x3b9ab5edca67896c2c,0x8e580000000440810060,0x3b1d80000c9ac0000192],#[0x56000024ea6e685f8bb4,0x1837a854a46389538,0x8000708f88f3218a289,0x421b80008311198593,0x95aa8af84ac0000a,0x6e13300019c309100000,0xdb537784c2f08c607621,0x8a2611b9352c4eec87c1,0xf443fcad0cf5b202f1da,0x46fb8151db505c073324,0xc7d322eb155b8c3468f8,0xaa25e06581c340002653,0x9070cde693234f627f99,0xf18582e000065a70c1f9,0xe82dcc5b963b07a90d4,0x4fc38f08a3ceff41eac8,0x810e2225a6220e945350,0x6029004d01bd744be20e,0x43ad80c852ee90,0xdfba33aa77b27048140,0x28000a12c8c180002885,0x453e42287877897e92f,0xce49b4d8ff237d4829e,0x6f103cd3400000006430,0x2d631ec3b26416000317,0x8ee3e1411d005b5b0a5e,0x8c640000000,0x2ecc0e64710000000,0x8168df21ac000000000,0xd89038ff2cfe40002711,0xae46ae70f4c6dc96617,0x19b0413d71c2e],#[0x1ef27ec44a00006214,0x6c000002ff0000887000,0x10d3400042e750e74,0x44c6c275149000005af,0x31f96458105800,0xec83d2ad0fb64bda4340,0xb0000ec48000338580d1,0x19d2832,0x91eb0bd8000221ecb5c0,0x8bb01b2818160ee,0xa900003623881a0c14b7,0xcc78000000040f6ed2e8,0x72280ea00000006553,0x87000067d2000045d000,0xcf5a1c9baa1c12300001,0x990086e253e,0xae5f1d9c02e95e800,0xc33e0f9e5a340be0,0x3d298c4121e8a375f574,0x549322000000c39ba708,0x4cfac93d0b8182685755,0xd1801418296f03c1e615,0x8202226572088e428bc1,0xc4fc94f692b902d80ad0,0xb456da375c41c1e8c7fa,0x434452aa3498eb830,0x4e8e00023b914f344200,0x810db67ee9f5916a8000,0x92c0000000831a85fa88,0xc7e1a31e42b8085806a5,0x2134ca5253cb39c20d5,0x2af153800000019dcc00],#[0x89d6000000048cd11f32,0x90000d0dc00028db0000,0x2b83c7038b09a6000200,0xe4eb0718000684300008,0x55548d4406e48b,0x3335c01c8f1200012a,0x4a9a0003473a32200000,0xd0000caba014d0e28000,0x18e5a867cb8dc6f893,0x116b9f8b1fa6483c0ba0,0x200002eee04ef4010856,0x669bdb2793e0446036c2,0x10fef390e04c00018,0x46b800014b100000000,0x3c0ca330ce5a000000,0x8c320001426454b00000,0x70c5d0149b18376c05c,0x1f3a2880000000e34400,0xa146501d22c8000c820a,0x5c345cd3820c04720000,0xbcc3ec000046e7130f87,0xa4c0c36800068d700010,0x28000d016000000056f5,0xf5622d25b7000018bb8d,0x890b0cc3699e086c,0x7a51f00000e54047f201,0x6aa2b2a41724fb054528,0x61d39bc1194e1000368c,0xac197831c91612e087c0,0xf74bb8e5b60fb3d1e809,0xc8c8000225996c5c7181,0x489a00019a2b21b04ba],#[0x3c00001836881c000000,0x875846d7415b181ef24a,0x2c2ec03c29201bbd41c9,0x844000411f0b1b17c0b4,0x7221cbd10ae0704d120,0x1a0ab23fe8642b0f27e5,0x2934c223d0ee8d38a6,0x63dd908a8ae462be2f80,0x38cb601b5e3b50000,0x126e04400f7a928000,0x789608737b800000000,0x1e74f000000032292503,0x3197213c8dac882881,0x84938932aee62850db20,0x40595438e22edc5088a5,0xdf438c667c4a89155a36,0x8b651ad20f423d283cf5,0xa79d603461040ad6411,0xc7d34b05c4c2cb09551a,0x87cb9ee815f000045b61,0x20465c9020001a5bc55c,0xa8304e36e94a93a2dcc0,0x26b00b3238e91a200001,0x1e8f30000a08000066e3,0x333b8000e2f28c2b16,0x80b000000000,0x78000839000008c061f5,0x52035d962f000000012e,0x109b84432f520a900018,0x31e8f670b240002418,0x2bd80000000000013d,0xa90d8f88a96336f00000],#[0x46fb0001600eb1de57e,0xbdac3f46840fd80001c1,0x121ac000000000004,0xd88270d0558880003738,0xdf012000000000003b4,0x18086b40000000c0932,0xd81530ad800032048000,0x8182800000000051d9a2,0x187b0000468e07800,0xbc2e00000a2520340272,0x116470c17b821cccf33b,0x43c813dc3e788ef11506,0x780000001950b1b85796,0x805d10800002b,0x4d2084a31a500008ecc0,0x7548dc85c520a34d917e,0xf54368000000051d11b,0x888d52c800028fd20ae0,0x8a7ca0b7c00002f982ea,0x68d2aa3575000143f011,0x45d00235145663102e44,0x907b6c4c71c941e3c564,0xb30000385ab09c1d928f,0x17e92230d023a6e7d99,0x1e76545fc205b4458608,0x7d20d665a208d48dfe8e,0x311083774367d,0x89782cc689ef120ce786,0x5dd97271e34516000333,0x9c11b288000e7f98,0xb800087b393762108000,0x33f3dd80000001077902],#[0x1a11f19c349e00006,0x5389889980003385323b,0x31ba5a1104e35d0c7028,0x203b08800002646e31ee,0x6a84680b103502286585,0xc9a97c723a02e175224,0xc7670fd739d0000cf438,0x2c60a000000012fe8000,0x386e800046a18b77c6,0x41fc0003214058710460,0x8800084d418180000000,0xb0e26f80000000000140,0x1c6480000000f1e15,0xf2850000022e42ce8475,0xb5c000000068fd0d3e46,0x219502f010695,0x183092dac174139c8000,0x14bf81fa000332,0x678000021395bc2fae0,0x2a1b981d40ab30d0c833,0x27e04fb069a51b87f812,0x84a262f538445bdcadc1,0xbd17de8b801953e59265,0x106c43074aae0002ab,0xc01a0002010000010a40,0x2591000162f00000000,0x5a2a419164000082c000,0x7e254d000028b02920c,0x27580000c1993d38000,0xfa80000000296a08e520,0xce9200013d80000cea3c,0x14bcc631a2d8000058a],#[0x60800060fc0e34000000,0xc3f2a2ce83c377c00164,0xee07b000114d50588000,0x6e119cc010c258007a0f,0x404400030d582e4c1771,0x6429e0f10000000000ef,0x1c4b60bceef6da2823,0xc4f0464c000000000000,0xf202d000102a80000000,0xc8e3af434324b79abda5,0x18,0xed25e00000086944a2cd,0x384b278787000000028a,0x4239802800001030000d,0x5000068070a48000420c,0x45c00058ef000019b312,0x911f98c13e0d5dacdf21,0x9d83b27858e86904c460,0xff334a43a86cf90d0324,0x8d748bc12427cc0eb78,0x84b400022958000,0x2c8c73a45d65fd222000,0xc6489b881a4b54f4cf71,0x370c90e8d04200001083,0x2be940f109f6998f00,0x6520c9a211294f190c60,0xf4590ed7dc92b9610757,0xb643a2b89ecabcdb86bc,0x4e029a8c8fbe871b10ad,0x1c3e7e8141cf5c25e57d,0x4003006092e6ff23fb07,0x81b320011e0c635cd722],#[0x620ba0aa289f0c522359,0x38b7e531510000021a,0x9bd3138800000000,0x2847100005a361488000,0x8c800034da4fe400028b,0x11dd075c00024e2891d0,0x85cc0fb815e48f2,0x381a6240000088800,0x180203e747c310880,0xfb18d0000039c0000000,0x3b2288e36fce9c0fbf80,0xcc46d3af90685f9c8555,0x23cdc03a00000000000,0x1000031bd2f9ba22800,0x11cdf1d8d79450aad,0x169020000000204ca8a9,0x211980000001968225,0x11210000000000000,0xa0000000019740000000,0x7700002610000000008a,0x10,0x33bb0a5a00033090000,0x63970000000000,0x4346ada239650620,0xc97fa3e0a7a8000,0x7040000367cefc858c00,0x8b3385101d38000d0ba8,0x502000061fc10d0000,0x227a227b27e4000000,0xac241262584e520,0x7a3c3861a000223474c1,0x80d2b340a744ac000220],#[0xc6ac000340c4281a9db4,0x18000e89f8f3c8500000,0x225441ffceab9569c5,0xc9f91653bac23ead1cc0,0x226f440246400000000,0x4e80007857c96a805000,0xc14708adc1c18a047e51,0x5e39400011ee400022a5,0xbeb882a5bf00000003c5,0x485f055f297018c086b9,0x6886c006195317a425d,0x8b631c000000,0xb10c0003a63800003760,0xec516f20c1a872af875a,0x40379e01b000141418f,0x50b00000000483c85292,0x4000005390703815e660,0x75733460e84e270b8d1a,0x70ac0002063000046a21,0x82ac87280004776,0x14b00000000000,0x8b178e6000070f784760,0x717fb000093db1ed8000,0x5640000000cda89a9039,0x503c0002a57b7f800000,0x957370001800a885658f,0x5708fd6000015,0x8284000000000000,0xe0000080c0000000214f,0x33400072530000000342,0x22ef00010,0x6e4900001632d12f844e],#[0x45c50000961b47,0x8838a1e8000564700000,0x6477cb8e1fdc0000687,0x4d941f227400011b5400,0x9e78000275c00019,0x48000008600023f73444,0x76f4462c00030c,0xc8f68da11ada09ac0aa0,0xba7d5000000022ace112,0x960394083d318200012e,0x31e40000000000083979,0xc39442de080,0x7d000000002f5c000000,0x607000031f9b21f4f291,0x26c10fa942ac231414e,0x247d80006b5ad2c400,0x14fb80000000899c0,0xb0000824a06f80000000,0xed99d7c33ae9e0474d06,0x49f19964287000000004,0x2f15e000018240006545,0x5744090000e6a20cda07,0x1476345a6a200005,0x990000,0x0,0x42701e5c000622e40dc0,0xfa162000104c23428000,0x5400063b781e014fd34,0xa280697817630cccb6e,0x4000069fb46203aa467a,0xcc7977c5410000a1c042,0x818600002c100008da10],#[0x80109839e954800007b1,0xb6c00000000000000238,0xae3000071ac9,0x6538b0000960d24b0000,0x232d078c070b21,0x4d0323011f0d0c800000,0x4281d8fe0e39bc31c4c1,0x1e40cec1dfaffc1afe14,0x8a614304adf44d8c4c5c,0x423085830b488e3,0x9280004461cf379e0800,0x124161b965da00001,0xc4115c4a0a34c0000000,0xfaf9e3e2f90faf121fbd,0xf17c8a5c000353dc080d,0xe043b10ca0001be108b4,0x3488c2a79f86c101a98f,0x464117d800048a70001a,0x6381a894c95cd93904a3,0xe5a3da8000e7498f91c5,0xcae00032f644c0c1e59,0x3c3667052197235ec720,0x1f8000019ef07e864612,0xade6621c00026ab8cc90,0x88fe00000004906,0x222f00000000000000,0x109a00000,0xc00008ed2000325c8000,0xed23f20780000514946,0xe2f14a280a0000051f40,0x1263000000000004588,0x23a28db39401ba000000],#[0x1c52a1118b558,0x46142fce000000044b6,0xf0a8000000,0x89c1d20018022af00000,0x50000cd6096a4080f851,0xb4e20147984bd049ee1d,0xe40400020b9866600018,0x6e7b92762c9b231,0xa2d16e000000000fb142,0x513617322450000702d4,0x6b88917c0006124,0xe4dbbc468d0000000000,0xce7e91c800002ceca680,0xf08c34d3d14ec0002842,0x79b2d4607245dc000339,0xca91969723d416f41921,0x445c8e360e6d21c416b,0x32eec8c24f8806c400,0x536c00000000fe60,0xe000000014cf800074fc,0x380f442991a247ed06,0xe4d4000000055f000000,0x1249a0e84000026be485,0x2938d964a5004a99fcb6,0x6ee0e08d33141812a855,0x907ab0000609c1fff4f4,0xdd794a28954ec51a6534,0x87491e6c4a23b400bd8,0xa817c2399870c932676e,0xff79288629d096204f3f,0x2ed920a5c47c0ce47079,0x4432cded0ee9383a0db],#[0x667829b06a000009e400,0xe35000022210000c7c10,0xd800000002901,0xcc3c9fd000,0x1c27c000000000000,0xdb8b81984ca,0xfcf12e0000404e217c00,0x8c708d2d91c8000e996c,0x1607900018849285c6df,0xf531d841870a02000115,0xab60000000403382520,0x6348c884005e436f0000,0xae6c0f000045e3429c13,0x896e8de0000459b00000,0x68000000180dc0005102,0x21e6508000010e510,0x208806dc00001b200000,0x28000088bc2a90bf8000,0x3800007fb0db4000033,0x10b718c4ca098,0xea63a60ea49e1387476c,0xe4800000000000000130,0x84081,0x980000001c6e302a0000,0x35ec000000032d,0x12718e9668807320,0x12b80958353,0xbc000262f0000e06c00,0x852c00000006106467da,0xbe5a1000000039c1f25a,0x4c7160800005400002bf,0x4b03913d087875688960],#[0x472a24e3c5eaab88000,0x37e3248000072182a000,0x406a,0x25ac00d7569c000632b,0x34030100000000000000,0x67741158000436400001,0x4956e06cac81f06840af,0x9f000014d30d740f4035,0x4103845e0f1e680cc454,0x3f3204c77907705b0000,0x214aa2c0000000022f,0x4a8787e0093c49887480,0xde35e053a11361ba2753,0xe6819ff06c702800010e,0x48260001b24102ccc370,0x8c607ae00000dc7232,0x7ff09080000000907c00,0x918a09cdab8000067de1,0x525e3e319185e3418000,0x26c000003489a9001c0f,0x3b12052c2a800006c40,0xa800063090a1b3bd06ce,0x3293c6e5e241720ba715,0xc6c696eda56873bb153a,0x431efe8ea12d10dfc284,0xf57163460ee467970a04,0x49d817ef0a1d656a38d0,0x9639f638a0415114424e,0x50f904cc129c32,0x52111aa21d1b1ec0,0xac1da61d800000932470,0x302c810b0000000022],#[0xc34e0000000000000000,0xea7ffc8de08d92da748f,0xcdd467827f0001126cc2,0x8e4800045a46d0d0,0x3800024b0493800021a6,0xc290223abc1db97240a,0x217a7266,0xe22de000088f6c29b106,0x43d8000c59e96e544,0xe4568bcb0700000cf580,0xfc1fa851ca07046de8da,0x5f7c1202d2cedf97df10,0xa7e0807c000000000018,0x3d26f46e29e961dde550,0x27ab82254c8d5b9d0713,0x1170c34d2e4232880820,0x3445400010c4314fd6de,0xff1319c78c43151f34a6,0x85438c0d02796df43dd9,0xdb1c7c8021d0e036e3c2,0xf1c236f28841490f3b19,0x90e5906c192c86c4fc71,0xd53672c5a1dd40005256,0xe6b97db4dc027c8e8d17,0x4305ccf79e6d1c909cf9,0x1e0690e4f13ce3f30000,0x83084ec2c2e62722ba14,0xb0b08dad01748e5026c1,0x8c196614393648da43a2,0xd519ff35502e9501c780,0xcb2c000000000006f21c,0xea4c78d192258a5c8000],#[0x24f4302537897c0001a6,0x892f9fea1b000018,0xd2067ad8800000004019,0xbaa0ec80000000000232,0x10ea00000000000cd6a9,0x31f6e6768e96c648000,0xc773a18800,0xc75200021eb000000000,0xfd189000000012940000,0x1dc000000030b8456a92,0xc47452e2a42e096e5e50,0x5c1ede01e851623ec3f9,0x70e382e53c000185d210,0xd08b98870fe21ba00fb1,0x2c34289c80c7400003eb,0x5351bdc89e43160003b1,0x88941c0345610e8812f8,0x3f83510ed49d34140000,0x11d7a1a4d1d019d937,0x1a9c00018936a5a0,0xa3e6000000027e0,0x6c05eb1cd70b6ccc800,0x128000116a0000436cc,0x8588975ac6661eb,0x4bf06453ff061ed5bc00,0x3ee032d451250500019,0x906e4293a00018d6e334,0x9773a691534d2b9ba0ad,0xe1f1c0923a0000000014,0x6800047930bad0f900ff,0x1f4c1467ea8c8ea1382d,0x49ca03eaa5600001064a],#[0xd14c584ecda2233a0648,0xcf542a66a8511a000200,0x31540b14000059fc9770,0x839ea2fe101c0005068,0x2e10e2a194427,0x1137040cc5a20,0xe91084652ff00ca,0x3d846e4598cfbdc64400,0x389c8022f77368c866a,0xb122e28fa00000004171,0xe09301e7670da3c68394,0x50a25e14000071944040,0x6277810f20e07338549a,0x3c580600000aee0003a2,0x10aa6233810d09d3a,0xbd7840ddc06a80000000,0xd339fab44ecea1df85a4,0x6edf1b3c9313772c39c1,0x64d60d6d07ed07655f2,0x8832e9800091bad53800,0x406d9df341b2527d1321,0xdc7c6c2ec21983fb0000,0x7670dae03e42b9ca5518,0xb09e49433da21d37055d,0x680000f8a94e131964f1,0x378806f0000000015,0x15a632d5800000000,0xbe14189fd13c8a4e0252,0xded116a048d17a18371f,0x9013d01699a307704a89,0x3a3be416e6061c673169,0x1fe291057600018f6a30],#[0xf85808ea6100000001c,0x600000000c25c29ca8bc,0x1269000010100b6332,0xc254000000052d367cc0,0xe478586029edf420e748,0x2229a2380001059f39,0xe25c00018348ec20,0x680f0bc800014070000,0x4ff16cc8d4c99b867000,0x22b8d0a26d0001d,0x1212e91d80002c19c510,0xffb3e98891d01952630d,0x8d5f17bc10a00008,0xf8000a9cccef43c2685e,0xadc00000000000000316,0x4ec78ff7457e3fa2ea98,0xa90f993c00067a3,0xa3f2ce36e8c933a2b52b,0x8461d3322a78000c9701,0x246ae010da3821028000,0x37e3f27708000080562c,0xedcf83ae4480000ec4c5,0xaf0f5c6109869c74710e,0x62d0018e5d5d17,0x1e3fd22440be00000,0x8a650b31a9800002bb,0x2f40004321000119b400,0x30d785d10000d,0x363e64c5800011ad25fc,0x5a73c780000000000040,0x19b48000602a85005,0x84cf320003440e42b],#[0x2c7bd09021e41e1ac400,0x1a32e1ec610ca3ea9,0x62070001e29d3c8d795,0xf8c00000000000000000,0x18b96926881f28100,0xa557364f200000000000,0x83890d828c29a39a4718,0x33031700014,0xc61a30001011f1218000,0x3ab00c38fd40b705a117,0x193c32cf67c904a75,0x8800000008774000181f,0x51188cbe02,0x8cd2497216d0000b1120,0x609100000000c668000,0x17c31f80000000000000,0x5240000114c664e,0xcc0cf64d9537b09ce494,0x45ce8ae2e3c7a3,0x1668873202900000,0xb8000cea5cd3c0000000,0x41c8000b1ba000081,0x7380000000000049a20,0x106b804e8000,0x230000615260401ea000,0x4071475236188e69,0xb82290001c9cc00047e1,0x94000309ce990a066bc,0x15bc4044c4f9cbdb1,0x464f889a34c54c9,0x220c00,0xac5c09df022264b00000],#[0xda88e6cb0141c0ea231f,0x9ac2f0e744000000009f,0x8ef38bf03df84fa00018,0x67ef000000031b6a7ed,0xe2813200000de58f2800,0x8eba8614000626147911,0x5c4ad2beb98153590519,0x37246b0146c9fa16033c,0x484d981298ba878c4886,0xf6469000115ec00015d7,0x1b1445e08f7c029908,0x80e81d2d2ba000000000,0x2c4af3d7,0x8fb01fe0a5e04f8f3000,0x6ab98e10000000000008,0x60c2000000000b0e618,0xf7400000006a57164800,0x350c70400008be70628,0x649700000000a59e15e,0x11423c26ff894989c000,0x31ee0000cb948,0x9c7af0000d670b9d0000,0x5a8dd8000203,0x19c0a1daa25940c40,0x3c7090d6e02560c9969a,0x104c486f4483003133,0x45915a2c000000001180,0x573900008d180000000,0x11f684de08b6d94000,0xa4512187199c1d200000,0xd8000709400000000000,0xbf1cec642018b0a4fa3],#[0xc31e64110aec546a720c,0xa8000ce2c00000000000,0x89a31cd73c23141fa240,0xcefa000093f017508071,0xbd83c688bd8eb029083b,0x998000022fe43a885a8a,0xae0c46ef26de2994c6ec,0xa00900a398602212622c,0xb4bc24e1bdd0e9470338,0xeb5ca1aa8ab022a0957c,0xf88b2899f227d8cb6166,0x2bd1a9330d41c5820d93,0x4244a3f3a69423fc7bde,0x548262ed699b9228a5db,0x39d126b2364f2a108d8e,0x70dd41d9b24c8ff826fd,0x4c81ae89600008acd6c8,0x142262219528bb4656b4,0x87a6162400022c789df0,0x880000c9a00030a62155,0xa70000041500019b2724,0xf02604d3c8373b4140d,0x8a1860001893c0000000,0x7ae00011b962f,0x4ae9c5f264c54a4d840,0xf80004e679b1c2d89267,0x19b7215]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0x54d51541415013048110,0x98e545956458d6158154,0xfdbdfeef5fd0f41d0264,0x877337fffdfdfbfbfbfb,0x57371acab05d666b1a,0x882141042420958012a0,0xb180b72012e40858410a,0x4ba80b74012e80798c0e,0x32a004b76012ec02dd40,0xc2eb184b710cac019540,0xd424ba84b74092e81798,0xdd045b908b76092ec12d,0x650865b88e560196ec22,0x3798c6eb18cb721b6843,0xa369906cb20da541b2a8,0xe512dd864bb0cb75192e,0x2eb165922caa45d63892,0xaaa452dc4b2b01497689,0x2aaa85798caeb194b722,0x1496ec525d8aab294b74,0x744a2c892dc928b124b7,0xd63242c242dd528b2a4b,0x8970912ec425d48cb211,0x48975932c92758e50a8c,0xb1956532aa868584c4bb,0xbaa8b74522c8a2dc144b,0x5ba2cb70592ed325c265,0x6e3a2de545baa8b7dc16,0x105b8a0b7043aa8f7dd1,0xd904bb21565434c88659,0xdc184bb39964712e0e2d,0x25d604b840b75616e2c2],#[0xa50805ba34b71696e0d,0x80a55014b902962052a4,0xec0a5d414b282974052c,0x2a21ad0434a0869310d2,0xd2861adc434b8869610d,0xd2e61a58c34a986b430,0x40d2c81a95034aa06b73,0x740d4e81a5d0343a06a6,0x9760d6ea1a5d434b286b,0xe964152c42a50855bb06,0xeb711d2e23a58474a88,0x90e9721d2c43a54874a1,0xb98e9731d2c63a54c75b,0x4ba8e9651d2c83a55075,0x34a946b761d2ec3add47,0x4b5a0969412d2cb1a58a,0x90b4b9169622d2e25a58,0x5d8b53a169742d4c85a5,0xa54535a0a69414d2629a,0x9ad0d34a1a69724d2e29,0x89a95134aa269734d2a6,0xcb2a59494baa6a744d2e,0x2e8aa55154b82a964352,0x52e28a5c114b21e97555,0x652e2ca5c194bb229644,0x46d2e2da5c1b4bab2973,0x3a0094013800153a3697,0x1027608701bc05a01280,0x847210803e00de031a0b,0x66817f85b8154851a132,0x5820187941d106ec1aa8,0x628109a825108f022c08],#[0x2fa8ba02d60b0e2b18a6,0x698d5e3428cb631b0c32,0x80f003b08e7438d8de63,0x90f042f10604018fb23d,0x26c48591ca4601152447,0x84f093864cf92f64aa9,0xc562954853e149a51714,0x5c296d659f964458215c,0x3b98aa61b981e5ec1750,0x1a4868319c065c193e6,0x9bfc6f11b826cb9ae66a,0xdce7609d2e73a1ca4716,0x607c91edc7a41e4a7821,0xa830a08280c1fe07eb9f,0x8a4a22a8782194853210,0xe23d08e523608c622da,0x7a61a974256e94624a69,0xa8009ed276e9c6a6c499,0xa42a7d29a4a4a28b2a14,0x72b022bb2ad22af0aa72,0x2b8eadecb61ad34b30ac,0xc182fe8be52f3ebb42e8,0xa4321ec74b176c45b0b6,0x9344ecf7336ecc3b2d0c,0x362cd7ab59ed53b4f4d2,0x84edf7b794dc9b6bcd9d,0x58e8139b0e55b8fce27b,0x4f133bdeee3bb1ceb03a,0xf963e00f6dbd4cf42bca,0x29c046ffe3f8cfc3beb6,0xdc281086c1c305540ff0,0xc47310843cd0dec3270a],#[0x6c1199c603169c54b138,0xa921648051e747391bcc,0x4c2c0305270497724648,0x81e460583581c060d0b8,0xd048a0c83d09020502c2,0x4e181b41a200e1f8522,0x820ac100618c150e0c84,0x2d0ea045e244009a1693,0xc2a8984470180701450,0x50441787c1c380080c69,0x18093c104e258069f4cc,0x21ca6d2e481911408358,0x28d1f41876274c08c8c4,0xe2c3d170481a33160800,0x8a50336f83ef904786c6,0xf54a065af8c2d8819eb8,0xb75ddae104853f390462,0x4bcda49216bf44700812,0xa3dd01207f6b80023cff,0x6924bbf3ef2784054b1f,0x67bc6fc1271c73e5d3,0x919a6b0e800cf52f184,0x668095b5c208a27bb5d0,0x4026478ec2066df53ae4,0x8cb73be04279c7924700,0x191e7df88a29125beda0,0xcfc060606bc9337ff210,0x8c5294267d9f7ce7123e,0xb8b3710267dbf602462f,0xc502499fbf44514092f,0x1248fe639080492b7ff4,0x230f866be236ee3e63d9],#[0x40661f0cff0461e2be68,0x3c048a27afd008d15f60,0xb538f01240fa858091c6,0xf1f840234fefcbe008f2,0x31fff05e0145d662014a,0xb0133f03820122ff3901,0x80486fd23ae0006875d7,0x133cad4fe100913f7e60,0xa7fdfb6b00484ffa0280,0xd43e01317f406a1f009,0x7b8308f7dfe914282fe8,0xdce249f7f9e8a812429d,0x85fd67123337f0800cd6,0x205078f7c135f1666014,0xc509efa1fa4102bb9f38,0x492479f5ad67140936f9,0xf05008d3db09647dffd8,0x309cf715028d3f181177,0xe6a12ae31f401024dee2,0x4d214a068bf93008507,0x823eff7c1e080204bcf,0xe84c0cb3fcc822ee37eb,0x473a6c136fe7885023b7,0x11a7c718b047dfcf10a0,0x8178b04a0fcd42698e64,0x85024ee08f5023eff77,0x478a1149fdc884e3c1e,0xbc37140cc9f7a8cac81a,0x33ac57ca846cb0cfe11b,0x2287866940cd9da98338,0x3f508d001fa8465b1d4,0x75cd4411c3da25a0665e],#[0x135f79e8142998e64119,0x39d42a3ee53e5429a1ea,0x6f89a08f79f0284f5e65,0x1e0f842a11f7c21508c2,0x95bd710a047dc89fd81,0xc36785c08e3fc2f11001,0x6c255f0dd08479f09508,0xd4295002693a3fb09ade,0x9268f131bf536424bee9,0x38cd00367d496bf54d80,0x9ba029d3d798d9002557,0x81d180254f76bc08d4fc,0x40929e030c2159c571f,0x40099bbdc701330f1638,0xa204d13f7d7602470fdb,0xeb8af4b96024981872f1,0x91f7d7e27aa4b4024c1,0x8492bfe51d091d617c8f,0x496fa764c099a7d40c0e,0x24e0c9e02691ef194562,0x30424b9f3c69e84905f,0x2496bc54038490bf3e82,0xffd698491c7ee8f19fa4,0xfd8091f7e178a9b41254,0x311e04cd3eb6c048f87d,0x212428fd8e40c4224c2d,0x24c2f3e860099e7bf7c2,0xec7f22475ff6de3e4201,0xef124c7f32ec481342f9,0xcd3e7d4e3802461e3ad6,0xf55a98c04025f7e4e000,0x346d7e1045ddae10465f],#[0x8dd2cba125d7e3a02801,0x244f5e438fdb8492c7af,0x9f6b1f0f111d4ac78f01,0x81fdc5802437eb6a4001,0x11e713ea08cabfb9a823,0xc012e7e16a011e7f0980,0xf27cb2d0025afc6e02aa,0x7f304025b4b1d481997f,0x81346d63ef1023cfd4ad,0x42f7af5b849203ccb26a,0x7f3f9200479f8f0bb802,0xfd983004adff8e48011d,0x89377f7ed0ad048de79,0x4f7ef446238e0bebb745,0x4ec012267f9654898026,0x4f5fe10514001a67e3d,0x36fffc33c10c128ce3df,0xadfd59c480492eb30803,0x7e66720246f6247c4804,0x9297ffe68568e240266f,0xfee98c0475ff6fef6124,0xccd8033ef85035520256,0x50132778d35202497f7,0x3bf22a6c80923dfda095,0x5c7ce0264e1d5690400d,0x3c5823efff1ce482c02,0x2e2819aabea84c0cfbff,0x940d4371638a0492ff8,0xfdf0782140949f99682d,0x1e13033b7f412a940d1b,0x33f7d4b504840d35cbe,0xd0285348ec264fe90a31],#[0x2812a7eb7b3f06049333,0xace1dd1a819f7ff2a704,0xe5c33c1084b3e71840c2,0xe7614efff132e28485ff,0xe668fec2833a0]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x3410004050100900c15,0xb000020180706007,0x15c20074a30000103c15,0x8023004000fc0602401,0x45d02c060000707800,0x168050180b030020000d,0x540d040090000903032,0x140000800050a40000a,0x10807044031d40005807,0x400000100080700850,0x830002e0003200412,0x42c03022098000b409,0x460012ac0001404008f3,0x700d0040a0942b01017,0x3700c2c0480502000,0xc4901c490ec1000000,0xb80001c5e0940207433,0x81400417000110a808,0xf48a1f0040100d00409,0x1f00c0980712c0a11c15,0xc2901c060180007801,0x4410148c0042609c2b,0x4002000060042f10001,0x474010602e0080301c06,0x28c3201c7e098a902c04,0x540504c000282d0000f,0x20011141220c0002c02,0x18000400004c0000000,0x1b44d05c10000b712419,0x2140030d01405c3e,0x7074270cc0001000,0x71df01c05000000f468],#[0xa00804c3905c0004c1c,0x4970001a1583b05411,0xbc04010321c42800026,0x682c024303b40101811,0x2c802048000004a0dc22,0x182c0f45f0f00a0e027,0x680411c01030bb00c10,0x7800018d38540200c09,0x80001007004a512809,0x6406010ab05c0a06801,0x4823018020a40607409,0x247d300100000e0e400,0x11819068972d4031b804,0x10ae0601b01c6b0187b,0xa084d30980601002,0x370040b403000020e413,0x8060207a2e0a02d469,0x17025064b90a00019cc8,0xc00004c120181802c88,0x34519dc3101cc437c2a,0x13c31044030606503c12,0x81e000225ac0306529,0x78a02940a0000106f15,0x80a9a0b610c4345903,0x38c0006c332301d1bc01,0x106144080ac3402418,0xcc430040a1e80b008e8,0x320216d0106f21003,0x92018050040600402,0x2caa004560195154c17,0x880f0f0080045501057,0x2780001ad20146847c13],#[0x347e048051480105408,0xa8d30124c4a401c404,0x4d81d5c8ef4d225fe2e8,0x352d2c9e626da1013859,0x225800023d7000006993,0x1df177c1ae0a404ea079,0xcc4d4609d58f38c8c4f,0xb8a039e40001acc4c060,0x40705cd000014181f50f,0x334500028398f35386,0x480004eb2221c5b40000,0xf213019ea8bb853ab7ab,0x883d5f8aa694141440ed,0x882ab65b2930889ec598,0x9000341bd15b3f991761,0x4f91027f6230b982f8d7,0x6e64c44ade83d57e552b,0xd7611855760f6fdd52c5,0x21ba9068000911a1b4cf,0x148c24d4bb0001a13ca6,0x42b5b10ec6b3f55d878d,0xe4bbe90b453856d4f872,0x4640a2686341f0c99e1f,0x1fb5c6a1713ea50974b6,0xaad99d75147ff4d22f84,0x146ca177379481f1a6aa,0x3db1270200067b58412a,0x6f0b9c39c4edb40e6ffa,0x111284db4a9c7e11,0x9484e6c05ccbcd3d24b,0x5520e757f4317c9a81d2,0x415fe05c24e540c61ad8],#[0x75a1526bda969f4147d2,0x10ab152a66cd0d178481,0xfb550e1b942f60eacca2,0x106f430b31ca67ed,0xc8089ab8f293a2334c00,0x701ce8c0900ed23f1a94,0x56b650000c15428b2bf1,0x9fc3a65400161326c0,0x3da88b0000f6a3458a5e,0x88dc20d48400276d535,0xf93180000ebe5468a1aa,0xd46a1aa449f338aa7a00,0x6c050a00029b642fc4e8,0xe699c319143300022b14,0x453f582a8fb8ccd59264,0x238d03746a612717bcd7,0x3a6685053857f096962f,0x4510b4b949ddc2203a23,0xa0ac0d9e1dd83468a291,0xff5db9922191951f9259,0x784098c942b22744462c,0x109c10a605957d3a9d80,0xbd0a6f4999465108d2ec,0x894a7cdbd473d52d572f,0x2418c2ae41812b38eb49,0x4146859b00381ecd4a84,0x3f104158315d117b5497,0x2ca7981d131d474e36b3,0x143c90914554d0920481,0x99ac5fc530ea8c473a27,0x672303c4738a6fcd01,0x8132fbb429635ca12b00],#[0xefe185f0fbae024df130,0xf3b96e83c006e7764158,0xf9d7b86333b04e850816,0xf88d489c417ccb61d04a,0x53787014a0375b1248cb,0x4234cc57101cf35b95b8,0x60dbc36c225b5dbd8491,0xe47e4479492384a00301,0x2e4d4ce8c3693081382,0x80281246a51215ec1e9b,0x65bd8108000927a2c704,0x180d5a62a2437f5dd713,0xcb43e00ae00eb5190002,0xd3274e170bf143843329,0x67f80aa44ec5a010a328,0x8d83b1156abcfd1994f3,0xab41f8342604488ece1c,0xadde580a3c1d5ac9ea47,0x9cda95e0b4a6aa3f2950,0x4e53412ed4a0407c318,0xa092913c4e6516304d10,0xe0c43dc861793869ea2c,0xf674d6cfd02c3801e2f7,0xf0404232e529413b019c,0xe21794c92f2c30c2ce81,0x3c94f8235a8d865886b0,0x2508f7593815517c55b2,0x90001d89c0ed48558525,0xeb29176762984a000126,0xb955b34148068c3160fe,0xd85908a4e94bf13844b4,0x741d05d080739d8d],#[0x2a64a57495c5cb4eec2a,0x48f113dcb51383808d,0x5d1ad498c3824bc28580,0x116c0d7000358f57f24f,0x6ad562c0be860067f587,0xf800029dec6952e21e88,0x4448420fc29d5e61280f,0xddf8214db72b519a0540,0x9c000088a83da18e36ca,0x64ab7c7416db1a200011,0xf330000e26f43b000324,0x9921d7938150408953d4,0x950ba2208a5c77f850b2,0x7271114e0ced236a7569,0x1cc03215170cb243009d,0x393790d6e53933410d9,0x1caa89b84da3baf00016,0x4b172bd410e104c0,0xdf6c780000000f4b8c10,0xa3aa4a48722d89fa21b0,0xfdda8c16515934d5fb67,0x39fd44e9330824c7708d,0x6500033f8a0b642350be,0x994d742daedf1710d1b4,0x94d187fcb91d06d68f24,0x33b1cd88233e54043abc,0x6fac7412994402b0c52d,0x2412cd4d45ec6ff08a4c,0xa170542526e518000000,0x188d8251c0f4fc08cf4a,0x4cc53300d7a4075d1322,0x209bd4a9ca600000e],#[0x469419d601a716427893,0x269f4c5ab29ec47c936c,0xf1edd7c00a7000283a57,0x25a52d554ab27,0xe2c5f800068513732ef8,0x7880fdc3889800060b25,0x8b7f54c13bd251b5ac56,0xb8d56093f407753dd2b0,0x153c0000000084175024,0xada0d8180b600001bbf8,0x1e0e1e8dc64af2270475,0xa50fb6aa56a3731a0e20,0x1362a3200016180fa44,0xcbf9aa9d2f4000c42000,0x93389280605bf0a7505b,0x201493f3ca1b05c0000,0x2012718a601c66806505,0x84cb870a948e89db000,0x6050e9304ce2c12f1560,0x20a1c43741ca0af07c61,0x14882a35306348407509,0xe7aa629573ac21072583,0x5806d502f50794cdc6d8,0x82f4472e869000137ece,0x3a953425c3c349de1b7d,0x8ee0192c44e5418183ba,0x9c768000c9b8de2d40f2,0x4152605c76058a01b117,0x9734a5aceb057626b,0xad5afc5676108e5d0ff0,0x720e984da76440eb8471,0x32200000d8cc249b5a35],#[0xf200000007586ac40c7a,0x508989175a837f2ec91,0xc24527c90825b0d17000,0x89bfa6a0003264,0xd55dc48d0000cc0e9c70,0x827d900c5ec43862400c,0x1a4c15998c901a21c81a,0x4ef9560b14413984f23,0x2c87c86ae5e62c2c069c,0xcd7d1dd000000057ae2e,0x9773e3400c199498d03f,0x300008cc388fd5dbdbe4,0x93f7f04f1e64008c6153,0x3b993743f04007cc3965,0x3c838d24f0287cb0d150,0x3731fddc307a265ccc4a,0xc6e3bd816edabb363e5d,0x50c4728cf1a52c629248,0x64a5b0a080b584641064,0xe4210f0b116e222c256f,0x4694bb42cc42f169cab,0x38468d553d104000259a,0xe71800096e346800020,0x12b80f1730549900031a,0xa5d08fcbc449bcffc000,0x6e8fd00035c848559c94,0xd1d1b1bd1c4063f5fac0,0xdac3eb48f206800015c,0x4b4e96257859970002,0x886a0589832988055980,0x179c5824644886549f16,0x2472d112582eecdc5948],#[0x4fa9795c296f0411c0c9,0xb288caed27b73569da8e,0x98ac08228581162d5970,0xd3a8a8a561314339c281,0x9f03eab5c3c95415616a,0xd21d1ac0528000167628,0x4c45f14208306c23ac11,0x432da2b44036b2804da1,0xb42ece49a6dd41858e67,0x2d038544a7d0e42b50e6,0x3fa72b113aa1c20fc028,0x80003187cb982a4c46f1,0x51900004d93941841c13,0xa449170087514a85510f,0xba2ed8891341855c278c,0x7d914b6c000434645087,0x1e7ea5b8299738000cba,0xb1662ddd86b4105a9792,0xc81ffd3f966a1b1b74e0,0x53ae3be4988c75e80291,0x6f22c6650d40235ca5d5,0x9b380da930af183aa01,0x52c90fa0320cf1f1db06,0x38900000006a39244536,0xd8556c2e05731d3b4d55,0x785711c2697b1ef93292,0x4ae72d9d704a69689592,0x3dafca860c44d60000,0xdf81181102eb47cf3df0,0xd0c0d1c63a7000005057,0x1b5804c5eeb291350062,0x829ad02e112bc6632ff],#[0x15d7475000220ca21f6,0x410c37b0002ad8687400,0x5ab1b3eb1a58db1d820a,0x9b2a58a2da4aa430a611,0x543ea6f857700015ade4,0x2830001482c8b8000843,0x1500015ab000032ad0ae,0xb803a14966df5b441e94,0xc70f0bc84390068aa4dc,0x54833b69500000000db0,0xd446e16d6040000149d1,0x5cfc33719d913561687,0xadc4761014c4000007d,0x6505d1324025e91840d5,0x35ea06452bf332365c3,0xcd353bd919d3cb40a45e,0xbec1294bfe33de44d935,0x214ce493a8892240008,0xd897ce3954fcf3d48600,0xac9087adce8e820092aa,0xbe0aaa1e95ca2f540b6,0x85251a0ac5f55d98c9f2,0x49571510d8e17a484059,0x435550399d7d8de952f,0x3bbfd4d780a38f395aae,0x4114c81b00db01d52370,0x17507254b4c3043a4845,0x78d28d11e40c94c3cee9,0xe40ced1bc876ccacd3c3,0xbe94347302e180eba85,0x25130d648cca8cd5354e,0xda076a9804180bcf14b0],#[0xf1222a27581000130fc6,0x47d7fe836e1e64e383c,0x5e09c9192c7f359e8b36,0x741ef197460c40c8d3a0,0x2655d9f15263c6c7df5c,0x3c5a8ae6010349544351,0xe312d0b592282f6f3801,0x24c794e92ea6ab346995,0xe5cb7740fd020561521,0xef45de2d757d62a712ca,0x13e7c2ac474ca2b0,0xaef4266e66da51802d47,0x4b33bfcef3087d28b0fd,0x7c559eb36375c8375f80,0x74d556440bb4fc489041,0xe16a0ee394849730e0c6,0x169e0a5c4cd231d3ed,0x54188a59705a186eb5c0,0xd1e345f871b5f3a281a3,0x1de090504727a907a55e,0xc781d0135a9582011535,0x853b340023310745a690,0x1a744703b414203aa48f,0xd78d299b24ad91c72891,0xf47675e6023249f6fe58,0x17585ae8424d0b84613e,0x4e0011c8fc1b7969148e,0xc4bca02c03a5c4fa318d,0xd34451f32a9cc825,0xdf8e9ba3d10723ab64d3,0xeb909d0860a6ea68b462,0x709a1111097394292b49],#[0x11f31e58fac00021120c,0x61505180b269f8000,0xfcc4a613e80000,0xb3631a5e0cb3f600,0x3594845cfe01c209a459,0xd20cac000913c521b324,0x437000054f789aa2305,0x89811ca2fe937782e000,0x1e644497aad5103df4db,0x4d7466027315510959,0xc00000000000a8116e91,0xf5412400092fdc0ac13,0x6ff345d764b14000497e,0x9e30babd8c5400043d34,0x8a31564d3011eb4f8a0c,0x46e3b5d2480001390000,0x5013ae0ce46d00028952,0x3550c07c54700014b388,0x12ab4a100031fa000,0xa64942a41456a36ed3b4,0xe4c312cbcc460b3f7dc0,0x86f3c2455173d54a6703,0x61f487e734ace5,0x14312d4810a4494d2840,0xf82e4978000943d5f610,0xa2d80205a265485d02a3,0x6515f74df8e6d5561181,0x517a0000d434a02ce35c,0x48d402664f24ffab2c1c,0x2745a987734f812ae500,0x4c8471373dab4cdc0008,0x83b249b3336b00aac546],#[0x3cc84c4000440,0xac966c3ecb3885b1aa48,0xed69519b48a558600dc5,0xd3d855f048c1e125252d,0xc2d27f88bdde00000dd2,0x1c5d7539c3665206dfd8,0x6098449a59c581c80cc9,0x432518632ef4f03fb50d,0x88cc8d387045c025cb03,0x40354845c3e60666b039,0x72792bd1763599875041,0x43bca7c7e69348187cea,0xea2430cff241e4f73169,0xe884d33dc1caf5c9df31,0x51b2ae216550a8451f58,0x895389951c86b8988a48,0x7922945781e616224fd1,0xf6a82f012f8184955fc2,0x14a212ce47a498227357,0xddc0348ac3d8147a3c31,0xe38a088329c122c000c2,0x5444d9d2dc4f424f917b,0xddc6bc261684224d965d,0x75006a5a6868390b14f0,0x8f98000caa29b4495ece,0x1ac57f622e51115d25ba,0x741f674b33c444c90288,0x5a20456edf9b53c00094,0x121b4d80000003039cb0,0x30832d3ab58382390ca4,0xd84e544ecdd30e240b21,0x8ab045ac54a36dc92d2f],#[0xaae4ba7541c6e577857c,0x37516051708b179722a4,0x5a8c4ad0fc2ac73fa45,0x3a8b38d4439522321123,0x50cc0a34400c1908152c,0xb830000059c2f948cab,0x91f74c853c800003ac00,0x541bd273f4000ea7f5c4,0x8cd4c22c0000b82ae0ba,0xa0578cf8d94f03425bb0,0xd000d71d3a61ec8dc,0xc8eef5c540af24eb404,0x46f93dd120f09e42655,0xaacaa725653a53636c00,0x71f05c0658c09165647a,0xb2a55aaba31f4d721953,0x800041e000014e63c54b,0x5654ad0518478b2300bd,0x2253c25dad78c349905a,0xa6eb34b7c0f74fe06cb0,0xf6eec2100038819098d1,0x467bde853eced00002c8,0xdc29a05b199e0002a7b3,0xb59f78211ffc34f41396,0x40a118e43fc85ad8b095,0x521f229417ca53e0378,0x913240db0002c72c7070,0xa7981de8d2c00011261a,0x28f362c8653a6b40a381,0xd9161a47b245c5ac0003,0xf28f00019cf0001c50d1,0x9d244431fb1800000d5b],#[0x1b5164307d6fb2224558,0x40d5a38f85cc2cc4d1cc,0xc4dc00093b2abac43125,0x2033de297404c84a8000,0x3c00095a3bad0002d9b1,0x247b1424445cb3c000c3,0x9ce585ce010ff0000f69,0x888ae253c06f74e149d1,0x4307f15e47f457a00010,0xcee33b30ae83d68685ce,0x63204850f760da9cc000,0x5]]
def g251D11 := limbs80 #[#[0xa0530a4144131963fff7,0xd51e8350698d60aa1d02,0x4ca9552b1d53e8750eb0,0x8da278640c0015973256,0xa5a899fc749925512e3f,0x3f6f1b84d8326bdad2a4,0x1860285c242c04145b0d,0x830203c089c18504000,0xf0c868d8d0a01078c0b0,0x1e41273a8131fa8128f8,0xd320982a077a5bcc21be,0xe96d6097e2d7412b881a,0x77ff8019fe00afb8057,0x21a8063d85a0293fb78,0xd00528603dfce0098f4e,0x80c7e9e809deda01cfc6,0x1f846502978]]
def g251H11 := limbs80 #[#[0xa1c00022646803c1c481,0x2c01a3e0110000084002,0xc69c00240005a6448422,0x8300055801e38614662,0x81062249100000233a90,0x82600883043808200280,0x2a8000b26080a2236c38,0x10164f000a826832790d,0x329c5c400342c2552802,0x2f7c41992f4db0935d70,0xcf08d000000001a00003,0x6950b07ae13b885092ba,0x4c48c3a81d8f306e6486,0xd35a18e6a7ddd30811f2,0xcd159e0fc13000e5d9b8,0x70008613e800b44000e4,0x434004a925a000000d,0xaa25670ee2f93a2b8520,0xd5b077d8ceaf2e800cc0,0xe04c0614aed87ce6df2e,0x6c00051c006e50012433,0xbbc4fdde1340016ab14c,0xe0030495000182b08e38,0x7341e71c4910c65000b4,0x6586782a007518000008,0x9e0001c8004884c6053,0xa38a00000000ed000000,0x2c48500090f1fc3f42,0x3001a3353a8e0,0x5e6a3721326561f7a000,0xf05891a7120003b00110,0x4b0008a3bfc5c6633850],#[0xa33686ec0f037986af0,0xa000001490011d91c800,0x2a099e95e17c0037e15,0xb965b00002c000ae0000,0x5140000015a108373,0x20000003a8168219a21b,0xa0019e80043a380d036,0x1c0004b5c881144ae2f8,0x7648629800005ed29000,0xd83e8d20d536a9827d96,0x3e2cc1671362b929b,0x169204ea8de573f19200,0xa1ec0032a4a61413d623,0x4f2b2bc91791c006bf76,0x6c2b861f8b80023d44f0,0x6c117de076ac17772728,0x205acdb1009694533800,0x7fb4a508d616ea6d26e8,0x86a244190011a8003b8f,0xc21000857157dba041c6,0xb2a5da7352581bee6aaa,0x89000f0fbe2975240308,0xd859bf62fb6591a93190,0xc4466ce31eefb103a000,0xe40074200008be5fda14,0x358004cb3900029adbf1,0xecc164ebf03c46e58335,0x33e96b63]]
def g251D12 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g251H12 := limbs80 #[#[0x223000893d32a2820000,0x7eaa04814418043a7040,0x105a0c9e60102a506806,0x690b001280004a3,0x480720]]
def g251L : Nat → Packing
  | 6 => (11,6,7,458763,52,7,1035,g251D6)
  | 7 => (571,5,7,10355064,137,15,1341,g251D7)
  | 8 => (2311,4,7,11600748,138,17,1398,g251D8)
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
theorem g251P8_0 : block g251 8 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_579 : block g251 9 579 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_33242

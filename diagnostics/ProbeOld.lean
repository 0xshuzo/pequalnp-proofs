import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35030.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35030
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffafffffffefffffffc,0xfffefffaeeeeaa00ffff,0xffffffffffffffffffff,0xfffffffafffffffeffff,0xfffcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
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
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
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
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
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


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


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

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
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
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
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
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
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
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
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
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
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
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
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

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[2,7]⟩,⟨.or,[4,6]⟩,⟨.or,[10,5]⟩,⟨.and,[9,11]⟩,⟨.or,[3,12]⟩,⟨.or,[13,0]⟩,⟨.or,[2,14]⟩,⟨.and,[8,15]⟩,⟨.or,[0,6]⟩,⟨.or,[13,4]⟩,⟨.and,[17,18]⟩,⟨.and,[1,10]⟩,⟨.or,[19,20]⟩,⟨.or,[16,21]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc00000000000,0x3fc03fffd0234511b807])),(BitVec.ofNat 152 (word80 [0x484848484848484848,0x48484848500145009007]))),((BitVec.ofNat 152 (word80 [0x3fc000,0x3fc0000004012047ef])),(BitVec.ofNat 152 (word80 [0xe2e2e2e2e2e2e2e2e2,0xe2e2e2e2c004002047a7]))),((BitVec.ofNat 152 (word80 [0x3fc000003fc0003f,0xc000000000408646009f])),(BitVec.ofNat 152 (word80 [0xc1c1c1c1c1c1c1c1c1,0xc1c1c1c1c0008002009f]))),((BitVec.ofNat 152 (word80 [0x3fc000003fc0003fc0,0x3fc08008880801])),(BitVec.ofNat 152 (word80 [0x818181818181818181,0x81818181800000000800]))),((BitVec.ofNat 152 (word80 [0xc000003fc000000000,0x3fffc00518f0f07118])),(BitVec.ofNat 152 (word80 [0x50505050505050505,0x5050505050880d02018]))),((BitVec.ofNat 152 (word80 [0x3fff,0xffc00000261f00ff8250])),(BitVec.ofNat 152 (word80 [0x161616161616161616,0x16161616241e00fd0240]))),((BitVec.ofNat 152 (word80 [0x3fffffffc000,0x381fff000462])),(BitVec.ofNat 152 (word80 [0x181818181818181818,0x1818181838136f000040]))),((BitVec.ofNat 152 (word80 [0xffffffc00000000000,0x3fe000000784])),(BitVec.ofNat 152 (word80 [0x202020202020202020,0x2020202002e000000500]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(1,0,254,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,2,173,80,10),(20,0,235,0,10),(16,2,173,64,9),(48,0,207,0,9),(64,2,173,16,9),(130,0,125,0,9),(0,32,82,141,8),(17,0,238,0,8),(33,0,222,0,8),(65,0,190,0,8),(80,0,173,0,8),(80,2,173,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(0,4,27,224,7),(1,2,172,80,7),(1,32,82,140,7),(4,32,82,137,7),(8,32,82,133,7),(32,2,141,80,7),(128,2,45,80,7),(128,32,82,13,7),(5,32,82,136,6),(9,32,82,132,6),(49,0,206,0,6),(64,4,27,160,6),(128,4,27,96,6),(129,32,82,12,6),(132,32,82,9,6),(136,32,82,5,6),(161,0,94,0,6),(81,0,172,0,5),(81,2,172,0,5),(97,0,158,0,5),(112,0,141,0,5),(112,2,141,0,5),(133,32,82,8,5),(137,32,82,4,5),(145,0,110,0,5),(176,0,79,0,5),(192,4,27,32,5),(208,0,45,0,5),(208,2,45,0,5),(224,0,27,0,4),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x272e71fba5957458140,0x140bcabc26d5765d1605,0x60502d6af09b565d7458,0x45c140b59bc36d5975d1,0x5d57050256e727b85957,0xd9655d140b93bc46d586,0xba065574502b2e703a85,0xa5681765d140e8b9865d,0x6ec9a55d974502b6af09,0xf09b869f9159150d8ad8,0xd7c36e1a7e45645428f9,0x87df1db869f9159150a3,0xa1f5c7ae1a7e4564542,0x54262f72ea85d9745915,0x9150b8afc26e1765d164,0x164542e27f0db85d9745,0x645c160a8bdcaae1765d,0x55d164582f0ef11855d5,0x61d7459160d8b987ec1a,0xd5875d164582e2ef01b5,0xdb561d7459160b8afc26,0xc2695a065f81592e27f0,0xbf09a5681765d164a3e7,0x9c481b0c03c0c03002b2,0xa12c9045210fc7833150,0x42204f06f361a4c05d2,0x8007e002074203d08080,0x2202000000030383a080,0xf2202001d80081c880f,0x1a08081c88]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0a074b9975957458140,0x55d170502cdddb30aba2,0x76cc2aeab828166e6db8,0x5db3b0695745c540b2f,0x17054345ed32edc2ae8a,0xc32a8b82a1e4ee197455,0x7175e85645c150d2f34f,0x542cdcda70cba2e0a86d,0xeab82a1a5e69975e1170,0x4619755c150d2f30dd22,0xcbcda70cbaae0a8597bb,0x8aa1679ec9a85d971542,0x5745c160b3af66d42ecb,0xbaf48b2ae0b059b9b4e1,0x171eed1755957058363c,0x5c560b9e760d2aecb8ac,0x49c2ae8b05ce7b269576,0xe5d5a0e51655c345ebb3,0x64a7cf64d2b2fc0ac995,0xa2c0a05cafb2695765d1,0x98755160502f9ddcaeaa,0x5776cc3aa8b02817aeed,0xa07cb9975957458140f,0x5d160502f5ddd2caba2c,0x2ec2ae8b0281f2e5d985,0x7cb9766557458140eb73,0x60503adccbb2aba2c0a0,0x2ae8b0281f2e5d9a55d1,0x9976957458140dd734cd,0x3e5cdaaecba2c0a075b,0x8b0281f2e6e1765d1605,0x65d7458140f9732ed32e],#[0xdddab2eba2c0a075b9b5,0x2817aeed19759560503a,0x7558140ed7768cbacab0,0xb350baac0a05f3bb4655,0x3be6dba85d56050277dd,0x81408ff373d42eab0281,0x2baac0a04febb26a5755,0xed1a95d5605027edd9b5,0x9f7369d4aeab02813ee,0xac0a04bf9b8ea5755814,0xa46556050375cbb748ca,0x736fd232ab02819ee65f,0xa06cfba75d995581409f,0xd9605032fdd3b2ecaac0,0x8d42ecb02817baec9a55,0xafbb66958758140bd776,0x502bf5d934acbac0a05,0xb2eb02815f6ecda565d6,0x865d5545c140af7768d2,0x36dcd3b0caa2e0a07d39,0xb828176eee1655d17050,0x15745c140bb7774b2ae8,0xcd330aba2e0a079b9866,0x81e6e69b855d170503cd,0x45c140f3730ccaae8b82,0x32aba2e0a079bb866557,0x6e619a55d170503adccb,0x140f3770cd2ae8b8281e,0xba2e0a06db9a6695745c,0x1ba55d170502edddb34a,0xf3736ac32e8b8281b6e6,0xe0a06d7ba85d5655c140],#[0x8595705026fcdbf50b2a,0x30cc2aeab82811fe6e7a,0x7979b5619755c140f2f,0x970502eddda32cbaae0a,0xd2b0cb82816eeed1a561,0xb9b0ea17655140b3f76e,0x503e5cd82ecb2ae8a04f,0xcaba281b2fea17659574,0x7ea1655d1409f7361d42,0x7dcd8752b2ae8a04dbdb,0xa28136f6dfa959574502,0x1955d140f17b0cbb30ab,0xc3740caae8a06db976e8,0x1aeee1ba0655745035dc,0x5d140f17b0cbb32aba28,0x40bb2e8a06cbfa65d995,0xe619a05d9745036dcd2b,0x40bb5f64d2aecba281f2,0xb2e8a078bd86695765d1,0xda561974503c5edab0cb,0xef361cc2eab2a8166fed,0xaa056f9b0e617659540a,0x61d65502c7edbd50bb2c,0x6fcc30eb2a814fe6c398,0x53f9b0aa58759540a3fb,0x655023fcd8750cbacaa0,0xc30cbaa811feedda0e61,0xfb6661865d540a7f760c,0x297edb730c32eaa052f,0xcbaa816cfed1a5619755,0x6a5865d540a7f760d4b0,0xefd9b52c32eaa053efb2],#[0xa814efed1a9619755029,0x865d540a7f36154b0cba,0xab51cb2eaa053bdb4aa5,0x47f6dea95d9855031bfd,0xd940afd764cab20bb281,0x4caaeca06aed86e89955,0xa63a2655765031f6cc74,0xb57f68d2b0cbb2818fb,0x2eca058ffb7695865d94,0xa46617650355fd3748cc,0xf760d2b30bb281cafe9b,0xa053efb2695985d940a7,0x61765029efd9b4acc2ec,0xcd2b30bb2814efed1a56,0x1ffb7695985d940a5ff6,0x65031dfda3534c2eca05,0x32ec32812ef6dfa46558,0xb069597e1940d57f4dd2,0x23dfda34dcab0ea053fb,0xc3a818fe65ba06558750,0x9b9561d40c7f72dd032a,0xdd834bcb30ea04bbfb46,0xa1f4e6d974551705429f,0x45c150fa736aba2c8b82,0x2eab22e0a87cb9965d16,0x5e6a57559170543e3ccb,0x150f2f70cd2ae8b82a1b,0xba2e0a86d79a6695745c,0x597565170542eddda32c,0xdaf74cbab28b82a1d5e6,0xa8a85d7bb4659755c150,0x85d954543c9f5c2ecba2],#[0xb70d3f22b22a165f6dea,0x863f6b869f9159150c7e,0x164543e1ebb34aba2c8a,0xbb2e8b22a1e2f6a1765d,0xbdb85d97459150f17d50,0x543c5f5c2ecba2c8a878,0xe8b22a16afed9a85d164,0x7aa17459150b57b6d542,0xd77d9350bb2c8a859bdb,0x22a16b7ecda85d964542,0x17659150b57f68d42ecb,0xda550bb2c8a858ffb76a,0x163f6dea85d964542d5e,0x59150a7df64d432eb22a,0x50cbac8a853dfb36a197,0xfed9a865d645429dfda3,0x50a3ff6ed432eb22a14b,0xbac8a853bdb4aa197591,0xea865d6454297edb550c,0x1ff6ccc2ecba2a147f6d,0x8a858fdb6a61765d150b,0x5d9745424fedd530bb2e,0x66d42ecba2a167bec9a8,0x59bfb46a1765d150b3bf,0x74542cdeda550bb2e8a8,0x4b0cba2a147f6e6a85d9,0xfb2661945d95093fb6fd,0x829efd9b30ca2eca853e,0x8b82c1f2e6d974551705,0x5d1645c160f9730aba2c,0x5cdaae8b22e0b07cb995,0x2c1f1e6157559170583e],#[0x645c160bd7768c2ac8b8,0x2b08ba2e0b05cfbb7615,0xe6e615845d170583e5cb,0xc160f9734cc22e8b82c1,0xaba2e0b05cfbba595745,0x5d5656117058367cd334,0xf2f30abab08b82c1f1e,0x2e0b059fbb7615845c16,0xa45d57058367dd32eaca,0xf768c2aeab82c1b5e617,0xb07cb9766817455160ba,0xd15458375cd3340ba2a8,0x1d42eaaa2c166f6dea85,0x7f9b0ea197551609ef36,0x458375cd2b40ba2c8b04,0xae8b22c1e2f61d855d16,0x876957459160bd7760d2,0x3c5edab0eba2c8b078bd,0xb22c1e2fed5875d16458,0xa17559160bc7f68c2aea,0x7d9350baac8b04efbb06,0xc13b7ecda85d56458277,0x5591609d7f68d42eab22,0x750baac8b04ef9b0ea17,0xaf61fa46156458275eda,0x1609d7b6fd230ab22c1a,0xc3ac8b068ffa761d8559,0xc9a561d64582d7dd834a,0xb5bf66d2b0eb22c16bbe,0xc8b05abfb46958759160,0x565d64582b7dd834acba,0xf68d2b2eb22c15bbec9a],#[0x7cb976611905d160ad7,0x174582b7ddcacac82e8b,0xb2b08ba2c1d3e5d99564,0xbd76615845d160f17b0e,0x583c5ec3b2cc22e8b078,0xcaba2c1e2fed18759574,0x7ea5655d160adf361cc2,0x67cbb740caae8b04cfdb,0xa2c19be65ba065574583,0x1955d160d3f30fd032ab,0xd834abb2e8b063fa98e8,0x173bec9a55d974582e7d,0x5d160b97f68d2aecba2c,0x4ac3ae8b05cbfb466176,0xbec9a561d74582cfdd83,0x60b3bf66d2b0eba2c167,0xc2e8b059bfb4695875d1,0x9a85d58458335fd3748c,0x7bf66d42eac22c12fbec,0x8b068ffa75d985611609,0x65f84582d77d934abb70,0x66d2b2fc22c14fbec9a5,0x56fbb0655945d960a7bf,0x87582b77d932aca2ecb0,0xab28c3ac1aafe9b94651,0xfb36559461d60a7df64c,0x829f7d932bca30eb053d,0x8c3ac14f7ecd95e51875,0x6979461d60a77b69caf2,0xefd9b4bca30eb053efb2,0x2e1e2f619855d1645c29,0x7459170bb7760d2ae8b2],#[0xa34dc2ac8b85cbfb6695,0x8efed1a9e15645c355fd,0xd1709bf361d4acaba2e1,0xcca70ab849fdb8ea5655,0xec9a5641765c69dfda34,0x4bbaf66d2b20bb2e3779,0xf02b26cbfa65d9905d15,0xa065f815931fad2b40cb,0xef60d2b2fc0ac94fded5,0xb273e7b269597e0564a7,0x4174593a5ebb32ac82e8,0xdd032aba2c9b2f5dba56,0xebdb0e99955d164d97ae,0x459365ed2b40bb2e8b24,0xaecba2c972fed5a05d97,0xb2695765d164b97f60d2,0x2b77d932ac82ecb27caf,0xc3ac95afed1956417659,0x559061d64d57f4dd2320,0x7d3744cab0eb253efb26,0xc9aafe9ba46558759357,0x56017495fb61d332ac3a,0x340bb2caba47bfb469b9,0x7fec1a7e61655d2e5fda,0x974a9fb61cb2ecc2ae91,0xc82ecba55efb2655905d,0xc3a4655765d2adfda32a,0xa6ff6ad0329c32eb36f6,0x8bb53efb26179460176,0x5643845da9f7d934ac87,0x7c814c02f00014f7ecda,0x504d8112038c0bf02820],#[0x88901f507441ad062416,0xb982c78a8e27f896e242,0x323840d8034c8c8c2ff0,0xe3d28ee63b10ea239a8e,0x44790ba4158ff23f40fa,0xcd13124b112344799156,0x513b24e413844de136c4,0x94945171424506140c4f,0x58c555153253e94c252d,0x85a9162a58215d056b9,0x8639989860797a45db17,0x69e19e8666996264a990,0x291c827129c126d59af2,0x89e567821dba7661d1e7,0x1f0c7ba9ede7af1e8479,0x7280ea0027f29fa87c6,0x3085d213c846a0cc8252,0x48cca2fa8bba2b68a522,0x8ffa3dc8e923988dda35,0x3da4d49272464910a420,0xba5a095fa55c94ea5189,0x27069b9269698ca62697,0x898a1828289f1278c9d5,0xa6a612978a50291ea342,0xaa9f2a18a8329eaa77a9,0xb2fac44afdab7cac62ac,0x8eae2eb832da8b512ce0,0xe2f7ebcc2eb6b9fae72b,0x313cc4130e2c2ab05cbf,0x28cc95321cc7eb1c2c5d,0xc6ce3b36cccd32fccb13,0xed21b464d10b420cffb3],#[0xd5fb546d493502d3834b,0xda36eeda8363cd8135b6,0xeb8d8e22b83cdf637a0d,0xbaeeeadba68e7bb95ee3,0xc28f01bbfaee5bb5eec9,0xd0f55bd1ef39bc98f12b,0x4faf3e84f933e2af823d,0x8bfeafecbf64fcb3ef,0x62413b040c0b501f4045,0x1c2f909fc247083c1c10,0xc41d0fec3ef0f343950d,0x4d312c44a511b446110f,0xe1175459d153c52d13d4,0xf1adc6ab1a2465118645,0x20747b91e047751c9c6e,0x4ac8c7223c8832184829,0x3ca2d27d49d3266c9632,0xcb3b2c0cae12a4ca7129,0xc492fecbd92e84b532d1,0x3337ecd973524cfb325c,0x93d84f293b6cea339ace,0x410d0213ffcff33f44f9,0x4450ab427d093421d065,0x6008e84f81717e0826f8,0xe0580a98ef83f03e10c0,0x2bf000b18ef82a4fe10,0x8502a23a45fc0f83f086,0x44fe10c60ee2fc1c27f0,0x83f03e111b17e0016f82,0xf84301682af190848bf,0xb85f8446c4f8023be0c1,0xe10d32183ec6d89c0fe0],#[0x7e10d7180aa8bf83f03,0x223be10c0400b6c4f81f,0xf81f07e10cf1a07fc0f8,0xc0b8df07e110054475c6,0x2fc2ca6281502005d45f,0xbc1fc105194c4f0be0c1,0x21ae2815f8223949fc21,0xfc2180adc4f80253e0fc,0xe161317e001121e33be0,0x63e161305e2183b8bf07,0xfb140bf83f83f03e10d0,0xe8cc17627c002df07e10,0x20bfc2c26341e83ff083,0x219d80c20360c18b8b05,0x231209824441437b14,0x6455c5b8002c4915716e,0x19097b8a4444058082c0,0x12e02c4426339e011110,0xd453c019e083708135c5,0xa12e05030c0c01602203,0x60dc16029784f07420c,0x86c0884338178ba1013,0x6fc205e10100808000,0x160244c1604214020400,0x84c10580982058098200,0xf08178406e28284c0885,0xc6728a78cf0050580826,0x741e248ab8d700088815,0x1c118a083818406cc704,0xca2a03bc015453c031c9,0x81705453c0068191031,0xc381605c25080a42052],#[0x540d81bc038a30328174,0x2e03f81c0b78c28ce51,0xfe064721453c67800a84,0x6c205a0b01198e78b24,0x38118a010103601c221e,0xff02c982a142bb8a7802,0x182c11df00319c082348,0x3987841601001669300e,0x60b04630184c1030982a,0x702c20640a8ec15b01e0,0xc81d0605c262702c262,0x60148ef028206f041b84,0xc5827f0323917040b850,0x19c8f80202e05808cc73,0x1420309f450847820b41,0x4000007a282000100f9,0xc1f800ec0076003a2803,0xe003a4fe005a4fe005a4,0x40400020141f800e9307,0x1c43800989b077001e8,0xe47c00c1621311df004,0x7040d4159130c89820b,0x1d717e009c4fe005c4c,0x80100ef80100ef801713,0x617c0041a746f80180ef,0x101c500e080182002b22,0x186841470ca780200014,0x626c0f0a3103d81b198,0x358023ac28b617602c4a,0x2818b05c0b1100d6450,0x390a218e048808e594f,0x201011d6168188615625],#[0x42001003a170188e116,0x1c010615a3583080704e,0x4141044420c1829046e2,0x380c88202c052e09c0e4,0x7d00204694fa006081c4,0xd032985d032985d0014a,0x4c1059d00205894fa007,0x32985f032984623a0049,0xe00494fe00494fe005f0,0x47c00929fc0092982623,0xba2020101040082904c,0x2010104008290410744,0x1b0f606530b606530800,0xb001489b001604059e02,0xec4176004b0641c1178b,0x16c00581010a07b00a3,0x60646ee001101e202cd8,0xc00dc07804443b806381,0x81ec0186730378044440,0x47147142b8ce919b11,0xc50816016d181857d19b,0x508083c4090801108675,0x40237515e0213102b54,0x581f40c26444308a084b,0xc180b0b0984b0bc1f400,0x496102c052f09e0e4416,0x5d03a205d001e800815,0x4317a004013a005d03a2,0xd00205805ba006013a00,0x3a205d001059d002009,0x2058013a007d03a205d,0x309c1613f07f003c27f0],#[0xa6280308a3dc050c1a1,0x9b48e913607831543091,0x912e05830f6048e0581c,0x98215c10008020614d84,0x6e0800dc13040057058,0xf440fa2020dc13040601,0xce801000dc148409ae2,0xc26082ce80170ce8017,0x1ec00f09ec008075c508,0x4c5d80268cd8010184f4,0x8001c080e98a10003b46,0x292e913a002910075c50,0x9d002e800c82e800c8,0x80e0401820800185f001,0xc251c0820c2b7143c2a0,0xc141eb8a704300038a70,0x181712282c391c0cc350,0x8f06821c31011d13f00,0xbf0421e1f0431cf1436,0xf01a10282f050e0f0410,0x15b00206a44c262603c2,0x100e226131301df003d,0x904029c099300a1513f8,0x20000014820dc1d08082,0x1d714]]
def g255H8 := limbs80 #[#[0xb0000000183d40007612,0x95e42762e9a362c0014e,0x5f0c82c2c3000b400000,0x4b5ff3748018200007,0x22200700026a000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7458140f8e5955458140,0xd6e65d7458140f2e5d9,0xd545c140f4e5d5545c14,0x40e6e615745c140b6e69,0x95745c140e6ee15745c1,0x140e6e619745c140b6ee,0xe59745c140e6ee19745c,0xc540e5e615755c140d6e,0xde15745c540e6d615745,0x5c150e2f619765d140e6,0x5e69d545c150f4e5d154,0x55c150e5e5d7845c150b,0xe5e619755c150b5ee917,0x545c550e5ee19755c150,0xe3d619765c550f4d5d1,0xd985d9508fbe89985d95,0x60f2e5d1645c1608f7e8,0xdb855c560f1e5d5655c1,0x571e2f61d7459160e3d5,0xe89955d971d3d5db9059,0xd154f0f5d9655d154b79,0xbe89985d954e2f619765,0xe0175b2fe81765d1648f,0xfbe8995e11768fbe8996,0x458140fce5d554581408,0xfae5d95458140fce6555,0x5458140eee61d5458140,0xdee65d5458140eeee1d,0xd5458140deee5d545814,0x40fae5957458140bee69,0x997458140beee9574581,0x140f6e65d7458140fae6],#[0x61d6558140f9e5d56558,0x8140ebee1d6558140ebe,0xee5d6558140dbe65d655,0x58140bbe69d6558140db,0xeee919558140bbee9d65,0x758140bbee957658140b,0xebee998758140bbee998,0x9758140beee919758140,0xf6e595745c140deee91,0x5745c140f6e615745c14,0x40f6e695745c140f6e65,0x59745c140f6e619745c1,0x140f6e699745c140f6e6,0x615755c140f5e5d5655c,0xc140e7e619755c140f5e,0xee99855c140e7ee19755,0x5c140afe69b855c140af,0x6d615745c540beee9196,0x555140f6d695745c540f,0xf2f5d9655d140bcfe997,0x855d140e6f5d9855d140,0xe6f5db855d140aefe99,0x1955d140aef69b855d14,0x40f6e681765d140beee8,0x899759540f2f619765d1,0x5408ffea197595409fbe,0x68398595409efe919859,0xd540adfe99855d5409fe,0xf6a3965d5409ef693965,0x5d5409fee81985d5408f,0xfe683985d5408ffe9998,0x6e15408ff69f96615409],#[0x8ff6a576e1540cbf6597,0x955d9409fe683955d940,0xabfe99985d9408ff6a3,0x1985d9409efe91985d94,0x40cbfe99985d940cefe9,0x9e985d940abf69a985d9,0x9408ff6a6985d940a7f6,0x693985d9409fe683985d,0x1940abfe9987619409ef,0xfe919761940aefe91956,0x61d40afee819561d40ae,0xefe919661d408ff69b95,0x45c150edee19545c150a,0xf6e5d1645c150bfce856,0x745c150f5e5d5645c150,0xe7e619745c150f5e695,0xb845c150e7ee19745c15,0x50f5e5d5945c150afe69,0x91865c150f5e659755c1,0x550afe693865c150afee,0x6a1745c550f5d695745c,0xc550e7daa1745c550e7d,0xdaa1765c550e7d6a1765,0x55150f4f5d97455150e7,0xdf65f8655150ecfe1974,0x755150adf69f8655150c,0xddd5d79159150adfe998,0x9159150cfd61f9159150,0x9fd69f9159150cfde1f,0x9765d150f2f5d9745915,0x508ffea5865d150e3f61,0xa7865d150aef693865d1],#[0x150a7f69e985d1508ff6,0x65976e1150cdf65975e1,0x11508ff6a576e1150cbf,0xf61b945d5508ffe9d96e,0x5d550adfe91865d550cd,0xbfe91865d950adf69386,0x85d950afbe89985d950a,0xa7fe9d985d950af7e8d9,0x985d9508ffe91985d950,0x8ff69f9461950a7f69e,0x39661d508ff69b9461d5,0x608ffe9196e1d508ff69,0xd5545c160f6e5d1545c1,0x160b7e69d545c160f5e5,0x611745c160f3e5d5645c,0xc160f3e595745c160f6e,0xee95745c160e7ee15745,0x5c160f3e699745c160b7,0xbee99945c160e7e5d784,0x55c160bbee91655c160b,0xf5e615755c160b7ee917,0x855c160b7ee9d855c160,0xf3d5d9855c560afe693,0x97455160f3d695765c56,0x60e6f61d7455160f2f5d,0x819755160bdee8175551,0x1608ffea197551609fee,0x61d7459160fae6817459,0x9160bbee817559160f2f,0xfe918759160bafe91855,0x5d160eafe918759160ba,0xbe659905d160f3e5d990],#[0x45d160f2f5d9845d160d,0xe3f61d655d160e6f61d8,0x855d160aef693855d160,0xa7f69f855d160e3f5db,0x3955d1608ff6a7855d16,0x609bf69b955d1609fe68,0x91875d1608ff6a3955d1,0x160aefe91985d160e6fe,0x692985d1609bfe99985d,0xd160a7f69e985d160aef,0xf69b985d1609fe683985,0x59560d9f5d794595609b,0xbfe1f9459560cbf61f94,0x5595609bf69f9459560c,0x9bfe919759560b9fe917,0x945d5609fe693905d560,0x8ff6a3945d5609bf69b,0x9985d5609fee81985d56,0x609f7e8d985d5609fbe8,0x5d76615609fe683985d5,0x560c7fe5d8761560d3fe,0xe81955d960cbf5d994e1,0xd960bbbe89955d960bbe,0xfe999461d609bf693955,0x61d60afee819561d60ab,0xf7e8d9561d60afbe8995,0x5e1d608ff6939561d60a,0xd7d5d791591708ffe919,0x7459170cfde179159170,0xabf69b8559170f2f619,0x1955d1708ff6a7855917,0x70b6fe91865d170b7ee8],#[0xd794595709fe68394595,0x5708ff6a39459570d5f5,0x6938559570b5fe917559,0x15708ffe9994e1570adf,0xd68174551718ffe9196e,0x5d171d7d655905d171f6,0x7de81955d171b7de9590,0x5d971f3d6817659571b,0xb7de95905d971d7d6559,0x955d971b7de81955d971,0x4b6fe81765d154f79e89,0x3965d554f4f695765d15,0x54afbe89985d9549df68,0x839661d54abfe99985d9,0x564afde8175e05648ff6,0x69597e0564cfd68197e0,0xd164f2f5d9905d164cfd,0xf5d9955d164bafe99905,0x5d164bafe99955d164f2,0x2f695765d164f2f68176,0x55d964bafe91905d964f,0xbafe91955d964bbbe899,0x9061d64aefe919061d64,0x4afbe899561d64abfe99,0x99561d64aefe919561d6,0x74d3fe597660174abfe9,0xdb90595748ffe9995e01,0x574f1f5d98559574d3f5,0xe899859574b3fe817659,0x95749efe9198595749fb,0xfe59766157497f69f985,0x5d974b6fe91905d974d3],#[0x6fe91955d974b7be8995,0x7e0165adfe9175e0165b,0xcdf5d590e11658ffe919,0x90e1165cbf5d990e1165,0x5abfe8176e11658ffe9d,0x39261d658ffe8197e116,0x65cfbe939261d65cfbe5,0x9190e1d658ff6839461d,0x1758ffe9994e01758ffe,0xe8196e11758ffe9196e0,0x1768ffe8194e19758ff,0xfe9195e0176afbe89856,0x58140afbe8985611768f,0xee65d5458140fee61d54,0x458140fee6157458140f,0xfee6957458140fee6557,0x6558140fee6a57458140,0xfbe65d6558140fbe61d,0x57558140fde615755814,0x40bfe6a17558140fde65,0xa57558140bfeea175581,0x140bfeea57558140bfe6,0x61d8558140fbe5d98558,0x8140dfe65d8558140efe,0xe61d9558140fbe5d9955,0x58140dfe65d9558140ef,0xbe6957658140bfee9d95,0x758140fbe6a17658140f,0xefe6958758140bfee958,0x9758140efee958758140,0xbfee959758140feee91,0x59758140dfe695975814],#[0x40fee619545c140dfee9,0x19755c140bfeea1655c1,0x140f7e659755c140f7e6,0x619955c140efe619855c,0xc140efee19955c140efe,0xe695865c140dfe659955,0x55140feee91965c140ef,0xee6817655140fcf61975,0x655140faf6197655140f,0xbefea17655140bef6a17,0x8655140eef61d8655140,0xbefe998755140def65d,0x98755140eef699875514,0x40befea1655d140eefe9,0xd9855d140befea5655d1,0x140eef619855d140f6f5,0x65b855d140eef659855d,0xd140f6f5d9955d140eef,0xfe19955d140eef619955,0x5d140def659955d140ee,0xef61b955d140befe9995,0x65d140f6f695765d140d,0xeef695865d140f6f6a17,0x7659540ddfe617559540,0xdbfe617659540fbe681,0x17659540ebf6a1765954,0x40cffe618759540ebfaa,0xa19759540cffaa587595,0x5409ff69f98595409ffe,0x661865d540edf619855d,0xd540cffe61865d540cff,0xf6a5865d540edf695865],#[0x5d540cffaa5865d540cf,0xffe99985d5409ff6a396,0x6615409ff69b985d5409,0xaff6a17661540ebf6197,0x8761540affea17661540,0xcffaa57661540affe99,0x1905d940cff6a576e154,0x40dfe655905d940feee9,0x89955d940fbe619905d9,0x940ebf619955d940bfbe,0xa61955d940cff661955d,0xd9409ff6a3955d940cff,0xfe91985d940ebf695865,0x5d940eefe91985d940be,0xefe91985d940ebfe9998,0x85d940cff695985d940d,0xaffe958761940cffe959,0x9561940eefe919561940,0xaffe9d9561940cff65d,0x59761940eefe91976194,0x40ebfe999761940affe9,0x819561d40cff69597e19,0xd409ff69b9561d40bfee,0x6599561d40befe919661,0x1d40cffe599561d40cff,0xf65b9561d40affe99956,0x61d40aff69b9561d40cf,0xff6979661d40eefe9196,0x45c150fbe659645c150c,0xf7e659745c150bfe6a56,0x945c150f7e699745c150,0xbfee99945c150dfe659],#[0x97455150bfee91965c15,0x50edfaa17655150fcf69,0x957459150dfd61f91591,0x150eef6a17459150fcf6,0x6a17659150eefaa17459,0x9150ebfaa17659150ebf,0xfaa19759150cff6a1975,0x5d150f5f5d9955d150cf,0xdf659955d150edfe1995,0x65d150e7f661765d150d,0xe7f6a1765d150e7fa617,0x865d150e7faa1765d150,0xaff6a7865d150affea5,0x1965d150cff661965d15,0x50affe99985d150cffa6,0xa576e1150aff69a985d1,0x950cff69d96e1150cff6,0x661945d950ebf619945d,0xd950cffa61945d950cff,0xf692985d950affe91985,0x5c160cff69f9461950af,0xbe655645c160fbe61564,0x45c160f7e615745c160f,0xf7e695745c160f7e6557,0x845c160fbe595845c160,0xefe615845c160f7e5d5,0x5945c160efe657845c16,0x60dfe655945c160f7e5d,0x817455160bfee91855c1,0x160faf6997455160fee6,0x6a17455160f6f61d7455,0x5160eefaa17455160eef],#[0xfea19755160bdfea1755,0x59160faf61574591609f,0xaf6a17459160faf69574,0x559160f9f6157559160f,0xbbfea17559160bbf6a17,0x8559160ebf61d8559160,0xbbfe9d8559160dbf65d,0x58759160fafe91875916,0x60ebf6958759160bbfe9,0x959759160ebfe9587591,0x160fee611905d160dbf6,0x655905d160fbe595905d,0xd160faf595845d160dfe,0xf659845d160eef615845,0x5d160f3f61d655d160fa,0xbfe61655d160dbf66165,0x55d160bbfea5655d160d,0xe7f61d855d160f3f5d98,0x855d160cff661855d160,0xaff6a7855d160cffe61,0x9955d160bfee81955d16,0x60dbf659955d160f3f5d,0x61955d160e7f61d955d1,0x160cffa61955d160cff6,0x695765d1609ff6a3955d,0xd160f3f661765d160f3f,0xfe91875d160f3f61d965,0x5d160e7f695875d160f6,0xefe91985d160e7fe9587,0x85d160eefe91985d160b,0xdbfe99985d160defe919,0x6561160f9f5d56561160],#[0xbbf69d6561160ebf61d,0x17561160bbfe9d656116,0x60edf6157561160bfee8,0xa17561160aff6a175611,0x160ebf5d98561160affe,0xe957661160affe9d8561,0x1160eefe918761160bbf,0xf69576e1160affe95876,0xe1160cff69597e1160eb,0xbf61f9459560cffe9597,0x759560bbfe918759560d,0xebfe918759560ebf6918,0x945d560ddf617945d560,0xbdfe91855d5609ff6a3,0x3985d5609ffe91985d56,0x60dbf5db94615609ff69,0x9f9461560cff61f94615,0x560bbfe9176615609ff6,0x69176e1560affe918761,0xd960dbf655945d960ebf,0xfe999461d60bbfe91955,0x61d60bfee819561d60bb,0xf7e8d9561d60bfbe8995,0x461d609ff6939561d60b,0xcff6559461d60eefe519,0x9461d60cffe559461d60,0xcff6579461d60ebfe99,0x79461d60cffe579461d6,0x60cffe979461d60cff69,0x939561d60affe919561d,0x170f6f6997455170aff6,0x6157459170dfd6179159],#[0x9170f6f6957459170f6f,0xf6617559170f3f619755,0x59170ebf6198559170d7,0xafe918659170cff66185,0x55d170defe919859170f,0xe7f619855d170b7fea56,0x955d170d7f659955d170,0xf6fe91865d170b7fe99,0x97561170e7f619756117,0x70cffe598561170d7fe5,0x919661170eefe9186611,0x570b7fe91865d570befe,0x69994e1570affe918661,0x1570cff69196e1570cff,0xd695905d171cffe9196e,0x5d971f7d695905d971f7,0x6f5d9905d154f7de9590,0x5d154def659905d154f,0xf6f681765d154befe999,0x75e0564cff6839661d54,0x4def655905d164efd681,0x1955d164befe95905d16,0x64fafe91905d964befe8,0x95905d964dbf655905d9,0x964bbfe81955d964bbfe,0xe919061d64fbbe89955d,0x1d64cff6559061d64eef,0xfe999061d64affe95906,0x61d64affe819561d64eb,0xefe919561d64efbe8995,0x560174ebfe999561d64e,0xaffea16560174f3f5d96],#[0x8560174e7f5d98560174,0x4affe998560174cffe59,0xb9560174d7f5db956017,0x749ff69b9560174cff61,0x817659574befe9196601,0x5749ff6839859574f3f6,0x61b9061574d7f5db9061,0xd9749ff6839661574cff,0xf655905d974f6fe91905,0x5d974b7fe95905d974d7,0x7be89955d974b7fe8195,0x6e0165cff69590e1974f,0xcff69d90e1165ebf6917,0x97e1165ebf68176e1165,0x5dbf651905d965cff681,0x39461d65bbfe91905d96,0x75cff68196e1175cff68,0x518460176cff68194e19,0x176cffe558460176eefe,0x6179460176bbfe999460,0x176affe918560176cff,0x7e8d9560176bfbe89956,0x60176b7fe9d9560176bf,0xffe8185611769ff69395,0xe1176efbe898561176a,0xcffe9590e1176cff6959,0x4200009ff6839461576,0x20e01c2016c012a00ac0,0x3b203700310029c025a0,0x53804f60482044003fe0,0x664062c05ea05b2057a0,0x81207a8075c071a06ba0],#[0x97a0942090008a0085e0,0xaba0a820a4a09fe09c60,0xc360be00b940b480afc0,0xd9e0d520cfc0cba0c780,0xf740f140ebe0e540dea0,0xf010ae1058100c0fb60,0x2a8124811de118811321,0x44c13ec13aa135e13081,0x62215c21576151614ac1,0x7ee178e174216ec16961,0x99c194618fa189a184e1,0xb401ad61a8a1a3419de1,0xcc61c7a1c421c141bb41,0xe421dec1daa1d681d121,0xfaa1f5e1f081ebc1e7a1,0x11c20da2098204220001,0x298224221f621a021542,0x3f623a0235e232622d02,0x5cc25582502249824562,0x78e273826e2268c262c2,0x93228e6289a284427e42,0xa862a3a29ee29ac296a2,0xc2a2bca2b602b142ad22,0xdc42d8c2d2c2cd62c762,0xf0e2ec22e762e3e2dfc2,0x76302a2fde2f922f502,0x20631b03178312c30cc3,0x35a331832e032a832483,0x4f4348a343433de33a63,0x698364235e2359635403,0x83237fa379a374436ee3,0x9ae396c392038d4387e3],#[0xb343ad43a743a3c39f03,0xcba3c503bfa3ba43b6c3,0xec23e763e203da23d2e3,0x5c40063fba3f643f183,0x1ec41aa414a410840b24,0x39a433a42e4428e42384,0x5524506449c444643e64,0x6a6465a461845ea45a84,0x7f047b84762472046de4,0x93a48ee48b6486048284,0xaf24aa64a3c49e649904,0xcbe4c5e4c1c4bc64b5c4,0xe4e4e024db64d564d144,0xfac4f6a4f284ee64e904,0x10a50be507c503a4ff84,0x272523051da518e514c5,0x3ee5398534252f652a05,0x560550a54c8548654445,0x6c85686564455f855b65,0x85857f857a2575657005,0x9c05992594658fa58ae5,0xb325adc5a7c5a3a59ee5,0xc9a5c4e5bf85bb65b6a5,0xdee5dac5d605d285cdc5,0xf425f0a5ec85e865e445,0xb46072601c5fc65f845,0x19a6162612a60fc60d86,0x2946252621a620061be6,0x37a6360632862fa62b86,0x4886450641863f463b26,0x58c6568651c64f864c06,0x65e6630660c65ca65b06],#[0x762673e670666ce66826,0x848680667e267a0677c6,0x94c691e68fa68b868806,0xa6e6a366a0869bc69846,0xb7c6b586b166ade6a926,0xc766c526c246bf66bbe6,0xd8e6d746d286cdc6cae6,0xe746e3c6e186de06dbc6,0xf3c6efa6eb86e9e6e8e6,0x2270086fe46fac6f6a6,0x10870da70987056703c7,0x1da71ac7188715a71407,0x2c0729c7264722c72087,0x3a67378734a731c72da7,0x4dc7490744e742073de7,0x5f475c67598756a75287,0x6e476987674763c760e7,0x7de77a6776e773677087,0x8f678b4787c783a78027,0x9c879ae79807952792e7,0xab87a807a5c7a2479f67,0xbb27b7a7b427b1e7ae67,0xcb67c887c467c227bea7,0xd6a7d467d227cf47cd07,0xe327dfa7dc27da87d847,0xf047ec27e9e7e847e607,0x127fda7f987f6a7f327,0x10c80e880b08096805e8,0x1fc81c481a0816881308,0x2b082788240823082208,0x3e683ae8376833e82fc8,0x4ea84b284848456841e8],#[0x5ee85c08588855a850e8,0x6f286b08682865486268,0x7c487968772873a87168,0x8a0885e8826880287de8,0x9ae89628934891088d88,0xab28a8e8a428a1e89f08,0xbc08b748b468b228aea8,0xcec8cb48c7c8c308bee8,0xe228dea8d9e8d708d2e8,0xf088eee8eb68e7e8e3c8,0xc8fe88fba8f6e8f368,0xac9088906e904a90269,0x192915a912c90fe90da9,0x26e9240921291ee91ca9,0x368934492f892d492b09,0x43a942093f293ce93969,0x51694e894ba949694689,0x638960a95dc959a95589,0x71496e696b8969e96709,0x7fa97d6979e975c97389,0x8d698a8987a984298149,0x9bc99a29960991e99049,0xaa29a749a509a1899ea9,0xb889b5a9b229afe9ada9,0xc789c4a9c129be49bb69,0xd9a9d4e9d209cf29cc49,0xea89e709e4c9e329de69,0xfac9f749f329f189ee09,0x9ca05aa036a0129fda9,0x178a14aa126a0e4a0c0a,0x27ca244a220a1e8a1b0a,0x33aa320a306a2cea2a0a],#[0x416a3d4a3b0a378a354a,0x510a4e2a4b4a472a444a,0x986a5dca5c2a58aa548a,0xf07c2280f22c13f07c20,0xa130325911f145883fc0,0x8c0fc5a1346f07c0f08c,0xc1f082618960560f4445,0xfc0f07c20988f1a0ff03,0x7c0f08261fc6b140383,0xf07c0f08261c07f1a16f,0xff03c1f08261bc671616,0x2bf1647f07c224cbf1a0,0x7c0f08985a1503fc0080,0x4c608216857c57180ff0,0xf08261c15f1426f07c22,0x208213198801c8bf03c1,0xc1f088f84c603783f07c,0x64704fc1f082b2c16717,0x826185885bc008383f1,0xf07c20986f1856f07c0f,0x4f03c1f0829140322fc0,0x82619c4f03c1f082916c,0x7c20a4501dc6f03c1f0,0xe0c8bf07c214c871bc0f,0x5e0fc1f08532416a428e,0xc0f081c18942459091f8,0xf83f07c00747d1b47e0f,0x5a11f07c224cae1746d1,0xf08261c26046c0457c51,0x2245131bc440e11f03c1,0x83f07c284c905ec5f07c,0x85444c60605609911f17],#[0x602ff0b131415b0fc1f0,0x31a0bf03c1f08261e178,0x1b1c07f0413f08261416,0x8351419d1b47e13c0f08,0x1fc0f0821142670fc1f0,0xe1b44e1fc0f081b1ac6e,0x7d1a0ff01c7f07c206c7,0x870420f22fc1f0a13098,0x9884440f04e8bf07c209,0x181603f46b17c0f07c20,0xb0986b140ff03c1f0826,0x11f08261911f07c0f0a8,0xfc0f07c206c883fc1f01,0x4fc1f08261ec50460f71,0xf07c0f08961c1183dc50,0x3f0413f089628117160f,0xc2444a0611183c26f030,0x1825a0ff1415a13c1f03,0xf84847c071fc1f081b20,0x1014f02c5f07c2098943,0xf03c1f090f09860c50fe,0x1b1784f07c0f08262211,0x84047c1f03c209870601,0x21171fc0f07c206c8b17,0x47c0f0454f0826180fe1,0x823c043fc144fc20b068,0x8e100f845c5f07c0f085,0x1bf1784f0511b1fc0f08,0xbc5b1f8451bc1f03c228,0x1fc1613c0f0898560f09,0x613c0f0898574606d0fb,0x20988b1f4609a15847c1],#[0x231c167160f71bc0f07c,0x8291bc6717c1f03c2098,0x5bc20989a13c0f07c209,0x24c915c8bf1903f07c00,0x9bc0447c591fc103fc2,0x544426f07c0a13c2054a,0x16c0fc1f089325c6163c,0x3c1f08261c26717c0160,0x41bf0823250fe12c6f0,0xf09932e15043c691fc0f,0x43c8ef002a05ec5857c1,0xe71a15f03c1f090f2111,0x8ed1fc1f03c2a2c805c8,0x88ef0747f09931c15c0c,0x1b47f0584f03c224150a,0xf07c223e13250f06e11b,0x284c261e166402322e47,0xc1f0913245760c16f07c,0x8261c4ef000f82f83b1f,0x8113201845ac5f03c1f0,0x8c60628045b83f07c20,0xf0a0f2016d1fc1f0913,0xc244c80611671820f07c,0x8321f8305bc023b47f07,0x858282602d0ff07c0f0,0x581143fc505704f07c0f,0x9bc091fc1f081343cb8,0x3b1fc0f08916216047c5,0xc20dc407019e1346d178,0xf45f07c244c26141bf03,0x1d83f0345f048ff0b131,0x2238403b83d1fc1f03c2],#[0x6d1432d1ec6f07c0e0fc,0x8321832b1bc1f03c20a4,0x3c2718806c8ff07c0f0,0xf08291784e0c0ed1fc1f,0x6f07c0f08231803f07c0,0x2ad17c1b1fc224c771ec,0xc20f03c1d17c2a4c8400,0x1bc1d1fc0f081b1c2ae0,0xd181bf07c0b17c22004d,0x23b83f07c244c60d347,0x46613c1d1f83f03c223c,0x8350ad13f07c0f08613b,0x44c50d42bf03c144fc21,0x1f0346f08723bc0f07c2,0xc0f07c2c4c8e0d47e13c,0x784f03c21f470d00e017,0x7c0e0fc2234660f47f0,0xb1fc20ac5d184e61347f,0xef03c10b3c244c8d03c1,0xc0b1fc1f082b142a43c0,0x4c843fc1f0032f08261b,0x240ee0f47f03c1b17c26,0x43c9b45b47b1bc1f03c2,0xa043c1a2fc0f08261831,0xc8b1b03b1385f0747f08,0x56f0515f08d32315c40,0x1703f07c2b4cbe16c008,0x158905c15b001041c8e6,0x5e15f1b03f07c0083c2,0x671ac4857c1f03c20809,0xc4857c1f03c24408e141,0x3c1b13c0d1fc2201671a],#[0x29f07c209880b01504,0xf07c0f08262107b1ac4f,0x4f0347f0897101571829,0x8bf0880b015b188ef05c,0x2531c15042c6f0747f01,0xa531c1705bc1e0fc208,0x94d9015000a783f0420f,0x3f0420f0a531820f07c2,0x83c1f0a5364060a78,0xdc615b83f03c1f08201d,0x1c1682ec7f07c214d101,0x31b4471c0ef03c1f0a10,0xc254c771fc0043c1f0a5,0x5c7f08af000ee0ec7f07,0x59764248d1985d1383f0,0x5d9571f4692344f07c22,0xd19c7d13c1f09901d906,0x3d1b44e15c7f07c22648,0x20e0fc1f0853204807f8,0x3c1f03c2080906016e14,0x3c20b0505b8516383d1,0xd1fc1f085308c5083c1f,0x291423b1bc1f03c20a46,0x6c7f03c21f44f07c0f08,0x6c7f08531c16d1010f0,0xf07c0f08291b85e0c2cf,0x7d13c1f03c20b060b344,0xc6e0c0ef07c0d1fc21dc,0xec603b83f0747f03c21d,0x2017b1b47f07c0043c21,0xb016e0c8ef0747f0853,0x47078509383f03c29609],#[0xc4e0fc0f04289607097c,0x108083c0f07c20b05e17,0x1b46e0c0ed1fc1f03c27,0x2b10922346f03c1f0829,0x50b1c7d1b85e0fc1f03c,0x3c20a45b13c1f03c20a4,0xfc1f03c20806b1bc1f0,0x5bc1f00cbf08261ec6e,0x1b23c0f04cbf08261786,0xc8b1411456c4f03c1f08,0xac006d15847c1717c2a4,0x980ff0215f07c2444932,0x717c0f07c2098715bc50,0x5717c1f03c24448046c4,0xc5f07c0f08561c16b121,0x111f0456f08932411855,0x3c1f0a11221509818f0,0xf02c4f08805c8e456c4f,0xf0894201bf1747f0511,0xc215c805611f0747713c,0xd112411e1a15713c0f07,0x615043c491fc0f07c206,0xf09931fc0f0426f082c1,0x22451320150a88ef0747,0x1309874629025147f07c,0xa4b098715d83063c1f0a,0xa4b098626016f03c1f0,0xf07c0f08571898f07c0f,0x4b1fc1f03c206c760e4b,0xc906fc1f03c20c8501b4,0x740099c503fc115bc284,0x9bc5063c1f091184c944],#[0x447c1f08d7c4c515b400,0xc2f008f07c00b3c244c5,0xbc02218f1783f06c744b,0x58a44ac7863c184544f0,0x440fb141561bc1f03c21,0xb17c0a0fc1f09132d182,0x204c912d188542605a0f,0x81580f09bc5f0147f07c,0x11f038351fc1f0a13311,0x3c209884611583fc5098,0x9131c18046c5d13c1f0,0xf0891202ae0ec5f0747f,0x2080705b44462c5f07c0,0xc5f08801386e0fc1f03c,0x81b1c2ae1b83083c1f02,0x9132006d1347f07c0f0,0xc4c80d347f02c5f0783f,0x22034d1c1bf03c1b17c2,0x6e182686215f0544f03c,0x3c227c023b83f07c244c,0xbc513986d1347f0783f0,0xf08723b83f03c1f09131,0x6f08851f86e0fc1f0344,0x132045d1183d1fc1f038,0x88d1fc513b83f03c1f09,0x557b1014f07c071f83f0,0x451871fc1852c4f03c22,0xf05c7b13c0447c21c314,0x7b1383f03c1053c22614,0xc0e0fc1f0857203703dc,0x3c1f0383f08a045c4853,0x8571c4e0dc0fd16c771],#[0xe0fc220117101bf07c0f,0x20a46d1437d1ec4f07c0,0xc0f08371037b13c1f03c,0xfc4d1fc0087c2a44606f,0x1745f1347f07c0a44221,0x1f082c1b86f03c1f0829,0xc00b3c2098626026f03c,0xf4571fc1f08932098f07,0x4426f03c20dc583b8305,0x20d45c4618f03c20bc54,0xc1b13c0f088042c5f07c,0x26f0837151126d18d1f,0x4786f13c0f082f1d11f0,0xe1bc4b17c1f00302318c,0x703bc1f03c2b148c6311,0xc1e0ec5f03c22386e0f4,0x3c1e0fc2714a03b47e1b,0x9951d976564861f46d1,0x2545329c592344d1bc1f,0x9a16047c5d0018f07c2,0x6e0ec5f0787d13c2f00a,0xc0f06c5f095321520394,0x7c0f083209860c783e1f,0x1b83f0544f03c22417f0,0xb13c0f0b87211626e18b,0x1153c20986d182cd17c1,0x45f07c0b13c226c4f03c,0x3c1f08261c2cd1837e1f,0x1fc0f07c21c1771346f0,0xf07c0f08311b4603b83e,0x3e1fc1b1bc0f08871b45,0x45f07c284c261b457138],#[0x816717c1f0b13098605b,0xc4c7b0fc1717c2083131,0x3098685a17083c170fc2,0xc2c4c261818d17c1f0a1,0x7c1f0820c4c6061c5f07,0x5c20f05c3f0b131ec371,0x85dc1b17c2c4c261a188,0x261e16f07c0f08580986,0xfc2201785bc0f0bc1160,0x4c6456c670fc1f0017c2,0xf0913102570424f0826c,0x706fc1f03c2b18809bc1,0x84e1bc1f08d71c32e134,0x41ad03c107fc221c3c23,0x7b40f07c207c8e1b8471,0xf0416f09132386e11c30,0x3f07c244c6b16c309a0f,0x1782fc1f08351bc083ec,0xbe03c10cbc244c6b0c,0xc26f1491f0418f0a132,0x5dc325018f0bc184c87,0x7b0fc0847c1f091319c5,0xc6852c5e0033863c2c4c,0x8351ac586214f07c244,0xf07c20d4544ec3f03c1f,0x3f0313b17c28d4844fc0,0xe0d3c1f09131c338bbc,0xbc00cbc1f09132116f00,0xcc6f07c0f0890d11803,0xb17c0f08826020e1215d,0x2150261f4303b84f0787,0xc2258261d18b0fc1f03c],#[0x7c0f08261c17463c0f07,0x9bc209f131345e1018f0,0xe13c21fc109bc244c40,0xc0f08321b4561f46f07c,0x984f07c0f08905c98f07,0xbc0860845820b0e15d1,0xf08371617c5833b1589f,0x7d0fc1f09931c1745bc0,0xc7f03c1f081b1a1403ac,0xc14b0fc1f01c7f088e1a,0x5814f05c7f09131f4465,0x71f44f07c0f082c182c0,0x570e14d13c1f03c22607,0x3c2070770f44f03c20dc,0x67c20846e1b4706dc4f0,0xf07c0b13c22386f03470,0x1f03c20806e1837e1747,0xc1e1fc0f081b1b86b0fc,0x6c6f0787f03c206c6b13,0xf083219c3d13c0f08371,0x4f03c20bc670f46f07c0,0xc1e1fc0b17c223118634,0x313b17c28d48d0c0ee1b,0x18c50980f1833a5343d0,0x508c34468b098305a0b5,0x826141b84d100b0484dc,0x310aa13149784c8b0c,0x6b1411185443c260c187,0xc7141008c20620f6102,0x10c00a446181b0420f05,0x1e10606d0fd1830c8c8c,0xc83038410370a41b308c],#[0x8c2842c008d13b14506c,0x31a10a2ac5b000b15460,0x100503098110401431d1,0xb0509a85610c7a10509a,0x704260dc50981011ac50,0x3060167002a84c515213,0xd8a701c5d187c11c506c,0x8443d19c509830c82908,0xc270784181b62c285484,0xac47178409830dc29099,0xf1c1b43f470c8a719c00,0x2614574458a7001bb150,0x5c00ac23141883d84b14,0x840290a10620170d8ab1,0x9351fc00ac6099840a43,0x19c01884846150c2d08e,0x42f45098515d121390a7,0x646dc004c1103c584c91,0x8450c35323033004e114,0x44582945b002b130313,0xe11703718584a0ab1ac0,0x2b429c67011bd1470584,0x1d0f151b059c6d1440d4,0xf1c2084f830c1b84c8e1,0x23142682e0ab002371a0,0xe8070113190a7020b0ac,0x71867003444c32408e81,0x360017142605c0b05a83,0x440c91382e83111382e8,0x140b44c320e83701130d,0x5704371112429c67002a,0xa91f04700340c4715dc],#[0x82c08e1351fc00ac7045,0x9a1304458108f06c20b,0x8084d0ed14584d1b63c3,0x141bb1c584d0ed1430ad,0xc7081b0745098246d469,0x8570398a7020b08c606d,0xb18405e8a522c0502c61,0x7f0023a4c2a180ea2ac0,0x305d4250693f0050b94,0xc9c608320a4203a93f0,0xbd01c008c93180e7182,0x30a323403000ed14643b,0x91f4031c5c2b4003b451,0x8293129308020530a,0x4dc10dc48551384430a9,0x3860351dc0045131026c,0x4515113b058005c5c4f8,0x40eb143b0580c4c0eb1,0x384d47f002b183406c2b,0x2b1011d1d1323c40b82,0x14340afc044c40d113f0,0x3717c018350c42a44fc0,0x1303bc07144039c27071,0x70530a31d45d000e1b,0xb1470b82a08c0eb1513f,0x71c603a8a62ac0700c7,0x13f002b102d0b023c4fc,0x2b1313f000e71440d5,0x5b150f100e08c20d513f,0xc306c1812040b14506d1,0x2ac0700c6b1474583143,0x571840528ab00303a8a6],#[0x140398a315c0143203ac,0x931426320c07183114,0x4140e60dc50c350c42bf,0xc023b851811c1ec0e14c,0x6103138509850acc8c1c,0x142016016440ca700604,0x23b070c26c1d8531285,0x9c014c40448ec1c8b101,0x6559071c494c20091043,0x8094c502f4060e531197,0x4c50834094c30a423d01,0xd018094c40a582607409,0x530c1060981f02531420,0x42005c1671a83140ef02,0x54e8316170595382c901,0x962086600231490039c0,0x182607441820910860c2,0x82062180d1040b02908,0x8094c40a65308c394c20,0x8d530c0eb02530c10b01,0x20b2530a430815308290,0x49023907b0053142c0a4,0x60253101060981b02531,0x2054c20b02954c303ac0,0x1ec0052c4182c839c70c,0x61510b00297144044105,0x11714291110716c40b02,0x457e19c512c32098609a,0x716111c8cb12c04502b1,0x51c2b145783e8cb001b,0x9c50985440290a8cb12c,0xb0309a860a4305911a1],#[0x503c2684d451585041c4,0x24b0983059c004d1b92c,0xd1430ad8084d0ed14526,0xf400b0506c106c184d0e,0x4d83d004b0c8545213e0,0xa815d01c00d11184c78,0x44141404283d00c7d106,0x340303441429308c1d03,0x1783d00c791144141b32,0x3d002c161444f8350010,0x4486044d02111014b148,0x9c1d0344174013b4471,0x3f00351c15d014b0c297,0xc003d1310320b9c184d8,0x1442511383dc5098551d,0x26c1304783143209b133,0x13244484ec00b08e12c0,0xc6063440989112c0700,0x117830c355214013845e,0x2c098911613183830c4e,0x3ac513830b0260c94d10,0xac4c200c0eb142521400,0xe83b14321457c4c4b0c2,0x4ec5a0dc00c84e182015,0xeb14509857b168302c54,0xc4a0c0eb143a0d80c4c0,0x51c160f441c341204006,0x52a47700341826060170,0x150d44b0018a0c40440f,0x426715c2707441e18062,0x1591315c5d10260c2c0a,0x40c42bf0113141805783],#[0x42a44fc0102af00350c3,0x5e1213a0cd1183d0070d,0x1d000f1a0c317400ac41,0x4420f40b14784a0cd10c,0xf0cd1340048518212833,0xd106c334015c0e31c543,0x303441817c30c230740,0x4044cc70ac403b0c3234,0x416c308631483d002c1f,0xd002b0a1283344d00231,0xc1170c02e47d00c77146,0x9c2705c514322521360d,0x461454444039c5082c03,0x451c181384b713831431,0xd4b10350ad0c711c046f,0xa424511004430601146,0x370a5c40c14710100c37,0xb04050930b0306dc408,0x2310370a6c40c1691644,0x40b91c45038485093e0c,0xd6131432d1583700931,0x110c1444c370dc1b0183,0x1c406d15b15111118b11,0xc5711b17471b18c5711d,0xc00ac30c41bb14306f18,0xa8c709c1b00c5b1070d6,0xafc024c4a300bb00303,0xc40c0e02cc5709c11435,0x142039c2705c5100e316,0x4b1440dc2c0a5c4100e7,0x1c5104a700350c31099c,0x1897717400a4465d9564],#[0x354c605c1602f4060f46,0x4013ac51a1b062c5d028,0x297513400a440d548a0d,0xe0f4084455214003ac51,0x830835e0fc00ac486044,0xc35102685d440a44083,0x8854305dc60c83529c0a,0x46a0c26914c551061121,0x11440c1613a8340ec515,0x643f835104e0d4408149,0x40e1018c0c4e12f45151,0x1031329c0718402e4611,0x29180e71020c4cc701c4,0x9c10a460c820621c5600,0x984714260837081c570,0x5a15c044c3510c6a140f,0x30b098303c0b23b8544c,0xb15c3160e038030c8416,0x8e0cc3e03130cd7354d0,0x31302cc3e00321780c4c,0xe00c3c4c4e0218845131,0x80c4c423b807171311c1,0x214c4cc1e0036141730f,0x31713b0c70ad13f00351,0xc4c0e7144039c1b01c0,0xb1370c40ad13f003513c,0xb80e306c5f03131fc00c,0xb80ef0437f01131c378,0x40b80eb17c1f01131c34,0xc591420d0c315026083,0x1140e90c5098c6915469,0x264c11038c50c8505193],#[0xc590dc064c0e1984080,0x24c40444008193b14505,0x15158409818143143d16,0x81790c320f13081c30c1,0xa4c30464530dc064c321,0x8430c62121586030a423,0x1c5e10200c26315c1a11,0x306c50d850981730c371,0x50c80e629c0714508217,0xc2c71c346f437038524c,0x70c30c49884c91e1450d,0x131685701130d440dc2c,0xa420ddc3081122c8ee15,0x50d6c024c30c82908370,0x51824c302e43b029350c,0x129302c4550dc1038644,0x8c5711d0c403cc564c37,0x408318c5711b17431b1,0x4c31082c51020456c546,0x6c4c603e45d00c5c4c56,0xc2705c51694038c1d003,0xb029a4c3039c50837039]]
def g255H9 := limbs80 #[#[0x61b80002018000a03,0x421e80c0004060e00c,0x4200104004000111004,0x8200100074de35078,0x1000047a120080404030,0x61d0d814040b0602c081,0xc01070685c020e0104c1,0x834000c0181808020387,0x1a2018004c0a806140b,0xb9622e7757c0050ce000,0xb7a49f0cf4000498887,0x34060002220001dd200,0x4550002856000b6980,0x898938c508048001e2e0,0x287397506c26f44d4823,0x217ee0bb2746bb000cae,0x902c00974f6935ade189,0x688a5264000c32388118,0x1818f4a2344000e6217,0x819c1d186ece00011080,0x26a5808a011f469d8,0xa86a16ac7804c835c08c,0x69b6ac7c055b65d7a4fc,0xa668023dc2f476a0eaaa,0x5b46dc5e91f6bdb936c2,0x1c50211e008044366b70,0x8d5463b09d5d616263b5,0x8b5e1d2a135d46740003,0x9c8749c8fb0000000d71,0x4d393141c44dff8b6428,0xeeca1a812efe05b369d6,0x1d28a0004ca55962e2f6],#[0x2b0cbc0010e3d7200010,0x17960c941aafc001c077,0x628c00000022e5865,0x34ca000b575114000313,0x87366bf4cb66e1785800,0x3a3e000000000000064,0x8553cc98347aae664c80,0x2008c53ee1c88d08a46,0xf06945b2ae10392322ee,0x324000062a6034000,0x1309927dbfb2d533,0xec0e3e2102e23f000000,0xe7aee279992de368a7d3,0x9580029672ac97c0001c,0x18dce761853d6f1339,0xe36a240001516346d1d4,0x8e35ae83393c631192f5,0x48cf9c4e1ff366664c9,0x24d0000000000150d23,0x1420000d9800,0x8ff48e29855450eea180,0x70a80000016c80002,0x800152cb3bd693a98000,0x24f0007b1400001ab3b,0xcdc2a5cae88d5a1893e1,0x752be1a0d3cb926000e5,0xe3bf84df91433482c12,0xa4ae257632bc1523eade,0x2370492912802000784c,0xe52e2a10000000000000,0x50916889e58c5334f60b,0x550feea013808b41b0c0],#[0xa51190ca8e3dd0ea6102,0x4f1c3e0f79a11b82d3f6,0xa4ab9c5b2706ee41713f,0x7cd0000ea4b78eb54d45,0x72820004305822f35000,0xcb4fe19a2bb160798d86,0x2be0f52acb2a205b0097,0x2ce2480000000000b3fa,0x1d6e7bc10f23a1a80004,0x2060000003]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xb6ae8b8a81db9745c140,0x7abb2e2b075e5d570543,0xeaecb2ae3db57455171e,0xebb2e8b24fd65f815939,0x2a8b02813ef9261d65e5,0xb2ac0a07ee5d160503f7,0xeb0281ef97658140f7c,0xbac0a06fee1d605037f3,0x8b82817fb9758140bfcc,0xae0a077e5d570503f72a,0xb8281bfb855c140dfcc2,0xe0a06fee19705037f30c,0x8a81fb5545c540bfdcb2,0x8a06fde15715037eb0ab,0x281f3d7555140f9eb2aa,0xa06efe1d5450377b0eaa,0x81bbd855d140bdecbaa8,0x5efe557450377f0aba2,0x1bbd865d140edebb2e8a,0x6dfe156550377f0cba28,0xb7d855d5409fecc2caa0,0xffe59855027fb30baa81,0xfd96e15409ffcbb0aa04,0xf619765027fb2fc2a813,0xf95619409fecc2eca06b,0x657865027ff2ec32813f,0x9561d409fecbf0ca04ff,0x57875027ff2cc3a813ff,0x45c1509fecb70ea04ff6,0x170543bf2e8b82a1f795,0x5c150dfcc32e0a86fee1,0x71543eeaa8b8aa1bfb86],#[0xc550dfbc22e2a877d5d1,0x15437eb0cb8aa1df5765,0x150f9eba2a8a86fde197,0x5436ff0caa2a1b7d8655,0x50dbfc3aa8a86df61d54,0x42fef22b22a177d97551,0x9fecb708a86df5d7845,0x2eff28baaa13fd97e115,0xdbfc32eaa86df6197554,0x7fb30bb2a1afd865d950,0xffcbb0ca84ffe5186542,0xfb2fc32a13fd94e19509,0xfcb30ea84ffe51875427,0xb2dc3aa13fd94e1d509f,0xba2e0b07be591705827f,0x28b82c1bfb845c160efc,0xaae0b07be59570582ff7,0xab8ac1bfb855c160efcb,0xaa8b06fde1571583deac,0xb22c16fd9655160f3eb2,0xc8b06bf61d64583d7ae8,0xa2c16fd9759160d7fc3a,0x8b067f61d745839faecb,0x2c1afd76e11609fecaf0,0xb05bfe51655827fb2fc2,0xc1afd8759560f3ebaaca,0x5bf65d655835ff0eb2a,0x17fb905d560b7fcbacab,0x6bf5db855827fb29c2ac,0x6ff945d9609fecbf0ab0,0xffe5187582dff2abb2c1,0xfd94e1d609ffcab0eb04],#[0xf5d1545c27fb2bc3ac13,0xd9755170ebebaaa8b876,0x5d1645c2fef22b22e15f,0x865d170affcaae8b876f,0x5b845c27fb2bc22e19ff,0x559570ebebaacab84ff6,0x3855c2bff28baae1b7f8,0xe19709fecb70ab84ff65,0x745c67fb2bc32e13fd94,0x9571efacaae8b8f7d641,0x65c7beb20bb2e37f7905,0x154bdfc82e8aa77d6557,0x553b7aecba2a9f3d655d,0x54bbfc82caaa6ef61974,0x536fb0eb2aa9e7d76595,0x4bbfcbacaaa5df65d655,0x36fb0cbaaa977f905d55,0xd7ec32ecaa5dfe597555,0x7ff20c32a93fd985d954,0xffc830eaa4ffe5d86552,0xeaebc0ac93ff9661d549,0xfc830eb25bfe41765937,0xb2bc02e93ff9561d649f,0xbb2caba4ff65b805d27f,0x2dc2ae93fd90e1574e7e,0x870cba57fe41765d27fb,0x9c02cb3fd95e19749fec,0x700b2edf5d7805967fb2,0xc22cb3fd97e0165d7ebb,0x8b2edf5d7845967fb21,0xaacb3fd97e1165d7ebb7,0xeb2dbfe4176596eff28b],#[0xacb3ff9061d65bf7c930,0xb2cffe51875977df24c3,0xeb3fd94e1d659fec870e,0xacff65b805d67fb29c02,0xb3fd96e11759fec8708b,0xcff643865d6fdf24c32e,0x3fd94e01769feca70cba,0xff643845da7fb2bc02ed,0xef92615769fecaf08bb4,0xf653855da7fb21c2aed7,0x98558140ffcbaac0a04f,0x61d60503ff32ab0281ff,0x655c140ffccbac0a07fe,0x5570503ff30ab8281ff9,0x65c140ffcc32e0a07fe6,0x954503feb0ab8a81ff99,0x55140fdec32a8a07ef5d,0x74503f7acaba281fbd87,0xd140fdecaae8a07ef615,0x5503f7b2cba281fbd865,0x540f7ebb2caa07df5d56,0x5037ff0eb2a81bfd8759,0x40bffcbacaa05ff65d65,0x2fff30b2a817fd98595,0xdfec32eaa07df615755,0x2fff2cbaa81bff865d54,0xbffcc2eaa05ff6617550,0x7fb0ec2a81bfd8661540,0xfebb70aa06ff5d985503,0xff2abb281ff9905d940d,0xecc2eca07bf61976502f,0xd30bb2817fd985d940df],#[0xc3b0ca05ffe61765037f,0x2ec3281bfd9561940dfe,0xb30ea05ffe55875037fb,0xac3a81bfd9561d40bffc,0x30ea06ff659875037ff2,0xb82a1ff9645c150dffcb,0xa8a87fe65970543ff328,0x22a1fbd7459150fbebb2,0x8a87bf5d964543efaeab,0x2a1bff8759150dfec3ac,0xa87df65574542ffb2eb2,0xa1bfd865d150efebb2e8,0x85ffe59745437ff0cba2,0x1bfe985d150dfecc2e8a,0x5ffe51765437faedc22a,0xbfe985d950dfecc2eca8,0xffe5186542fff28c32a1,0xf9845c160ffcaa2e0b06,0xe61570583ff328b82c1f,0x5855c560ffccaae0b07f,0x5d554583f7ae8aa2c1ff,0x7655160fbec2aa8b07df,0x1d545837fb0eaa2c1efd,0x855160bfecbaa8b06ffe,0x564583dfaeab22c17fd9,0x5d160f7ec3ac8b07bf61,0x74583f7b08ba2c1ff990,0xd160dffc2ae8b07bf595,0x4583dfb2cba2c17ff955,0x160dfecc2e8b077f61d7,0x5837fd30ba2c17fd985d,0x60f7eb2b08b05ffe6174],#[0x83dfaecc22c1bfd85611,0xdfebaf08b06ff61d845,0x2fff28baac1efd875956,0xbfecc2eab07df6157558,0xfff28c2ac17ff985d560,0xfec3b0ab07bf5d985582,0xfb28bb2c17ff9761560d,0xfca30eb07bf65576583d,0xb28c3ac17ff9561d60bf,0xcab0eb06ffe51875837f,0xeab22e1bff9561d60dfe,0x32c8b86ffe15645c3bfa,0xaba2e17fd9859170f7ec,0xae8b877f615745c3bfac,0xba2e1dfd865d170efeca,0x8b877f5d5845c3bfb2c,0x22e1bfd8661170dfec2b,0xab85ffe51655c2fff2cc,0x2e1bfd8661570efec32e,0xaa7ef64174552fff28c3,0xa97ff905d954fdecb2e8,0xa6ff66176553efb2abb2,0x9fbd905d164dffcb30ea,0x5ffe4175593f7b2aba2c,0xefd955d964f7ec82ecb2,0xff655875937fb20c3ac9,0xff9560174dfec2b00ba6,0xf619805d3bfaecc02e97,0xd65e0174bffcb300ba6f,0x615655d2fff20b2ae9bf,0x9859574bfecc2caba7df,0xd9855d2fff20c2ae97ff],#[0x661574dfec330aba77f5,0x5765d3bfb20bb2e97ff9,0x5d965bffca300b2f7f65,0x87597dfb28bb2cbefd90,0x1175dffca30eb2dffe51,0x5dafff28c32eb7ff966,0x176bffca300bb6ff6118,0x5dafff2ac02edbfd8560,0x76bffc830abb6ff61584,0x2fff28c2aedfef92615,0xffec32eaa07ff61d655,0x3ffb2abb281ffd766154,0xffecab0ea07ff6617650,0xffb0eb22a1ffd9661d40,0xfeca2eca87ff65974543,0xfb0aba2c1ffd8755160f,0xecc2e8b07ff65574583f,0xb28c3ac1ffd7561160ff,0xcab0eb07ffe5187583ff,0xab22e1fff9561d60ffe,0xa30cb87ff659845c3ffb,0xbb2a9fff9461970ffec,0xb00ba7ff64175593ffb2,0xc02e9ffd9560174ffeb2,0xbb7ff651805dbffb2c,0x2edffd9560176fffca3,0x7e009c00ae0003fff2ac,0x99c11101cb02fa05040,0x807fe0ec41a402fa0558,0xe985730a5c141024d846,0x1d4038a06bd0ca818602,0x5112e212440687d10f2a],#[0x358a1d139e25e049088e,0x2fa05d60b7916562b085,0xf1a8233f06648c8d186c,0x860ed91d1639606fc0d8,0x429082b101a1f743d8c7,0x23d646e08b9913721ae,0xc9135625fe4ac493f123,0x5340a4a144f28264f809,0xe2c7657fcadd156c2a2a,0xfe97a62e9e5bbcb59966,0x6534c8418cc310e612cb,0x8358269a8d0e19c53300,0x461c5038046f3cdb31b1,0x7824ee21d6439f672fce,0x13f667d94f991ec93ce4,0xc8213041e88299027a00,0x8bc9156a25f444687550,0x8490290cd1f2a38e4680,0x1d25e34b18954128ea4d,0x9dbd39526e54d5299b53,0x851d8a29d42827f04f68,0x452a455400a7114bb292,0xaeb55c1ab4755f2ab195,0xe59b2b2756352c2557c0,0x1c2e055bb6b6356a8ad1,0xbeb17b82f2b5da8b9f57,0x76264c3b584b30485fe2,0x51b267647ac7e18d0b17,0xd05d9e93384666ccbc59,0x96b04d4d1a7c34bc68ca,0x9936ed6d50d9d5b1835d,0xe22dc1eb8016f78ddb9b],#[0x473fee6c5cb6391e718e,0xf2bb7c764aeb81d3bba4,0xf63de933cd87914f115d,0xa7e2afb1df413e467bf0,0x8b40bf80d10021fd43f5,0xa4e12bc2098389056e0,0xb888d0fbe1bec32685b1,0x8c5c38afd149e271448,0x1eca3a946e98d3719363,0xc92dd245e452c8609037,0xaecafd9571296250549b,0x33fa6614c6298172eae5,0x59d8739fa7064db59aab,0x625076a0633fb27c64f3,0x492a8f9d1a5a2d344928,0xea7594d0e97f52cba531,0xd6d55faa475356a3f541,0x5c1ab5c567cac6f57caa,0x2b173618ac05d7abae97,0x5d5a6cb40766d6cb8592,0x716ee06dbc8b7076c8ed,0x7bc53776eec25d24b989,0x155fc1bee77c96f675e7,0x882b0d56141c1c3822b0,0xfc7b18e07190e2afc4b1,0xf1658bca69932f235e42,0x9e9f3ace702cd4598e72,0x9d321a4c3468688bd069,0xa4eb0dd591aa33523e9f,0xb3876456c45d7ddae3b5,0xbdd05b8d36ea6d8fda83,0x38f02cdfe1beaf7aeeee],#[0xc7bb8c77140e1e5c2b78,0xbe6fbccbf97e7293e467,0x9ff4d6e923d133a03f3c,0xdbcbb56f644ebedd65ba,0xef073dff7bd7f785ee93,0xe77989f29be423c66787,0xec0fd567a70f469e82bc,0x6f871f03bde07b96f6a3,0xe27d7ffa99f467e65fc8,0xfbe7f67fe93fc9df803e,0x5818541fc1e07089fe8f,0x142d83e0f0826385b8dc,0x170a8411dc0e0f08a47f,0x71707c1e104c703f1b88,0x1c30b7078413258c910c,0x4880a818e1d1783c2099,0x101fe2f0d8f86c270784,0x238602dc5e1f0784131c,0x9a2c8c2f130d47e07084,0x8413238111e383f83c20,0xe104cb4b03f8b1163f07,0x1b07f00a811e3c3d17c1,0x960230fe2b1f83c20990,0xc0fe2e118fc1e051b845,0x5a158fc1e10ac50ac452,0xb011e2d198fc1e070b08,0x4261d8fc1e10ac40ac3c,0xf091657198a0fe07078,0x4c383c37c62bc3c2bc0e,0xe109864401d17c1e0708,0x78347e124cb62f041fc0,0x20793150883f802015f1],#[0x4c6107162b476370781c,0xc209a2c7e289b83c20aa,0xf078420898c8fc1f068f,0xcc5e0d1f848f898c0dc1,0xc20d900f81f078413130,0xf084c471a090fe031f83,0x3c2130c1607f1a8bc0e0,0x3f0383c20d934507f038,0x83c0e10809e300c170f6,0xe070840401f8d048b60f,0x781c20b11c662c581fc1,0x163703844f1a1f8362f0,0x1f84132f8a588785b07c,0x44581e20e0717062be0d,0x8a20e2c5a8fc1e103c26,0x3c2898806c1f07842089,0x1f038347e10388c18038,0x747e0f03840e251184c,0xe07078493118c0803613,0x10ac7e0f038420118a07,0x81c210100803f028bc1e,0xa3f0826581a8b84c1f07,0xca2c04441c0e2e0c57c1,0x8ac1dc0e2e0e8fc1e144,0x856460f83c21044c51a,0x20898a0e0401780c7e0f,0xd1b83c0e103c9c1f0784,0xfc1e07081c48c41cc7e2,0x37038431280cc5c260e8,0x8423181d83a3e138bc16,0xa3f07842b201d47e0f03,0x7808be10985070200a00],#[0x62b4402bc1e070916570,0x1d89c1e070852304041c,0x45c281d8dc0e0f084c38,0x1a3f08a63b1b81c1e10a,0xf0bc1e114c84822f07c,0xc1a3f0920531720202b6,0xe404058c2e0f83c22991,0x8914861707c1a3f08a64,0x20201b47e0f08a690192,0x14c5e3110ad83e070784,0x7c1e1040a6360f83c210,0x18398fc1e070a163f021,0x387a27038210e10806c,0x9c1e1134463f038383e1,0x10408c871f0b462460e8,0x20531c1c9763d1383c0e,0xe07085230b381c7e0f08,0xd89c0e0f0852281a89c1,0x52331b07c0e0d1f840e1,0xe0f084052218dc0e0f08,0x81c481c8d85e216307c0,0x3270a04a351f07c0e0f0,0x2c077038f83c2f07845,0x36140946c1f0383c2101,0x70852381f81c1e114c46,0x3c0e10a46040128dc1e0,0x231b83c0e10a47033138,0x807e0f038420118a080,0x3c24992046304381c1e1,0x124c8133022a11e2d1f8,0x84112423c52b4442bc1e,0xa9220e2c568ec4e0f03],#[0x880889b8b866270781c2,0x52c29c46284781c1e109,0x81b2bc442bc0c370784c,0x132023c1e07084c28478,0xc4c64a2458b47e0f0b06,0x3c209898562f068fc248,0x590007c1e104c4c312f8,0x81c52b44706c7e0f0826,0xe2e0d8fc1e144ca13046,0x58fc208c4c70c0468026,0x563f0707c2099626a070,0x1381c22431110df006bc,0xc2a2165648f143183e0d,0x30560aa478b83c370781,0x411099183e0f08411314,0x7082240838a9863f078,0x841409900e63f1689c1e,0xe0f08364f1f8111c1f07,0x78426220dc441c4780c7,0x1e109860c0478945e070,0x1f81c1e106caa284781c,0xc1e1098788c1a8bc401b,0x70383c22b9111e205381,0x145e0f0856324507c4c3,0xc31e8bc1e070822401f8,0x986c1f0781c2100fc44,0xdc478b83e0f08301320,0x78911c1b1781c1e10608,0xee2e0e8f86e0f0384c42,0x130d83a3f0781c207100,0xe040140147e0f085640,0x8130d83a3f0781c20712],#[0xbc62585b83c0e1098762,0x4be10986e070497c2130,0x12307c1a2708901f0382,0xd83e0f08a64e578b87a3,0xb7078426144d404af142,0x8dc5137078415298dc00,0x1c20a8e0ea270383c214,0x70784261f8a26a27078,0x8dc0e0f081c38510746e,0x1b1381c1e10a46c3e0e,0x30787e37078145e10c4a,0x3c3b1b83c0e151490731,0x9a8dc1e07082a383b898,0xc80751b81c1e10a46e28,0x3206215e2b0c2dc1e144,0x4c61305f861662f07851,0xc1e144c761e1f83c22a4,0x6385c1898e15e2b0c31,0xa16e0707842619861713,0xc1859016e0f082626170,0x4c4c316386166370385,0xbc1e144c4c22000fc1e1,0xc1e106c785f078413130,0x42f85c10d8f8463d1b81,0xdc00a7078426168cc7e0,0xc20d8f84e070784170d8,0xf082e9315100be07068f,0x8003f078413130d0be0,0x20228d47c270383c20d9,0x7078513130bc1e144c4c,0x206c251f83c0e106c7e0,0x3e101dc3e0b1b81c2191],#[0x86c7c34218b84e0f089a,0x1360187c1e1062263b5f,0x106c70701587c1e10d46,0x81c20712c5c251f81c1e,0xe10d48033170987e0d0f,0xb830b241c080280287c1,0x20d8e204b1538618e070,0x784351c0d84c3f0781c,0xc3e0f086a20200600a2f,0x83987c5a370781c20b12,0x984c3d1b81c1e106c718,0xc10a7083637078493130,0x50c29c0e0f084c431f81,0x8c70a70383c20d8e98e2,0x670187c70a7078513200,0x1c9763d1383c0e105081,0xe470d30c7e0f0828131c,0xb92c7e1f0429c0a27086,0x60745387866270383c20,0xdc506c286381c1e1098,0xf83c0e106c80e51f81c2,0x70df03841c270a04c351,0x189c21b9385e20070d4,0xc1e10807a383b0dc3e0f,0x7078493130a046185381,0xe066205f83c0e106c700,0x291808c6e005f83c20d8,0x7038437200d44e0f0384,0x1c20dc5c76370f8217a2,0x370383c2148d85a30738,0x89c3a370781c20b9004a,0xc48380b43e0f086a30c9],#[0x18a04c361e87c1e07081,0x70730f8b44e0f0384182,0x8c1186c3d1381c1e106c,0x83638ce2fc48a0bf81c2,0x1e10d450261b0fc1e070,0x1b83c062f0b08580e8bc,0xc2118ac70da5e230f63d,0x31783c21592c7e004383,0x1c2a303cb1670020c70a,0x89431888552dc563f078,0xf0a9638ac7e0f0385840,0x221ec6c270383c2130f0,0x48087198bc1e07084c23,0xb2c210fc270781c2130a,0xa11453001fc5e0d1f842,0xc09b83c0e16102a589a2,0x8fc247c4c8878458dc52,0xe0f08262618469045f06,0xf8013e0c2f842b1c1f45,0x6e303f83c085f084c431,0x218b1687f078413130e1,0x8a8b71817c1e07084c23,0x95c17c641f042dc0e109,0xec0e284f8347e10aca87,0x4f8383e10d49134581,0x81c163f0836489a1ec56,0xe0f0826261c288fc251b,0x28dc0e0f084c58503145,0x247898718a591f450a61,0x383c20d9014a370383c,0xc0e11504c303f094663f,0xb91fc1e144c4c3e1383],#[0x1be3f04a9c247c4c820,0x302c37c1a3f038423278,0x1d83a2f068fc2499810e,0xe07091e4a451e2ae005c,0x926571c2e0ea2b1a8fc1,0x47f083649001f83e0f0,0x8ae8f1c9029e351f83c,0xc1e108c56486f8dc1e07,0x7084c231d154763c2f81,0x7c1e124c4042598dc1e0,0x1f078420498c23800630,0x8a1508f078458899018c,0xc231707c1e0708b0423f,0x823c0e0d1f841347960f,0xb2c7078513285458e289,0x3f85132c6820c1f038a2,0x38c4541ba3f178035e0a,0x23c710714b08fe0f0a26,0xfc215981be2f0781c22c,0x44c964ac2a8b4062f058,0x51771f8023e0f085648c,0xd78bc063f07842b2226c,0xc5a3f0781c28786c8898,0x85b8bc1637038431238c,0x223e331783c0e1098a0d,0x2f078026e10c478b2285,0x81c51a8af83c24995c66,0x6370781c21891151889b,0x30bc1e151da650982dc5,0x114f084c484180208ac4,0x384262a07076303f81c,0x2018530708b118d85e0f],#[0xb1f8453242183e0f08a6,0x4c7a995401015b0b83e0,0x99210a025d200ec1f078,0xca0080b185c1f058fc22,0x520ec2e0d8fc1e154c,0xc7e0f0921531d2e95485,0x6158f83e0f08a6608280,0x4202b12582b0d3801007,0x1510a0bf1817c1c1f038,0x72c15b0a20c1b1b83c0e,0x480e16c2e0f83c229880,0x8a656210016a3f078453,0x22b080a0803b0785e0f0,0x58714a2047c6c1f0781c,0x10298c20e370781c2481,0xf0784532c101863f0785,0x1c0e0f084048401d85c1,0x7092058230a29e260cb,0x83c21014c54408389c1e,0x6261f07c1e114c402e0f,0x3f0856591e23c1e07099,0xc134541e8c600478bc1a,0x5b8a266270781c2c3054,0xc0e0f082226286311079,0xf084c2924204762f1029,0x491899111083170dc0e0,0x104c4c360d2094a3f078,0x81c1e112c36405897c1e,0x25f078513130e17c331f,0x123c1e104e96261c2810,0x64c24783c0e152c4c3a6,0xe106c848f0781c2a5898],#[0xa26261c238663f03824b,0x363f0a2650b88023e0f0,0x4626535e801b88b17838,0x48b0281063f018bc1e10,0x8018137158fc1e104626,0x488578a0fe0f08ad1326,0xf8bc0e0d1f8413489631,0x5e0f0826262054561303,0x1783c289a4470a20c22c,0xc5e0e0f81c22b1016a3b,0xf038383e104cac58470c,0x3c248c4c81a2444c18e2,0xb70785132cac18e28578,0x2650d06220c1f038a2b2,0xa83747e07146bc148f0a,0x4710714adc148f0a2638,0x215901be2f0781c22b24,0x8565a528fc009b1783c,0x6251210ca3b1f80c5e0f,0x234009f1782c7e10aca1,0xa07158fc1e10aca13260,0xf83c0e14449132612b0c,0x108f084c405c1cc5a231,0x383c22b9018e251781c,0xc1e106d2248470cc4c1f,0xa47841b2429c4087028f,0x4912b914514f128fc0e0,0x124c58412037c4e0f038,0x83c2131614e00438fc1e,0x293014a2c43884708f03,0x47a23102345e07078426,0x408fc0e0f084c2c2530],#[0x13e2e0f83c21a9414e2,0xc70383c21316260c4458,0x85112829116295f88830,0x2037188af168fc162703,0xc9e23168fc1e07083711,0x4544dc0e28d457c1e124,0xdc58c45623c1e0709886,0x2f0781c21315831351f0,0x81c21312298c4470dc46,0xc1d4c98c4470dc462f07,0x6a6350036974af058bc2,0x1e1254a655018bc1e125,0x54a6589b8b83a006023c,0x8e0c6a2b0df038bc1e12,0x2d836351381c1e109891,0x62f0689c0e1098524b16,0x897c1e07082c26242f16,0x6e0f0385440a961741f1,0xf84352a2c1863715222,0x26244c188a9298ac0e0e,0x90830b51a89c062f0784,0x87c5a1f46e0707842614,0xe8ac51331b83c00af0a8,0xe10c4918a622c9187e0,0x504c386f0616e2f058dc,0xc0e1098ac1b1381c1e11,0xa4a14c0c30c46351783,0x4c45d22c66270781c213,0x223c5a370589c0e1454b,0x6e0f0217c21311830dc6,0x27c1e142c6a383f8c1,0x872c70781c2c5898661b],#[0x3130c170a22f85c18989,0x3850b0d8e8017707851,0xc3e0f082d132a8ec6e0f,0xf082d1324638007b144c,0x457c98e32c005d860be0,0xf08311324378061f078,0x31c18994c3c009b8a11e,0x1a903762e002ec30a708,0x86a3b0e27c5e00af83c2,0xe1098a89f0f802ee0f0,0x5880b43d8c43a370517c,0x162f8cc5a1f0781c2104,0x3015a2c3e87c1e07098c,0x6024e8b43e0f086a60c5,0x78493189031134561ec5,0x1e14584c38802a0fe2f0,0x5383c28989860a31b81c,0x170b02f83c2898987619,0x2898e40177078513130c,0x84c322041c32a7052dc,0xc1e10d480bf1a17c1e07,0xf0784352864c60bd0e17,0x6321c651761b01274385,0x161030505c17c3e0f092,0x305c582ac3e294783c0e,0x582ec56195385c0e0e10,0x84c450f83c21024c51bc,0x11a9011e261431c0e0f0,0x5036345181c309e1785c,0xc4e1704363d1f81c1e14,0x70781c20dc5c7c351f80,0xb46e070785170d8f85a2],#[0x2b012745a1f0784352f0,0x23c18c70926489a2b116,0xe070784262a86208af16,0x841182222c421d1030c5,0x2e08d4b62f1287c0e0f0,0xe374ba52874089b0d8bc,0x3627881721f0384261b8,0x8d178a7108345e07084c,0x88f1308170a70f84931b,0x5300ae910dd151e4258a,0xf10a024e1623130c924,0x68f20af13608dca8262c,0x488c61a0c45547601622,0x8031878d470dc5914c01,0xa00a52a90070c2a8aa29,0x8b185600812056298e97,0x962610acc010240b0531,0x4a24226c51609864c246,0x8c4c92ba0e2632258986,0x2240d0622aa3e0d80564,0x1a8f1286500af0f0db16,0x62ac4105515463118111,0xb8c31584c1888a488c44,0x4ad4c88c4444cc510581,0x62a2b1c521b4be0e8090,0x1ac5456412b06c01a8c,0x622b11620a312631306c,0xc1c39622651c58985c1c,0x62a09862ad1700292815,0x1580298b08c849c3d8b1,0x1560459262b1c6420453,0xd22ac08c24c5630d063],#[0x983181491158c445262,0x1888b144c20dc411162b,0x1]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x4042828000c6020000,0x80003002708420,0x18a3080210082049020,0x423000c012024000a3,0x100202004500000004c2,0x840100c8d3042008001,0xa1484200000120041,0x9843088001840500002,0x9c40004621800410060,0xac093246158c2600000,0x384fb4f06040121000a4,0x9690003ccb3788000000,0x3,0x74c4000109122000000,0xfa55ca30003a49c22800,0x5840000001a2e9410a32,0xa8000e63000000000004,0xac74f1bf29c59ace0024,0xb92,0x0,0xd2adc4c702400000000,0x45ed908000116463ec00,0x0,0x0,0x0,0xa9600039381129282000,0x63f8000000384944b8,0x7896e85b9b4000c60c0,0x17c9da30000000976400,0x851ec950001891,0x878510000000c0b40000,0xc0000000453728ac7a00],#[0xd2bc149d27000386e86b,0x10000000000008a40a2e,0x974340000003d630001c,0x626253226a49cbe6cd8f,0x458000271c000d5f0075,0xfda9e0000000a61c000f,0x25b90002c0655d000042,0x3153a708000000,0x5f5c408700035dd52b0,0x98df6,0x15d10000000000000,0x78a60e3,0x655db000000000010450,0x241aca4d92516,0x0,0x1a64000d01f5070000,0xf000000000000000000,0x93a40000002d20000000,0x7bad09b88f13e55e8000,0x81ce550a70ad698e03a5,0x57352dc000596c00022,0x48b40000000000000,0x907c0004aa00000000,0x3cbb000000000000,0x247499600020db000000,0x74b56a5704c041,0xf46a4fac9680000,0x4186518fe03f35c00000,0x48cfa620000000b8f,0x5297d89eb000014ff77c,0x54a318eb58ac2e00001,0xda5c0004950248a9b000],#[0x30c000881000066a356c,0x4431a8a396,0x3517a08993700024b300,0x51ec9140000000000000,0xd29862c8490000aa0d,0x85ff24d4a77c2600000,0x2df00000000250000,0x7bf93f0002a88d763608,0x6cf058000819cd467,0x0,0x2246e238000000,0x38f26a700000005318,0x39a568240,0xe5040000000000000000,0xe1900000000000,0x36fc000064ea940,0xc0000000e43000000000,0x12d800000035ca906,0xf17400000000000000,0xe0000000c8d800000000,0x35f3452227,0xd9c0000,0x0,0x0,0x13a00000000000000000,0x85f75800000000000001,0x2da0000000000030,0xd9d55a38de000000,0x83c0000003d0a3606a7b,0x7200dd15ae1e9514cf5f,0x35dae26c0002344000e3,0x1549000000022f],#[0x8f26f400000000000000,0x212c0cdf960a,0xf34000,0x3726a74c008000,0x6c00008c4000347141c0,0xf57c58500021ba25,0x31a725941698e6000,0xfd000000000000000000,0x446624cab19a1e800015,0x287647b766,0x1ef97662940000000000,0x2e7700000003,0x8000e0c0000000061800,0x72f,0x0,0x70000000000000046f00,0x161bf466d7,0x2db10000000000344d,0x187c41d49700000,0x40000000000693800000,0x5b700000000000000286,0x20d8000759e96a0000,0x8718000000018ef00000,0x33101130001c55246c0e,0xc2c304600025b5,0x21e4528400000004d40,0xa9fc000e67c00000,0x450c0498590001e84000,0x8450,0xa000000091cb93b00000,0x3a2,0x68980000000000],#[0x8b1000344e00000000,0x7cf2001400000018ff00,0x2680000000000186529e,0x2,0xe84bc14089000000000,0x315ce9f5650000000,0x29430001a270000000,0x29d0000000060200000,0x59c0002a14000000000,0x0,0x35500000,0x80dc00000000,0x0,0x920c000000347e,0x0,0xd1fc000000066a00,0x20aa0000000000,0x46b8,0xb7380000003862e99c0,0xe37400,0x3dc00000000000000000,0x900000002134a688000a,0xc000000244841dc000fa,0x90308c000d9f1ce4579,0x33f798000000343946b6,0x126e7a9800000001,0x1cfe33c000000000,0x5e30000000,0xf43000000000000,0x0,0xe0d743df954000000,0x630800069e0],#[0x900000000003c8200000,0x7872a06c97400000008c,0x44080003624000,0x2291b5e021500000000,0x64b000000000,0x873e2300009533d92000,0x2,0xf55400081f000000000,0x573000058ac00087dc00,0x39a600034718064000,0x20f62a8800000000000,0x80000000000f42c00000,0x62100001e50003159f82,0x8cd70c0001220000a569,0x1911000000000026,0x595c0000000000000000,0x5ad00a00000000000000,0xc00da000198876e00009,0x296d19c61940002e86b3,0x0,0x524580000000185e0000,0x30000000417c000540f6,0xcd3c830e01000021,0x0,0x300002a7e590c6440000,0x40000000000f547831d0,0x5b59a,0x28b8e2641a70000,0xb10fad0100019cd00000,0x21c600000000002e3,0x225c9700000000000000,0x2427216000000000007],#[0x246d0000000048814a00,0x43f4000000,0x86384385700000000000,0x90002535000291f00018,0x8c000071e4000b2b8a8,0x3cec00000000003c04,0x58000000000000000000,0x20ed0000000360800029,0x503d698e2a,0x13d00000000,0x10000000000000000000,0x60f0000452fcc,0xb2bc000,0x382b927c00000000000,0xc85c640e51000000,0xdf10000000000282f000,0x1,0xad0b000096eea4115b80,0x4989d300014e,0x7e800000000540002d58,0x4,0x8454000000000000,0x965c0000000000000,0x84f82f8e746d80000000,0xaa8400077d795ee4865,0x862c0000000000000000,0xa8c0001999e3e0000000,0x7c000a90800000000033,0x6c7000028b4000000089,0xe28f29c0000000000e41,0xce000166000015750002,0x100025a4000000000018],#[0x43ac5300000000275e41,0x0,0x1d50002d2f00000000,0x54e4000000000000,0x45c09440000000000000,0x4f000061d00001fc6a6e,0x24b504a72,0xb2000000000000000000,0x59800000022116063825,0x1120000d0f23cda3f6,0x18cc00,0xa3a00000000000000000,0x9322,0x983400000000,0xb2480000000000000000,0x523795d0000000,0xb9940000,0x4000000368d9103cd200,0x10320000000838,0xa0000000000000000000,0x2000000000034d55723e,0xc44000000021dee5c19b,0x3195,0x16720001da100000000,0x80000000000000000000,0x810000000931d49495c,0xfa2800000000000771,0xe57ecd23d07bcd900000,0x562849,0x3e000080d2084e37e29a,0x46802f5038a,0x35f80000815455a8eed3],#[0x3710c0ee40007d000,0x126f7668,0xa5bc000b808000d7a80,0x9abb05c00,0xa6340000000000,0x6c20ba0,0xa9420000000d933a8e00,0x114de41,0x80a270e1af66f5184360,0x30000000531643f811e6,0xc22da7,0x9e800000000000000000,0x1287000000000000002,0x7c4200034e02a4800000,0x1dc10002607d98,0xe2f71448f0000,0xa6d00000002e3800000,0xd7d0000000000000,0x67800017d0000a78614e,0x4ea340000000c8d4000c,0x2a0400089,0x87500000000000000,0x1d3d62740000000,0xf8580,0x39780003080000000000,0x0,0xf8000000000000002760,0x4000e6039570003dd286,0x80b000000067f800077e,0x289361ac,0x24fc00000,0x0],#[0x71875c05258000,0xcb001000102800000000,0x2e0e00010d6000000032,0x152c0000000000,0x0,0xe0000000000000095940,0x283b0000000e889d7,0x0,0x24b90,0x46a8000000000000,0x1e0a2a40000000000000,0x863d,0x80a800000000,0xdac491c0007a4000,0x23c4000910c979,0x40cc00000000000,0x3c9a47fc000000000000,0x2551878b7a4000000,0x44000000017b0000f9d4,0x3e,0x150ea8bc000b4d800]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xe0564df5765c77d5d171,0x503fe5c140ff960502fd,0xfbd74503ef55140ff571,0x61940bff85502ff61540,0x502ff61d40bff86502ff,0xff571543fe5c150bff87,0x5d550bff84543df55150,0x542ffe1950bfd86543df,0xff970582ffe1d50bfd87,0xe1160efd64583fd5c560,0x582ffe1560efd65582ff,0xbff87582ff61d60efd76,0x5d570bff845c37f5d170,0x5c6ffe1970bff855c37f,0xfbd74553fd59571ff554,0x61954f7d75553df59554,0x593ef5d164bfd87552ff,0xbff805d2ff61d64efd76,0xe1974dfd765d2ffe1574,0x596ffe1165bff80596ff,0xbfd87597bf5d965f7d75,0xe1175bff805d6ffe1d65,0x5daffe0176bff865d6ff,0xffd65502ffe1576bff84,0x5d940ffd85503ff5d540,0x543ff61d40ffd86503ff,0xffd84543ff5d150ffd64,0x61d50ffd86543ff5d950,0x583ff5d160ffd54583ff,0xffd85583ff5d560ffd84,0x59170ffd545c3ff61d60,0x5c3ff59570ffd845c3ff],#[0xffd76553ff61970ffd85,0x59574ffd805d3ff5d564,0x597ff61974ffd855d3ff,0xffd87597ff61165ffd80,0x61975ffd845d7ff60175,0x5dbff61176ffd805dbff,0x806101f007c000ffd85,0xb3051c2280ed06502ac1,0x4a82290ff077c3601910,0x1a90c6c5f02c514d09ec,0xc8483f91ed0edc730371,0xd281137c970499235110,0xdcba85b12c715cca9852,0xe135b1a4cce064530f17,0xe7cf007613a31c7ce006,0x885433211d0507f53e51,0x25ad268901471231d150,0x8a7151d283d3c89bd4c9,0xd2dcd690b215792b2d52,0x50c75625309d800bd15c,0xd7360dab0d35683334d9,0xd40e7972b38bdc10ddd6,0x131fdbde90f2177b3b4d,0xf07084c70716c5c3c1c2,0x3860884c1c2201c63170,0x443f1f1707084c8c7c5c,0xfc6c584c1c0c2472700,0xb223f160f051f084c715,0x91c9c7c60f83c1c0c20,0xc20b30583f1b160f0703,0x100f082307c68320c1c0,0x2132b1f19170703083c7],#[0x4c7110f2bc0c7c583c1c,0xc1c0c22f031f1707083c,0x83c716150fc6c5478483,0xc1c2472b1b151f07030,0x7094ca201510c6c485c,0xc20b25008241360e151f,0x308407c7c60e1083c1c0,0x3c0c1c2472b1f1913070,0x17070308cc6c417100e8,0x10205044401f10811a0e,0x308a4d08c7c446c1c0c2,0xc54403a0d1e171b13070,0x1c9c6c447c1c0c2101c5,0x131c544713161b070309,0xf07084c89183c547c1c2,0x5c1c211131f1f0047160,0x1f111703070a0cac0c7c,0xc445c1c0c2111c6c5047,0x4713160f0703091c9c7,0x1c5c4834786c1c0c22c6,0x17111f07030844718151,0x1615c6c5c144c0c28327,0x3289b1b1513070308548,0x71b1715c6c4c045c1c28,0xc215271b111703070854,0x84d2c62608c5c446c1c0,0x5c387c1c213210e1f070,0xc591f0703082c820544,0x1483c00bc1c22613231b,0x71b0c385d1f0307082c9,0xa140b0703c0c1c226132,0x5c580f186d1f0703082c],#[0xc880c5c31647c1c21320,0x2132a03170c611f07084,0x587181635c0c5c347c1c,0xc0c2161f1b150f070308,0xd1b070b02109c6c345c1,0x5c3c1c2161318605b170,0x131f1f110f070308507c,0x30b051cac0c7c3c1c214,0x2c1472b105c503b0e1b0,0xb04c201814c4c385c0c,0x605c500e17111e186f03,0x85c7c4c347c0c1c2141c,0xc1c2171f1b110f03070,0xd1b0307085c8c6c344c,0xc5c443c1c0c2181c2313,0x1c2181f170f0708604c6,0x146f07084ccc4c345c0c,0xc21b343f0150523f1e0d,0x8f0f57c6834584c1c047,0x3c2f1f1b0703088c917,0x8188fc54783c1c213284,0x3f031c4f170708ac90f5,0x15c6c547c1c0c20f2844,0x3031e160f07094ca3116,0x4483c1c0c2203640384,0x8808c856101685c6479,0xc1c0c22034403c2f0703,0x958108518c447904683,0x92d1050451b030708408,0x71510c647c40ec0c1c22,0x4700471e0f07084d2c91,0x561691c54783c1c2132a],#[0x43f031c4f170708ac911,0x4835786c047c1c21b344,0x9b07030844b17911145c,0xc0c21124b050411f1114,0x3092c9881815c4c547c1,0x7c183c2532a1a0c57070,0x7030854c26954015c58,0x2628c60c583f189b1513,0x8c1545c4148346c0c1c2,0x4420f191710a70307089,0x6c5c446c1c0c2152c5c5,0xd1f0b062c4c88318112,0x17c34547c1c293296063,0xb150f07030858a570e80,0x74520c2c1132cc4543f1,0x7030858a96141654c38,0xc1c23524c85d0f18982f,0x70850809181640c5c313,0x1c21320204441110f030,0x30b04506c9140b401bc,0xec0c1c22930605d111f,0x85c6c8171510c685c443,0x2c1171b2859182f03070,0x3086091814854446c0c,0xc1c23524544717110f07,0x30b0460b181640c5c313,0xdd145d0f10509b0]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x11010000100000c02,0x2000092590410000800,0x61000800008104308b04,0x1048000000000248,0x0,0x0,0x61800,0xe8ca9200000000000000,0x0,0x65840000005328001afc,0xaa98000000000000,0x1247113000000,0xeba0007870001c0c00,0xe5380000,0xdf2000000149519c0000,0x13eb,0x144a0000000000000000,0x0,0xf45000000000,0xeac00000,0x1260000118d2e40000,0xed2dbe80000000000000,0x1,0x80000000000000000000,0x317,0x754800000000,0x388003de400000000000,0x6,0x0,0x22fc000000,0x0,0x195a00000009cc00],#[0x0,0x0,0x1925d20000001b330000,0x196de070003a3e,0x0,0x231800000,0x298c00000,0x3d80000000000004b340,0xa,0x115813ee53c,0x20e8000000000,0xd23000000063fd55000,0x86e56000416998000000,0xf5ec26c0000000005c,0x1613a37b6600000,0x60a80000000000000,0x4e00000,0x0,0x0,0x1f7500,0x4e800000027f00000000,0xe620000000000000000e,0x1ce40000000000000,0x12bc000000,0x0,0x2ad200,0xf3f00000,0xee848f00000000,0x2aba0000000,0x2068,0xc0000000000000000000,0x1b8000000000000021b],#[0x11400004d1df4400000,0x0,0x0,0x0,0x217c000c468000c89ce3,0x8507a50b3e000000000,0x0,0x35000000000000000000,0x12c00000000000000018,0x7320000005,0x0,0x1c02000,0x0,0x593bf1471100,0x0,0x1ca00000000000,0x4b800000000017a0000,0x628c0000148000000000,0x2c5,0x0,0x5d00041a800122200000,0x12,0x0,0x252c0000000000000000,0x44d000,0x0,0x5b80010b200,0xe7280000,0x1bd800000120b0,0x6a500000000000000000,0x0,0x0],#[0x383400,0x0,0x3e0c000d448000e040,0xccb80000000000000,0xdb60000000000000,0x0,0x9800315000011d000000,0x16f80000003e7600024,0x3aaa780000003c780000,0x9573480000000000000e,0x8850000000000bb30001,0x1012000122c000000,0x0,0x0,0x0,0x47000000000000,0x186c0000,0x51858e0000000,0x0,0x20000000000000232800,0x23,0x21cc000000e9480000,0x0,0x0,0x1e560000000000000,0x3a6a000000000,0x0,0x15f00000,0x3b291e0000005a0c0000,0x7,0x80000000d40000000000,0x6000000000000000087b],#[0x2f2,0x0,0xcae00011400000,0xc2100000000000,0x34580000000000,0xa479590628000000000,0xe9b83cc000000000000,0x41000021e5a9800,0x0,0xe4300000020b20,0x95a0,0x8002183727000686c000,0x819,0x0,0x7d086842000000000000,0x2a,0x29ac0000000,0x0,0x3a8a00000045500010b7,0xe0000000000000000000,0x2d80000f4b0001afe47,0x129aa7480,0xc680004c30003cc80000,0xf7780009040000005,0x1948000,0x3cd8000000000000,0x6050000000000000000,0x1ce16d0000000000000,0x0,0x0,0x0,0xf3c0005cd79dc000000],#[0x598ca3584a6000000000,0x649e0,0x109200000000,0x65d80000,0x82b00000000000009af0,0x1f38a820003d32,0x0,0x26c8000000000000,0x0,0x0,0x71700000000,0x662c0000000000000,0x0,0x10f8000000000000,0x0,0x0,0x0,0xcf00000000000,0x800000000000005a34aa,0x26c,0x3664bd800,0x0,0x9d0000000fb600000,0x3140,0x241ba5a0006570,0x1c940000000000000e54,0x54c000,0x0,0x59688000000e8700000,0x22300001,0x28780000000,0x1f730000000000],#[0x2b6000d0b,0x18000ede000000000000,0x1d677b,0x55400000000000000,0x0,0x0,0x0,0x0,0x11738000000000000000,0x63,0x0,0x7c0000007898,0x325c,0x0,0x0,0x2a2e00000,0x2a180000,0x0,0xce20000000,0x0,0x243d960000000000,0x330600,0x0,0x20400000000065a80000,0x7,0x150400098c0000000000,0x57805dc00070c000,0x78002b4a0000001c6c00,0x4440000000000e0,0x53900000,0x89d34c0000,0x0],#[0x1418,0x2100000000000000000,0x3448000000000028800,0x4b2c00000000000,0x9a100000000000,0x0,0x0,0x6dd0000e69000,0x600e44da000000000000,0x76e0000000e48f2,0x534a9362000000000000,0x0,0x26c0007c08000,0x1aa0000000000000000,0x70000000000000000000,0xd52000b6b8000001d8,0xd0b2e400000,0x3da000000000000000,0x0,0x1200000,0x0,0x131a000000000000,0x84000000000263ab0100,0xc1eab88003d,0x3cce0000,0x70500000000000000424,0xf0b0000000000000,0xe0000000000000000000,0xa88001af,0x11e800013800000000,0xb1c00198500000000000,0x5],#[0x11420000000000000,0x2606000000,0x298400,0x100000006e466d774d00,0xe5d80007,0x80800000000000005960,0x63680000000000000,0x5160000000e742ff,0x554f8000000000000000,0x380e000000000000104,0x517e90000000000000,0x886ec000000,0x9700000000,0xd600000000000,0x0,0x0,0x577000000000000,0x27800000000000000000,0x36ae0000,0x53f0,0x0,0x705c000000000000,0x0,0x0,0x0,0x39f9b00000000,0x8d594f00000000000000,0xcbd3a8c000b26808,0x78000001562000562400,0xd1b800f5a6000b9,0x3825ae4000b3400000,0x3864b120],#[0x620800000000005b04a0,0x24b718400046408a16c9,0xa0000000000000000000,0x8a70000000c2,0x64b4e0e00000000,0x0,0x40000000000,0x13650000000000,0x115a000000,0x0,0x0,0x7ad5e40,0x137044a800332a0000,0xf598000d200000000000,0x2644d2a00036a0000000,0x0,0x0,0x76e800000000073e00,0x4b00000,0x0,0x11a70000000000,0xac80000000000000000,0x0,0x0,0x3c70f9d00000000,0xf0300000000000,0x0,0x2b50000000000000,0x32f0000000000000000,0x0,0x1b8e00000,0x2000000000073f40000],#[0x0,0x6a940000006750000000,0x0,0x0,0xedf000000000000000,0x0,0x12f80000,0x32c00000000000000000,0x2d40000000,0x0,0x0,0x0,0x24d31620,0x8476660000,0xceb0000000c42,0x25f0000000000000000,0x0,0x24000000000000000000,0x61800000000000015,0x15c00000001d80008620,0xd7680000000000000003,0x30320000000000000000,0x0,0xc5c00,0x61000000000,0x135100000000000,0xe5100000000000000000,0x20ec0000000000000000,0xb3d0000000000000000,0xb46a4000000000000000,0x1c000000000000000061,0x25e200043700025],#[0x127a47d80000000000,0x34880038000000000000,0x684000e870003b04000,0x2c80000000000000,0x2f000,0x67800000000000000]]
def g255D12 := limbs80 #[#[0xffac1ff543fea07f571,0x65ffae9ff593feaa7fd7,0x1061f001ff5dbfebaffd,0x51f2540ae0312a921a64,0x2112006c5861e093844,0xb06042247c78d1420383,0xc0e0c0844908f1a2030,0x5881c1c181089231e245,0xc78f1a1c1810858e5634,0x120c2804c08f161c1844,0x6182c0830892d1a2c30e,0x890c3858106112523c48,0x88b121870d0614024bc6,0x1]]
def g255H12 := limbs80 #[#[0x94822027b0144129808,0x22812621412001729e60,0x800000348002b10860b,0x584c16f4000170018573,0x1e440061d4c9b575cc,0x5f46acd9ad31c9e97800,0x129fe90000c819b8a909,0xb100002800000401a3c2,0x8008840024b5d618c8ab,0xd00136c0032d00000382,0x338cc001aeca80039aed,0x22d87238d74834005a43,0xc0000000000000000001,0x80031e003a700007913,0x91364000001424e,0x101946000061670000,0x7f35c3800000820001b2,0x9a9800fb5f03d0da864,0x5dc4777d44e2f8006bd6,0x8afab83644b602,0x300147f4dca2b9753000,0x6958dee000e92d97c968,0x1228002]]
def g255D13 (j : Nat) := if j=0 then 0x7185103040088ff else 0
def g255H13 := limbs80 #[#[0x109400f500d300d60000,0xb21900000000000000,0x0,0x17000a,0x9100000000,0xb8]]
def g255L : Nat → Packing
  | 7 => (25,6,6,0,0,9,0,g255D7)
  | 8 => (323,5,6,0,0,14,0,g255D8)
  | 9 => (681,4,6,0,0,16,0,g255D9)
  | 10 => (426,3,6,0,0,15,0,g255D10)
  | 11 => (102,2,6,0,0,13,0,g255D11)
  | 12 => (11,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 41 3 9 5 0 g255H8
  | 9 => lookupWord 80 397 9 13 9 0 g255H9
  | 10 => lookupWord 170 1709 5 14 10 0 g255H10
  | 11 => lookupWord 106 2179 3 13 9 0 g255H11
  | 12 => lookupWord 25 151 5 11 7 0 g255H12
  | 13 => lookupWord 2 59 0 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_37 : block g255 9 37 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_35030
